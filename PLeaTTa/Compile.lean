-- SPDX-License-Identifier: Apache-2.0

/-
PLeaTTa compile equations (see PETTA-LP.md §2). Definitional: this function
is PART of PeTTa's semantics — PeTTa is defined by compilation to definite
clauses. Flattening is the classic functional-logic transform: nested calls
become prefix goals with fresh result variables; function calls in PATTERNS
flatten the same way (head narrowing). `Atom`-typed argument positions pass
syntactically (PeTTa's compile-time evaluation-point commitment).

Unsupported forms are loud `Except.error`s: each is a spec gap to close HERE.
-/
import PLeaTTa.Types
import PLeaTTa.Chain
import PLeaTTa.PeTTaUnification
import Std.Data.String.ToNat

namespace PLeaTTa

open Metta (Atom Subst)

/-- Compile-time environment: defined rule heads, builtin membership, and
    the per-position `Atom`-typed staging mask from type declarations. -/
structure CEnv where
  defined : List String
  /-- Translator hooks registered before the current source event. Pure hook
      calls are staged as an ordinary call followed by live `eval`. -/
  translatorRules : List String := []
  /-- Functions registered from a Prolog source module. Calls lower through
      the explicit `translatePredicate` host boundary, including calls created
      later by meta-circular `eval`. -/
  prologFunctions : List String := []
  /-- Source-registered function arities, counted as MeTTa input parameters
      (Prolog predicate arity minus the output slot). -/
  arities : String → List Nat := fun _ => []
  isBin : String → Bool
  /-- `atomTyped f i` = argument `i` of `f` is declared `Expression`
      [SPEC translator.pl:354-363] (pass as data input). -/
  atomTyped : String → Nat → Bool
  /-- The declared arrow chains of a head (each = param types ++ [return]);
      typed heads dispatch per chain with get-type checks
      [SPEC translator.pl:310-317, 341-363]. -/
  typeChains : String → List (List Atom) := fun _ => []
  /-- Top-level bangs are compiled before earlier runtime `add-atom` effects
      execute, so unknown atom heads need runtime dispatch there. Rule bodies
      are translated when the rule is asserted; unknown atom heads are data
      at that translation point [SPEC translator.pl:302-326]. -/
  dynamicUnknown : Bool := true

abbrev CompileM := Except String

/-- Strict identity used by pinned `list_to_set/2` after `findall/3` has made
one fresh copy of every matching declaration.  Closed equal chains are
duplicates.  A chain containing a logical variable is never identical to a
different `findall/3` answer, even when the two declarations use the same
source variable spelling. [SPEC translator.pl:317-321] -/
def sameCollectedTypeChain (left right : List Atom) : Bool :=
  (left.flatMap Atom.vars).isEmpty &&
    (right.flatMap Atom.vars).isEmpty && left == right

/-- Recognize one matching arrow declaration without copying or deduplicating
its type chain. [SPEC translator.pl:317] -/
def declaredTypeChain? (head : String)
    (declaration : Atom × Atom) : Option (List Atom) :=
  match declaration with
  | (subject, declaredType) =>
      if subject == Atom.sym head then
        match declaredType with
        | Atom.expr (Atom.sym "->" :: types) => some types
        | _ => none
      else none

/-- Ordered `findall/3` candidate extraction before `list_to_set/2` removes
strictly identical closed answers. [SPEC translator.pl:317] -/
def collectRawTypeChains (decls : List (Atom × Atom)) (head : String) :
    List (List Atom) :=
  decls.filterMap (declaredTypeChain? head)

/-- Collect the arrow chains declared for one function head and reproduce the
first-occurrence `findall/3` plus `list_to_set/2` behavior.  Closed duplicate
declarations collapse; open declarations retain occurrence multiplicity
because their Prolog variables are fresh per collected answer.
[SPEC translator.pl:317-321] -/
def collectTypeChains (decls : List (Atom × Atom)) (head : String) :
    List (List Atom) :=
  (collectRawTypeChains decls head).eraseDupsBy sameCollectedTypeChain

def mkEnv (isBin : String → Bool) (heads : List String)
    (arities0 : List (String × Nat))
    (decls : List (Atom × Atom)) : CEnv :=
  let arities : String → List Nat := fun f =>
    arities0.filterMap (fun (g, n) => if g == f then some n else none)
  let atomTyped : String → Nat → Bool := fun f i =>
    decls.any (fun (s, t) =>
      s == Atom.sym f &&
      match t with
      | Atom.expr (Atom.sym "->" :: tys) =>
          (tys.getD i (Atom.sym "?")) == Atom.sym "Expression"
      | _ => false)
  let typeChains : String → List (List Atom) := fun f =>
    collectTypeChains decls f
  { defined := heads, arities, isBin, atomTyped, typeChains }

/-- Recognize the source form registered as a function by pinned
`filereader.pl`'s first pass.  The stored arity counts MeTTa inputs; native
PeTTa adds the result slot when asserting its Prolog `arity/2` fact.
[SPEC filereader.pl:20-23] -/
def sourceFunctionArity? : Atom → Option (String × Nat)
  | Atom.expr [Atom.sym "=", Atom.expr (Atom.sym head :: parameters), _] =>
      some (head, parameters.length)
  | _ => none

/-- Source-ordered function/arity table shared by both compiler entry points.
Keeping this pass explicit makes the loader registration algorithm available
to soundness and completeness proofs instead of duplicating mutable loops. -/
def collectSourceFunctionArities (atoms : List Atom) :
    List (String × Nat) :=
  atoms.filterMap sourceFunctionArity?

/-- First-occurrence order of the source-registered function heads. -/
def collectSourceFunctionHeads (atoms : List Atom) : List String :=
  (collectSourceFunctionArities atoms).map Prod.fst |>.eraseDups

/-- Executable spelling of one compiler-generated logic variable. -/
def compilerGeneratedName (n : Nat) : String := s!"_q{n}"

/-- Recognize the exact numeric namespace used by compiler-generated logic
variables.  Leading zeroes are accepted conservatively: source `$_q025`
therefore reserves the same numeric slot as generated `_q25`. -/
def compilerGeneratedIndex? (name : String) : Option Nat :=
  match name.toList with
  | '_' :: 'q' :: digits => (String.ofList digits).toNat?
  | _ => none

/-- The first generated index strictly beyond this source-variable name. -/
def compilerSeedHighWaterName (name : String) : Nat :=
  match compilerGeneratedIndex? name with
  | some index => index + 1
  | none => 0

/-- The first generated index strictly beyond every listed source variable. -/
def compilerSeedHighWaterNames : List String → Nat
  | [] => 0
  | name :: names =>
      max (compilerSeedHighWaterName name) (compilerSeedHighWaterNames names)

/-- The generated-variable high-water mark of one source atom. -/
def compilerSeedHighWaterAtom (atom : Atom) : Nat :=
  compilerSeedHighWaterNames atom.vars

/-- The generated-variable high-water mark of a source-atom collection. -/
def compilerSeedHighWaterAtoms (atoms : List Atom) : Nat :=
  compilerSeedHighWaterNames (atoms.flatMap Atom.vars)

/-- Preserve the caller's allocation supply while advancing it beyond every
source variable that occupies the executable `_qN` namespace. -/
def compilerFreshCounterForAtom (counter : Nat) (atom : Atom) : Nat :=
  max counter (compilerSeedHighWaterAtom atom)

/-- Collection form used by rule compilation. -/
def compilerFreshCounterForAtoms (counter : Nat) (atoms : List Atom) : Nat :=
  max counter (compilerSeedHighWaterAtoms atoms)

def fresh (n : Nat) : Atom × Nat :=
  (Atom.var s!"_q{n}", n + 1)

/-- Distinct variables occurring in one declared arrow chain, in their first
occurrence order.  Native PeTTa obtains a fresh copy of every chain through
Prolog's `findall/3`; making that copy explicit prevents type variables from
aliasing source variables or variables in another overload branch.
[SPEC translator.pl:317-324,349-370] -/
def compilerTypeVarNames (chain : List Atom) : List String :=
  (chain.flatMap Atom.vars).eraseDups

/-- The finite substitution used to make one declared arrow chain a fresh
variant.  Repeated occurrences share one generated variable, while distinct
source variables receive consecutive compiler-owned names. -/
def compilerTypeFresheningSubst (counter : Nat)
    (chain : List Atom) : Metta.Subst :=
  (compilerTypeVarNames chain).mapIdx (fun index name =>
    (name, Atom.var (compilerGeneratedName (counter + index))))

/-- Produce one branch-local fresh variant of a declared arrow chain and the
first unused compiler counter.  This is executable compiler machinery rather
than a proof-only copy; its laws live in `CompilerTypeFreshening`. -/
def freshenTypeChain (counter : Nat) (chain : List Atom) : List Atom × Nat :=
  (chain.map (Metta.Subst.apply
      (compilerTypeFresheningSubst counter chain)),
    counter + (compilerTypeVarNames chain).length)

def compilerTrueA : Atom := Atom.sym "True"
def compilerFalseA : Atom := Atom.sym "False"

/-- Canonical impossible goal used where pinned Prolog emits `fail`.  Its two
closed symbols are distinct; `PrologCoreAdequacy.unifyB_true_false_none`
proves that the executable unifier rejects this equation under every binding. -/
def compilerFailureGoal : Goal :=
  Goal.eq compilerTrueA compilerFalseA

def compileBinArity : String → Option Nat
  | "=" | "==" | "!=" | "+" | "-" | "*" | "/" | "%" | "<" | ">" | "<=" | ">="
  | "min" | "max"
  | "and" | "or" | "cons" | "cons-atom" | "member" | "is-member" | "union-atom"
  | "intersection-atom" | "subtraction-atom" | "exclude-item"
  | "index-atom" | "=alpha" | "is-alpha-member" => some 2
  | "#test-results" => some 2
  | "not" | "car-atom" | "cdr-atom" | "last" | "size-atom" | "repr" | "parse"
  | "repra" | "unique-atom" | "list_to_set" | "msort" | "println!"
  | "Predicate"
  | "add-translator-rule!" | "remove-translator-rule!"
  | "is-ground" | "is-expr" | "is-space" | "argv" => some 1
  | _ => none

def partialValue (f : String) (args : List Atom) : Atom :=
  partialC f (chainOf args)

private def chainListC : Atom → Option (List Atom)
  | Atom.gnd (.external "PLeaTTa.internal" "nil") => some []
  | Atom.expr [Atom.sym "#c", h, t] => (chainListC t).map (h :: ·)
  | _ => none

private def partialValue? (a : Atom) : Option (String × List Atom) :=
  match partialView? a with
  | some (f, boundList) =>
      (chainListC boundList).map (fun bound => (f, bound))
  | _ => none

/-- A nested Prolog condition preserves bindings for every source variable it
    mentions. `Goal.softcut` replays one template value into the caller, so
    the template must carry those variables even when they occur only in the
    condition's generated goals and not in its result term. -/
def bindingTemplate (base : Atom) (sources : List Atom) : Atom :=
  let vars := (sources.flatMap Atom.vars).eraseDups
  chainOf (base :: vars.map Atom.var)

/-- Source-faithful ordinary Prolog if-then-else, `(Condition -> Then ; Else)`,
expressed through the demand-driven soft-cut kernel.  `onceg` commits the
condition to its first answer under its own cut barrier; the surrounding
streaming soft cut transfers exactly that answer's template bindings and
suppresses `Else` even when `Then` subsequently fails.

Keeping this as a structural composition rather than a mode on `Goal.softcut`
prevents ordinary `->` sites from accidentally inheriting `*->`'s remaining
condition answers. [SPEC translator.pl:151-183,399-406] -/
def committedIfGoal (template : Atom) (condition thenGoals elseGoals : List Goal) :
    Goal :=
  Goal.softcut template [Goal.onceg template condition template]
    thenGoals elseGoals

/-- Source-faithful Prolog negation-as-failure, `\+ Condition`.  The committed
condition probe stops after its first answer; success enters an explicit
failing branch, while exhaustion selects the empty success branch.  Condition
bindings are therefore discarded, cuts are call-local, and persistent world
effects remain threaded exactly as for `\+/1`. [SPEC translator.pl:171-172] -/
def negatedGoals (condition : List Goal) : List Goal :=
  [committedIfGoal (Atom.sym "#negation") condition
    [compilerFailureGoal] []]

/-- Whether pinned `translate_args_by_type/4` emits a post-translation
`get-type`/`get-metatype` check for this declared type. -/
def typeRequiresCheck : Atom → Bool
  | Atom.sym name =>
      name != "%Undefined%" && name != "Atom" && name != "Expression"
  | _ => true

/-- Whether pinned `typed_functioncall_branch/8` checks a declared result
type. Unlike input staging, `Expression` is an ordinary checked result type;
only `%Undefined%` and `Atom` suppress the result check.
[SPEC translator.pl:349-356] -/
def resultTypeRequiresCheck : Atom → Bool
  | Atom.sym name => name != "%Undefined%" && name != "Atom"
  | _ => true

/-- Carry declared type variables out of the committed type-check subrun.
Concrete types retain the historical `#u` template exactly; an open type uses
the shared binding template so an input check constrains the same fresh type
variable later observed by the result check. [SPEC translator.pl:349-370] -/
def typeCheckBindingTemplate (expected : Atom) : Atom :=
  if expected.vars.isEmpty then Atom.sym "#u"
  else bindingTemplate (Atom.sym "#u") [expected]

@[simp] theorem typeCheckBindingTemplate_sym (expected : String) :
    typeCheckBindingTemplate (Atom.sym expected) = Atom.sym "#u" := by
  simp [typeCheckBindingTemplate, Atom.vars]

/-- Shared construction of the generated type/meta-type soft-cut. Argument
and result positions choose different source-faithful policies below, while
the emitted goal and counter behavior remain defined once. -/
def compileTypeCheckWhen (requiresCheck : Bool) (value expected : Atom)
    (counter : Nat) : List Goal × Nat :=
  if requiresCheck then
    let (directType, nextCounter) := fresh counter
    let (metaType, finalCounter) := fresh nextCounter
    ([Goal.softcut (typeCheckBindingTemplate expected)
       [Goal.bin "get-type" [value] directType,
        Goal.eq directType (chainify expected)]
       []
       [Goal.bin "get-metatype" [value] metaType,
        Goal.eq metaType (chainify expected)]], finalCounter)
  else
    ([], counter)

/-- Compile the ordered type/meta-type fallback used for refined argument and
input types. This is outside application dispatch so its exact goal and
fresh-counter behavior is kernel-visible to adequacy proofs.
[SPEC translator.pl:356-370] -/
def compileTypeCheck (value expected : Atom) (counter : Nat) :
    List Goal × Nat :=
  compileTypeCheckWhen (typeRequiresCheck expected) value expected counter

/-- Compile the output-position type/meta-type fallback. The distinct policy
is source-significant: `Expression` inputs remain data, but an `Expression`
result is checked. [SPEC translator.pl:349-356] -/
def compileResultTypeCheck (value expected : Atom) (counter : Nat) :
    List Goal × Nat :=
  compileTypeCheckWhen (resultTypeRequiresCheck expected) value expected
    counter

/-- PeTTa's `build_branch/4` aliases a variable-valued branch result to the
enclosing result while translating a nonempty branch conjunction. Native
Prolog sharing makes that alias visible outside the selected branch. The
first component therefore reifies the translation-time alias as a logical
equality before condition execution. Keeping the original branch goals makes
the normalization explicit: the equality, rather than an implementation-side
rewrite, carries the alias into every surrounding occurrence.
[SPEC translator.pl:394-397] -/
def compileBranch (out : Atom) :
    Atom × List Goal → List Goal × (Atom × List Goal)
  | (Atom.var name, goals) =>
      if goals.isEmpty then ([], (Atom.var name, goals))
      else
        ([Goal.compileAlias (Atom.var name) out],
          (out, goals))
  | branch => ([], branch)

/-- Normalize one syntactic `superpose` branch after the enclosing output is
known.  Empty branches retain the compact `(value, [])` representation: the
ordinary `amb` result equality is their complete branch.  A nonempty variable
branch lifts `build_branch/4`'s translation-time alias before the disjunction;
a nonvariable branch embeds its value equality before its body goals.  Every
nonempty normalized branch uses `out` as its template, marking that its exact
result constraint is already present in the branch body.
[SPEC translator.pl:112-114,394-397,414-416] -/
def compileSuperposeBranch (out : Atom)
    (branch : Atom × List Goal) : List Goal × (Atom × List Goal) :=
  if branch.2.isEmpty then
    ([], branch)
  else
    let normalized := compileBranch out branch
    let goals :=
      if normalized.2.1 == out then normalized.2.2
      else Goal.eq normalized.2.1 out :: normalized.2.2
    (normalized.1, (out, goals))

/-- Normalize syntactic `superpose` branches in source order, concatenating
the explicit aliases that native Prolog creates while translating the branch
list.  Those aliases execute once, before any alternative is selected.
[SPEC translator.pl:112-114,394-397,414-416] -/
def compileSuperposeBranches (out : Atom) :
    List (Atom × List Goal) → List Goal × List (Atom × List Goal)
  | [] => ([], [])
  | branch :: rest =>
      let head := compileSuperposeBranch out branch
      let tail := compileSuperposeBranches out rest
      (head.1 ++ tail.1, head.2 :: tail.2)

/-- [SPEC translator.pl:384-386] A pinned `let*` contains one or more
well-formed `(pattern value)` pairs and becomes source-ordered nested `let`s.
The `Option` result keeps malformed input distinct from an empty computation:
the translator rejects it instead of silently dropping bad entries. -/
def desugarLetStar? : List Atom → Atom → Option Atom
  | [Atom.expr [pattern, value]], body =>
      some (Atom.expr [Atom.sym "let", pattern, value, body])
  | Atom.expr [pattern, value] :: rest, body =>
      (desugarLetStar? rest body).map fun nested =>
        Atom.expr [Atom.sym "let", pattern, value, nested]
  | _, _ => none

private def specialHead : String → Bool
  | "quote" | "unquote" | "empty" | "cut" | "if" | "let" | "let*" | "case"
  | "and-then" | "or-else"
  | "collapse" | "once" | "superpose" | "hyperpose" | "unify" | "chain"
  | "foldall" | "forall" | "progn" | "prog1"
  | "with_mutex" | "transaction"
  | "unique" | "alpha-unique" | "union" | "intersection" | "subtraction"
  | "eval" | "catch" | "call" | "reduce" | "get-type-space" | "get-atoms"
  | "get-type" | "get-metatype" | "match" | "find" | "==" | "="
  | "add-atom" | "remove-atom" | "bind!" | "get-state" | "change-state!"
  | "succeedsPredicate" | "for" | "test" | "trace!" | "cons" | "#+" | "#-" => true
  | _ => false

private def staticDataHead (env : CEnv) : Atom → Bool
  | Atom.expr (Atom.sym h :: _) =>
      !(env.defined.contains h) && !(env.isBin h) && !specialHead h
  | _ => false

/-- Tagged runtime partial values can never be mistaken for a source-shaped
compound data head.  Their first child is the ordinary-Prolog-compound
external tag shared with `Predicate/2`, not a source symbol. -/
theorem staticDataHead_partialC_false (env : CEnv) (head : String)
    (encodedArguments : Atom) :
    staticDataHead env (partialC head encodedArguments) = false := by
  rfl

def dynamicUnknownHead : String → Bool
  | h =>
      match h.toList with
      | c :: _ => c.isLower
      | [] => false

def rewriteBinaryStreamOp? (atomOp : String) : List Atom → Option Atom
  | [Atom.expr (Atom.sym "superpose" :: left),
      Atom.expr (Atom.sym "superpose" :: right)] =>
      some (Atom.expr [Atom.sym "call", Atom.expr [Atom.sym "superpose",
        Atom.expr [Atom.sym atomOp,
          Atom.expr [Atom.sym "collapse",
            Atom.expr (Atom.sym "superpose" :: left)],
          Atom.expr [Atom.sym "collapse",
            Atom.expr (Atom.sym "superpose" :: right)]]]])
  | _ => none

def rewriteTrace? : List Atom → Option Atom
  | [message, value] =>
      some (Atom.expr [Atom.sym "progn",
        Atom.expr [Atom.sym "println!", message], value])
  | _ => none

def rewriteUnique? (atomOp : String) : List Atom → Option Atom
  | [source] =>
      some (Atom.expr [Atom.sym "call", Atom.expr [Atom.sym "superpose",
        Atom.expr [Atom.sym atomOp,
          Atom.expr [Atom.sym "collapse", source]]]])
  | _ => none

def rewriteStreamOpForHead (head : String) : List Atom → Option Atom :=
  if head == "trace!" then rewriteTrace?
  else if head == "unique" then rewriteUnique? "unique-atom"
  else if head == "alpha-unique" then rewriteUnique? "alpha-unique-atom"
  else if head == "union" then rewriteBinaryStreamOp? "union-atom"
  else if head == "intersection" then rewriteBinaryStreamOp? "intersection-atom"
  else if head == "subtraction" then rewriteBinaryStreamOp? "subtraction-atom"
  else fun _ => none

/-- [SPEC translator.pl:73-90] The pinned stream rewrites run before head
translation and translator-rule lookup. Returning `none` means that the source
shape is not one of those exact rewrites and must continue through ordinary
translation unchanged. Head-first clauses keep every unrelated compiler
equation definitionally transparent. -/
def rewriteStreamOp? : String → List Atom → Option Atom
  | head, args => rewriteStreamOpForHead head args

/-- `#+` is not one of pinned `rewrite_streamops/2`'s source heads. -/
theorem rewriteStreamOp_hashPlus_none (args : List Atom) :
    rewriteStreamOp? "#+" args = none := by
  simp only [rewriteStreamOp?, rewriteStreamOpForHead,
    show ("#+" == "trace!") = false by decide,
    show ("#+" == "unique") = false by decide,
    show ("#+" == "alpha-unique") = false by decide,
    show ("#+" == "union") = false by decide,
    show ("#+" == "intersection") = false by decide,
    show ("#+" == "subtraction") = false by decide,
    Bool.false_eq_true, ↓reduceIte]

/-- `#-` is not one of pinned `rewrite_streamops/2`'s source heads. -/
theorem rewriteStreamOp_hashMinus_none (args : List Atom) :
    rewriteStreamOp? "#-" args = none := by
  simp only [rewriteStreamOp?, rewriteStreamOpForHead,
    show ("#-" == "trace!") = false by decide,
    show ("#-" == "unique") = false by decide,
    show ("#-" == "alpha-unique") = false by decide,
    show ("#-" == "union") = false by decide,
    show ("#-" == "intersection") = false by decide,
    show ("#-" == "subtraction") = false by decide,
    Bool.false_eq_true, ↓reduceIte]

/-- The pinned `trace!` stream rewrite is selected independently of the
translator-rule environment. -/
theorem rewriteStreamOp_trace_pair (message value : Atom) :
    rewriteStreamOp? "trace!" [message, value] =
      some (.expr [.sym "progn", .expr [.sym "println!", message], value]) := by
  simp only [rewriteStreamOp?, rewriteStreamOpForHead,
    show ("trace!" == "trace!") = true by decide,
    if_true, rewriteTrace?]

/-- `unquote` is not one of pinned `rewrite_streamops/2`'s source heads. -/
theorem rewriteStreamOp_unquote_none (args : List Atom) :
    rewriteStreamOp? "unquote" args = none := by
  simp only [rewriteStreamOp?, rewriteStreamOpForHead,
    show ("unquote" == "trace!") = false by decide,
    show ("unquote" == "unique") = false by decide,
    show ("unquote" == "alpha-unique") = false by decide,
    show ("unquote" == "union") = false by decide,
    show ("unquote" == "intersection") = false by decide,
    show ("unquote" == "subtraction") = false by decide,
    Bool.false_eq_true, ↓reduceIte]

private theorem rewriteStreamOp_chain_none (args : List Atom) :
    rewriteStreamOp? "chain" args = none := by
  simp only [rewriteStreamOp?, rewriteStreamOpForHead,
    show ("chain" == "trace!") = false by decide,
    show ("chain" == "unique") = false by decide,
    show ("chain" == "alpha-unique") = false by decide,
    show ("chain" == "union") = false by decide,
    show ("chain" == "intersection") = false by decide,
    show ("chain" == "subtraction") = false by decide,
    Bool.false_eq_true, ↓reduceIte]

private theorem rewriteStreamOp_quote_none (args : List Atom) :
    rewriteStreamOp? "quote" args = none := by
  simp only [rewriteStreamOp?, rewriteStreamOpForHead,
    show ("quote" == "trace!") = false by decide,
    show ("quote" == "unique") = false by decide,
    show ("quote" == "alpha-unique") = false by decide,
    show ("quote" == "union") = false by decide,
    show ("quote" == "intersection") = false by decide,
    show ("quote" == "subtraction") = false by decide,
    Bool.false_eq_true, ↓reduceIte]

/-- Whether a declared-type collection requires explicit typed branches.
One chain needs them exactly when an input or result check is observable;
multiple distinct chains also need them to preserve branch order and
multiplicity. [SPEC translator.pl:317-324,349-370] -/
def shouldUseTypedDispatch (chains : List (List Atom)) : Bool :=
  let needsChecks : List Atom → Bool := fun chain =>
    chain.dropLast.any typeRequiresCheck ||
      match chain.getLast? with
      | some resultType => resultTypeRequiresCheck resultType
      | none => false
  match chains with
  | [] => false
  | [chain] => needsChecks chain
  | _ :: _ :: _ => true

/-- A nonempty source call cannot traverse a type chain that runs out of
parameter types. An empty inner chain also lacks the mandatory result type;
an empty outer chain list means that no type declaration exists. Pinned
`maplist(typed_functioncall_branch, ...)` fails the whole translation when
either occurs; this guard preserves that failure before the existing selector,
including for fragments lowered through the ordinary path.
[SPEC translator.pl:317-324,349-370] -/
def typedDispatchInputShortage (chains : List (List Atom))
    (argumentCount : Nat) : Bool :=
  chains.any (fun chain =>
    chain.isEmpty || chain.dropLast.length < argumentCount)

/-- Pinned `build_call_or_partial/6` specialized to an already translated
typed argument list. The returned atom is the branch template: a complete
arity calls into the shared result, while an incomplete arity is a partial
value and emits no call goal. [SPEC translator.pl:335-346] -/
def compileTypedCallOrPartial (arities : List Nat) (result : Atom)
    (head : String) (terms : List Atom) : Atom × List Goal :=
  if arities.contains terms.length then
    (result, [Goal.call head terms result])
  else
    (partialValue head terms, [])

/-- A complete typed branch emits exactly one local call and preserves the
shared result template.  Consumers use this equation instead of reopening the
arity decision. -/
@[simp] theorem compileTypedCallOrPartial_complete
    (arities : List Nat) (result : Atom) (head : String) (terms : List Atom)
    (complete : terms.length ∈ arities) :
    compileTypedCallOrPartial arities result head terms =
      (result, [Goal.call head terms result]) := by
  simp [compileTypedCallOrPartial, complete]

/-- An incomplete typed branch is a first-class partial value and emits no
call goal. -/
@[simp] theorem compileTypedCallOrPartial_partial
    (arities : List Nat) (result : Atom) (head : String) (terms : List Atom)
    (incomplete : terms.length ∉ arities) :
    compileTypedCallOrPartial arities result head terms =
      (partialValue head terms, []) := by
  simp [compileTypedCallOrPartial, incomplete]

/-- One arrow-chain branch of typed dispatch. Each chain is first made a
fresh variant, reproducing Prolog's branch-local copying through `findall/3`;
the advanced counter then feeds typed argument translation and result checks.
Naming this executable step makes its counter threading and ordered fold
independently checkable. [SPEC translator.pl:317-324,349-370] -/
def compileTypedDispatchStepWith
    (compileTypedArgs : Nat → List Atom →
      CompileM (List Atom × List Goal × Nat))
    (result : Atom) (head : String) (arities : List Nat)
    (accumulator : List (Atom × List Goal) × Nat) (chain : List Atom) :
    CompileM (List (Atom × List Goal) × Nat) :=
  let (freshChain, freshCounter) := freshenTypeChain accumulator.2 chain
  match freshChain.dropLast, freshChain.getLast? with
  | parameterTypes, some resultType =>
      do
      let (terms, goals, checkedArgumentsCounter) ←
        compileTypedArgs freshCounter parameterTypes
      let (branchResult, callGoals) :=
        compileTypedCallOrPartial arities result head terms
      let (resultChecks, nextCounter) :=
        compileResultTypeCheck branchResult resultType checkedArgumentsCounter
      .ok (accumulator.1 ++ [(branchResult,
        goals ++ callGoals ++ resultChecks)], nextCounter)
  | _, none => .error "typed dispatch: missing result type"

mutual

/-- Apply a compile-time PeTTa substitution deeply throughout one emitted
goal.  Native `maplist(typed_functioncall_branch, ...)` constructs every
branch around the same Prolog `Out`; when an incomplete branch binds that
variable, the binding is visible retroactively in goals constructed for
earlier branches. [SPEC translator.pl:320-321,335-358] -/
def substCompiledGoal (binding : Subst) : Goal → Goal
  | .call head arguments result =>
      .call head (arguments.map (subst binding)) (subst binding result)
  | .bin operation arguments result =>
      .bin operation (arguments.map (subst binding)) (subst binding result)
  | .callDyn head arguments result =>
      .callDyn (subst binding head) (arguments.map (subst binding))
        (subst binding result)
  | .evalg value result =>
      .evalg (subst binding value) (subst binding result)
  | .catchg template goals result =>
      .catchg (subst binding template) (substCompiledGoals binding goals)
        (subst binding result)
  | .catchExit template result =>
      .catchExit (subst binding template) (subst binding result)
  | .softcut template condition thenGoals elseGoals =>
      .softcut (subst binding template)
        (substCompiledGoals binding condition)
        (substCompiledGoals binding thenGoals)
        (substCompiledGoals binding elseGoals)
  | .softcutExit template => .softcutExit (subst binding template)
  | .eq left right => .eq (subst binding left) (subst binding right)
  | .compileAlias left right =>
      .compileAlias (subst binding left) (subst binding right)
  | .cut => .cut
  | .cutAt barrier => .cutAt barrier
  | .findall template goals result =>
      .findall (subst binding template) (substCompiledGoals binding goals)
        (subst binding result)
  | .onceg template goals result =>
      .onceg (subst binding template) (substCompiledGoals binding goals)
        (subst binding result)
  | .transactiong template goals =>
      .transactiong (subst binding template)
        (substCompiledGoals binding goals)
  | .amb branches result =>
      .amb (substCompiledBranches binding branches) (subst binding result)
  | .spread value result =>
      .spread (subst binding value) (subst binding result)
  | .ite condition thenBranch elseBranch result =>
      .ite (subst binding condition)
        (subst binding thenBranch.1,
          substCompiledGoals binding thenBranch.2)
        (subst binding elseBranch.1,
          substCompiledGoals binding elseBranch.2)
        (subst binding result)
  | .smatch pattern => .smatch (subst binding pattern)
  | .wact operation arguments result =>
      .wact operation (arguments.map (subst binding))
        (subst binding result)

/-- Deep compile-time substitution over an ordered goal sequence. -/
def substCompiledGoals (binding : Subst) : List Goal → List Goal
  | [] => []
  | goal :: goals =>
      substCompiledGoal binding goal :: substCompiledGoals binding goals

/-- Deep compile-time substitution over the templates and goals of an
ordered nondeterministic branch collection. -/
def substCompiledBranches (binding : Subst) :
    List (Atom × List Goal) → List (Atom × List Goal)
  | [] => []
  | (template, goals) :: branches =>
      (subst binding template, substCompiledGoals binding goals) ::
        substCompiledBranches binding branches

end

/-! ## Translation-time alias finalization

Pinned Prolog performs the variable case of `build_branch/4` while translating
the whole surrounding expression.  Consequently that sharing can affect goals
which the enclosing construct schedules before the child branch.  A runtime
equality inside the child is therefore not compositional.  The raw compiler
keeps these equalities as explicit `Goal.compileAlias` metadata; source-facing
entry points collect them through the complete goal tree, solve them once, and
apply the resulting substitution everywhere before execution.
-/

mutual

/-- Translation-time aliases contained in one raw compiled goal, in the same
left-to-right order in which its nested source expressions were translated. -/
def collectCompileAliasesGoal : Goal → List (Atom × Atom)
  | .call _ _ _ | .bin _ _ _ | .callDyn _ _ _ | .evalg _ _
  | .catchExit _ _ | .softcutExit _ | .eq _ _ | .cut | .cutAt _
  | .spread _ _ | .smatch _
  | .wact _ _ _ => []
  | .compileAlias left right => [(left, right)]
  | .catchg _ goals _ => collectCompileAliasesGoals goals
  | .softcut _ condition thenGoals elseGoals =>
      collectCompileAliasesGoals condition ++
        collectCompileAliasesGoals thenGoals ++
        collectCompileAliasesGoals elseGoals
  | .findall _ goals _ | .onceg _ goals _ | .transactiong _ goals =>
      collectCompileAliasesGoals goals
  | .amb branches _ => collectCompileAliasesBranches branches
  | .ite _ thenBranch elseBranch _ =>
      collectCompileAliasesGoals thenBranch.2 ++
        collectCompileAliasesGoals elseBranch.2

/-- Translation-time aliases in an ordered raw goal sequence. -/
def collectCompileAliasesGoals : List Goal → List (Atom × Atom)
  | [] => []
  | goal :: goals =>
      collectCompileAliasesGoal goal ++ collectCompileAliasesGoals goals

/-- Translation-time aliases in source-ordered nondeterministic branches. -/
def collectCompileAliasesBranches : List (Atom × List Goal) →
    List (Atom × Atom)
  | [] => []
  | branch :: branches =>
      collectCompileAliasesGoals branch.2 ++
        collectCompileAliasesBranches branches

end

mutual

/-- Erase one compiler-only alias marker while recursively preserving every
runtime goal and every source-order boundary. -/
def eraseCompileAliasesGoal : Goal → Option Goal
  | .compileAlias _ _ => none
  | .call head arguments result => some (.call head arguments result)
  | .bin operation arguments result => some (.bin operation arguments result)
  | .callDyn head arguments result => some (.callDyn head arguments result)
  | .evalg value result => some (.evalg value result)
  | .catchg template goals result =>
      some (.catchg template (eraseCompileAliasesGoals goals) result)
  | .catchExit template result => some (.catchExit template result)
  | .softcut template condition thenGoals elseGoals =>
      some (.softcut template
        (eraseCompileAliasesGoals condition)
        (eraseCompileAliasesGoals thenGoals)
        (eraseCompileAliasesGoals elseGoals))
  | .softcutExit template => some (.softcutExit template)
  | .eq left right => some (.eq left right)
  | .cut => some .cut
  | .cutAt barrier => some (.cutAt barrier)
  | .findall template goals result =>
      some (.findall template (eraseCompileAliasesGoals goals) result)
  | .onceg template goals result =>
      some (.onceg template (eraseCompileAliasesGoals goals) result)
  | .transactiong template goals =>
      some (.transactiong template (eraseCompileAliasesGoals goals))
  | .amb branches result =>
      some (.amb (eraseCompileAliasesBranches branches) result)
  | .spread value result => some (.spread value result)
  | .ite condition thenBranch elseBranch result =>
      some (.ite condition
        (thenBranch.1, eraseCompileAliasesGoals thenBranch.2)
        (elseBranch.1, eraseCompileAliasesGoals elseBranch.2) result)
  | .smatch pattern => some (.smatch pattern)
  | .wact operation arguments result =>
      some (.wact operation arguments result)

/-- Remove compiler-only alias markers from an ordered goal sequence. -/
def eraseCompileAliasesGoals : List Goal → List Goal
  | [] => []
  | goal :: goals =>
      match eraseCompileAliasesGoal goal with
      | some runtimeGoal => runtimeGoal :: eraseCompileAliasesGoals goals
      | none => eraseCompileAliasesGoals goals

/-- Remove compiler-only alias markers from every ordered branch. -/
def eraseCompileAliasesBranches : List (Atom × List Goal) →
    List (Atom × List Goal)
  | [] => []
  | branch :: branches =>
      (branch.1, eraseCompileAliasesGoals branch.2) ::
        eraseCompileAliasesBranches branches

end


/-- Solve the ordered translation-time alias ledger.  Every marker emitted by
`compileBranch` relates variables, but using the exact compiler unifier keeps
chains and future extensions honest and turns an impossible inconsistency into
an explicit compilation error. -/
def resolveCompileAliases (aliases : List (Atom × Atom)) : CompileM Subst :=
  aliases.foldlM (fun binding alias =>
    match unifyTopExact (subst binding alias.1) (subst binding alias.2) with
    | some generated => .ok (Metta.Subst.compose generated binding)
    | none => .error "compiler aliases: incompatible translation-time sharing")
    []

/-- Finalize a raw expression result by applying every translation-time alias
to the result and entire runtime goal tree, then erase the metadata. -/
def finalizeCompiledExpression (term : Atom) (goals : List Goal)
    (nextCounter : Nat) : CompileM (Atom × List Goal × Nat) := do
  let binding ← resolveCompileAliases (collectCompileAliasesGoals goals)
  let runtimeGoals := eraseCompileAliasesGoals goals
  .ok (subst binding term, substCompiledGoals binding runtimeGoals, nextCounter)

/-- Clause-level counterpart of `finalizeCompiledExpression`.  RHS aliases
also apply to head parameters and pattern goals because native Prolog created
that sharing before the clause can run. -/
def finalizeCompiledClause (clause : Clause) : CompileM Clause := do
  let binding ← resolveCompileAliases
    (collectCompileAliasesGoals clause.body)
  let runtimeBody := eraseCompileAliasesGoals clause.body
  .ok { params := clause.params.map (subst binding)
        result := subst binding clause.result
        body := substCompiledGoals binding runtimeBody }

/-- Add the constraint contributed by one raw typed branch to the single
shared result variable used by pinned `maplist/2`.  A complete branch returns
that variable unchanged and contributes no compile-time binding.  An
incomplete branch returns a partial value, which unifies with the shared
result immediately; an incompatible later partial rejects the translation.
[SPEC translator.pl:320-321,335-358] -/
def bindTypedSharedResult (sharedResult : Atom) (binding : Subst)
    (branch : Atom × List Goal) : CompileM Subst :=
  if branch.1 == sharedResult then
    .ok binding
  else
    match unifyTopExact (subst binding sharedResult)
        (subst binding branch.1) with
    | some generated => .ok (Metta.Subst.compose generated binding)
    | none => .error "typed dispatch: incompatible shared result"

/-- Resolve the one Prolog `Out` shared by every typed overload branch.
Branch compilation is source-independent of `Out`, so collecting raw
branches first and then replaying their result constraints left-to-right is
equivalent to pinned `maplist/2` on the atom-headed, empty-prefix,
non-specializing fragment.  The final substitution is applied retroactively
to every branch exactly as Prolog variable sharing does.
[SPEC translator.pl:320-321,335-358] -/
def resolveTypedSharedResult (sharedResult : Atom)
    (branches : List (Atom × List Goal)) :
    CompileM (Atom × List (Atom × List Goal)) := do
  let binding ← branches.foldlM (bindTypedSharedResult sharedResult) []
  .ok (subst binding sharedResult, substCompiledBranches binding branches)

/-- Compile an ordered collection of nondeterministic branches.  The callback
is the executable expression compiler; naming the fold makes its left-to-right
counter threading independently checkable. -/
def compileAmbBranchesWith
    (compileExpr : Nat → Atom → CompileM (Atom × List Goal × Nat))
    (counter : Nat) (expressions : List Atom) :
    CompileM (List (Atom × List Goal) × Nat) :=
  expressions.foldlM
    (fun (acc : List (Atom × List Goal) × Nat) expression => do
      let (term, goals, nextCounter) ← compileExpr acc.2 expression
      .ok (acc.1 ++ [(term, goals)], nextCounter))
    ([], counter)

/-- Pinned special-form heads understood by `compileAppCoreFuel`.  Classifying
the head once keeps the executable dispatch finite and gives proofs a small
inductive discriminator instead of a large nest of string comparisons. -/
inductive AppCoreHead where
  | hQuote
  | hPredicate
  | hTranslatePredicate
  | hCallPredicate
  | hAssertaPredicate
  | hAssertzPredicate
  | hRetractPredicate
  | hProcessMettaString
  | hUnquote
  | hEmpty
  | hCut
  | hTest
  | hTrace
  | hAndThen
  | hOrElse
  | hHashPlus
  | hHashMinus
  | hCons
  | hIf
  | hLet
  | hLetStar
  | hCase
  | hCollapse
  | hOnce
  | hSuperpose
  | hUnify
  | hSucceedsPredicate
  | hFor
  | hChain
  | hFoldall
  | hForall
  | hProgn
  | hProg1
  | hWithMutex
  | hTransaction
  | hHyperpose
  | hUnique
  | hUnion
  | hIntersection
  | hSubtraction
  | hEval
  | hCatch
  | hCall
  | hReduce
  | hGetTypeSpace
  | hGetAtoms
  | hGetType
  | hGetMetatype
  | hMatch
  | hFind
  | hDoubleEqual
  | hEqual
  | hAddAtom
  | hRemoveAtom
  | hBind
  | hGetState
  | hChangeState
  | other
  deriving DecidableEq, Repr

/-- Classify exactly the pinned special-form spellings.  A recognized head
with an unsupported arity still falls through to ordinary application using
the original source spelling. -/
@[simp] def classifyAppCoreHead : String → AppCoreHead
  | "quote" => .hQuote
  | "Predicate" => .hPredicate
  | "translatePredicate" => .hTranslatePredicate
  | "callPredicate" => .hCallPredicate
  | "assertaPredicate" => .hAssertaPredicate
  | "assertzPredicate" => .hAssertzPredicate
  | "retractPredicate" => .hRetractPredicate
  | "process_metta_string" => .hProcessMettaString
  | "unquote" => .hUnquote
  | "empty" => .hEmpty
  | "cut" => .hCut
  | "test" => .hTest
  | "trace!" => .hTrace
  | "and-then" => .hAndThen
  | "or-else" => .hOrElse
  | "#+" => .hHashPlus
  | "#-" => .hHashMinus
  | "cons" => .hCons
  | "if" => .hIf
  | "let" => .hLet
  | "let*" => .hLetStar
  | "case" => .hCase
  | "collapse" => .hCollapse
  | "once" => .hOnce
  | "superpose" => .hSuperpose
  | "unify" => .hUnify
  | "succeedsPredicate" => .hSucceedsPredicate
  | "for" => .hFor
  | "chain" => .hChain
  | "foldall" => .hFoldall
  | "forall" => .hForall
  | "progn" => .hProgn
  | "prog1" => .hProg1
  | "with_mutex" => .hWithMutex
  | "transaction" => .hTransaction
  | "hyperpose" => .hHyperpose
  | "unique" => .hUnique
  -- These heads are special only when `rewriteStreamOp?` has already
  -- recognized two syntactic `superpose` operands.  Every other shape follows
  -- pinned ordinary application/data translation rather than a core shortcut.
  | "union" => .other
  | "intersection" => .other
  | "subtraction" => .other
  | "eval" => .hEval
  | "catch" => .hCatch
  | "call" => .hCall
  | "reduce" => .hReduce
  | "get-type-space" => .hGetTypeSpace
  | "get-atoms" => .hGetAtoms
  | "get-type" => .hGetType
  | "get-metatype" => .hGetMetatype
  | "match" => .hMatch
  | "find" => .hFind
  | "==" => .hDoubleEqual
  | "=" => .hEqual
  | "add-atom" => .hAddAtom
  | "remove-atom" => .hRemoveAtom
  | "bind!" => .hBind
  | "get-state" => .hGetState
  | "change-state!" => .hChangeState
  | _ => .other

/-- Generic application dispatch after every pinned special form has declined.
The recursive compiler traversals are explicit parameters: this is the actual
executable fallback, while its small interface keeps counter and adequacy
proofs independent of the large special-form matcher. -/
def compileAppDefaultWith
    (compileArgs : Nat → CompileM (List Atom × List Goal × Nat))
    (compileTypedArgs : Nat → List Atom →
      CompileM (List Atom × List Goal × Nat))
    (compileList : Nat → CompileM (List Atom × List Goal × Nat))
    (env : CEnv) (counter : Nat) (head : String) (arguments : List Atom) :
    CompileM (Atom × List Goal × Nat) := do
  if env.prologFunctions.contains head then do
    let (terms, goals, nextCounter) ← compileArgs counter
    let (result, resultCounter) := fresh nextCounter
    let (ok, finalCounter) := fresh resultCounter
    let predicate :=
      chainify (Atom.expr (Atom.sym head :: terms ++ [result]))
    .ok (result,
      goals ++ [Goal.bin "translatePredicate" [predicate] ok], finalCounter)
  else if env.defined.contains head then do
    let chains0 := env.typeChains head
    if typedDispatchInputShortage chains0 arguments.length then
      .error "typed arguments: arity mismatch"
    else if shouldUseTypedDispatch chains0 then do
      let (result, firstCounter) := fresh counter
      let (branches, branchCounter) ← chains0.foldlM
        (compileTypedDispatchStepWith compileTypedArgs result head
          (env.arities head))
        ([], firstCounter)
      if branches.isEmpty then do
        let (terms, goals, nextCounter) ← compileArgs counter
        if (env.arities head).contains terms.length then
          let (fallbackResult, finalCounter) := fresh nextCounter
          .ok (fallbackResult,
            goals ++ [Goal.call head terms fallbackResult], finalCounter)
        else
          .ok (partialValue head terms, goals, nextCounter)
      else
        let (sharedResult, resolvedBranches) ←
          resolveTypedSharedResult result branches
        .ok (sharedResult,
          [Goal.amb resolvedBranches sharedResult], branchCounter)
    else do
      let (terms, goals, nextCounter) ← compileArgs counter
      if (env.arities head).contains terms.length then
        let (result, finalCounter) := fresh nextCounter
        .ok (result, goals ++ [Goal.call head terms result], finalCounter)
      else
        .ok (partialValue head terms, goals, nextCounter)
  else if env.isBin head then do
    let (terms, goals, nextCounter) ← compileArgs counter
    match compileBinArity head with
    | some arity =>
        if arity == terms.length then
          let (result, finalCounter) := fresh nextCounter
          .ok (result, goals ++ [Goal.bin head terms result], finalCounter)
        else
          .ok (partialValue head terms, goals, nextCounter)
    | none =>
        let (result, finalCounter) := fresh nextCounter
        .ok (result, goals ++ [Goal.bin head terms result], finalCounter)
  else do
    let (terms, goals, nextCounter) ← compileList counter
    if env.dynamicUnknown && dynamicUnknownHead head then
      -- Unknown lowercase heads in a bang may be functions introduced by
      -- earlier top-level `add-atom` effects; resolve them at run time.
      let (result, finalCounter) := fresh nextCounter
      .ok (result,
        goals ++ [Goal.callDyn (Atom.sym head) terms result], finalCounter)
    else
      -- Unknown non-function heads are data at this translation point
      -- [SPEC translator.pl:318-326].
      .ok (chainOf (Atom.sym head :: terms), goals, nextCounter)

set_option maxHeartbeats 2000000 in
mutual

/-- `C⟦e⟧ = (t, G)` with the fresh counter threaded.  The explicit fuel makes
the actual executable compiler transparent to Lean's kernel; adequacy proves a
sufficient bound for every supported source form. -/
def compileExprFuel : Nat → CEnv → Nat → Atom →
    CompileM (Atom × List Goal × Nat)
  | 0, _, _, _ => .error "compiler fuel exhausted"
  | _ + 1, _, n, Atom.var v => .ok (Atom.var v, [], n)
  | _ + 1, _, n, Atom.sym s => .ok (canonBool (Atom.sym s), [], n)
  | _ + 1, _, n, Atom.gnd g => .ok (canonBool (Atom.gnd g), [], n)
  | _ + 1, _, n, Atom.expr [] => .ok (nilA, [], n)   -- () is the empty list
  | _ + 1, _, n, Atom.expr [Atom.sym "#c", h, t] =>
      -- Internal chain values produced by the compiler (not source calls)
      -- stay as data. Captured lambdas use `partialValue`, whose bound
      -- argument list is a #c-chain [SPEC translator.pl:253-254].
      .ok (Atom.expr [Atom.sym "#c", h, t], [], n)
  | _ + 1, _, n, Atom.expr
      [Atom.gnd (.external "PLeaTTa.internal" "prolog-compound"),
       Atom.sym "partial",
       Atom.expr
         [Atom.sym "#c", Atom.sym functor,
          Atom.expr
            [Atom.sym "#c", encodedArgs,
             Atom.gnd (.external "PLeaTTa.internal" "nil")]]] =>
      -- Binder desugaring and Predicate/2 materialize the same pinned
      -- `partial(Fun, Bound)` compound.  Its exact arity-two private spine is
      -- already compiler data: recursively translating it as a
      -- compound-headed source application would destroy the closure before
      -- the enclosing application can dispatch it
      -- [SPEC metta.pl:275; translator.pl:59-61,244-261].
      .ok (partialC functor encodedArgs, [], n)
  | fuel + 1, env, n, Atom.expr (Atom.sym h :: args) => compileAppFuel fuel env n h args
  | fuel + 1, env, n, Atom.expr (Atom.var v :: args) => do
      -- first-class function value: dynamic application
      let (ts, gs, n1) ← compileListFuel fuel env n args
      let (r, n2) := fresh n1
      .ok (r, gs ++ [Goal.callDyn (Atom.var v) ts r], n2)
  | fuel + 1, env, n, Atom.expr (hd :: args) => do
      -- compound-headed application `(E a1..an)`: evaluate the head, then
      -- callDyn dispatches at runtime (apply if it is a fun/partial/defined
      -- symbol, else data) — mirrors petta's translate_expr on `[H|T]` with
      -- H a list [SPEC translator.pl:97-99, 302-326]
      let (th, gh, n1) ← compileExprFuel fuel env n hd
      let (ts, gs, n2) ← compileListFuel fuel env n1 args
      if !env.dynamicUnknown && staticDataHead env hd then
        .ok (chainOf (th :: ts), gh ++ gs, n2)
      else
        let (r, n3) := fresh n2
        .ok (r, gh ++ gs ++ [Goal.callDyn th ts r], n3)
termination_by structural fuel _ _ _ => fuel

def compilePatternFuel : Nat → CEnv → Nat → Atom →
    CompileM (Atom × List Goal × Nat)
  | 0, _, _, _ => .error "compiler fuel exhausted"
  | _ + 1, _, n, Atom.var v => .ok (Atom.var v, [], n)
  | _ + 1, _, n, Atom.sym s => .ok (canonBool (Atom.sym s), [], n)
  | _ + 1, _, n, Atom.gnd g => .ok (canonBool (Atom.gnd g), [], n)
  | _ + 1, _, n, Atom.expr [] => .ok (nilA, [], n)
  | fuel + 1, env, n, Atom.expr (Atom.sym f :: args) =>
      let fallback :=
        if env.defined.contains f || env.isBin f || specialHead f then
          compileExprFuel fuel env n (Atom.expr (Atom.sym f :: args))
        else do
          let (ts, gs, n1) ← compilePatternListFuel fuel env n args
          .ok (chainOf (Atom.sym f :: ts), gs, n1)
      match args with
      | [h, t] =>
          if f == "#c" then
            .ok (Atom.expr [Atom.sym "#c", h, t], [], n)
          else if f == "cons" then do
            let (ph, gh, n1) ← compilePatternFuel fuel env n h
            let (pt, gt, n2) ← compilePatternFuel fuel env n1 t
            .ok (consC ph pt, gh ++ gt, n2)
          else fallback
      | _ => fallback
  | fuel + 1, env, n, Atom.expr es => do
      let (ts, gs, n1) ← compilePatternListFuel fuel env n es
      .ok (chainOf ts, gs, n1)
termination_by structural fuel _ _ _ => fuel

def compileAppFuel : Nat → CEnv → Nat → String → List Atom →
    CompileM (Atom × List Goal × Nat)
  | 0, _, _, _, _ => .error "compiler fuel exhausted"
  | fuel + 1, env, n, h, args => do
    match rewriteStreamOp? h args with
    | some rewritten => compileExprFuel fuel env n rewritten
    | none =>
      if env.translatorRules.contains h then
        -- [SPEC translator.pl:99-110] a translator rule calls the registered
        -- user predicate to obtain source code, then translates that returned
        -- code. It does not compile the ordinary builtin of the same name.
        let (terms, goals, n1) ← compileArgsAtFuel fuel env n h 0 args
        let (code, n2) := fresh n1
        let (r, n3) := fresh n2
        .ok (r, goals ++ [Goal.call h terms code, Goal.evalg code r], n3)
      else
        compileAppCoreFuel fuel env n h args
termination_by structural fuel _ _ _ _ => fuel

def compileAppCoreFuel : Nat → CEnv → Nat → String → List Atom →
    CompileM (Atom × List Goal × Nat)
  | 0, _, _, _, _ => .error "compiler fuel exhausted"
  | fuel + 1, env, n, h, args => do
    match classifyAppCoreHead h, args with
    | .hQuote, [e] => .ok (chainify e, [], n)              -- syntactic value
    | .hPredicate, [goal] => do
        -- `Predicate` is an ordinary registered function. Its argument uses
        -- the same staging mask as pinned `translate_args`: untyped arguments
        -- evaluate, while an explicit `Expression` declaration stays data.
        -- The actual `=../2` conversion must remain a runtime goal so empty,
        -- open-head, and non-atom-head behavior is not erased at compilation.
        -- [SPEC metta.pl:275; translator.pl:310-370]
        let (terms, goals, n1) ←
          compileArgsAtFuel fuel env n h 0 [goal]
        let (r, n2) := fresh n1
        .ok (r, goals ++ [Goal.bin "Predicate" terms r], n2)
    | .hTranslatePredicate, [goal] => do
        -- The argument is Prolog syntax, not a MeTTa subexpression.  Preserve it
        -- as data and make the trusted-host boundary explicit at execution.
        let (r, n1) := fresh n
        .ok (r, [Goal.bin "translatePredicate" [chainify goal] r], n1)
    | .hCallPredicate, [predicate] => do
        let (term, goals, n1) ← compileExprFuel fuel env n predicate
        let (r, n2) := fresh n1
        -- Both source forms share one typed ownership-dispatch point: local
        -- predicates stay in the core, imported predicates cross the host
        -- boundary.  The executor accepts the quoted `Predicate` wrapper.
        .ok (r, goals ++ [Goal.bin "translatePredicate" [term] r], n2)
    | .hAssertaPredicate, [predicate] => do
        let (term, goals, n1) ← compileExprFuel fuel env n predicate
        let (r, n2) := fresh n1
        .ok (r, goals ++ [Goal.wact "assertaPredicate" [term] r], n2)
    | .hAssertzPredicate, [predicate] => do
        let (term, goals, n1) ← compileExprFuel fuel env n predicate
        let (r, n2) := fresh n1
        .ok (r, goals ++ [Goal.wact "assertzPredicate" [term] r], n2)
    | .hRetractPredicate, [predicate] => do
        let (term, goals, n1) ← compileExprFuel fuel env n predicate
        let (r, n2) := fresh n1
        .ok (r, goals ++ [Goal.wact "retractPredicate" [term] r], n2)
    | .hProcessMettaString, [source] => do
        let (term, goals, n1) ← compileExprFuel fuel env n source
        let (r, n2) := fresh n1
        .ok (r, goals ++ [Goal.wact "process_metta_string" [term] r], n2)
    | .hUnquote, [Atom.expr [Atom.sym "quote", e]] => compileAppFuel fuel env n "eval" [e]
    | .hUnquote, [e] => .ok (chainify (Atom.expr [Atom.sym "unquote", e]), [], n)
    | .hEmpty, [] => .ok (compilerTrueA, [Goal.eq compilerTrueA compilerFalseA], n) -- branch failure
    | .hCut, [] => .ok (compilerTrueA, [Goal.cut], n)
    | .hTest, [e, expected] => do
        -- Native collects every answer of `e`, unwraps a singleton, evaluates
        -- the expected expression, then performs variant comparison.
        -- [SPEC translator.pl:118-126, metta.pl:203-207]
        let (te, ge, n1) ← compileExprFuel fuel env n e
        let (answers, n2) := fresh n1
        let (tx, gx, n3) ← compileExprFuel fuel env n2 expected
        let (r, n4) := fresh n3
        .ok (r, [Goal.findall te ge answers] ++ gx ++
          [Goal.bin "#test-results" [answers, tx] r], n4)
    | .hTrace, [message, value] =>
        -- [SPEC translator.pl:74-75] trace! is a stream rewrite to
        -- `(progn (println! message) value)`; println!'s pure value is True.
        compileAppFuel fuel env n "progn"
          [Atom.expr [Atom.sym "println!", message], value]
    | .hAndThen, [a, b] =>
        -- [SPEC translator.pl:177-180] evaluate `b` only when `a` is True,
        -- then unify the enclosing result with `b`'s value. The equality is
        -- deliberately after `gb`: unlike `if`'s `build_branch/4`, this
        -- direct pinned clause does not move it ahead of branch effects.
        let (ta, ga, n1) ← compileExprFuel fuel env n a
        let (tb, gb, n2) ← compileExprFuel fuel env n1 b
        let (r, n3) := fresh n2
        .ok (r, ga ++ [Goal.ite ta
          (r, gb ++ [Goal.eq r tb])
          (r, [Goal.eq r compilerFalseA]) r], n3)
    | .hOrElse, [a, b] =>
        -- [SPEC translator.pl:181-184] skip `b` when `a` is already True;
        -- on the false path execute `b` before unifying its value with the
        -- enclosing result.
        let (ta, ga, n1) ← compileExprFuel fuel env n a
        let (tb, gb, n2) ← compileExprFuel fuel env n1 b
        let (r, n3) := fresh n2
        .ok (r, ga ++ [Goal.ite ta
          (r, [Goal.eq r compilerTrueA])
          (r, gb ++ [Goal.eq r tb]) r], n3)
    | .hHashPlus, [a, b] => compileAppFuel fuel env n "+" [a, b]   -- petta's flexible +
    | .hHashMinus, [a, b] => compileAppFuel fuel env n "-" [a, b]
    | .hCons, [h, t] => do
        -- the list constructor IS structure: narrows via unification
        let (th, gh, n1) ← compileExprFuel fuel env n h
        let (tt, gt, n2) ← compileExprFuel fuel env n1 t
        .ok (consC th tt, gh ++ gt, n2)
    | .hIf, [c, t] => do
        let (tc, gc, n1) ← compileExprFuel fuel env n c
        let (tt, gt, n2) ← compileExprFuel fuel env n1 t
        let (r, n3) := fresh n2
        let (branchAliases, thenBranch) := compileBranch r (tt, gt)
        -- [SPEC translator.pl:151-155] the condition is tested by Prolog
        -- identity (`Cv == true`), not unification. An open condition must
        -- therefore take the failing path without becoming bound to True.
        .ok (r, branchAliases ++ gc ++ [Goal.ite tc thenBranch
          (r, [Goal.eq compilerTrueA compilerFalseA]) r], n3)
    | .hIf, [c, t, e] => do
        let (tc, gc, n1) ← compileExprFuel fuel env n c
        let (tt, gt, n2) ← compileExprFuel fuel env n1 t
        let (te, ge, n3) ← compileExprFuel fuel env n2 e
        let (r, n4) := fresh n3
        let (thenAliases, thenBranch) := compileBranch r (tt, gt)
        let (elseAliases, elseBranch) := compileBranch r (te, ge)
        .ok (r, thenAliases ++ elseAliases ++ gc ++
          [Goal.ite tc thenBranch elseBranch r], n4)
    | .hLet, [p, v, b] => do
        -- [SPEC translator.pl:185-188] translate pattern, value, and body in
        -- that order; emit (Pv=V), Gp, Gv, Gi. The result terms unify first,
        -- then pattern goals (narrowing), value goals, and the body.
        let (tp, gp, n1) ← compileExprFuel fuel env n p
        let (tv, gv, n2) ← compileExprFuel fuel env n1 v
        let (tb, gb, n3) ← compileExprFuel fuel env n2 b
        .ok (tb, [Goal.eq tp tv] ++ gp ++ gv ++ gb, n3)
    | .hLetStar, [Atom.expr binds, b] => do
        match desugarLetStar? binds b with
        | some nested => compileExprFuel fuel env n nested
        | none => .error "malformed let* bindings"
    | .hCase, [scrut, Atom.expr arms] => do
        -- first-match commits (variable patterns are catch-alls in order);
        -- an `Empty` arm fires when the SCRUTINEE produces no value
        let (ts, gs, n1) ← compileExprFuel fuel env n scrut
        let (sv, n2) := fresh n1
        let (r, n3) := fresh n2
        let emptyArm := arms.findSome? (fun arm =>
          match arm with
          | Atom.expr [Atom.sym "Empty", body] => some body
          | _ => none)
        let (armGs, n4) ← compileCaseArmsFuel fuel env sv r n3 arms
        match emptyArm with
          | some body => do
              let (tb, gb, m) ← compileExprFuel fuel env n4 body
              let failGs := gb ++ [Goal.eq r tb]
              -- [SPEC translator.pl:163-176] This is deliberately the pinned
              -- `(Gk, CaseGoal) ; (\+ Gk, DefaultThen)` tree, not a soft cut.
              -- The positive guard is caller-cut-transparent; the fallback
              -- re-runs the guard under call-local negation.  `amb` introduces
              -- no barrier, and both nonempty branches already constrain `r`.
              let guard := gs ++ [Goal.eq sv ts]
              let positive := guard ++ armGs
              let fallback := negatedGoals guard ++ failGs
              .ok (r, [Goal.amb [(r, positive), (r, fallback)] r], m)
          | none =>
              -- [SPEC translator.pl:174-176] no-default `case` leaves the
              -- scrutinee goals in ordinary Prolog flow (`Gk, KeyGoal, IfGoal`);
              -- do not eagerly collect every scrutinee answer before branches.
              .ok (r, gs ++ [Goal.eq sv ts] ++ armGs, n4)
    | .hCollapse, [e] => do
        let (te, ge, n1) ← compileExprFuel fuel env n e
        let (r, n2) := fresh n1
        .ok (r, [Goal.findall te ge r], n2)
    | .hOnce, [e] => do
        let (te, ge, n1) ← compileExprFuel fuel env n e
        let (r, n2) := fresh n1
        .ok (r, [Goal.onceg te ge r], n2)
    | .hSuperpose, [Atom.expr es] =>
        if es.isEmpty then
          -- [SPEC translator.pl:112-114,414-416,419-422] Branch construction
          -- returns [], but disj_list/2 has no empty clause, so native
          -- translation fails after committing to the superpose branch.
          .error "superpose: empty"
        else do
          -- each SYNTACTIC element evaluated in its own branch (NONDET-1)
          let (branches, n1) ← compileAmbBranchesWith
            (fun counter expression =>
              compileExprFuel fuel env counter expression) n es
          let (r, n2) := fresh n1
          let normalized := compileSuperposeBranches r branches
          .ok (r, normalized.1 ++ [Goal.amb normalized.2 r], n2)
    | .hUnify, [Atom.sym "&self", pat, thn, els] => do
        if !env.defined.contains "unify" then do
          let (ts, gs, n1) ← compileListFuel fuel env n [Atom.sym "&self", pat, thn, els]
          .ok (chainOf (Atom.sym "unify" :: ts), gs, n1)
        else
          -- [SPEC lib_he.metta:24-31] space-unify: match the pattern in
          -- `&self`; on success evaluate `then`, on Empty evaluate `else`.
          let (tt, gt, n1) ← compileExprFuel fuel env n thn
          let (te, ge, n2) ← compileExprFuel fuel env n1 els
          let (r, n3) := fresh n2
          let p := chainify pat
          .ok (r, [Goal.softcut p [Goal.smatch p]
                    (gt ++ [Goal.eq r tt]) (ge ++ [Goal.eq r te])], n3)
    | .hUnify, [a, bb, thn, els] => do
        if !env.defined.contains "unify" then do
          let (ts, gs, n1) ← compileListFuel fuel env n [a, bb, thn, els]
          .ok (chainOf (Atom.sym "unify" :: ts), gs, n1)
        else
          -- soft cut: bindings from the successful unification reach `thn`
          let (ta, ga, n1) ← compileExprFuel fuel env n a
          let (tb2, gb2, n2) ← compileExprFuel fuel env n1 bb
          let (tt, gt, n3) ← compileExprFuel fuel env n2 thn
          let (te, ge, n4) ← compileExprFuel fuel env n3 els
          let (r, n5) := fresh n4
          let carry := bindingTemplate (chainOf [ta, tb2]) [a, bb]
          .ok (r, [Goal.softcut carry (ga ++ gb2 ++ [Goal.eq ta tb2])
                    (gt ++ [Goal.eq r tt]) (ge ++ [Goal.eq r te])], n5)
    | .hSucceedsPredicate, [Atom.expr (sp :: Atom.sym rel :: args)] => do
        -- [SPEC lib_spaces.metta + translator.pl:101-105,264-267]:
        -- the translator hook turns a space predicate expression into the
        -- corresponding Prolog predicate call. In PLeaTTa's space model this
        -- is exactly a space match that returns True once per proof, or False
        -- if the predicate has no proof.
        let (ts, gs, n1) ← compileExprFuel fuel env n sp
        let (r, n2) := fresh n1
        let pat := chainify (Atom.expr (Atom.sym rel :: args))
        .ok (r, gs ++ [Goal.softcut pat [Goal.smatch (spacePat ts pat)]
          [Goal.eq r compilerTrueA] [Goal.eq r compilerFalseA]], n2)
    | .hFor, [v, collection, body] =>
        -- [SPEC lib_patrick.metta:14-18] translator-rule macro:
        -- `(for $x xs body)` compiles as `(let $x (superpose xs) body)`.
        compileAppFuel fuel env n "let" [v, Atom.expr [Atom.sym "superpose", collection], body]
    | .hChain, [first, second, body] => do
        -- [SPEC translator.pl:185-188] `chain` and `let` share one native
        -- clause, which traverses their three source arguments literally from
        -- left to right.  Do not swap the first two arguments merely because
        -- conventional MeTTa uses `(chain value $pattern body)`.
        let (tFirst, gFirst, n1) ← compileExprFuel fuel env n first
        let (tSecond, gSecond, n2) ← compileExprFuel fuel env n1 second
        let (tBody, gBody, n3) ← compileExprFuel fuel env n2 body
        .ok (tBody,
          [Goal.eq tFirst tSecond] ++ gFirst ++ gSecond ++ gBody, n3)
    | .hFoldall, [f, gen, init] => do
        let (tg, gg, n1) ← compileExprFuel fuel env n gen
        let (lst, n2) := fresh n1
        let (tf, gf, n3) ← compileExprFuel fuel env n2 f
        let (ti, gi, n4) ← compileExprFuel fuel env n3 init
        let (r, n5) := fresh n4
        .ok (r, [Goal.findall tg gg lst] ++ gf ++ gi ++
                [Goal.call "#foldacc" [tf, lst, ti] r], n5)
    | .hForall, [gen, f] => do
        let (tg, gg, n1) ← compileExprFuel fuel env n gen
        let (lst, n2) := fresh n1
        let (tf, gf, n3) ← compileExprFuel fuel env n2 f
        let (r, n4) := fresh n3
        .ok (r, [Goal.findall tg gg lst] ++ gf ++
                [Goal.call "#allacc" [tf, lst] r], n4)
    | .hProgn, args => do
        if args.isEmpty then .error "progn: empty" else do
        let (ts, gs, n1) ← compileListFuel fuel env n args
        .ok (ts.getLast!, gs, n1)
    | .hProg1, args => do
        if args.isEmpty then .error "prog1: empty" else do
        let (ts, gs, n1) ← compileListFuel fuel env n args
        .ok (ts.head!, gs, n1)
    | .hWithMutex, [_mutex, body] =>
        -- [SPEC translator.pl:137-138] the mutex serializes the translated
        -- body. PLeaTTa's machine is already sequential, so its answer
        -- relation is exactly the body's answer relation.
        compileExprFuel fuel env n body
    | .hTransaction, [body] => do
        -- [SPEC translator.pl:139-140] SWI transaction/1 commits its first
        -- successful branch and rolls dynamic updates back on failure.
        let (tb, gb, n1) ← compileExprFuel fuel env n body
        let carry := bindingTemplate tb [body]
        .ok (tb, [Goal.transactiong carry gb], n1)
    | .hSuperpose, [e] => do
        -- computed tuple: spread its members at run time
        let (te, ge, n1) ← compileExprFuel fuel env n e
        let (r, n2) := fresh n1
        .ok (r, ge ++ [Goal.spread te r], n2)
    | .hHyperpose, [Atom.expr es] => do
        -- [SPEC translator.pl:129-135,417-424] `hyperpose` has the same
        -- result semantics as one evaluated branch per element. Native runs
        -- those branches concurrently; PLeaTTa preserves the answer relation.
        let (branches, n1) ← compileAmbBranchesWith
          (fun counter expression =>
            compileExprFuel fuel env counter expression) n es
        let (r, n2) := fresh n1
        .ok (r, [Goal.amb branches r], n2)
    | .hHyperpose, [e] => do
        -- Runtime/computed list path: enumerate the computed tuple, then eval
        -- each element as code (`hyperpose_runtime(Exprs, Out) :- ... eval`).
        let (te, ge, n1) ← compileExprFuel fuel env n e
        let (elem, n2) := fresh n1
        let (r, n3) := fresh n2
        .ok (r, ge ++ [Goal.spread te elem, Goal.evalg elem r], n3)
    | .hUnique, [e] => do
        -- stream dedup: distinct solutions, order preserved
        let (te, ge, n1) ← compileExprFuel fuel env n e
        let (lst, n2) := fresh n1
        let (ded, n3) := fresh n2
        let (r, n4) := fresh n3
        .ok (r, [Goal.findall te ge lst,
                 Goal.bin "unique-atom" [lst] ded, Goal.spread ded r], n4)
    | .hUnion, [e1, e2] => do
        -- Unreachable from source: the shaped form is rewritten before core
        -- classification, and every unshaped `union` classifies as ordinary.
        let (t1, g1, n1) ← compileExprFuel fuel env n e1
        let (t2, g2, n2) ← compileExprFuel fuel env n1 e2
        let (l1, n3) := fresh n2
        let (l2, n4) := fresh n3
        let (cc, n5) := fresh n4
        let (r, n6) := fresh n5
        .ok (r, [Goal.findall t1 g1 l1, Goal.findall t2 g2 l2,
                 Goal.bin "union-atom" [l1, l2] cc, Goal.spread cc r], n6)
    | .hIntersection, [e1, e2] => do
        -- See `hUnion`: retained only to keep the classifier result type
        -- stable while the source-facing classifier excludes this branch.
        let (t1, g1, n1) ← compileExprFuel fuel env n e1
        let (t2, g2, n2) ← compileExprFuel fuel env n1 e2
        let (l1, n3) := fresh n2
        let (l2, n4) := fresh n3
        let (cc, n5) := fresh n4
        let (r, n6) := fresh n5
        .ok (r, [Goal.findall t1 g1 l1, Goal.findall t2 g2 l2,
                 Goal.bin "intersection-atom" [l1, l2] cc, Goal.spread cc r], n6)
    | .hSubtraction, [e1, e2] => do
        -- See `hUnion`: this constructor is not returned for source heads.
        let (t1, g1, n1) ← compileExprFuel fuel env n e1
        let (t2, g2, n2) ← compileExprFuel fuel env n1 e2
        let (l1, n3) := fresh n2
        let (l2, n4) := fresh n3
        let (cc, n5) := fresh n4
        let (r, n6) := fresh n5
        .ok (r, [Goal.findall t1 g1 l1, Goal.findall t2 g2 l2,
                 Goal.bin "subtraction-atom" [l1, l2] cc, Goal.spread cc r], n6)
    | .hEval, [e] => do
        let (te, ge, n1) ← compileExprFuel fuel env n e
        let (r, n2) := fresh n1
        .ok (r, ge ++ [Goal.evalg te r], n2)
    | .hCatch, [e] => do
        -- [SPEC translator.pl:293-300] catch wraps the translated goals for
        -- the expression, returning normal answers, failing on ordinary no
        -- answer, and reifying runtime/type exceptions as `(Error ...)`.
        let (te, ge, n1) ← compileExprFuel fuel env n e
        let (r, n2) := fresh n1
        .ok (r, [Goal.catchg te ge r], n2)
    | .hCall, [Atom.expr [Atom.sym "superpose", source]] => do
        -- [SPEC metta.pl:105, translator.pl:278-283] manual dispatch to the
        -- registered `superpose/2` predicate enumerates an already-computed
        -- list. Stream rewrites deliberately pass through this exact path.
        let (term, goals, n1) ← compileExprFuel fuel env n source
        let (r, n2) := fresh n1
        .ok (r, goals ++ [Goal.spread term r], n2)
    | .hCall, [Atom.expr (Atom.sym f :: xs)] => do
        -- [SPEC translator.pl:271-276] manual compile-time dispatch:
        -- translate the embedded expression's arguments, then emit a direct
        -- predicate call `f(args..., Out)`.
        let (ts, gs, n1) ← compileArgsAtFuel fuel env n f 0 xs
        let (r, n2) := fresh n1
        .ok (r, gs ++ [Goal.call f ts r], n2)
    | .hReduce, [e] => compileAppFuel fuel env n "eval" [e]
    | .hGetTypeSpace, [_sp, e] => compileAppFuel fuel env n "get-type" [e]
    | .hGetAtoms, [sp] => do
        let (ts, gs, n1) ← compileExprFuel fuel env n sp
        let (r, n2) := fresh n1
        .ok (r, gs ++ [Goal.smatch (spacePat ts r)], n2)
    | .hGetType, [e] => do
        -- PeTTa's automatic function dispatch translates the argument before
        -- asking for its type [SPEC translator.pl:301-310,410].
        let (te, ge, n1) ← compileExprFuel fuel env n e
        let (r, n2) := fresh n1
        .ok (r, ge ++ [Goal.bin "get-type" [te] r], n2)
    | .hGetMetatype, [e] => do
        let (te, ge, n1) ← compileExprFuel fuel env n e
        let (r, n2) := fresh n1
        .ok (r, ge ++ [Goal.bin "get-metatype" [te] r], n2)
    | .hMatch, [sp, p, tmpl] => do
        let (ts, gs, n0) ← compileExprFuel fuel env n sp
        -- A `,`-headed pattern is a CONJUNCTIVE query: one smatch per conjunct,
        -- shared bindings joining them (the relational join).
        let (tt, gt, n1) ← compileExprFuel fuel env n0 tmpl
        let pats := match p with
          | Atom.expr (Atom.sym "," :: ps) => ps
          | _ => [p]
        .ok (tt, gs ++ pats.map (fun q => Goal.smatch (spacePat ts (chainify q))) ++ gt, n1)
    | .hFind, [sp, p] => do
        -- [SPEC lib_spaces.metta:8-11] `find` is match-as-Boolean, but its
        -- successful True answers must carry pattern bindings into the caller.
        let (ts, gs, n0) ← compileExprFuel fuel env n sp
        let (r, n1) := fresh n0
        let pat := chainify p
        .ok (r, gs ++ [Goal.softcut pat [Goal.smatch (spacePat ts pat)]
          [Goal.eq r compilerTrueA] [Goal.eq r compilerFalseA]], n1)
    | .hMatch, [sp, p] => do
        -- under-applied registered fun => partial value [SPEC translator.pl:58]
        .ok (partialC "match" (chainOf [chainify sp, chainify p]), [], n)
    | .hDoubleEqual, [Atom.expr [Atom.sym "size-atom", e], kA] => do
        -- shape constraint: `(== (size-atom e) k)` with literal k constrains
        -- e's STRUCTURE (a k-slot chain) — structural, so enumeration
        -- terminates exactly as in native PeTTa/swipl
        match kA with
        | Atom.gnd (Metta.Ground.int k) => do
            let (te, ge, n1) ← compileExprFuel fuel env n e
            let (slots, n2) := (List.range k.toNat).foldl
              (fun (acc : List Atom × Nat) _ =>
                let (v, m) := fresh acc.2; (acc.1 ++ [v], m)) ([], n1)
            .ok (compilerTrueA, ge ++ [Goal.eq te (chainOf slots)], n2)
        | _ => .error "==: size-atom vs non-literal"
    | .hEqual, [a, b] => do
        -- Boolean unification predicate [SPEC metta.pl registers `=/3`]:
        -- success returns True with bindings, failure returns False.
        let (ta, ga, n1) ← compileExprFuel fuel env n a
        let (tb, gb, n2) ← compileExprFuel fuel env n1 b
        let (r, n3) := fresh n2
        let carry := bindingTemplate (chainOf [ta, tb]) [a, b]
        .ok (r, [Goal.softcut carry (ga ++ gb ++ [Goal.eq ta tb])
                  [Goal.eq r compilerTrueA] [Goal.eq r compilerFalseA]], n3)
    | .hAddAtom, [sp, a] => do
        -- [SPEC spaces.pl:5-7 plus native probes] `add-atom` asserts the atom
        -- argument as data; surrounding bindings instantiate its variables at
        -- run time, but known/builtin subexpressions inside the atom are not
        -- evaluated. Rule forms still pass syntactically so the world effect can
        -- compile the asserted clause.
        let (tsp, gsp, n0) ← compileExprFuel fuel env n sp
        match a with
        | Atom.expr (Atom.sym "=" :: _) =>
            let (r, n1) := fresh n0
            .ok (r, gsp ++ [Goal.wact "add-atom" [tsp, chainify a] r], n1)
        | _ =>
            let (r, n1) := fresh n0
            .ok (r, gsp ++ [Goal.wact "add-atom" [tsp, chainify a] r], n1)
    | .hRemoveAtom, [sp, a] => do
        let (tsp, gsp, n0) ← compileExprFuel fuel env n sp
        match a with
        | Atom.expr (Atom.sym "=" :: _) =>
            let (r, n1) := fresh n0
            .ok (r, gsp ++ [Goal.wact "remove-atom" [tsp, chainify a] r], n1)
        | _ =>
            let (r, n1) := fresh n0
            .ok (r, gsp ++ [Goal.wact "remove-atom" [tsp, chainify a] r], n1)
    | .hBind, [name, Atom.expr [Atom.sym "new-state", e]] => do
        -- [SPEC metta.pl:240] bind!(A, [new-state,B], C) :- change-state!(A,B,C)
        compileAppFuel fuel env n "change-state!" [name, e]
    | .hBind, [_name, _value] =>
        -- [SPEC metta.pl:240,303] `bind!` is registered, but native PeTTa only
        -- defines the `(new-state ...)` clause; other values fail as calls.
        .ok (compilerTrueA, [Goal.eq compilerTrueA compilerFalseA], n)
    | .hGetState, [name] => do
        let (tn, gn, n1) ← compileExprFuel fuel env n name
        let (r, n2) := fresh n1
        .ok (r, gn ++ [Goal.wact "get-state" [tn] r], n2)
    | .hChangeState, [name, e] => do
        let (tn, gn, n1) ← compileExprFuel fuel env n name
        let (te, ge, n2) ← compileExprFuel fuel env n1 e
        let (r, n3) := fresh n2
        .ok (r, gn ++ ge ++ [Goal.wact "change-state!" [tn, te] r], n3)
    | _, _ =>
        compileAppDefaultWith
          (fun counter => compileArgsAtFuel fuel env counter h 0 args)
          (fun counter parameterTypes =>
            compileTypedArgsFuel fuel env counter args parameterTypes)
          (fun counter => compileListFuel fuel env counter args)
          env n h args
termination_by structural fuel _ _ _ _ => fuel

/-- Compile the ordered arms of `case`.  Giving this traversal its own fuelled
equations keeps both the list recursion and its calls back into expression
compilation visible to the kernel. -/
def compileCaseArmsFuel : Nat → CEnv → Atom → Atom → Nat → List Atom →
    CompileM (List Goal × Nat)
  | 0, _, _, _, _, _ => .error "compiler fuel exhausted"
  | _ + 1, _, _, _, m, [] =>
      .ok ([Goal.eq compilerTrueA compilerFalseA], m)
  | fuel + 1, env, scrutinee, result, m,
      Atom.expr [Atom.sym name, body] :: more =>
      if name == "Empty" then
        compileCaseArmsFuel fuel env scrutinee result m more
      else do
        let (compiledPattern, patternGoals, m1) ←
          compilePatternFuel fuel env m (Atom.sym name)
        let (compiledBody, bodyGoals, m2) ←
          compileExprFuel fuel env m1 body
        let (elseGoals, m3) ←
          compileCaseArmsFuel fuel env scrutinee result m2 more
        let carry := bindingTemplate compiledPattern [Atom.sym name]
        .ok ([committedIfGoal carry
          (patternGoals ++ [Goal.eq compiledPattern scrutinee])
          (bodyGoals ++ [Goal.eq result compiledBody]) elseGoals], m3)
  | fuel + 1, env, scrutinee, result, m,
      Atom.expr [pattern, body] :: more => do
      let (compiledPattern, patternGoals, m1) ←
        compilePatternFuel fuel env m pattern
      let (compiledBody, bodyGoals, m2) ←
        compileExprFuel fuel env m1 body
      let (elseGoals, m3) ←
        compileCaseArmsFuel fuel env scrutinee result m2 more
      let carry := bindingTemplate compiledPattern [pattern]
      .ok ([committedIfGoal carry
        (patternGoals ++ [Goal.eq compiledPattern scrutinee])
        (bodyGoals ++ [Goal.eq result compiledBody]) elseGoals], m3)
  | _ + 1, _, _, _, _, _ :: _ => .error "case: malformed arm"
termination_by structural fuel _ _ _ _ _ => fuel

/-- Compile application arguments from a given positional index, honoring the
`Atom`-typed staging mask.  Structural list recursion exposes the sequencing
equations needed by compiler-adequacy proofs. -/
def compileArgsAtFuel : Nat → CEnv → Nat → String → Nat → List Atom →
    CompileM (List Atom × List Goal × Nat)
  | 0, _, _, _, _, _ => .error "compiler fuel exhausted"
  | _ + 1, _, n, _, _, [] => .ok ([], [], n)
  | fuel + 1, env, n, h, index, a :: args => do
      if env.atomTyped h index then
        -- Expression-typed arguments stay as source data. Native PeTTa's data
        -- input is a Prolog list term; PLeaTTa's corresponding value is a
        -- chain, so cons-patterns like `(cons , $xs)` can narrow it.
        let (ts, gs, n1) ←
          compileArgsAtFuel fuel env n h (index + 1) args
        .ok (chainify a :: ts, gs, n1)
      else
        let (t, g, n1) ← compileExprFuel fuel env n a
        let (ts, gs, n2) ←
          compileArgsAtFuel fuel env n1 h (index + 1) args
        .ok (t :: ts, g ++ gs, n2)
termination_by structural fuel _ _ _ _ _ => fuel

/-- Translate arguments against one explicit pinned arrow-chain input-type
list. Unlike the staging-mask helper, this traversal retains each full
declared type and therefore emits refined type checks.
[SPEC translator.pl:362-370] -/
def compileTypedArgsFuel : Nat → CEnv → Nat → List Atom → List Atom →
    CompileM (List Atom × List Goal × Nat)
  | 0, _, _, _, _ => .error "compiler fuel exhausted"
  -- [SPEC translator.pl:362] the cut base clause ignores any unconsumed
  -- declared parameter types once all supplied source arguments are gone.
  | _ + 1, _, counter, [], _ => .ok ([], [], counter)
  | fuel + 1, env, counter, source :: sources, ty :: types => do
      if ty == Atom.sym "Expression" then
        let (terms, goals, nextCounter) ←
          compileTypedArgsFuel fuel env counter sources types
        .ok (chainify source :: terms, goals, nextCounter)
      else
        let (term, termGoals, middleCounter) ←
          compileExprFuel fuel env counter source
        let (checkGoals, checkedCounter) :=
          compileTypeCheck term ty middleCounter
        let (terms, goals, nextCounter) ←
          compileTypedArgsFuel fuel env checkedCounter sources types
        .ok (term :: terms, termGoals ++ checkGoals ++ goals, nextCounter)
  | _ + 1, _, _, _, _ => .error "typed arguments: arity mismatch"
termination_by structural fuel _ _ _ _ => fuel

def compileListFuel : Nat → CEnv → Nat → List Atom →
    CompileM (List Atom × List Goal × Nat)
  | 0, _, _, _ => .error "compiler fuel exhausted"
  | _ + 1, _, n, [] => .ok ([], [], n)
  | fuel + 1, env, n, e :: es => do
      let (t, g, n1) ← compileExprFuel fuel env n e
      let (ts, gs, n2) ← compileListFuel fuel env n1 es
      .ok (t :: ts, g ++ gs, n2)
termination_by structural fuel _ _ _ => fuel

def compilePatternListFuel : Nat → CEnv → Nat → List Atom →
    CompileM (List Atom × List Goal × Nat)
  | 0, _, _, _ => .error "compiler fuel exhausted"
  | _ + 1, _, n, [] => .ok ([], [], n)
  | fuel + 1, env, n, e :: es => do
      let (t, g, n1) ← compilePatternFuel fuel env n e
      let (ts, gs, n2) ← compilePatternListFuel fuel env n1 es
      .ok (t :: ts, g ++ gs, n2)
termination_by structural fuel _ _ _ => fuel

end

/-- Exact compiler equation for an already-materialized partial/2 value.

Naming this equation keeps downstream proofs independent of the raw private
compound spine while the executable match remains exact-arity and
definitionally checkable. -/
@[simp] theorem compileExprFuel_partialC (fuel : Nat) (env : CEnv)
    (counter : Nat) (functor : String) (encodedArguments : Atom) :
    compileExprFuel (fuel + 1) env counter
        (partialC functor encodedArguments) =
      .ok (partialC functor encodedArguments, [], counter) := by
  simp [partialC, prologCompoundC, prologCompoundTagA, chainOf, consC,
    nilA, compileExprFuel]

/-- Publicly named fuelled argument traversal, starting at argument zero. -/
def compileArgsFuel (fuel : Nat) (env : CEnv) (counter : Nat)
    (head : String) (arguments : List Atom) :
    CompileM (List Atom × List Goal × Nat) :=
  compileArgsAtFuel fuel env counter head 0 arguments

/-- Exhausted argument-traversal fuel is an explicit compiler error.  This
equation is exported manually because Lean does not generate a usable
standalone equation theorem for this member of the mutual compiler. -/
theorem compileArgsAtFuel_zero_eq (env : CEnv) (counter : Nat)
    (head : String) (index : Nat) (arguments : List Atom) :
    compileArgsAtFuel 0 env counter head index arguments =
      .error "compiler fuel exhausted" := by
  rfl

/-- Exhausted case-arm fuel is an explicit compiler error. -/
theorem compileCaseArmsFuel_zero_eq (env : CEnv) (scrutinee result : Atom)
    (counter : Nat) (arms : List Atom) :
    compileCaseArmsFuel 0 env scrutinee result counter arms =
      .error "compiler fuel exhausted" := by
  rfl

/-- Empty case-arm traversal emits the explicit failing fallback and preserves
the counter. -/
theorem compileCaseArmsFuel_nil_eq (fuel : Nat) (env : CEnv)
    (scrutinee result : Atom) (counter : Nat) :
    compileCaseArmsFuel (fuel + 1) env scrutinee result counter [] =
      .ok ([Goal.eq compilerTrueA compilerFalseA], counter) := by
  rfl

/-- An `Empty` arm is handled by the enclosing case compiler and therefore is
skipped by the ordinary ordered-arm traversal. -/
theorem compileCaseArmsFuel_empty_eq (fuel : Nat) (env : CEnv)
    (scrutinee result : Atom) (counter : Nat) (body : Atom)
    (more : List Atom) :
    compileCaseArmsFuel (fuel + 1) env scrutinee result counter
        (Atom.expr [Atom.sym "Empty", body] :: more) =
      compileCaseArmsFuel fuel env scrutinee result counter more := by
  rfl

/-- A variable-pattern arm exposes its three ordered recursive compiler
calls. -/
theorem compileCaseArmsFuel_var_pair_eq (fuel : Nat) (env : CEnv)
    (scrutinee result : Atom) (counter : Nat) (name : String) (body : Atom)
    (more : List Atom) :
    compileCaseArmsFuel (fuel + 1) env scrutinee result counter
        (Atom.expr [Atom.var name, body] :: more) = (do
      let (compiledPattern, patternGoals, patternCounter) ←
        compilePatternFuel fuel env counter (Atom.var name)
      let (compiledBody, bodyGoals, bodyCounter) ←
        compileExprFuel fuel env patternCounter body
      let (elseGoals, nextCounter) ←
        compileCaseArmsFuel fuel env scrutinee result bodyCounter more
      let carry := bindingTemplate compiledPattern [Atom.var name]
      .ok ([committedIfGoal carry
        (patternGoals ++ [Goal.eq compiledPattern scrutinee])
        (bodyGoals ++ [Goal.eq result compiledBody]) elseGoals], nextCounter)) := by
  change (do
    let (compiledPattern, patternGoals, patternCounter) ←
      compilePatternFuel fuel env counter (Atom.var name)
    let (compiledBody, bodyGoals, bodyCounter) ←
      compileExprFuel fuel env patternCounter body
    let (elseGoals, nextCounter) ←
      compileCaseArmsFuel fuel env scrutinee result bodyCounter more
    let carry := bindingTemplate compiledPattern [Atom.var name]
    .ok ([committedIfGoal carry
      (patternGoals ++ [Goal.eq compiledPattern scrutinee])
      (bodyGoals ++ [Goal.eq result compiledBody]) elseGoals], nextCounter)) = _
  rfl

/-- A grounded-pattern arm exposes the same ordered recursive calls. -/
theorem compileCaseArmsFuel_gnd_pair_eq (fuel : Nat) (env : CEnv)
    (scrutinee result : Atom) (counter : Nat) (ground : Metta.Ground)
    (body : Atom) (more : List Atom) :
    compileCaseArmsFuel (fuel + 1) env scrutinee result counter
        (Atom.expr [Atom.gnd ground, body] :: more) = (do
      let (compiledPattern, patternGoals, patternCounter) ←
        compilePatternFuel fuel env counter (Atom.gnd ground)
      let (compiledBody, bodyGoals, bodyCounter) ←
        compileExprFuel fuel env patternCounter body
      let (elseGoals, nextCounter) ←
        compileCaseArmsFuel fuel env scrutinee result bodyCounter more
      let carry := bindingTemplate compiledPattern [Atom.gnd ground]
      .ok ([committedIfGoal carry
        (patternGoals ++ [Goal.eq compiledPattern scrutinee])
        (bodyGoals ++ [Goal.eq result compiledBody]) elseGoals], nextCounter)) := by
  change (do
    let (compiledPattern, patternGoals, patternCounter) ←
      compilePatternFuel fuel env counter (Atom.gnd ground)
    let (compiledBody, bodyGoals, bodyCounter) ←
      compileExprFuel fuel env patternCounter body
    let (elseGoals, nextCounter) ←
      compileCaseArmsFuel fuel env scrutinee result bodyCounter more
    let carry := bindingTemplate compiledPattern [Atom.gnd ground]
    .ok ([committedIfGoal carry
      (patternGoals ++ [Goal.eq compiledPattern scrutinee])
      (bodyGoals ++ [Goal.eq result compiledBody]) elseGoals], nextCounter)) = _
  rfl

/-- A compound-pattern arm exposes the same ordered recursive calls. -/
theorem compileCaseArmsFuel_expr_pair_eq (fuel : Nat) (env : CEnv)
    (scrutinee result : Atom) (counter : Nat) (items : List Atom)
    (body : Atom) (more : List Atom) :
    compileCaseArmsFuel (fuel + 1) env scrutinee result counter
        (Atom.expr [Atom.expr items, body] :: more) = (do
      let (compiledPattern, patternGoals, patternCounter) ←
        compilePatternFuel fuel env counter (Atom.expr items)
      let (compiledBody, bodyGoals, bodyCounter) ←
        compileExprFuel fuel env patternCounter body
      let (elseGoals, nextCounter) ←
        compileCaseArmsFuel fuel env scrutinee result bodyCounter more
      let carry := bindingTemplate compiledPattern [Atom.expr items]
      .ok ([committedIfGoal carry
        (patternGoals ++ [Goal.eq compiledPattern scrutinee])
        (bodyGoals ++ [Goal.eq result compiledBody]) elseGoals], nextCounter)) := by
  change (do
    let (compiledPattern, patternGoals, patternCounter) ←
      compilePatternFuel fuel env counter (Atom.expr items)
    let (compiledBody, bodyGoals, bodyCounter) ←
      compileExprFuel fuel env patternCounter body
    let (elseGoals, nextCounter) ←
      compileCaseArmsFuel fuel env scrutinee result bodyCounter more
    let carry := bindingTemplate compiledPattern [Atom.expr items]
    .ok ([committedIfGoal carry
      (patternGoals ++ [Goal.eq compiledPattern scrutinee])
      (bodyGoals ++ [Goal.eq result compiledBody]) elseGoals], nextCounter)) = _
  rfl

/-- A non-`Empty` symbol-pattern arm exposes the same ordered recursive
calls. -/
theorem compileCaseArmsFuel_sym_pair_eq (fuel : Nat) (env : CEnv)
    (scrutinee result : Atom) (counter : Nat) (name : String)
    (notEmpty : name ≠ "Empty") (body : Atom) (more : List Atom) :
    compileCaseArmsFuel (fuel + 1) env scrutinee result counter
        (Atom.expr [Atom.sym name, body] :: more) = (do
      let (compiledPattern, patternGoals, patternCounter) ←
        compilePatternFuel fuel env counter (Atom.sym name)
      let (compiledBody, bodyGoals, bodyCounter) ←
        compileExprFuel fuel env patternCounter body
      let (elseGoals, nextCounter) ←
        compileCaseArmsFuel fuel env scrutinee result bodyCounter more
      let carry := bindingTemplate compiledPattern [Atom.sym name]
      .ok ([committedIfGoal carry
        (patternGoals ++ [Goal.eq compiledPattern scrutinee])
        (bodyGoals ++ [Goal.eq result compiledBody]) elseGoals], nextCounter)) := by
  change (if name == "Empty" then
      compileCaseArmsFuel fuel env scrutinee result counter more
    else do
      let (compiledPattern, patternGoals, patternCounter) ←
        compilePatternFuel fuel env counter (Atom.sym name)
      let (compiledBody, bodyGoals, bodyCounter) ←
        compileExprFuel fuel env patternCounter body
      let (elseGoals, nextCounter) ←
        compileCaseArmsFuel fuel env scrutinee result bodyCounter more
      let carry := bindingTemplate compiledPattern [Atom.sym name]
      .ok ([committedIfGoal carry
        (patternGoals ++ [Goal.eq compiledPattern scrutinee])
        (bodyGoals ++ [Goal.eq result compiledBody]) elseGoals], nextCounter)) = _
  simp [notEmpty]

/-- Non-expression case arms are malformed. -/
theorem compileCaseArmsFuel_var_malformed_eq (fuel : Nat) (env : CEnv)
    (scrutinee result : Atom) (counter : Nat) (name : String)
    (more : List Atom) :
    compileCaseArmsFuel (fuel + 1) env scrutinee result counter
        (Atom.var name :: more) = .error "case: malformed arm" := by
  rfl

theorem compileCaseArmsFuel_sym_malformed_eq (fuel : Nat) (env : CEnv)
    (scrutinee result : Atom) (counter : Nat) (name : String)
    (more : List Atom) :
    compileCaseArmsFuel (fuel + 1) env scrutinee result counter
        (Atom.sym name :: more) = .error "case: malformed arm" := by
  rfl

theorem compileCaseArmsFuel_gnd_malformed_eq (fuel : Nat) (env : CEnv)
    (scrutinee result : Atom) (counter : Nat) (ground : Metta.Ground)
    (more : List Atom) :
    compileCaseArmsFuel (fuel + 1) env scrutinee result counter
        (Atom.gnd ground :: more) = .error "case: malformed arm" := by
  rfl

/-- Expression arms with zero, one, or at least three members are malformed. -/
theorem compileCaseArmsFuel_expr_nil_malformed_eq (fuel : Nat) (env : CEnv)
    (scrutinee result : Atom) (counter : Nat) (more : List Atom) :
    compileCaseArmsFuel (fuel + 1) env scrutinee result counter
        (Atom.expr [] :: more) = .error "case: malformed arm" := by
  rfl

theorem compileCaseArmsFuel_expr_singleton_malformed_eq (fuel : Nat)
    (env : CEnv) (scrutinee result : Atom) (counter : Nat) (item : Atom)
    (more : List Atom) :
    compileCaseArmsFuel (fuel + 1) env scrutinee result counter
        (Atom.expr [item] :: more) = .error "case: malformed arm" := by
  cases item <;> rfl

theorem compileCaseArmsFuel_expr_many_malformed_eq (fuel : Nat) (env : CEnv)
    (scrutinee result : Atom) (counter : Nat) (first second third : Atom)
    (rest more : List Atom) :
    compileCaseArmsFuel (fuel + 1) env scrutinee result counter
        (Atom.expr (first :: second :: third :: rest) :: more) =
      .error "case: malformed arm" := by
  cases first <;> rfl

/-- Exhausted pattern-compilation fuel is an explicit compiler error. -/
theorem compilePatternFuel_zero_eq (env : CEnv) (counter : Nat)
    (pattern : Atom) :
    compilePatternFuel 0 env counter pattern =
      .error "compiler fuel exhausted" := by
  rfl

set_option maxHeartbeats 2000000 in
/-- Empty typed-argument traversal preserves the counter and emits no terms or
goals.  [SPEC translator.pl:362] -/
theorem compileArgsAtFuel_nil_eq (fuel : Nat) (env : CEnv) (counter : Nat)
    (head : String) (index : Nat) :
    compileArgsAtFuel (fuel + 1) env counter head index [] =
      .ok ([], [], counter) := by
  rfl

set_option maxHeartbeats 2000000 in
/-- An `Expression`-typed argument is staged as source data before traversal
continues at the next position.  [SPEC translator.pl:363-365] -/
theorem compileArgsAtFuel_staged_eq (fuel : Nat) (env : CEnv)
    (counter : Nat) (head : String) (index : Nat) (source : Atom)
    (sources : List Atom) (staged : env.atomTyped head index = true) :
    compileArgsAtFuel (fuel + 1) env counter head index (source :: sources) =
      (do
        let (terms, goals, nextCounter) ←
          compileArgsAtFuel fuel env counter head (index + 1) sources
        pure (chainify source :: terms, goals, nextCounter)) := by
  change (if env.atomTyped head index then
      (do
        let (terms, goals, nextCounter) ←
          compileArgsAtFuel fuel env counter head (index + 1) sources
        pure (chainify source :: terms, goals, nextCounter))
    else
      (do
        let (term, termGoals, middleCounter) ←
          compileExprFuel fuel env counter source
        let (terms, goals, nextCounter) ←
          compileArgsAtFuel fuel env middleCounter head (index + 1) sources
        pure (term :: terms, termGoals ++ goals, nextCounter))) = _
  simp only [staged, if_true]

set_option maxHeartbeats 2000000 in
/-- A non-`Expression` argument is translated before traversal continues at
the next position.  [SPEC translator.pl:363,365-370] -/
theorem compileArgsAtFuel_evaluated_eq (fuel : Nat) (env : CEnv)
    (counter : Nat) (head : String) (index : Nat) (source : Atom)
    (sources : List Atom) (evaluated : env.atomTyped head index = false) :
    compileArgsAtFuel (fuel + 1) env counter head index (source :: sources) =
      (do
        let (term, termGoals, middleCounter) ←
          compileExprFuel fuel env counter source
        let (terms, goals, nextCounter) ←
          compileArgsAtFuel fuel env middleCounter head (index + 1) sources
        pure (term :: terms, termGoals ++ goals, nextCounter)) := by
  change (if env.atomTyped head index then
      (do
        let (terms, goals, nextCounter) ←
          compileArgsAtFuel fuel env counter head (index + 1) sources
        pure (chainify source :: terms, goals, nextCounter))
    else
      (do
        let (term, termGoals, middleCounter) ←
          compileExprFuel fuel env counter source
        let (terms, goals, nextCounter) ←
          compileArgsAtFuel fuel env middleCounter head (index + 1) sources
        pure (term :: terms, termGoals ++ goals, nextCounter))) = _
  simp only [evaluated, Bool.false_eq_true, ↓reduceIte]

/-- The three pinned no-check input types leave goals and the fresh counter
unchanged. [SPEC translator.pl:367-368] -/
theorem compileTypeCheck_unchecked_symbol_eq (value : Atom) (counter : Nat) :
    (∀ expected ∈ ["%Undefined%", "Atom", "Expression"],
      compileTypeCheck value (.sym expected) counter = ([], counter)) := by
  intro expected member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    simp [compileTypeCheck, compileTypeCheckWhen, typeRequiresCheck]

/-- The two pinned no-check result types leave goals and the fresh counter
unchanged. [SPEC translator.pl:355-356] -/
theorem compileResultTypeCheck_unchecked_symbol_eq (value : Atom)
    (counter : Nat) :
    (∀ expected ∈ ["%Undefined%", "Atom"],
      compileResultTypeCheck value (.sym expected) counter = ([], counter)) := by
  intro expected member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;>
    simp [compileResultTypeCheck, compileTypeCheckWhen,
      resultTypeRequiresCheck]

/-- A supported simple refined type emits the exact pinned soft-cut fallback
and consumes two generated variables. [SPEC translator.pl:367-370] -/
theorem compileTypeCheck_refined_symbol_eq (value : Atom) (counter : Nat)
    (expected : String)
    (notUndefined : expected ≠ "%Undefined%")
    (notAtom : expected ≠ "Atom")
    (notExpression : expected ≠ "Expression")
    (notTrue : expected ≠ "true")
    (notFalse : expected ≠ "false") :
    compileTypeCheck value (.sym expected) counter =
      ([Goal.softcut (.sym "#u")
         [Goal.bin "get-type" [value] (.var s!"_q{counter}"),
          Goal.eq (.var s!"_q{counter}") (.sym expected)]
         []
         [Goal.bin "get-metatype" [value] (.var s!"_q{counter + 1}"),
          Goal.eq (.var s!"_q{counter + 1}") (.sym expected)]],
       counter + 2) := by
  simp [compileTypeCheck, compileTypeCheckWhen, typeRequiresCheck,
    notUndefined, notAtom, notExpression, notTrue, notFalse, fresh, chainify,
    canonBool]

/-- Every supported simple result type other than the two unchecked result
types emits the exact pinned soft-cut fallback and consumes two generated
variables. In particular, `Expression` is checked here.
[SPEC translator.pl:349-356] -/
theorem compileResultTypeCheck_refined_symbol_eq (value : Atom)
    (counter : Nat) (expected : String)
    (notUndefined : expected ≠ "%Undefined%")
    (notAtom : expected ≠ "Atom")
    (notTrue : expected ≠ "true")
    (notFalse : expected ≠ "false") :
    compileResultTypeCheck value (.sym expected) counter =
      ([Goal.softcut (.sym "#u")
         [Goal.bin "get-type" [value] (.var s!"_q{counter}"),
          Goal.eq (.var s!"_q{counter}") (.sym expected)]
         []
         [Goal.bin "get-metatype" [value] (.var s!"_q{counter + 1}"),
          Goal.eq (.var s!"_q{counter + 1}") (.sym expected)]],
       counter + 2) := by
  simp [compileResultTypeCheck, compileTypeCheckWhen,
    resultTypeRequiresCheck, notUndefined, notAtom, notTrue, notFalse, fresh,
    chainify, canonBool]

/-- Empty exact typed traversal preserves the counter. -/
theorem compileTypedArgsFuel_nil_eq (fuel : Nat) (env : CEnv)
    (counter : Nat) :
    compileTypedArgsFuel (fuel + 1) env counter [] [] =
      .ok ([], [], counter) := by
  rfl

/-- `Expression` preserves its source argument as data and recurses without a
type check. [SPEC translator.pl:363-365] -/
theorem compileTypedArgsFuel_expression_eq (fuel : Nat) (env : CEnv)
    (counter : Nat) (source : Atom) (sources types : List Atom) :
    compileTypedArgsFuel (fuel + 1) env counter (source :: sources)
        (.sym "Expression" :: types) =
      (do
        let (terms, goals, nextCounter) ←
          compileTypedArgsFuel fuel env counter sources types
        pure (chainify source :: terms, goals, nextCounter)) := by
  simp only [compileTypedArgsFuel,
    show ((.sym "Expression" : Atom) == .sym "Expression") = true by decide,
    if_true]
  rfl

/-- Every non-`Expression` declared type evaluates its source argument, emits
the type-specific check, then recurses left-to-right. -/
theorem compileTypedArgsFuel_evaluated_eq (fuel : Nat) (env : CEnv)
    (counter : Nat) (source ty : Atom) (sources types : List Atom)
    (notExpression : (ty == .sym "Expression") = false) :
    compileTypedArgsFuel (fuel + 1) env counter (source :: sources)
        (ty :: types) =
      (do
        let (term, termGoals, middleCounter) ←
          compileExprFuel fuel env counter source
        let (checkGoals, checkedCounter) :=
          compileTypeCheck term ty middleCounter
        let (terms, goals, nextCounter) ←
          compileTypedArgsFuel fuel env checkedCounter sources types
        pure (term :: terms, termGoals ++ checkGoals ++ goals, nextCounter)) := by
  simp only [compileTypedArgsFuel, notExpression, Bool.false_eq_true,
    ↓reduceIte]
  rfl

/-- Typed traversal fails when a supplied source argument has no declared
parameter type. [SPEC translator.pl:363-370] -/
theorem compileTypedArgsFuel_missing_type_eq (fuel : Nat) (env : CEnv)
    (counter : Nat) (source : Atom) (sources : List Atom) :
    compileTypedArgsFuel (fuel + 1) env counter (source :: sources) [] =
      .error "typed arguments: arity mismatch" := by
  rfl

/-- Pinned `translate_args_by_type([], _, [], [])` ignores every surplus
declared parameter type after source arguments are exhausted.
[SPEC translator.pl:362] -/
theorem compileTypedArgsFuel_surplus_type_eq (fuel : Nat) (env : CEnv)
    (counter : Nat) (ty : Atom) (types : List Atom) :
    compileTypedArgsFuel (fuel + 1) env counter [] (ty :: types) =
      .ok ([], [], counter) := by
  rfl

set_option maxHeartbeats 2000000 in
/-- Empty expression-list compilation preserves the counter and emits no
terms or goals. -/
theorem compileListFuel_nil_eq (fuel : Nat) (env : CEnv) (counter : Nat) :
    compileListFuel (fuel + 1) env counter [] = .ok ([], [], counter) := by
  rw [compileListFuel.eq_2]

set_option maxHeartbeats 2000000 in
/-- Nonempty expression-list compilation exposes its left-to-right counter
and goal threading to adequacy proofs. -/
theorem compileListFuel_cons_eq (fuel : Nat) (env : CEnv) (counter : Nat)
    (source : Atom) (sources : List Atom) :
    compileListFuel (fuel + 1) env counter (source :: sources) = (do
      let (term, goals, nextCounter) ←
        compileExprFuel fuel env counter source
      let (terms, remainingGoals, finalCounter) ←
        compileListFuel fuel env nextCounter sources
      pure (term :: terms, goals ++ remainingGoals, finalCounter)) := by
  rw [compileListFuel.eq_3]
  rfl

set_option maxHeartbeats 2000000 in
/-- Atomic pattern variables are preserved, emit no constraints, and leave
the fresh-variable counter unchanged. -/
theorem compilePatternFuel_var_eq (fuel : Nat) (env : CEnv) (counter : Nat)
    (name : String) :
    compilePatternFuel (fuel + 1) env counter (.var name) =
      .ok (.var name, [], counter) := by
  rfl

set_option maxHeartbeats 2000000 in
/-- Atomic pattern symbols are preserved modulo the executable boolean
representation, with no emitted constraints. -/
theorem compilePatternFuel_sym_eq (fuel : Nat) (env : CEnv) (counter : Nat)
    (name : String) :
    compilePatternFuel (fuel + 1) env counter (.sym name) =
      .ok (canonBool (.sym name), [], counter) := by
  rfl

set_option maxHeartbeats 2000000 in
/-- Atomic grounded pattern values are preserved modulo the executable boolean
representation, with no emitted constraints. -/
theorem compilePatternFuel_gnd_eq (fuel : Nat) (env : CEnv) (counter : Nat)
    (value : Metta.Ground) :
    compilePatternFuel (fuel + 1) env counter (.gnd value) =
      .ok (canonBool (.gnd value), [], counter) := by
  rfl

set_option maxHeartbeats 2000000 in
/-- The empty source list is the atomic empty-list pattern. -/
theorem compilePatternFuel_nil_eq (fuel : Nat) (env : CEnv)
    (counter : Nat) :
    compilePatternFuel (fuel + 1) env counter (.expr []) =
      .ok (nilA, [], counter) := by
  rfl

set_option maxHeartbeats 2000000 in
/-- A source `(cons Head Tail)` pattern recursively constrains its head before
its tail, appends the resulting goals in that order, and constructs one
internal list cell.  [SPEC translator.pl:3-8] -/
theorem compilePatternFuel_cons_eq (fuel : Nat) (env : CEnv) (counter : Nat)
    (head tail : Atom) :
    compilePatternFuel (fuel + 1) env counter
        (.expr [.sym "cons", head, tail]) = (do
      let (headTerm, headGoals, headCounter) ←
        compilePatternFuel fuel env counter head
      let (tailTerm, tailGoals, nextCounter) ←
        compilePatternFuel fuel env headCounter tail
      pure (consC headTerm tailTerm, headGoals ++ tailGoals, nextCounter)) := by
  rfl

/-- Internal compiler chains remain data in pattern position. -/
theorem compilePatternFuel_chain_eq (fuel : Nat) (env : CEnv)
    (counter : Nat) (head tail : Atom) :
    compilePatternFuel (fuel + 1) env counter
        (.expr [.sym "#c", head, tail]) =
      .ok (.expr [.sym "#c", head, tail], [], counter) := by
  rfl

/-- Non-symbol-headed pattern applications recursively compile their members
as ordered pattern data. -/
theorem compilePatternFuel_var_head_eq (fuel : Nat) (env : CEnv)
    (counter : Nat) (name : String) (arguments : List Atom) :
    compilePatternFuel (fuel + 1) env counter
        (.expr (.var name :: arguments)) = (do
      let (terms, goals, nextCounter) ←
        compilePatternListFuel fuel env counter (.var name :: arguments)
      .ok (chainOf terms, goals, nextCounter)) := by
  change (do
    let (terms, goals, nextCounter) ←
      compilePatternListFuel fuel env counter (.var name :: arguments)
    .ok (chainOf terms, goals, nextCounter)) = _
  rfl

theorem compilePatternFuel_gnd_head_eq (fuel : Nat) (env : CEnv)
    (counter : Nat) (ground : Metta.Ground) (arguments : List Atom) :
    compilePatternFuel (fuel + 1) env counter
        (.expr (.gnd ground :: arguments)) = (do
      let (terms, goals, nextCounter) ←
        compilePatternListFuel fuel env counter (.gnd ground :: arguments)
      .ok (chainOf terms, goals, nextCounter)) := by
  change (do
    let (terms, goals, nextCounter) ←
      compilePatternListFuel fuel env counter (.gnd ground :: arguments)
    .ok (chainOf terms, goals, nextCounter)) = _
  rfl

theorem compilePatternFuel_expr_head_eq (fuel : Nat) (env : CEnv)
    (counter : Nat) (items : List Atom) (arguments : List Atom) :
    compilePatternFuel (fuel + 1) env counter
        (.expr (.expr items :: arguments)) = (do
      let (terms, goals, nextCounter) ←
        compilePatternListFuel fuel env counter (.expr items :: arguments)
      .ok (chainOf terms, goals, nextCounter)) := by
  change (do
    let (terms, goals, nextCounter) ←
      compilePatternListFuel fuel env counter (.expr items :: arguments)
    .ok (chainOf terms, goals, nextCounter)) = _
  rfl

/-- Symbol-headed patterns outside the two structural two-argument cases use
ordinary function-pattern dispatch or ordered pattern-list construction. -/
theorem compilePatternFuel_sym_nil_eq (fuel : Nat) (env : CEnv)
    (counter : Nat) (name : String) :
    compilePatternFuel (fuel + 1) env counter (.expr [.sym name]) =
      (if env.defined.contains name || env.isBin name || specialHead name then
        compileExprFuel fuel env counter (.expr [.sym name])
      else do
        let (terms, goals, nextCounter) ←
          compilePatternListFuel fuel env counter []
        .ok (chainOf (.sym name :: terms), goals, nextCounter)) := by
  change (if env.defined.contains name || env.isBin name || specialHead name
    then compileExprFuel fuel env counter (.expr [.sym name])
    else do
      let (terms, goals, nextCounter) ←
        compilePatternListFuel fuel env counter []
      .ok (chainOf (.sym name :: terms), goals, nextCounter)) = _
  rfl

theorem compilePatternFuel_sym_singleton_eq (fuel : Nat) (env : CEnv)
    (counter : Nat) (name : String) (argument : Atom) :
    compilePatternFuel (fuel + 1) env counter
        (.expr [.sym name, argument]) =
      (if env.defined.contains name || env.isBin name || specialHead name then
        compileExprFuel fuel env counter (.expr [.sym name, argument])
      else do
        let (terms, goals, nextCounter) ←
          compilePatternListFuel fuel env counter [argument]
        .ok (chainOf (.sym name :: terms), goals, nextCounter)) := by
  change (if env.defined.contains name || env.isBin name || specialHead name
    then compileExprFuel fuel env counter (.expr [.sym name, argument])
    else do
      let (terms, goals, nextCounter) ←
        compilePatternListFuel fuel env counter [argument]
      .ok (chainOf (.sym name :: terms), goals, nextCounter)) = _
  rfl

theorem compilePatternFuel_sym_many_eq (fuel : Nat) (env : CEnv)
    (counter : Nat) (name : String) (first second third : Atom)
    (rest : List Atom) :
    compilePatternFuel (fuel + 1) env counter
        (.expr (.sym name :: first :: second :: third :: rest)) =
      (if env.defined.contains name || env.isBin name || specialHead name then
        compileExprFuel fuel env counter
          (.expr (.sym name :: first :: second :: third :: rest))
      else do
        let (terms, goals, nextCounter) ←
          compilePatternListFuel fuel env counter
            (first :: second :: third :: rest)
        .ok (chainOf (.sym name :: terms), goals, nextCounter)) := by
  change (if env.defined.contains name || env.isBin name || specialHead name
    then compileExprFuel fuel env counter
      (.expr (.sym name :: first :: second :: third :: rest))
    else do
      let (terms, goals, nextCounter) ←
        compilePatternListFuel fuel env counter
          (first :: second :: third :: rest)
      .ok (chainOf (.sym name :: terms), goals, nextCounter)) = _
  rfl

theorem compilePatternFuel_sym_pair_other_eq (fuel : Nat) (env : CEnv)
    (counter : Nat) (name : String) (first second : Atom)
    (notChain : name ≠ "#c") (notCons : name ≠ "cons") :
    compilePatternFuel (fuel + 1) env counter
        (.expr [.sym name, first, second]) =
      (if env.defined.contains name || env.isBin name || specialHead name then
        compileExprFuel fuel env counter (.expr [.sym name, first, second])
      else do
        let (terms, goals, nextCounter) ←
          compilePatternListFuel fuel env counter [first, second]
        .ok (chainOf (.sym name :: terms), goals, nextCounter)) := by
  change (if name == "#c" then _ else if name == "cons" then _ else
    if env.defined.contains name || env.isBin name || specialHead name then
      compileExprFuel fuel env counter (.expr [.sym name, first, second])
    else do
      let (terms, goals, nextCounter) ←
        compilePatternListFuel fuel env counter [first, second]
      .ok (chainOf (.sym name :: terms), goals, nextCounter)) = _
  simp [notChain, notCons]

set_option maxHeartbeats 2000000 in
/-- Empty pattern-list compilation preserves the counter and emits no goals. -/
theorem compilePatternListFuel_nil_eq (fuel : Nat) (env : CEnv)
    (counter : Nat) :
    compilePatternListFuel (fuel + 1) env counter [] =
      .ok ([], [], counter) := by
  rw [compilePatternListFuel.eq_2]

set_option maxHeartbeats 2000000 in
/-- Nonempty pattern-list compilation exposes its ordered recursive shape. -/
theorem compilePatternListFuel_cons_eq (fuel : Nat) (env : CEnv)
    (counter : Nat) (source : Atom) (sources : List Atom) :
    compilePatternListFuel (fuel + 1) env counter (source :: sources) = (do
      let (term, goals, nextCounter) ←
        compilePatternFuel fuel env counter source
      let (terms, remainingGoals, finalCounter) ←
        compilePatternListFuel fuel env nextCounter sources
      pure (term :: terms, goals ++ remainingGoals, finalCounter)) := by
  rw [compilePatternListFuel.eq_3]
  rfl

set_option maxHeartbeats 2000000 in
/-- Once stream rewriting and translator-rule shadowing are excluded, the
application dispatcher is exactly the core classifier. This is the reusable
priority bridge for every unshadowed application adequacy proof. -/
theorem compileAppFuel_unshadowed_eq (fuel : Nat) (env : CEnv)
    (counter : Nat) (head : String) (arguments : List Atom)
    (noRewrite : rewriteStreamOp? head arguments = none)
    (noHook : env.translatorRules.contains head = false) :
    compileAppFuel (fuel + 1) env counter head arguments =
      compileAppCoreFuel fuel env counter head arguments := by
  rw [compileAppFuel.eq_2]
  rw [noRewrite]
  simp only
  rw [noHook]
  rfl

/-- Expression-level form of `compileAppFuel_unshadowed_eq`. The explicit
internal-cons premise discharges the sole application-pattern overlap. -/
theorem compileExprFuel_unshadowed_app_eq (fuel : Nat) (env : CEnv)
    (counter : Nat) (head : String) (arguments : List Atom)
    (noRewrite : rewriteStreamOp? head arguments = none)
    (notInternalCons : ∀ first second,
      arguments = [first, second] → head ≠ "#c")
    (noHook : env.translatorRules.contains head = false) :
    compileExprFuel (fuel + 2) env counter
        (.expr (.sym head :: arguments)) =
      compileAppCoreFuel fuel env counter head arguments := by
  rw [show fuel + 2 = (fuel + 1) + 1 by omega]
  rw [compileExprFuel.eq_8 (x_4 := notInternalCons)]
  exact compileAppFuel_unshadowed_eq fuel env counter head arguments
    noRewrite noHook

set_option maxHeartbeats 2000000 in
/-- A successful pinned stream rewrite is selected before translator-rule
lookup and re-enters expression compilation with the rewritten source.  The
internal-cons premise discharges the expression compiler's sole overlapping
application pattern; every pinned stream head satisfies it. -/
theorem compileExprFuel_stream_rewrite_eq (fuel : Nat) (env : CEnv)
    (counter : Nat) (head : String) (arguments : List Atom) (expanded : Atom)
    (notInternalCons : ∀ first second,
      arguments = [first, second] → head ≠ "#c")
    (rewrite : rewriteStreamOp? head arguments = some expanded) :
    compileExprFuel (fuel + 2) env counter
        (.expr (.sym head :: arguments)) =
      compileExprFuel fuel env counter expanded := by
  rw [show fuel + 2 = (fuel + 1) + 1 by omega]
  rw [compileExprFuel.eq_8 (x_4 := notInternalCons)]
  rw [compileAppFuel.eq_2, rewrite]

set_option maxHeartbeats 2000000 in
/-- Exact executable shape for a nonempty syntactic `superpose` once its
ordered branches have been compiled. -/
theorem compileExprFuel_superpose_eq (branchFuel : Nat) (env : CEnv)
    (counter branchCounter : Nat) (first : Atom) (sources : List Atom)
    (branches normalizedBranches : List (Atom × List Goal))
    (aliases : List Goal)
    (noHook : env.translatorRules.contains "superpose" = false)
    (compiled : compileAmbBranchesWith
      (fun next expression => compileExprFuel branchFuel env next expression)
      counter (first :: sources) = .ok (branches, branchCounter))
    (normalized : compileSuperposeBranches (.var s!"_q{branchCounter}") branches =
      (aliases, normalizedBranches)) :
    compileExprFuel (branchFuel + 3) env counter
        (.expr [.sym "superpose", .expr (first :: sources)]) =
      .ok (.var s!"_q{branchCounter}",
        aliases ++ [Goal.amb normalizedBranches
          (.var s!"_q{branchCounter}")], branchCounter + 1) := by
  rw [show branchFuel + 3 = (branchFuel + 1) + 2 by omega]
  rw [compileExprFuel_unshadowed_app_eq (branchFuel + 1) env counter
    "superpose" [.expr (first :: sources)] (by rfl) (by simp) noHook]
  simp only [compileAppCoreFuel, classifyAppCoreHead, List.isEmpty_cons]
  rw [compiled]
  simp only [Bool.false_eq_true, if_false, Bind.bind, Except.bind, fresh]
  rw [normalized]

/-- Exact executable rejection corresponding to pinned `disj_list/2` having
no empty clause.  Translator-rule priority remains explicit. -/
theorem compileExprFuel_empty_superpose_eq (fuel : Nat) (env : CEnv)
    (counter : Nat)
    (noHook : env.translatorRules.contains "superpose" = false) :
    compileExprFuel (fuel + 3) env counter
        (.expr [.sym "superpose", .expr []]) =
      .error "superpose: empty" := by
  rw [show fuel + 3 = (fuel + 1) + 2 by omega]
  rw [compileExprFuel_unshadowed_app_eq (fuel + 1) env counter
    "superpose" [.expr []] (by rfl) (by simp) noHook]
  rfl

set_option maxHeartbeats 2000000 in
/-- Exact executable shape of pinned manual dispatch to `superpose/2`: compile
the already-computed list, allocate the enclosing result, then enumerate the
list through `Goal.spread`. -/
theorem compileExprFuel_call_superpose_eq (bodyFuel : Nat) (env : CEnv)
    (counter : Nat) (source term : Atom) (goals : List Goal)
    (nextCounter : Nat)
    (noHook : env.translatorRules.contains "call" = false)
    (body : compileExprFuel bodyFuel env counter source =
      .ok (term, goals, nextCounter)) :
    compileExprFuel (bodyFuel + 3) env counter
        (.expr [.sym "call", .expr [.sym "superpose", source]]) =
      .ok (.var s!"_q{nextCounter}",
        goals ++ [Goal.spread term (.var s!"_q{nextCounter}")],
        nextCounter + 1) := by
  rw [show bodyFuel + 3 = (bodyFuel + 1) + 2 by omega]
  rw [compileExprFuel_unshadowed_app_eq (bodyFuel + 1) env counter "call"
    [.expr [.sym "superpose", source]] (by rfl) (by simp) noHook]
  simp only [compileAppCoreFuel, classifyAppCoreHead]
  rw [body]
  rfl

set_option maxHeartbeats 2000000 in
/-- A head classified outside every pinned special-form clause reaches the
generic application dispatcher.  This small equation hides the generated
negative premises of the large special-form match without changing the
executable compiler. -/
theorem compileAppCoreFuel_other_eq (fuel : Nat) (env : CEnv)
    (counter : Nat) (head : String) (arguments : List Atom)
    (other : classifyAppCoreHead head = .other) :
    compileAppCoreFuel (fuel + 1) env counter head arguments =
      compileAppDefaultWith
        (fun next => compileArgsAtFuel fuel env next head 0 arguments)
        (fun next types =>
          compileTypedArgsFuel fuel env next arguments types)
        (fun next => compileListFuel fuel env next arguments)
        env counter head arguments := by
  rw [compileAppCoreFuel.eq_69] <;> simp_all only <;> simp

set_option maxHeartbeats 2000000 in
/-- Exact executable equation for a direct fixed-arity builtin application.

The argument traversal is supplied as evidence because it is shared with the
independent adequacy proof. All higher-priority dispatch premises remain
explicit, and the arity equality is stated over the compiled argument list so
partial application cannot be silently folded into this branch. -/
theorem compileExprFuel_fixed_builtin_eq (argumentFuel : Nat) (env : CEnv)
    (counter : Nat) (head : String) (arguments terms : List Atom)
    (goals : List Goal) (nextCounter : Nat)
    (noRewrite : rewriteStreamOp? head arguments = none)
    (notInternalCons : ∀ first second,
      arguments = [first, second] → head ≠ "#c")
    (noHook : env.translatorRules.contains head = false)
    (other : classifyAppCoreHead head = .other)
    (notProlog : env.prologFunctions.contains head = false)
    (notDefined : env.defined.contains head = false)
    (isBuiltin : env.isBin head = true)
    (fixedArity : compileBinArity head = some terms.length)
    (argumentsCompiled :
      compileArgsAtFuel argumentFuel env counter head 0 arguments =
        .ok (terms, goals, nextCounter)) :
    compileExprFuel (argumentFuel + 3) env counter
        (.expr (.sym head :: arguments)) =
      .ok (.var s!"_q{nextCounter}",
        goals ++ [Goal.bin head terms (.var s!"_q{nextCounter}")],
        nextCounter + 1) := by
  rw [show argumentFuel + 3 = (argumentFuel + 1) + 2 by omega]
  rw [compileExprFuel_unshadowed_app_eq (argumentFuel + 1) env counter head
    arguments noRewrite notInternalCons noHook]
  rw [compileAppCoreFuel_other_eq argumentFuel env counter head arguments
    other]
  simp only [compileAppDefaultWith]
  rw [notProlog]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [notDefined]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [isBuiltin]
  simp only [↓reduceIte]
  rw [argumentsCompiled]
  rw [fixedArity]
  simp only [Bind.bind, Except.bind]
  simp [fresh]

set_option maxHeartbeats 2000000 in
/-- Exact executable equation for an ordinary direct call to a source-defined
function. Every higher-priority dispatch condition is explicit. Typed
nondeterministic dispatch and incomplete-arity partial values are excluded by
their own premises rather than being hidden in the conclusion. -/
theorem compileExprFuel_defined_direct_eq (argumentFuel : Nat) (env : CEnv)
    (counter : Nat) (head : String) (arguments terms : List Atom)
    (goals : List Goal) (nextCounter : Nat)
    (noRewrite : rewriteStreamOp? head arguments = none)
    (notInternalCons : ∀ first second,
      arguments = [first, second] → head ≠ "#c")
    (noHook : env.translatorRules.contains head = false)
    (other : classifyAppCoreHead head = .other)
    (notProlog : env.prologFunctions.contains head = false)
    (defined : env.defined.contains head = true)
    (typedInputsAvailable :
      typedDispatchInputShortage (env.typeChains head) arguments.length = false)
    (direct : shouldUseTypedDispatch (env.typeChains head) = false)
    (argumentsCompiled :
      compileArgsAtFuel argumentFuel env counter head 0 arguments =
        .ok (terms, goals, nextCounter))
    (completeArity : (env.arities head).contains terms.length = true) :
    compileExprFuel (argumentFuel + 3) env counter
        (.expr (.sym head :: arguments)) =
      .ok (.var s!"_q{nextCounter}",
        goals ++ [Goal.call head terms (.var s!"_q{nextCounter}")],
        nextCounter + 1) := by
  rw [show argumentFuel + 3 = (argumentFuel + 1) + 2 by omega]
  rw [compileExprFuel_unshadowed_app_eq (argumentFuel + 1) env counter head
    arguments noRewrite notInternalCons noHook]
  rw [compileAppCoreFuel_other_eq argumentFuel env counter head arguments
    other]
  simp only [compileAppDefaultWith]
  rw [notProlog]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [defined]
  simp only [↓reduceIte]
  rw [typedInputsAvailable]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [direct]
  simp only [Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind]
  rw [argumentsCompiled]
  simp only
  rw [completeArity]
  simp [fresh]

set_option maxHeartbeats 2000000 in
/-- Exact executable equation for the incomplete-arity source-defined branch.
The same ordinary dispatch premises as a direct call apply, but a failed
arity lookup returns the partial-function value without allocating a result
variable or appending a call goal. -/
theorem compileExprFuel_defined_partial_eq (argumentFuel : Nat) (env : CEnv)
    (counter : Nat) (head : String) (arguments terms : List Atom)
    (goals : List Goal) (nextCounter : Nat)
    (noRewrite : rewriteStreamOp? head arguments = none)
    (notInternalCons : ∀ first second,
      arguments = [first, second] → head ≠ "#c")
    (noHook : env.translatorRules.contains head = false)
    (other : classifyAppCoreHead head = .other)
    (notProlog : env.prologFunctions.contains head = false)
    (defined : env.defined.contains head = true)
    (typedInputsAvailable :
      typedDispatchInputShortage (env.typeChains head) arguments.length = false)
    (direct : shouldUseTypedDispatch (env.typeChains head) = false)
    (argumentsCompiled :
      compileArgsAtFuel argumentFuel env counter head 0 arguments =
        .ok (terms, goals, nextCounter))
    (incompleteArity : (env.arities head).contains terms.length = false) :
    compileExprFuel (argumentFuel + 3) env counter
        (.expr (.sym head :: arguments)) =
      .ok (partialValue head terms, goals, nextCounter) := by
  rw [show argumentFuel + 3 = (argumentFuel + 1) + 2 by omega]
  rw [compileExprFuel_unshadowed_app_eq (argumentFuel + 1) env counter head
    arguments noRewrite notInternalCons noHook]
  rw [compileAppCoreFuel_other_eq argumentFuel env counter head arguments
    other]
  simp only [compileAppDefaultWith]
  rw [notProlog]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [defined]
  simp only [↓reduceIte]
  rw [typedInputsAvailable]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [direct]
  simp only [Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind]
  rw [argumentsCompiled]
  simp only
  rw [incompleteArity]
  rfl

set_option maxHeartbeats 2000000 in
/-- Exact executable equation for an ordinary unary builtin application.

Every dispatch premise is explicit: stream rewriting and translator-rule,
imported-Prolog, and locally-defined ownership all take priority over the
builtin catalog.  The arity premise excludes partial application. -/
theorem compileExprFuel_unary_builtin_eq (argumentFuel : Nat) (env : CEnv)
    (counter : Nat) (head : String) (argument term : Atom)
    (goals : List Goal) (nextCounter : Nat)
    (noRewrite : rewriteStreamOp? head [argument] = none)
    (noHook : env.translatorRules.contains head = false)
    (other : classifyAppCoreHead head = .other)
    (notProlog : env.prologFunctions.contains head = false)
    (notDefined : env.defined.contains head = false)
    (isBuiltin : env.isBin head = true)
    (unary : compileBinArity head = some 1)
    (argumentCompiled :
      compileArgsAtFuel argumentFuel env counter head 0 [argument] =
        .ok ([term], goals, nextCounter)) :
    compileExprFuel (argumentFuel + 3) env counter
        (.expr [.sym head, argument]) =
      .ok (.var s!"_q{nextCounter}",
        goals ++ [Goal.bin head [term] (.var s!"_q{nextCounter}")],
        nextCounter + 1) := by
  exact compileExprFuel_fixed_builtin_eq argumentFuel env counter head
    [argument] [term] goals nextCounter noRewrite (by simp) noHook other
    notProlog notDefined isBuiltin (by simpa using unary) argumentCompiled

set_option maxHeartbeats 2000000 in
/-- Negative sequencing example: native `progn` requires at least one
expression, so the empty form is rejected explicitly. -/
theorem compileExprFuel_progn_empty_eq (fuel counter : Nat) (env : CEnv)
    (noHook : env.translatorRules.contains "progn" = false) :
    compileExprFuel (fuel + 3) env counter (.expr [.sym "progn"]) =
      .error "progn: empty" := by
  rw [show fuel + 3 = (fuel + 2) + 1 by omega]
  rw [compileExprFuel.eq_8 (x_4 := by simp)]
  rw [show fuel + 2 = (fuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_36]
  all_goals try simp only [classifyAppCoreHead]
  rfl

set_option maxHeartbeats 2000000 in
/-- Negative sequencing example: native `prog1` requires at least one
expression, so the empty form is rejected explicitly. -/
theorem compileExprFuel_prog1_empty_eq (fuel counter : Nat) (env : CEnv)
    (noHook : env.translatorRules.contains "prog1" = false) :
    compileExprFuel (fuel + 3) env counter (.expr [.sym "prog1"]) =
      .error "prog1: empty" := by
  rw [show fuel + 3 = (fuel + 2) + 1 by omega]
  rw [compileExprFuel.eq_8 (x_4 := by simp)]
  rw [show fuel + 2 = (fuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_37]
  all_goals try simp only [classifyAppCoreHead]
  rfl

set_option maxHeartbeats 2000000 in
/-- A nonempty `progn` selects the last value produced by its already-compiled
left-to-right argument sequence. -/
theorem compileExprFuel_progn_eq (listFuel : Nat) (env : CEnv)
    (counter : Nat) (source : Atom) (sources terms : List Atom)
    (goals : List Goal) (nextCounter : Nat)
    (noHook : env.translatorRules.contains "progn" = false)
    (compiled : compileListFuel listFuel env counter (source :: sources) =
      .ok (terms, goals, nextCounter)) :
    compileExprFuel (listFuel + 3) env counter
        (.expr (.sym "progn" :: source :: sources)) =
      .ok (terms.getLast!, goals, nextCounter) := by
  rw [show listFuel + 3 = (listFuel + 2) + 1 by omega]
  rw [compileExprFuel.eq_8 (x_4 := by simp)]
  rw [show listFuel + 2 = (listFuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_36]
  all_goals try simp only [classifyAppCoreHead]
  simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
  rw [compiled]
  rfl

set_option maxHeartbeats 2000000 in
/-- A nonempty `prog1` selects the first value produced by its already-compiled
left-to-right argument sequence. -/
theorem compileExprFuel_prog1_eq (listFuel : Nat) (env : CEnv)
    (counter : Nat) (source : Atom) (sources terms : List Atom)
    (goals : List Goal) (nextCounter : Nat)
    (noHook : env.translatorRules.contains "prog1" = false)
    (compiled : compileListFuel listFuel env counter (source :: sources) =
      .ok (terms, goals, nextCounter)) :
    compileExprFuel (listFuel + 3) env counter
        (.expr (.sym "prog1" :: source :: sources)) =
      .ok (terms.head!, goals, nextCounter) := by
  rw [show listFuel + 3 = (listFuel + 2) + 1 by omega]
  rw [compileExprFuel.eq_8 (x_4 := by simp)]
  rw [show listFuel + 2 = (listFuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_37]
  all_goals try simp only [classifyAppCoreHead]
  simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
  rw [compiled]
  rfl

set_option maxHeartbeats 2000000 in
/-- A singleton `progn` returns its only value while preserving that
expression's ordered goals and fresh-variable counter.  Positivity of the
child budget supplies the one list-cell step for the empty tail. -/
theorem compileExprFuel_progn_singleton_eq (bodyFuel : Nat)
    (positive : 0 < bodyFuel) (env : CEnv) (counter : Nat)
    (source term : Atom) (goals : List Goal) (nextCounter : Nat)
    (noHook : env.translatorRules.contains "progn" = false)
    (body : compileExprFuel bodyFuel env counter source =
      .ok (term, goals, nextCounter)) :
    compileExprFuel (bodyFuel + 4) env counter
        (.expr [.sym "progn", source]) =
      .ok (term, goals, nextCounter) := by
  rw [show bodyFuel + 4 = (bodyFuel + 3) + 1 by omega]
  rw [compileExprFuel.eq_8 (x_4 := by simp)]
  rw [show bodyFuel + 3 = (bodyFuel + 2) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [rewriteStreamOp?, rewriteStreamOpForHead]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [show bodyFuel + 2 = (bodyFuel + 1) + 1 by omega]
  rw [compileAppCoreFuel.eq_36]
  all_goals try simp only [classifyAppCoreHead]
  simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
  rw [compileListFuel_cons_eq, body]
  dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind]
  obtain ⟨tailFuel, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  rw [compileListFuel_nil_eq]
  dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind,
    Pure.pure, Applicative.toPure, Monad.toApplicative, Except.pure]
  simp [List.getLast!]

set_option maxHeartbeats 2000000 in
/-- A singleton `prog1` returns its only value while preserving that
expression's ordered goals and fresh-variable counter. -/
theorem compileExprFuel_prog1_singleton_eq (bodyFuel : Nat)
    (positive : 0 < bodyFuel) (env : CEnv) (counter : Nat)
    (source term : Atom) (goals : List Goal) (nextCounter : Nat)
    (noHook : env.translatorRules.contains "prog1" = false)
    (body : compileExprFuel bodyFuel env counter source =
      .ok (term, goals, nextCounter)) :
    compileExprFuel (bodyFuel + 4) env counter
        (.expr [.sym "prog1", source]) =
      .ok (term, goals, nextCounter) := by
  rw [show bodyFuel + 4 = (bodyFuel + 3) + 1 by omega]
  rw [compileExprFuel.eq_8 (x_4 := by simp)]
  rw [show bodyFuel + 3 = (bodyFuel + 2) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [rewriteStreamOp?, rewriteStreamOpForHead]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [show bodyFuel + 2 = (bodyFuel + 1) + 1 by omega]
  rw [compileAppCoreFuel.eq_37]
  all_goals try simp only [classifyAppCoreHead]
  simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
  rw [compileListFuel_cons_eq, body]
  dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind]
  obtain ⟨tailFuel, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  rw [compileListFuel_nil_eq]
  dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind,
    Pure.pure, Applicative.toPure, Monad.toApplicative, Except.pure]
  simp [List.head!]

set_option maxHeartbeats 2000000 in
/-- `collapse` compiles its child, allocates one result variable, and records
the child's complete ordered answer bag with `findall`. -/
theorem compileExprFuel_collapse_eq (bodyFuel : Nat) (env : CEnv)
    (counter : Nat) (source term : Atom) (goals : List Goal)
    (nextCounter : Nat)
    (noHook : env.translatorRules.contains "collapse" = false)
    (body : compileExprFuel bodyFuel env counter source =
      .ok (term, goals, nextCounter)) :
    compileExprFuel (bodyFuel + 3) env counter
        (.expr [.sym "collapse", source]) =
      .ok (.var s!"_q{nextCounter}",
        [Goal.findall term goals (.var s!"_q{nextCounter}")],
        nextCounter + 1) := by
  rw [show bodyFuel + 3 = (bodyFuel + 2) + 1 by omega]
  rw [compileExprFuel.eq_8 (x_4 := by simp)]
  rw [show bodyFuel + 2 = (bodyFuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_26, body]
  all_goals try simp only [classifyAppCoreHead]
  rfl

set_option maxHeartbeats 2000000 in
/-- Pinned `Predicate/2` is a runtime `=../2` conversion, not a compile-time
wrapper.  Its sole argument follows the ordinary typed staging traversal,
then the compiler allocates exactly one result and appends exactly one owned
builtin goal.  Supplying the traversal as evidence keeps both the evaluated
and explicitly `Expression`-staged cases in one reusable equation.
[SPEC metta.pl:275; translator.pl:310-370] -/
theorem compileExprFuel_Predicate_eq (argumentFuel : Nat) (env : CEnv)
    (counter : Nat) (source payload : Atom) (goals : List Goal)
    (nextCounter : Nat)
    (noHook : env.translatorRules.contains "Predicate" = false)
    (argumentCompiled :
      compileArgsAtFuel argumentFuel env counter "Predicate" 0 [source] =
        .ok ([payload], goals, nextCounter)) :
    compileExprFuel (argumentFuel + 3) env counter
        (.expr [.sym "Predicate", source]) =
      .ok (.var s!"_q{nextCounter}",
        goals ++ [Goal.bin "Predicate" [payload]
          (.var s!"_q{nextCounter}")],
        nextCounter + 1) := by
  rw [show argumentFuel + 3 = (argumentFuel + 2) + 1 by omega]
  rw [compileExprFuel.eq_8 (x_4 := by simp)]
  rw [show argumentFuel + 2 = (argumentFuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_def]
  simp only [classifyAppCoreHead]
  rw [argumentCompiled]
  rfl

set_option maxHeartbeats 2000000 in
/-- Locally owned `assertaPredicate` compiles its payload, allocates one
result, and appends exactly one sealed front-insertion world action.  The
equation is fuel-parametric and therefore reusable by the independent
translation adequacy proof. -/
theorem compileExprFuel_assertaPredicate_eq (payloadFuel : Nat) (env : CEnv)
    (counter : Nat) (source payload : Atom) (goals : List Goal)
    (nextCounter : Nat)
    (noHook : env.translatorRules.contains "assertaPredicate" = false)
    (compiled : compileExprFuel payloadFuel env counter source =
      .ok (payload, goals, nextCounter)) :
    compileExprFuel (payloadFuel + 3) env counter
        (.expr [.sym "assertaPredicate", source]) =
      .ok (.var s!"_q{nextCounter}",
        goals ++
          [Goal.wact "assertaPredicate" [payload]
            (.var s!"_q{nextCounter}")],
        nextCounter + 1) := by
  rw [show payloadFuel + 3 = (payloadFuel + 2) + 1 by omega]
  rw [compileExprFuel.eq_8 (x_4 := by simp)]
  rw [show payloadFuel + 2 = (payloadFuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_6, compiled]
  all_goals try simp only [classifyAppCoreHead]
  rfl

set_option maxHeartbeats 2000000 in
/-- Locally owned `assertzPredicate` has the corresponding exact
back-insertion world-action shape. -/
theorem compileExprFuel_assertzPredicate_eq (payloadFuel : Nat) (env : CEnv)
    (counter : Nat) (source payload : Atom) (goals : List Goal)
    (nextCounter : Nat)
    (noHook : env.translatorRules.contains "assertzPredicate" = false)
    (compiled : compileExprFuel payloadFuel env counter source =
      .ok (payload, goals, nextCounter)) :
    compileExprFuel (payloadFuel + 3) env counter
        (.expr [.sym "assertzPredicate", source]) =
      .ok (.var s!"_q{nextCounter}",
        goals ++
          [Goal.wact "assertzPredicate" [payload]
            (.var s!"_q{nextCounter}")],
        nextCounter + 1) := by
  rw [show payloadFuel + 3 = (payloadFuel + 2) + 1 by omega]
  rw [compileExprFuel.eq_8 (x_4 := by simp)]
  rw [show payloadFuel + 2 = (payloadFuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_7, compiled]
  all_goals try simp only [classifyAppCoreHead]
  rfl

set_option maxHeartbeats 2000000 in
/-- Locally owned `retractPredicate` has the same ordered payload/result
lowering, with the actual first-unifying removal kept inside the sealed world
action. [SPEC metta.pl:279-280; translator.pl:310-324,335-346] -/
theorem compileExprFuel_retractPredicate_eq (payloadFuel : Nat) (env : CEnv)
    (counter : Nat) (source payload : Atom) (goals : List Goal)
    (nextCounter : Nat)
    (noHook : env.translatorRules.contains "retractPredicate" = false)
    (compiled : compileExprFuel payloadFuel env counter source =
      .ok (payload, goals, nextCounter)) :
    compileExprFuel (payloadFuel + 3) env counter
        (.expr [.sym "retractPredicate", source]) =
      .ok (.var s!"_q{nextCounter}",
        goals ++
          [Goal.wact "retractPredicate" [payload]
            (.var s!"_q{nextCounter}")],
        nextCounter + 1) := by
  rw [show payloadFuel + 3 = (payloadFuel + 2) + 1 by omega]
  rw [compileExprFuel.eq_8 (x_4 := by simp)]
  rw [show payloadFuel + 2 = (payloadFuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_8, compiled]
  all_goals try simp only [classifyAppCoreHead]
  rfl

set_option maxHeartbeats 2000000 in
/-- Executable `once` shape: compile the body, allocate a fresh result, and
capture the first body answer through `onceg`. Native translation instead
retains the body term; their observational correspondence is a separate
unification obligation. -/
theorem compileExprFuel_once_eq (bodyFuel : Nat) (env : CEnv)
    (counter : Nat) (source term : Atom) (goals : List Goal)
    (nextCounter : Nat)
    (noHook : env.translatorRules.contains "once" = false)
    (body : compileExprFuel bodyFuel env counter source =
      .ok (term, goals, nextCounter)) :
    compileExprFuel (bodyFuel + 3) env counter
        (.expr [.sym "once", source]) =
      .ok (.var s!"_q{nextCounter}",
        [Goal.onceg term goals (.var s!"_q{nextCounter}")],
        nextCounter + 1) := by
  rw [show bodyFuel + 3 = (bodyFuel + 2) + 1 by omega]
  rw [compileExprFuel.eq_8 (x_4 := by simp)]
  rw [show bodyFuel + 2 = (bodyFuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_27, body]
  all_goals try simp only [classifyAppCoreHead]
  rfl

set_option maxHeartbeats 2000000 in
/-- The two-argument conditional compiles its children in source order,
reifies any branch alias before the condition, and uses an explicit failing
else branch. [SPEC translator.pl:151-155,394-397] -/
theorem compileAppCoreFuel_ifThen_eq (childFuel : Nat) (env : CEnv)
    (counter : Nat) (conditionSource thenSource : Atom)
    (conditionTerm thenTerm : Atom)
    (conditionGoals thenGoals branchAliases : List Goal)
    (conditionCounter thenCounter : Nat) (thenBranch : Atom × List Goal)
    (conditionCompiled :
      compileExprFuel childFuel env counter conditionSource =
        .ok (conditionTerm, conditionGoals, conditionCounter))
    (thenCompiled :
      compileExprFuel childFuel env conditionCounter thenSource =
        .ok (thenTerm, thenGoals, thenCounter))
    (branchCompiled :
      compileBranch (.var s!"_q{thenCounter}") (thenTerm, thenGoals) =
        (branchAliases, thenBranch)) :
    compileAppCoreFuel (childFuel + 1) env counter "if"
        [conditionSource, thenSource] =
      .ok (.var s!"_q{thenCounter}",
        branchAliases ++ conditionGoals ++
          [Goal.ite conditionTerm thenBranch
            (.var s!"_q{thenCounter}", [Goal.eq compilerTrueA compilerFalseA])
            (.var s!"_q{thenCounter}")],
        thenCounter + 1) := by
  simp only [compileAppCoreFuel, classifyAppCoreHead]
  rw [conditionCompiled]
  dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind]
  rw [thenCompiled]
  dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind]
  simp only [fresh]
  rw [branchCompiled]

set_option maxHeartbeats 2000000 in
/-- The three-argument conditional compiles all children left-to-right and
schedules both explicit alias equalities before the condition.
[SPEC translator.pl:156-162,394-397] -/
theorem compileAppCoreFuel_ifThenElse_eq (childFuel : Nat) (env : CEnv)
    (counter : Nat) (conditionSource thenSource elseSource : Atom)
    (conditionTerm thenTerm elseTerm : Atom)
    (conditionGoals thenGoals elseGoals : List Goal)
    (thenAliases elseAliases : List Goal)
    (conditionCounter thenCounter elseCounter : Nat)
    (thenBranch elseBranch : Atom × List Goal)
    (conditionCompiled :
      compileExprFuel childFuel env counter conditionSource =
        .ok (conditionTerm, conditionGoals, conditionCounter))
    (thenCompiled :
      compileExprFuel childFuel env conditionCounter thenSource =
        .ok (thenTerm, thenGoals, thenCounter))
    (elseCompiled :
      compileExprFuel childFuel env thenCounter elseSource =
        .ok (elseTerm, elseGoals, elseCounter))
    (thenBranchCompiled :
      compileBranch (.var s!"_q{elseCounter}") (thenTerm, thenGoals) =
        (thenAliases, thenBranch))
    (elseBranchCompiled :
      compileBranch (.var s!"_q{elseCounter}") (elseTerm, elseGoals) =
        (elseAliases, elseBranch)) :
    compileAppCoreFuel (childFuel + 1) env counter "if"
        [conditionSource, thenSource, elseSource] =
      .ok (.var s!"_q{elseCounter}",
        thenAliases ++ elseAliases ++ conditionGoals ++
          [Goal.ite conditionTerm thenBranch elseBranch
            (.var s!"_q{elseCounter}")],
        elseCounter + 1) := by
  simp only [compileAppCoreFuel, classifyAppCoreHead]
  rw [conditionCompiled]
  dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind]
  rw [thenCompiled]
  dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind]
  rw [elseCompiled]
  dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind]
  simp only [fresh]
  rw [thenBranchCompiled, elseBranchCompiled]

set_option maxHeartbeats 2000000 in
/-- Public expression equation for unshadowed two-argument `if`. -/
theorem compileExprFuel_ifThen_eq (childFuel : Nat) (env : CEnv)
    (counter : Nat) (conditionSource thenSource : Atom)
    (conditionTerm thenTerm : Atom)
    (conditionGoals thenGoals branchAliases : List Goal)
    (conditionCounter thenCounter : Nat) (thenBranch : Atom × List Goal)
    (noHook : env.translatorRules.contains "if" = false)
    (conditionCompiled :
      compileExprFuel childFuel env counter conditionSource =
        .ok (conditionTerm, conditionGoals, conditionCounter))
    (thenCompiled :
      compileExprFuel childFuel env conditionCounter thenSource =
        .ok (thenTerm, thenGoals, thenCounter))
    (branchCompiled :
      compileBranch (.var s!"_q{thenCounter}") (thenTerm, thenGoals) =
        (branchAliases, thenBranch)) :
    compileExprFuel (childFuel + 3) env counter
        (.expr [.sym "if", conditionSource, thenSource]) =
      .ok (.var s!"_q{thenCounter}",
        branchAliases ++ conditionGoals ++
          [Goal.ite conditionTerm thenBranch
            (.var s!"_q{thenCounter}", [Goal.eq compilerTrueA compilerFalseA])
            (.var s!"_q{thenCounter}")],
        thenCounter + 1) := by
  rw [show childFuel + 3 = (childFuel + 2) + 1 by omega]
  rw [compileExprFuel.eq_8 (x_4 := by simp)]
  rw [show childFuel + 2 = (childFuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [rewriteStreamOp?, rewriteStreamOpForHead]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  exact compileAppCoreFuel_ifThen_eq childFuel env counter conditionSource
    thenSource conditionTerm thenTerm conditionGoals thenGoals branchAliases
    conditionCounter thenCounter thenBranch conditionCompiled thenCompiled
    branchCompiled

set_option maxHeartbeats 2000000 in
/-- Public expression equation for unshadowed three-argument `if`. -/
theorem compileExprFuel_ifThenElse_eq (childFuel : Nat) (env : CEnv)
    (counter : Nat) (conditionSource thenSource elseSource : Atom)
    (conditionTerm thenTerm elseTerm : Atom)
    (conditionGoals thenGoals elseGoals : List Goal)
    (thenAliases elseAliases : List Goal)
    (conditionCounter thenCounter elseCounter : Nat)
    (thenBranch elseBranch : Atom × List Goal)
    (noHook : env.translatorRules.contains "if" = false)
    (conditionCompiled :
      compileExprFuel childFuel env counter conditionSource =
        .ok (conditionTerm, conditionGoals, conditionCounter))
    (thenCompiled :
      compileExprFuel childFuel env conditionCounter thenSource =
        .ok (thenTerm, thenGoals, thenCounter))
    (elseCompiled :
      compileExprFuel childFuel env thenCounter elseSource =
        .ok (elseTerm, elseGoals, elseCounter))
    (thenBranchCompiled :
      compileBranch (.var s!"_q{elseCounter}") (thenTerm, thenGoals) =
        (thenAliases, thenBranch))
    (elseBranchCompiled :
      compileBranch (.var s!"_q{elseCounter}") (elseTerm, elseGoals) =
        (elseAliases, elseBranch)) :
    compileExprFuel (childFuel + 3) env counter
        (.expr [.sym "if", conditionSource, thenSource, elseSource]) =
      .ok (.var s!"_q{elseCounter}",
        thenAliases ++ elseAliases ++ conditionGoals ++
          [Goal.ite conditionTerm thenBranch elseBranch
            (.var s!"_q{elseCounter}")],
        elseCounter + 1) := by
  rw [show childFuel + 3 = (childFuel + 2) + 1 by omega]
  rw [compileExprFuel.eq_8 (x_4 := by simp)]
  rw [show childFuel + 2 = (childFuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [rewriteStreamOp?, rewriteStreamOpForHead]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  exact compileAppCoreFuel_ifThenElse_eq childFuel env counter conditionSource
    thenSource elseSource conditionTerm thenTerm elseTerm conditionGoals
    thenGoals elseGoals thenAliases elseAliases conditionCounter thenCounter
    elseCounter thenBranch elseBranch conditionCompiled thenCompiled
    elseCompiled thenBranchCompiled elseBranchCompiled

set_option maxHeartbeats 2000000 in
/-- The built-in `and-then` core compiles both operands left-to-right, keeps
the body's goals inside only the true branch, and allocates one enclosing
result. [SPEC translator.pl:177-180] -/
theorem compileAppCoreFuel_andThen_eq (childFuel : Nat) (env : CEnv)
    (counter : Nat) (conditionSource bodySource : Atom)
    (conditionTerm bodyTerm : Atom)
    (conditionGoals bodyGoals : List Goal)
    (conditionCounter bodyCounter : Nat)
    (conditionCompiled :
      compileExprFuel childFuel env counter conditionSource =
        .ok (conditionTerm, conditionGoals, conditionCounter))
    (bodyCompiled :
      compileExprFuel childFuel env conditionCounter bodySource =
        .ok (bodyTerm, bodyGoals, bodyCounter)) :
    compileAppCoreFuel (childFuel + 1) env counter "and-then"
        [conditionSource, bodySource] =
      .ok (.var s!"_q{bodyCounter}",
        conditionGoals ++
          [Goal.ite conditionTerm
            (.var s!"_q{bodyCounter}",
              bodyGoals ++ [Goal.eq (.var s!"_q{bodyCounter}") bodyTerm])
            (.var s!"_q{bodyCounter}",
              [Goal.eq (.var s!"_q{bodyCounter}") compilerFalseA])
            (.var s!"_q{bodyCounter}")],
        bodyCounter + 1) := by
  simp only [compileAppCoreFuel, classifyAppCoreHead]
  rw [conditionCompiled]
  dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind]
  rw [bodyCompiled]
  rfl

set_option maxHeartbeats 2000000 in
/-- The built-in `or-else` core keeps the translated body inside only the
false branch and returns `True` immediately on the true branch.
[SPEC translator.pl:181-184] -/
theorem compileAppCoreFuel_orElse_eq (childFuel : Nat) (env : CEnv)
    (counter : Nat) (conditionSource bodySource : Atom)
    (conditionTerm bodyTerm : Atom)
    (conditionGoals bodyGoals : List Goal)
    (conditionCounter bodyCounter : Nat)
    (conditionCompiled :
      compileExprFuel childFuel env counter conditionSource =
        .ok (conditionTerm, conditionGoals, conditionCounter))
    (bodyCompiled :
      compileExprFuel childFuel env conditionCounter bodySource =
        .ok (bodyTerm, bodyGoals, bodyCounter)) :
    compileAppCoreFuel (childFuel + 1) env counter "or-else"
        [conditionSource, bodySource] =
      .ok (.var s!"_q{bodyCounter}",
        conditionGoals ++
          [Goal.ite conditionTerm
            (.var s!"_q{bodyCounter}",
              [Goal.eq (.var s!"_q{bodyCounter}") compilerTrueA])
            (.var s!"_q{bodyCounter}",
              bodyGoals ++ [Goal.eq (.var s!"_q{bodyCounter}") bodyTerm])
            (.var s!"_q{bodyCounter}")],
        bodyCounter + 1) := by
  simp only [compileAppCoreFuel, classifyAppCoreHead]
  rw [conditionCompiled]
  dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind]
  rw [bodyCompiled]
  rfl

set_option maxHeartbeats 2000000 in
/-- Public expression equation for unshadowed `and-then`. -/
theorem compileExprFuel_andThen_eq (childFuel : Nat) (env : CEnv)
    (counter : Nat) (conditionSource bodySource : Atom)
    (conditionTerm bodyTerm : Atom)
    (conditionGoals bodyGoals : List Goal)
    (conditionCounter bodyCounter : Nat)
    (noHook : env.translatorRules.contains "and-then" = false)
    (conditionCompiled :
      compileExprFuel childFuel env counter conditionSource =
        .ok (conditionTerm, conditionGoals, conditionCounter))
    (bodyCompiled :
      compileExprFuel childFuel env conditionCounter bodySource =
        .ok (bodyTerm, bodyGoals, bodyCounter)) :
    compileExprFuel (childFuel + 3) env counter
        (.expr [.sym "and-then", conditionSource, bodySource]) =
      .ok (.var s!"_q{bodyCounter}",
        conditionGoals ++
          [Goal.ite conditionTerm
            (.var s!"_q{bodyCounter}",
              bodyGoals ++ [Goal.eq (.var s!"_q{bodyCounter}") bodyTerm])
            (.var s!"_q{bodyCounter}",
              [Goal.eq (.var s!"_q{bodyCounter}") compilerFalseA])
            (.var s!"_q{bodyCounter}")],
        bodyCounter + 1) := by
  rw [show childFuel + 3 = (childFuel + 2) + 1 by omega]
  rw [compileExprFuel.eq_8 (x_4 := by simp)]
  rw [show childFuel + 2 = (childFuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [rewriteStreamOp?, rewriteStreamOpForHead]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  exact compileAppCoreFuel_andThen_eq childFuel env counter conditionSource
    bodySource conditionTerm bodyTerm conditionGoals bodyGoals
    conditionCounter bodyCounter conditionCompiled bodyCompiled

set_option maxHeartbeats 2000000 in
/-- Public expression equation for unshadowed `or-else`. -/
theorem compileExprFuel_orElse_eq (childFuel : Nat) (env : CEnv)
    (counter : Nat) (conditionSource bodySource : Atom)
    (conditionTerm bodyTerm : Atom)
    (conditionGoals bodyGoals : List Goal)
    (conditionCounter bodyCounter : Nat)
    (noHook : env.translatorRules.contains "or-else" = false)
    (conditionCompiled :
      compileExprFuel childFuel env counter conditionSource =
        .ok (conditionTerm, conditionGoals, conditionCounter))
    (bodyCompiled :
      compileExprFuel childFuel env conditionCounter bodySource =
        .ok (bodyTerm, bodyGoals, bodyCounter)) :
    compileExprFuel (childFuel + 3) env counter
        (.expr [.sym "or-else", conditionSource, bodySource]) =
      .ok (.var s!"_q{bodyCounter}",
        conditionGoals ++
          [Goal.ite conditionTerm
            (.var s!"_q{bodyCounter}",
              [Goal.eq (.var s!"_q{bodyCounter}") compilerTrueA])
            (.var s!"_q{bodyCounter}",
              bodyGoals ++ [Goal.eq (.var s!"_q{bodyCounter}") bodyTerm])
            (.var s!"_q{bodyCounter}")],
        bodyCounter + 1) := by
  rw [show childFuel + 3 = (childFuel + 2) + 1 by omega]
  rw [compileExprFuel.eq_8 (x_4 := by simp)]
  rw [show childFuel + 2 = (childFuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [rewriteStreamOp?, rewriteStreamOpForHead]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  exact compileAppCoreFuel_orElse_eq childFuel env counter conditionSource
    bodySource conditionTerm bodyTerm conditionGoals bodyGoals
    conditionCounter bodyCounter conditionCompiled bodyCompiled

set_option maxHeartbeats 2000000 in
/-- The built-in `let` core compiles pattern, value, and body in pinned order.
Unlike the public application dispatcher, this equation deliberately has no
translator-hook premise; it is also the target of native `chain` after that
head's own hook check. -/
theorem compileAppCoreFuel_let_eq (childFuel : Nat) (env : CEnv)
    (counter : Nat) (pattern value bodySource : Atom)
    (patternTerm valueTerm bodyTerm : Atom)
    (patternGoals valueGoals bodyGoals : List Goal)
    (patternCounter valueCounter nextCounter : Nat)
    (patternCompiled : compileExprFuel childFuel env counter pattern =
      .ok (patternTerm, patternGoals, patternCounter))
    (valueCompiled : compileExprFuel childFuel env patternCounter value =
      .ok (valueTerm, valueGoals, valueCounter))
    (bodyCompiled : compileExprFuel childFuel env valueCounter bodySource =
      .ok (bodyTerm, bodyGoals, nextCounter)) :
    compileAppCoreFuel (childFuel + 1) env counter "let"
        [pattern, value, bodySource] =
      .ok (bodyTerm,
        [Goal.eq patternTerm valueTerm] ++ patternGoals ++ valueGoals ++
          bodyGoals,
        nextCounter) := by
  rw [compileAppCoreFuel.eq_23, patternCompiled]
  all_goals try simp only [classifyAppCoreHead]
  dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind]
  rw [valueCompiled]
  dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind]
  rw [bodyCompiled]

set_option maxHeartbeats 2000000 in
/-- `let` follows pinned translator order: compile pattern, value, and body,
then place unification before the pattern, value, and body goals. -/
theorem compileExprFuel_let_eq (childFuel : Nat) (env : CEnv)
    (counter : Nat) (pattern value bodySource : Atom)
    (patternTerm valueTerm bodyTerm : Atom)
    (patternGoals valueGoals bodyGoals : List Goal)
    (patternCounter valueCounter nextCounter : Nat)
    (noHook : env.translatorRules.contains "let" = false)
    (patternCompiled : compileExprFuel childFuel env counter pattern =
      .ok (patternTerm, patternGoals, patternCounter))
    (valueCompiled : compileExprFuel childFuel env patternCounter value =
      .ok (valueTerm, valueGoals, valueCounter))
    (bodyCompiled : compileExprFuel childFuel env valueCounter bodySource =
      .ok (bodyTerm, bodyGoals, nextCounter)) :
    compileExprFuel (childFuel + 3) env counter
        (.expr [.sym "let", pattern, value, bodySource]) =
      .ok (bodyTerm,
        [Goal.eq patternTerm valueTerm] ++ patternGoals ++ valueGoals ++
          bodyGoals,
        nextCounter) := by
  rw [show childFuel + 3 = (childFuel + 2) + 1 by omega]
  rw [compileExprFuel.eq_8 (x_4 := by simp)]
  rw [show childFuel + 2 = (childFuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  exact compileAppCoreFuel_let_eq childFuel env counter pattern value
    bodySource patternTerm valueTerm bodyTerm patternGoals valueGoals
    bodyGoals patternCounter valueCounter nextCounter patternCompiled
    valueCompiled bodyCompiled

set_option maxHeartbeats 2000000 in
/-- `chain` follows the same pinned translation clause as `let`, traversing
its first argument, second argument, and body literally in source order.  Its
own hook check is the only dispatch guard; a `let` hook cannot capture it. -/
theorem compileExprFuel_chain_eq (childFuel : Nat) (env : CEnv)
    (counter : Nat) (first second bodySource : Atom)
    (firstTerm secondTerm bodyTerm : Atom)
    (firstGoals secondGoals bodyGoals : List Goal)
    (firstCounter secondCounter nextCounter : Nat)
    (noHook : env.translatorRules.contains "chain" = false)
    (firstCompiled : compileExprFuel childFuel env counter first =
      .ok (firstTerm, firstGoals, firstCounter))
    (secondCompiled : compileExprFuel childFuel env firstCounter second =
      .ok (secondTerm, secondGoals, secondCounter))
    (bodyCompiled : compileExprFuel childFuel env secondCounter bodySource =
      .ok (bodyTerm, bodyGoals, nextCounter)) :
    compileExprFuel (childFuel + 3) env counter
        (.expr [.sym "chain", first, second, bodySource]) =
      .ok (bodyTerm,
        [Goal.eq firstTerm secondTerm] ++ firstGoals ++ secondGoals ++
          bodyGoals,
        nextCounter) := by
  rw [show childFuel + 3 = (childFuel + 2) + 1 by omega]
  rw [compileExprFuel.eq_8 (x_4 := by simp)]
  rw [show childFuel + 2 = (childFuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  rw [rewriteStreamOp_chain_none]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_33]
  all_goals try simp only [classifyAppCoreHead]
  rw [firstCompiled]
  dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind]
  rw [secondCompiled]
  dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind]
  rw [bodyCompiled]

set_option maxHeartbeats 2000000 in
/-- A well-formed `let*` compiles by expanding its nonempty binding list to the
source-ordered nested `let` selected by pinned `letstar_to_rec_let/3`, then
compiling that expansion. -/
theorem compileExprFuel_letStar_eq (nestedFuel : Nat) (env : CEnv)
    (counter : Nat) (bindings : List Atom) (bodySource nestedSource : Atom)
    (internal : Atom) (goals : List Goal) (nextCounter : Nat)
    (noHook : env.translatorRules.contains "let*" = false)
    (expanded : desugarLetStar? bindings bodySource = some nestedSource)
    (nestedCompiled : compileExprFuel nestedFuel env counter nestedSource =
      .ok (internal, goals, nextCounter)) :
    compileExprFuel (nestedFuel + 3) env counter
        (.expr [.sym "let*", .expr bindings, bodySource]) =
      .ok (internal, goals, nextCounter) := by
  rw [show nestedFuel + 3 = (nestedFuel + 2) + 1 by omega]
  rw [compileExprFuel.eq_8 (x_4 := by simp)]
  rw [show nestedFuel + 2 = (nestedFuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_24, expanded]
  all_goals try simp only [classifyAppCoreHead]
  exact nestedCompiled

set_option maxHeartbeats 2000000 in
/-- In the sequential executable target, `with_mutex` compiles to its body.
The independent operational semantics proves separately that this preserves
the complete ordered observation when no competing thread can interleave. -/
theorem compileExprFuel_withMutex_eq (bodyFuel : Nat) (env : CEnv)
    (counter : Nat) (mutex bodySource bodyTerm : Atom)
    (bodyGoals : List Goal) (nextCounter : Nat)
    (noHook : env.translatorRules.contains "with_mutex" = false)
    (bodyCompiled : compileExprFuel bodyFuel env counter bodySource =
      .ok (bodyTerm, bodyGoals, nextCounter)) :
    compileExprFuel (bodyFuel + 3) env counter
        (.expr [.sym "with_mutex", mutex, bodySource]) =
      .ok (bodyTerm, bodyGoals, nextCounter) := by
  rw [show bodyFuel + 3 = (bodyFuel + 2) + 1 by omega]
  rw [compileExprFuel.eq_8 (x_4 := by simp)]
  rw [show bodyFuel + 2 = (bodyFuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_38]
  all_goals try simp only [classifyAppCoreHead]
  exact bodyCompiled

set_option maxHeartbeats 2000000 in
/-- The implementation equation for the zero-argument `cut` form when no
translator hook shadows that head.  This small exported equation prevents
downstream proofs from unfolding the complete application compiler. -/
theorem compileExprFuel_cut_eq (fuel counter : Nat) (env : CEnv)
    (noHook : env.translatorRules.contains "cut" = false) :
    compileExprFuel (fuel + 3) env counter (.expr [.sym "cut"]) =
      .ok (.sym "True", [Goal.cut], counter) := by
  rw [compileExprFuel.eq_8 (x_4 := by simp)]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_13]
  all_goals try simp only [classifyAppCoreHead]
  rfl

set_option maxHeartbeats 2000000 in
/-- The implementation equation for syntactic quotation when no translator
hook shadows the `quote` head. -/
theorem compileExprFuel_quote_eq (fuel counter : Nat) (env : CEnv)
    (source : Atom)
    (noHook : env.translatorRules.contains "quote" = false) :
    compileExprFuel (fuel + 3) env counter (.expr [.sym "quote", source]) =
      .ok (chainify source, [], counter) := by
  rw [compileExprFuel.eq_8 (x_4 := by simp)]
  rw [compileAppFuel.eq_2]
  rw [rewriteStreamOp_quote_none]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_2]
  all_goals try simp only [classifyAppCoreHead]

set_option maxHeartbeats 2000000 in
/-- The implementation equation for zero-argument `empty` when no translator
hook shadows the pinned built-in.  The executable represents guaranteed
branch failure by an impossible equality. -/
theorem compileExprFuel_empty_eq (fuel counter : Nat) (env : CEnv)
    (noHook : env.translatorRules.contains "empty" = false) :
    compileExprFuel (fuel + 3) env counter (.expr [.sym "empty"]) =
      .ok (.sym "True",
        [Goal.eq (.sym "True") (.sym "False")], counter) := by
  rw [compileExprFuel.eq_8 (x_4 := by simp)]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_12]
  all_goals try simp only [classifyAppCoreHead]
  rfl

-- Keep elaboration from unfolding the large compiler automatically.  The
-- exported equations above remain available for explicit adequacy proofs,
-- while native code generation still uses these definitions normally.
attribute [irreducible]
  compileExprFuel compilePatternFuel compileAppFuel compileAppCoreFuel
  compileCaseArmsFuel compileArgsAtFuel compileListFuel compilePatternListFuel

/-- A syntax-derived recursion budget for the transparent compiler.  The
adequacy development proves that this budget cannot be exhausted on the
supported source fragment; exhaustion remains an explicit result outside that
fragment. -/
def compilerFuel (atom : Atom) : Nat :=
  64 * (atom.size + 1)

/-- A shared budget for a source list. -/
def compilerListFuel (atoms : List Atom) : Nat :=
  64 * ((atoms.map Atom.size).sum + 1)

/-- Public compiler entry point. -/
def compileExpr (env : CEnv) (n : Nat) (atom : Atom) :
    CompileM (Atom × List Goal × Nat) :=
  compileExprFuel (compilerFuel atom + 64) env n atom

/-- Public pattern-compiler entry point. -/
def compilePattern (env : CEnv) (n : Nat) (atom : Atom) :
    CompileM (Atom × List Goal × Nat) :=
  compilePatternFuel (compilerFuel atom + 64) env n atom

/-- Public application-compiler entry point. -/
def compileApp (env : CEnv) (n : Nat) (head : String) (args : List Atom) :
    CompileM (Atom × List Goal × Nat) :=
  compileAppFuel (compilerListFuel (Atom.sym head :: args) + 64) env n head args

/-- Public application-core entry point. -/
def compileAppCore (env : CEnv) (n : Nat) (head : String) (args : List Atom) :
    CompileM (Atom × List Goal × Nat) :=
  compileAppCoreFuel (compilerListFuel (Atom.sym head :: args) + 64) env n head args

/-- Public argument-list compiler entry point. -/
def compileArgs (env : CEnv) (n : Nat) (head : String) (args : List Atom) :
    CompileM (List Atom × List Goal × Nat) :=
  compileArgsFuel (compilerListFuel (Atom.sym head :: args) + 64) env n head args

/-- Public exact typed-argument traversal used by adequacy statements. Runtime
application compilation invokes the same `compileTypedArgsFuel` function with
its enclosing source-derived budget. -/
def compileTypedArgs (env : CEnv) (counter : Nat) (arguments types : List Atom) :
    CompileM (List Atom × List Goal × Nat) :=
  compileTypedArgsFuel (compilerListFuel arguments + 64) env counter arguments
    types

/-- Public expression-list compiler entry point. -/
def compileList (env : CEnv) (n : Nat) (atoms : List Atom) :
    CompileM (List Atom × List Goal × Nat) :=
  compileListFuel (compilerListFuel atoms + 64) env n atoms

/-- Public pattern-list compiler entry point. -/
def compilePatternList (env : CEnv) (n : Nat) (atoms : List Atom) :
    CompileM (List Atom × List Goal × Nat) :=
  compilePatternListFuel (compilerListFuel atoms + 64) env n atoms

/-- Compile one rule `(= (f p1..pn) rhs)` to a clause (patterns narrow). -/
def compileRule (env : CEnv) (n : Nat) (params : List Atom) (rhs : Atom) :
    CompileM (Clause × Nat) := do
  let env := { env with dynamicUnknown := false }
  let (ps, gps, n1) ← compilePatternList env n params
  let (tr, gr, n2) ← compileExpr env n1 rhs
  match partialValue? tr with
  | some (base, bound) =>
      let arities :=
        match compileBinArity base with
        | some ar => [ar]
        | none => env.arities base
      match arities.find? (fun ar => bound.length < ar) with
      | some ar =>
          let extraN := ar - bound.length
          let (extras, n3) := (List.range extraN).foldl
            (fun (acc : List Atom × Nat) _ =>
              let (v, m) := fresh acc.2
              (acc.1 ++ [v], m)) ([], n2)
          let (out, n4) := fresh n3
          let call :=
            if env.isBin base then Goal.bin base (bound ++ extras) out
            else Goal.call base (bound ++ extras) out
          .ok ({ params := ps ++ extras, result := out,
                 body := gps ++ gr ++ [call] }, n4)
      | none =>
          .ok ({ params := ps, result := tr, body := gps ++ gr }, n2)
  | none =>
      .ok ({ params := ps, result := tr, body := gps ++ gr }, n2)

/-- Source-facing expression compiler.  The raw `compileExpr` remains the
counter-parametric proof surface; executable callers use this wrapper so a
legal source variable such as `$_q25` cannot alias generated `_q25`. -/
def compileExprFresh (env : CEnv) (counter : Nat) (source : Atom) :
    CompileM (Atom × List Goal × Nat) := do
  let (term, goals, nextCounter) ←
    compileExpr env (compilerFreshCounterForAtom counter source) source
  finalizeCompiledExpression term goals nextCounter

/-- Source-facing rule compiler, seeded beyond variables in both the head
patterns and body before pattern compilation allocates any temporaries. -/
def compileRuleFresh (env : CEnv) (counter : Nat) (params : List Atom)
    (rhs : Atom) : CompileM (Clause × Nat) := do
  let (clause, nextCounter) ←
    compileRule env (compilerFreshCounterForAtoms counter (rhs :: params))
      params rhs
  let finalized ← finalizeCompiledClause clause
  .ok (finalized, nextCounter)

/-- Surface desugaring: HE-style binder forms become synthesized rules plus
    the function-value form —
    `(map-atom l $x body)`       → `(map-atom l #lamK)`  + `(= (#lamK $x) body)`
    `(filter-atom l $x body)`    → likewise
    `(foldl-atom l i $a $x body)`→ `(foldl-atom l i #lamK)` + 2-param rule;
    `(|-> params body)` closure-converts to a synthesized rule whose value is
    the bare `#lam` symbol or the partially applied `(#lam captures…)`. -/
private def _desugarDoc : Unit := ()

mutual

/-- Collect the $-variables of a surface atom in first-occurrence order.
The companion list traversal makes the recursion structurally total and
transparent to the kernel. -/
def surfaceVars (a : Atom) (acc : List String := []) : List String :=
  match a with
  | Atom.var v => if acc.contains v then acc else acc ++ [v]
  | Atom.expr atoms => surfaceVarsList atoms acc
  | _ => acc
termination_by 2 * a.size
decreasing_by
  all_goals simp_all [Atom.size] <;> omega

/-- Structurally recursive list companion for `surfaceVars`. -/
def surfaceVarsList : List Atom → List String → List String
  | [], acc => acc
  | atom :: rest, acc =>
      surfaceVarsList rest (surfaceVars atom acc)
termination_by atoms _ =>
  2 * (atoms.map Atom.size).sum + 1
decreasing_by
  all_goals
    simp only [List.map_cons, List.sum_cons]
    have positive : 0 < atom.size := by
      cases atom <;> simp [Atom.size] <;> omega
    omega

end

/-- Construct the synthesized rule and closure value shared by both supported
lambda parameter spellings. -/
def finishLambdaDesugaring (parameters : List Atom) (body : Atom)
    (nestedDefinitions : List Atom) (nextCounter : Nat) :
    Atom × List Atom × Nat :=
  let function := s!"#lam{nextCounter}"
  let parameterVariables :=
    parameters.foldl (fun acc atom => surfaceVars atom acc) []
  let captures :=
    (surfaceVars body).filter
      (fun name => !parameterVariables.contains name)
  let rule := Atom.expr [Atom.sym "=",
    Atom.expr
      (Atom.sym function :: (captures.map Atom.var) ++ parameters), body]
  let value :=
    if captures.isEmpty then Atom.sym function
    else partialValue function (captures.map Atom.var)
  (value, nestedDefinitions ++ [rule], nextCounter + 1)

mutual

/-- Structurally total binder conversion.  Generated-name counters are
threaded left-to-right through the companion list traversal. -/
def desugarBinders (a : Atom) (k : Nat) :
    Atom × List Atom × Nat :=
  match a with
  | Atom.expr [Atom.sym "quote", _] =>
      -- [SPEC translator.pl:297-299] `quote` returns its sole argument as
      -- syntax. Binder-looking forms below it are data, not source forms to
      -- closure-convert or lift into synthesized rules.
      (a, [], k)
  | Atom.expr [Atom.sym "|->", Atom.expr ps, body] =>
      -- λ closure conversion: captured outer vars become leading params;
      -- the VALUE is the bare symbol (no captures) or the partially
      -- applied chain (#lamK cap…), completed by callDyn at application
      let (body', definitions, nextCounter) :=
        desugarBinders body k
      finishLambdaDesugaring ps body' definitions nextCounter
  | Atom.expr [Atom.sym "|->", Atom.var pv, body] =>
      -- This spelling is semantically the singleton parameter list.  Handle
      -- it directly rather than recursively constructing a larger atom.
      let (body', definitions, nextCounter) :=
        desugarBinders body k
      finishLambdaDesugaring [Atom.var pv] body' definitions nextCounter
  | Atom.expr [Atom.sym "map-atom", l, Atom.var x, body] =>
      let (l', ds1, k1) := desugarBinders l k
      let (b', ds2, k2) := desugarBinders body k1
      let f := s!"#lam{k2}"
      (Atom.expr [Atom.sym "map-atom", l', Atom.sym f],
       ds1 ++ ds2 ++ [Atom.expr [Atom.sym "=",
         Atom.expr [Atom.sym f, Atom.var x], b']], k2 + 1)
  | Atom.expr [Atom.sym "filter-atom", l, Atom.var x, body] =>
      let (l', ds1, k1) := desugarBinders l k
      let (b', ds2, k2) := desugarBinders body k1
      let f := s!"#lam{k2}"
      (Atom.expr [Atom.sym "filter-atom", l', Atom.sym f],
       ds1 ++ ds2 ++ [Atom.expr [Atom.sym "=",
         Atom.expr [Atom.sym f, Atom.var x], b']], k2 + 1)
  | Atom.expr [Atom.sym "foldl-atom", l, i, Atom.var acc, Atom.var x, body] =>
      let (l', ds1, k1) := desugarBinders l k
      let (i', ds2, k2) := desugarBinders i k1
      let (b', ds3, k3) := desugarBinders body k2
      let f := s!"#lam{k3}"
      (Atom.expr [Atom.sym "foldl-atom", l', i', Atom.sym f],
       ds1 ++ ds2 ++ ds3 ++ [Atom.expr [Atom.sym "=",
         Atom.expr [Atom.sym f, Atom.var acc, Atom.var x], b']], k3 + 1)
  | Atom.expr atoms =>
      let (atoms', definitions, nextCounter) :=
        desugarBinderList atoms k
      (Atom.expr atoms', definitions, nextCounter)
  | other => (other, [], k)
termination_by 2 * a.size
decreasing_by
  all_goals simp_all [Atom.size] <;> omega

/-- Structurally recursive list companion for `desugarBinders`. -/
def desugarBinderList : List Atom → Nat → List Atom × List Atom × Nat
  | [], counter => ([], [], counter)
  | atom :: rest, counter =>
      let (atom', definitions, nextCounter) :=
        desugarBinders atom counter
      let (rest', restDefinitions, finalCounter) :=
        desugarBinderList rest nextCounter
      (atom' :: rest', definitions ++ restDefinitions, finalCounter)
termination_by atoms _ =>
  2 * (atoms.map Atom.size).sum + 1
decreasing_by
  all_goals
    simp only [List.map_cons, List.sum_cons]
    have positive : 0 < atom.size := by
      cases atom <;> simp [Atom.size] <;> omega
    omega

end

/-- Hoist binder-generated definitions without separating a split bang marker
from the query it owns.

The reader represents `!query` as the adjacent pair `!`, `query`.  Pinned
PeTTa translates any lambda inside that runnable while processing the
runnable, registering the synthesized clause before executing its translated
goals [SPEC filereader.pl:20-24, translator.pl:244-261].  Therefore generated
definitions belong before the marker/query pair, never between them.  Inline
`(! query)` forms go through the ordinary branch and obey the same ordering.
-/
def desugarProgramAtoms : List Atom → Nat → List Atom × Nat
  | [], counter => ([], counter)
  | Atom.sym "!" :: query :: rest, counter =>
      let (query', definitions, nextCounter) :=
        desugarBinders query counter
      let (rest', finalCounter) :=
        desugarProgramAtoms rest nextCounter
      (definitions ++ [Atom.sym "!", query'] ++ rest', finalCounter)
  | atom :: rest, counter =>
      let (atom', definitions, nextCounter) :=
        desugarBinders atom counter
      let (rest', finalCounter) :=
        desugarProgramAtoms rest nextCounter
      (definitions ++ [atom'] ++ rest', finalCounter)

/-- Partition and compile a parsed program; bangs become queries
    `(goals, resultVar)`. -/
def compileProgram (isBin : String → Bool) (atoms0 : List Atom) :
    CompileM (Prog × List (List Goal × Atom)) := do
  let (atoms, _) := desugarProgramAtoms atoms0 0
  -- pass 1: collect rule heads, type decls, facts, bangs
  let mut decls : List (Atom × Atom) := []
  let mut facts : List Atom := []
  let mut rules : List (String × List Atom × Atom) := []
  let mut bangs : List Atom := []
  let mut pendingBang := false
  for a in atoms do
    if pendingBang then
      bangs := bangs ++ [a]; pendingBang := false
    else
      match a with
      | Atom.sym "!" => pendingBang := true
      | Atom.expr [Atom.sym "!", q] => bangs := bangs ++ [q]
      | Atom.expr [Atom.sym "=", Atom.expr (Atom.sym f :: ps), rhs] =>
          rules := rules ++ [(f, ps, rhs)]
      | Atom.expr [Atom.sym ":", subj, ty] => decls := decls ++ [(subj, ty)]
      | other => facts := facts ++ [other]
  -- [SPEC translator.pl:354-363] only `Expression`-typed argument positions
  -- stay syntactic; `Atom`/`%Undefined%` translate unchecked; other types
  -- translate with a get-type post-check (the check is a v2 item, ledgered)
  let arities := collectSourceFunctionArities atoms
  let heads := collectSourceFunctionHeads atoms
  let env : CEnv := mkEnv isBin heads arities decls
  let mut n := 0
  let mut clauses : List (String × Clause) := []
  for (f, ps, rhs) in rules do
    let (c, n') ← compileRuleFresh env n ps rhs
    clauses := clauses ++ [(f, c)]; n := n'
  let queryEnv : CEnv := mkEnv isBin heads
    (arities ++ clauses.map (fun (f, c) => (f, c.params.length))) decls
  let mut queries : List (List Goal × Atom) := []
  for q in bangs do
    let (t, gs, n') ← compileExprFresh queryEnv n q
    -- the query's answers are its result term's instances
    queries := queries ++ [(gs, t)]; n := n'
  .ok ({ clauses, facts, typeDecls := decls }, queries)

inductive SourceForm where
  | atom (value : Atom) (observable : Bool := true)
  | hostImport (moduleName : String) (observable : Bool := true)
  | prologRegister (functions : List String) (observable : Bool := true)
  | importBegin
  | importEnd (observable : Bool := true)
deriving Repr, Inhabited, BEq

/-- Source-form counterpart of `desugarProgramAtoms`.

Only two adjacent atom forms can constitute a split runnable.  Typed import
and registration boundaries are left in their original position, so malformed
`!`-before-boundary inputs continue to be rejected by the sequential compiler
rather than being silently reordered.  Generated definitions inherit the
query form's visibility, while the bang marker retains its own visibility and
therefore continues to control the query event.
-/
def desugarSourceForms : List SourceForm → Nat → List SourceForm × Nat
  | [], counter => ([], counter)
  | .atom (Atom.sym "!") bangObservable ::
      .atom query queryObservable :: rest, counter =>
      let (query', definitions, nextCounter) :=
        desugarBinders query counter
      let (rest', finalCounter) :=
        desugarSourceForms rest nextCounter
      (definitions.map (SourceForm.atom · queryObservable) ++
        [.atom (Atom.sym "!") bangObservable,
         .atom query' queryObservable] ++ rest',
        finalCounter)
  | .atom atom observable :: rest, counter =>
      let (atom', definitions, nextCounter) :=
        desugarBinders atom counter
      let (rest', finalCounter) :=
        desugarSourceForms rest nextCounter
      (definitions.map (SourceForm.atom · observable) ++
        [.atom atom' observable] ++ rest', finalCounter)
  | form :: rest, counter =>
      let (rest', finalCounter) := desugarSourceForms rest counter
      (form :: rest', finalCounter)

inductive TopEvent where
  | fact (a : Atom)
  | typeDecl (subj : Atom) (ty : Atom)
  | clause (src : Atom) (f : String) (c : Clause)
  | tabled (f : String) (arity : Nat) (observable : Bool := true)
  | hostImport (moduleName : String) (observable : Bool)
  | prologRegister (functions : List String) (observable : Bool)
  | importBegin
  | importEnd (observable : Bool)
  | query (goals : List Goal) (qterm : Atom) (observable : Bool := true)
deriving Repr, Inhabited, BEq

/-- Sequential top-level compilation [SPEC filereader.pl:16-28]:
    function heads are registered by the parse pass, but facts, type
    declarations, clauses, and bangs become live strictly in source order. -/
def compileProgramSequentialForms (isBin : String → Bool)
    (forms0 : List SourceForm) :
    CompileM (Prog × List TopEvent) := do
  let (forms, _) := desugarSourceForms forms0 0
  let sourceAtoms := forms.filterMap fun
    | .atom atom _ => some atom
    | _ => none
  let arities := collectSourceFunctionArities sourceAtoms
  let heads := collectSourceFunctionHeads sourceAtoms
  let mut decls : List (Atom × Atom) := []
  let mut facts : List Atom := []
  let mut clauses : List (String × Clause) := []
  let mut events : List TopEvent := []
  let mut translatorRules : List String := []
  let mut prologFunctions : List String := []
  let mut pendingBang := false
  let mut pendingObservable := true
  let mut n := 0
  for form in forms do
    match form with
    | .importBegin =>
        if pendingBang then
          throw "import boundary cannot follow a split bang marker"
        events := events ++ [TopEvent.importBegin]
    | .importEnd observable =>
        if pendingBang then
          throw "import boundary cannot follow a split bang marker"
        events := events ++ [TopEvent.importEnd observable]
    | .hostImport moduleName observable =>
        if pendingBang then
          throw "host import cannot follow a split bang marker"
        events := events ++ [TopEvent.hostImport moduleName observable]
    | .prologRegister functions observable =>
        if pendingBang then
          throw "Prolog registration cannot follow a split bang marker"
        prologFunctions := (prologFunctions ++ functions).eraseDups
        events := events ++ [TopEvent.prologRegister functions observable]
    | .atom a observable =>
      if pendingBang then
        match a with
        | Atom.expr [Atom.sym "add-translator-rule!", Atom.sym f] =>
            translatorRules := (translatorRules ++ [f]).eraseDups
            events := events ++ [TopEvent.query [] compilerTrueA pendingObservable]
            pendingBang := false
            continue
        | Atom.expr [Atom.sym "remove-translator-rule!", Atom.sym f] =>
            translatorRules := translatorRules.erase f
            events := events ++ [TopEvent.query [] compilerTrueA pendingObservable]
            pendingBang := false
            continue
        | Atom.expr [Atom.sym "tabled", Atom.expr (Atom.sym f :: args)] =>
            events := events ++ [TopEvent.tabled f args.length pendingObservable]
            pendingBang := false
            continue
        | _ => pure ()
        let liveArities := arities ++ clauses.map (fun (f, c) =>
          (f, c.params.length))
        let env := { mkEnv isBin heads liveArities decls with
          translatorRules, prologFunctions }
        let (t, gs, n') ← compileExprFresh env n a
        events := events ++ [TopEvent.query gs t pendingObservable]
        n := n'; pendingBang := false
      else
        match a with
        | Atom.sym "!" =>
            pendingBang := true
            pendingObservable := observable
        | Atom.expr [Atom.sym "!", Atom.expr [Atom.sym "tabled",
            Atom.expr (Atom.sym f :: args)]] =>
            events := events ++ [TopEvent.tabled f args.length observable]
        | Atom.expr [Atom.sym "!",
            Atom.expr [Atom.sym "add-translator-rule!", Atom.sym f]] =>
            translatorRules := (translatorRules ++ [f]).eraseDups
            events := events ++ [TopEvent.query [] compilerTrueA observable]
        | Atom.expr [Atom.sym "!",
            Atom.expr [Atom.sym "remove-translator-rule!", Atom.sym f]] =>
            translatorRules := translatorRules.erase f
            events := events ++ [TopEvent.query [] compilerTrueA observable]
        | Atom.expr [Atom.sym "!", q] =>
            let liveArities := arities ++ clauses.map (fun (f, c) =>
              (f, c.params.length))
            let env := { mkEnv isBin heads liveArities decls with
              translatorRules, prologFunctions }
            let (t, gs, n') ← compileExprFresh env n q
            events := events ++ [TopEvent.query gs t observable]
            n := n'
        | Atom.expr [Atom.sym "=", Atom.expr (Atom.sym f :: ps), rhs] =>
            let env := { mkEnv isBin heads arities decls with
              translatorRules, prologFunctions }
            let (c, n') ← compileRuleFresh env n ps rhs
            clauses := clauses ++ [(f, c)]
            events := events ++ [TopEvent.clause a f c]
            n := n'
        | Atom.expr [Atom.sym ":", subj, ty] =>
            decls := decls ++ [(subj, ty)]
            events := events ++ [TopEvent.typeDecl subj ty]
        | other =>
            facts := facts ++ [other]
            events := events ++ [TopEvent.fact other]
  .ok ({ clauses, facts, typeDecls := decls }, events)

def compileProgramSequential (isBin : String → Bool) (atoms : List Atom) :
    CompileM (Prog × List TopEvent) :=
  compileProgramSequentialForms isBin (atoms.map (SourceForm.atom · true))

end PLeaTTa
