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

namespace PLeaTTa

open Metta (Atom)

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
    decls.filterMap (fun (subj, t) =>
      if subj == Atom.sym f then
        match t with
        | Atom.expr (Atom.sym "->" :: tys) => some tys
        | _ => none
      else none)
  { defined := heads, arities, isBin, atomTyped, typeChains }

def fresh (n : Nat) : Atom × Nat := (Atom.var s!"_q{n}", n + 1)

private def trueA : Atom := Atom.sym "True"
private def falseA : Atom := Atom.sym "False"

private def compileBinArity : String → Option Nat
  | "=" | "==" | "!=" | "+" | "-" | "*" | "/" | "%" | "<" | ">" | "<=" | ">="
  | "min" | "max"
  | "and" | "or" | "cons" | "cons-atom" | "member" | "is-member" | "union-atom"
  | "intersection-atom" | "subtraction-atom" | "exclude-item"
  | "index-atom" | "=alpha" | "is-alpha-member" => some 2
  | "#test-results" => some 2
  | "not" | "car-atom" | "cdr-atom" | "last" | "size-atom" | "repr" | "parse"
  | "repra" | "unique-atom" | "list_to_set" | "msort" | "println!"
  | "add-translator-rule!" | "remove-translator-rule!"
  | "is-ground" | "is-expr" | "is-space" | "argv" => some 1
  | _ => none

private def partialValue (f : String) (args : List Atom) : Atom :=
  chainOf [Atom.sym "partial", Atom.sym f, chainOf args]

private def chainListC : Atom → Option (List Atom)
  | Atom.sym "#nil" => some []
  | Atom.expr [Atom.sym "#c", h, t] => (chainListC t).map (h :: ·)
  | _ => none

private def partialValue? (a : Atom) : Option (String × List Atom) :=
  match chainListC a with
  | some [Atom.sym "partial", Atom.sym f, boundList] =>
      (chainListC boundList).map (fun bound => (f, bound))
  | _ => none

/-- A nested Prolog condition preserves bindings for every source variable it
    mentions. `Goal.softcut` replays one template value into the caller, so
    the template must carry those variables even when they occur only in the
    condition's generated goals and not in its result term. -/
private def bindingTemplate (base : Atom) (sources : List Atom) : Atom :=
  let vars := (sources.flatMap Atom.vars).eraseDups
  chainOf (base :: vars.map Atom.var)

/-- PeTTa's `build_branch/4` aliases a variable-valued branch result to the
enclosing result while translating a nonempty branch conjunction. This is a
translation-time alias, so recursive calls remain in last-call position
instead of leaving a runtime equality frame. [SPEC translator.pl:387-390] -/
private def compileBranch (out : Atom) : Atom × List Goal → Atom × List Goal
  | (Atom.var name, goals) =>
      if goals.isEmpty then (Atom.var name, goals)
      else (out, instantiateGoals [(name, out)] goals)
  | branch => branch

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

private def dynamicUnknownHead : String → Bool
  | h =>
      match h.toList with
      | c :: _ => c.isLower
      | [] => false

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
  | _ + 1, _, n, Atom.expr [Atom.sym "#c", h, t] =>
      .ok (Atom.expr [Atom.sym "#c", h, t], [], n)
  | fuel + 1, env, n, Atom.expr [Atom.sym "cons", h, t] => do
      let (ph, gh, n1) ← compilePatternFuel fuel env n h
      let (pt, gt, n2) ← compilePatternFuel fuel env n1 t
      .ok (consC ph pt, gh ++ gt, n2)
  | fuel + 1, env, n, Atom.expr (Atom.sym f :: args) =>
      if env.defined.contains f || env.isBin f || specialHead f then
        compileExprFuel fuel env n (Atom.expr (Atom.sym f :: args))
      else do
        let (ts, gs, n1) ← compilePatternListFuel fuel env n args
        .ok (chainOf (Atom.sym f :: ts), gs, n1)
  | fuel + 1, env, n, Atom.expr es => do
      let (ts, gs, n1) ← compilePatternListFuel fuel env n es
      .ok (chainOf ts, gs, n1)
termination_by structural fuel _ _ _ => fuel

def compileAppFuel : Nat → CEnv → Nat → String → List Atom →
    CompileM (Atom × List Goal × Nat)
  | 0, _, _, _, _ => .error "compiler fuel exhausted"
  | fuel + 1, env, n, h, args => do
    if env.translatorRules.contains h then
      let ordinaryEnv :=
        { env with translatorRules := env.translatorRules.erase h }
      let (code, goals, n1) ← compileAppCoreFuel fuel ordinaryEnv n h args
      let (r, n2) := fresh n1
      .ok (r, goals ++ [Goal.evalg code r], n2)
    else
      compileAppCoreFuel fuel env n h args
termination_by structural fuel _ _ _ _ => fuel

def compileAppCoreFuel : Nat → CEnv → Nat → String → List Atom →
    CompileM (Atom × List Goal × Nat)
  | 0, _, _, _, _ => .error "compiler fuel exhausted"
  | fuel + 1, env, n, h, args => do
    match h, args with
    | "quote", [e] => .ok (chainify e, [], n)              -- syntactic value
    | "Predicate", [goal] =>
        -- [SPEC metta.pl:275] `Predicate` converts a MeTTa expression to a
        -- Prolog term without evaluating the expression's members.
        .ok (chainify (Atom.expr [Atom.sym "Predicate", goal]), [], n)
    | "translatePredicate", [goal] => do
        -- The argument is Prolog syntax, not a MeTTa subexpression.  Preserve it
        -- as data and make the trusted-host boundary explicit at execution.
        let (r, n1) := fresh n
        .ok (r, [Goal.bin "translatePredicate" [chainify goal] r], n1)
    | "callPredicate", [predicate] => do
        let (term, goals, n1) ← compileExprFuel fuel env n predicate
        let (r, n2) := fresh n1
        -- Both source forms share one typed ownership-dispatch point: local
        -- predicates stay in the core, imported predicates cross the host
        -- boundary.  The executor accepts the quoted `Predicate` wrapper.
        .ok (r, goals ++ [Goal.bin "translatePredicate" [term] r], n2)
    | "assertaPredicate", [predicate] => do
        let (term, goals, n1) ← compileExprFuel fuel env n predicate
        let (r, n2) := fresh n1
        .ok (r, goals ++ [Goal.wact "assertaPredicate" [term] r], n2)
    | "assertzPredicate", [predicate] => do
        let (term, goals, n1) ← compileExprFuel fuel env n predicate
        let (r, n2) := fresh n1
        .ok (r, goals ++ [Goal.wact "assertzPredicate" [term] r], n2)
    | "retractPredicate", [predicate] => do
        let (term, goals, n1) ← compileExprFuel fuel env n predicate
        let (r, n2) := fresh n1
        .ok (r, goals ++ [Goal.wact "retractPredicate" [term] r], n2)
    | "process_metta_string", [source] => do
        let (term, goals, n1) ← compileExprFuel fuel env n source
        let (r, n2) := fresh n1
        .ok (r, goals ++ [Goal.wact "process_metta_string" [term] r], n2)
    | "unquote", [Atom.expr [Atom.sym "quote", e]] => compileAppFuel fuel env n "eval" [e]
    | "unquote", [e] => .ok (chainify (Atom.expr [Atom.sym "unquote", e]), [], n)
    | "empty", [] => .ok (trueA, [Goal.eq trueA falseA], n) -- branch failure
    | "cut", [] => .ok (trueA, [Goal.cut], n)
    | "test", [e, expected] => do
        -- Native collects every answer of `e`, unwraps a singleton, evaluates
        -- the expected expression, then performs variant comparison.
        -- [SPEC translator.pl:118-126, metta.pl:203-207]
        let (te, ge, n1) ← compileExprFuel fuel env n e
        let (answers, n2) := fresh n1
        let (tx, gx, n3) ← compileExprFuel fuel env n2 expected
        let (r, n4) := fresh n3
        .ok (r, [Goal.findall te ge answers] ++ gx ++
          [Goal.bin "#test-results" [answers, tx] r], n4)
    | "trace!", [message, value] =>
        -- [SPEC translator.pl:74-75] trace! is a stream rewrite to
        -- `(progn (println! message) value)`; println!'s pure value is True.
        compileAppFuel fuel env n "progn"
          [Atom.expr [Atom.sym "println!", message], value]
    | "and-then", [a, b] =>
        -- [SPEC translator.pl:177-180] evaluate `b` only when `a` is True.
        compileAppFuel fuel env n "if" [a, b, Atom.sym "False"]
    | "or-else", [a, b] =>
        -- [SPEC translator.pl:181-184] skip `b` when `a` is already True.
        compileAppFuel fuel env n "if" [a, Atom.sym "True", b]
    | "#+", [a, b] => compileAppFuel fuel env n "+" [a, b]   -- petta's flexible +
    | "#-", [a, b] => compileAppFuel fuel env n "-" [a, b]
    | "cons", [h, t] => do
        -- the list constructor IS structure: narrows via unification
        let (th, gh, n1) ← compileExprFuel fuel env n h
        let (tt, gt, n2) ← compileExprFuel fuel env n1 t
        .ok (consC th tt, gh ++ gt, n2)
    | "if", [c, t] => do
        let (tc, gc, n1) ← compileExprFuel fuel env n c
        let (tt, gt, n2) ← compileExprFuel fuel env n1 t
        .ok (tt, gc ++ [Goal.eq tc trueA] ++ gt, n2)
    | "if", [c, t, e] => do
        let (tc, gc, n1) ← compileExprFuel fuel env n c
        let (tt, gt, n2) ← compileExprFuel fuel env n1 t
        let (te, ge, n3) ← compileExprFuel fuel env n2 e
        let (r, n4) := fresh n3
        .ok (r, gc ++ [Goal.ite tc (compileBranch r (tt, gt))
          (compileBranch r (te, ge)) r], n4)
    | "let", [p, v, b] => do
        -- [SPEC translator.pl:185-188] translate pattern, value, and body in
        -- that order; emit (Pv=V), Gp, Gv, Gi. The result terms unify first,
        -- then pattern goals (narrowing), value goals, and the body.
        let (tp, gp, n1) ← compileExprFuel fuel env n p
        let (tv, gv, n2) ← compileExprFuel fuel env n1 v
        let (tb, gb, n3) ← compileExprFuel fuel env n2 b
        .ok (tb, [Goal.eq tp tv] ++ gp ++ gv ++ gb, n3)
    | "let*", [Atom.expr binds, b] => do
        -- desugar to nested lets
        let e := binds.foldr (fun bind acc =>
          match bind with
          | Atom.expr [p, v] => Atom.expr [Atom.sym "let", p, v, acc]
          | _ => acc) b
        compileExprFuel fuel env n e
    | "case", [scrut, Atom.expr arms] => do
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
              -- [SPEC translator.pl:163-176] the `Empty` arm is selected only
              -- when the scrutinee has no solution, so this path stays
              -- failure-sensitive.
              let carry := bindingTemplate sv [scrut]
              .ok (r, [Goal.softcut carry (gs ++ [Goal.eq sv ts]) armGs failGs], m)
          | none =>
              -- [SPEC translator.pl:174-176] no-default `case` leaves the
              -- scrutinee goals in ordinary Prolog flow (`Gk, KeyGoal, IfGoal`);
              -- do not eagerly collect every scrutinee answer before branches.
              .ok (r, gs ++ [Goal.eq sv ts] ++ armGs, n4)
    | "collapse", [e] => do
        let (te, ge, n1) ← compileExprFuel fuel env n e
        let (r, n2) := fresh n1
        .ok (r, [Goal.findall te ge r], n2)
    | "once", [e] => do
        let (te, ge, n1) ← compileExprFuel fuel env n e
        let (r, n2) := fresh n1
        .ok (r, [Goal.onceg te ge r], n2)
    | "superpose", [Atom.expr es] => do
        -- each SYNTACTIC element evaluated in its own branch (NONDET-1)
        let (branches, n1) ← es.foldlM (fun (acc : List (Atom × List Goal) × Nat) e => do
          let (te, ge, m) ← compileExprFuel fuel env acc.2 e
          .ok (acc.1 ++ [(te, ge)], m)) (([], n))
        let (r, n2) := fresh n1
        .ok (r, [Goal.amb branches r], n2)
    | "unify", [Atom.sym "&self", pat, thn, els] => do
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
    | "unify", [a, bb, thn, els] => do
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
    | "succeedsPredicate", [Atom.expr (sp :: Atom.sym rel :: args)] => do
        -- [SPEC lib_spaces.metta + translator.pl:101-105,264-267]:
        -- the translator hook turns a space predicate expression into the
        -- corresponding Prolog predicate call. In PLeaTTa's space model this
        -- is exactly a space match that returns True once per proof, or False
        -- if the predicate has no proof.
        let (ts, gs, n1) ← compileExprFuel fuel env n sp
        let (r, n2) := fresh n1
        let pat := chainify (Atom.expr (Atom.sym rel :: args))
        .ok (r, gs ++ [Goal.softcut pat [Goal.smatch (spacePat ts pat)]
          [Goal.eq r trueA] [Goal.eq r falseA]], n2)
    | "for", [v, collection, body] =>
        -- [SPEC lib_patrick.metta:14-18] translator-rule macro:
        -- `(for $x xs body)` compiles as `(let $x (superpose xs) body)`.
        compileAppFuel fuel env n "let" [v, Atom.expr [Atom.sym "superpose", collection], body]
    | "chain", [e, v, body] =>
        -- [SPEC translator.pl:185-188] `chain` shares the native `let`
        -- clause after translator-rule dispatch has already selected the
        -- `chain` head.  Enter the built-in `let` core directly: re-entering
        -- `compileAppFuel` would incorrectly let an unrelated `let` hook
        -- capture a source `chain`.
        compileAppCoreFuel fuel env n "let" [v, e, body]
    | "foldall", [f, gen, init] => do
        let (tg, gg, n1) ← compileExprFuel fuel env n gen
        let (lst, n2) := fresh n1
        let (tf, gf, n3) ← compileExprFuel fuel env n2 f
        let (ti, gi, n4) ← compileExprFuel fuel env n3 init
        let (r, n5) := fresh n4
        .ok (r, [Goal.findall tg gg lst] ++ gf ++ gi ++
                [Goal.call "#foldacc" [tf, lst, ti] r], n5)
    | "forall", [gen, f] => do
        let (tg, gg, n1) ← compileExprFuel fuel env n gen
        let (lst, n2) := fresh n1
        let (tf, gf, n3) ← compileExprFuel fuel env n2 f
        let (r, n4) := fresh n3
        .ok (r, [Goal.findall tg gg lst] ++ gf ++
                [Goal.call "#allacc" [tf, lst] r], n4)
    | "progn", args => do
        if args.isEmpty then .error "progn: empty" else do
        let (ts, gs, n1) ← compileListFuel fuel env n args
        .ok (ts.getLast!, gs, n1)
    | "prog1", args => do
        if args.isEmpty then .error "prog1: empty" else do
        let (ts, gs, n1) ← compileListFuel fuel env n args
        .ok (ts.head!, gs, n1)
    | "with_mutex", [_mutex, body] =>
        -- [SPEC translator.pl:137-138] the mutex serializes the translated
        -- body. PLeaTTa's machine is already sequential, so its answer
        -- relation is exactly the body's answer relation.
        compileExprFuel fuel env n body
    | "transaction", [body] => do
        -- [SPEC translator.pl:139-140] SWI transaction/1 commits its first
        -- successful branch and rolls dynamic updates back on failure.
        let (tb, gb, n1) ← compileExprFuel fuel env n body
        let carry := bindingTemplate tb [body]
        .ok (tb, [Goal.transactiong carry gb], n1)
    | "superpose", [e] => do
        -- computed tuple: spread its members at run time
        let (te, ge, n1) ← compileExprFuel fuel env n e
        let (r, n2) := fresh n1
        .ok (r, ge ++ [Goal.spread te r], n2)
    | "hyperpose", [Atom.expr es] => do
        -- [SPEC translator.pl:129-135,417-424] `hyperpose` has the same
        -- result semantics as one evaluated branch per element. Native runs
        -- those branches concurrently; PLeaTTa preserves the answer relation.
        let (branches, n1) ← es.foldlM (fun (acc : List (Atom × List Goal) × Nat) e => do
          let (te, ge, m) ← compileExprFuel fuel env acc.2 e
          .ok (acc.1 ++ [(te, ge)], m)) (([], n))
        let (r, n2) := fresh n1
        .ok (r, [Goal.amb branches r], n2)
    | "hyperpose", [e] => do
        -- Runtime/computed list path: enumerate the computed tuple, then eval
        -- each element as code (`hyperpose_runtime(Exprs, Out) :- ... eval`).
        let (te, ge, n1) ← compileExprFuel fuel env n e
        let (elem, n2) := fresh n1
        let (r, n3) := fresh n2
        .ok (r, ge ++ [Goal.spread te elem, Goal.evalg elem r], n3)
    | "unique", [e] => do
        -- stream dedup: distinct solutions, order preserved
        let (te, ge, n1) ← compileExprFuel fuel env n e
        let (lst, n2) := fresh n1
        let (ded, n3) := fresh n2
        let (r, n4) := fresh n3
        .ok (r, [Goal.findall te ge lst,
                 Goal.bin "unique-atom" [lst] ded, Goal.spread ded r], n4)
    | "union", [e1, e2] => do
        -- stream union: concatenated enumerations
        let (t1, g1, n1) ← compileExprFuel fuel env n e1
        let (t2, g2, n2) ← compileExprFuel fuel env n1 e2
        let (l1, n3) := fresh n2
        let (l2, n4) := fresh n3
        let (cc, n5) := fresh n4
        let (r, n6) := fresh n5
        .ok (r, [Goal.findall t1 g1 l1, Goal.findall t2 g2 l2,
                 Goal.bin "union-atom" [l1, l2] cc, Goal.spread cc r], n6)
    | "intersection", [e1, e2] => do
        let (t1, g1, n1) ← compileExprFuel fuel env n e1
        let (t2, g2, n2) ← compileExprFuel fuel env n1 e2
        let (l1, n3) := fresh n2
        let (l2, n4) := fresh n3
        let (cc, n5) := fresh n4
        let (r, n6) := fresh n5
        .ok (r, [Goal.findall t1 g1 l1, Goal.findall t2 g2 l2,
                 Goal.bin "intersection-atom" [l1, l2] cc, Goal.spread cc r], n6)
    | "subtraction", [e1, e2] => do
        let (t1, g1, n1) ← compileExprFuel fuel env n e1
        let (t2, g2, n2) ← compileExprFuel fuel env n1 e2
        let (l1, n3) := fresh n2
        let (l2, n4) := fresh n3
        let (cc, n5) := fresh n4
        let (r, n6) := fresh n5
        .ok (r, [Goal.findall t1 g1 l1, Goal.findall t2 g2 l2,
                 Goal.bin "subtraction-atom" [l1, l2] cc, Goal.spread cc r], n6)
    | "eval", [e] => do
        let (te, ge, n1) ← compileExprFuel fuel env n e
        let (r, n2) := fresh n1
        .ok (r, ge ++ [Goal.evalg te r], n2)
    | "catch", [e] => do
        -- [SPEC translator.pl:293-300] catch wraps the translated goals for
        -- the expression, returning normal answers, failing on ordinary no
        -- answer, and reifying runtime/type exceptions as `(Error ...)`.
        let (te, ge, n1) ← compileExprFuel fuel env n e
        let (r, n2) := fresh n1
        .ok (r, [Goal.catchg te ge r], n2)
    | "call", [Atom.expr (Atom.sym f :: xs)] => do
        -- [SPEC translator.pl:271-276] manual compile-time dispatch:
        -- translate the embedded expression's arguments, then emit a direct
        -- predicate call `f(args..., Out)`.
        let (ts, gs, n1) ← compileArgsAtFuel fuel env n f 0 xs
        let (r, n2) := fresh n1
        .ok (r, gs ++ [Goal.call f ts r], n2)
    | "reduce", [e] => compileAppFuel fuel env n "eval" [e]
    | "get-type-space", [_sp, e] => compileAppFuel fuel env n "get-type" [e]
    | "get-atoms", [sp] => do
        let (ts, gs, n1) ← compileExprFuel fuel env n sp
        let (r, n2) := fresh n1
        .ok (r, gs ++ [Goal.smatch (spacePat ts r)], n2)
    | "get-type", [e] => do
        -- PeTTa's automatic function dispatch translates the argument before
        -- asking for its type [SPEC translator.pl:301-310,410].
        let (te, ge, n1) ← compileExprFuel fuel env n e
        let (r, n2) := fresh n1
        .ok (r, ge ++ [Goal.bin "get-type" [te] r], n2)
    | "get-metatype", [e] => do
        let (te, ge, n1) ← compileExprFuel fuel env n e
        let (r, n2) := fresh n1
        .ok (r, ge ++ [Goal.bin "get-metatype" [te] r], n2)
    | "match", [sp, p, tmpl] => do
        let (ts, gs, n0) ← compileExprFuel fuel env n sp
        -- A `,`-headed pattern is a CONJUNCTIVE query: one smatch per conjunct,
        -- shared bindings joining them (the relational join).
        let (tt, gt, n1) ← compileExprFuel fuel env n0 tmpl
        let pats := match p with
          | Atom.expr (Atom.sym "," :: ps) => ps
          | _ => [p]
        .ok (tt, gs ++ pats.map (fun q => Goal.smatch (spacePat ts (chainify q))) ++ gt, n1)
    | "find", [sp, p] => do
        -- [SPEC lib_spaces.metta:8-11] `find` is match-as-Boolean, but its
        -- successful True answers must carry pattern bindings into the caller.
        let (ts, gs, n0) ← compileExprFuel fuel env n sp
        let (r, n1) := fresh n0
        let pat := chainify p
        .ok (r, gs ++ [Goal.softcut pat [Goal.smatch (spacePat ts pat)]
          [Goal.eq r trueA] [Goal.eq r falseA]], n1)
    | "match", [sp, p] => do
        -- under-applied registered fun => partial value [SPEC translator.pl:58]
        .ok (chainOf [Atom.sym "partial", Atom.sym "match",
                      chainOf [chainify sp, chainify p]], [], n)
    | "==", [Atom.expr [Atom.sym "size-atom", e], kA] => do
        -- shape constraint: `(== (size-atom e) k)` with literal k constrains
        -- e's STRUCTURE (a k-slot chain) — structural, so enumeration
        -- terminates exactly as in native PeTTa/swipl
        match kA with
        | Atom.gnd (Metta.Ground.int k) => do
            let (te, ge, n1) ← compileExprFuel fuel env n e
            let (slots, n2) := (List.range k.toNat).foldl
              (fun (acc : List Atom × Nat) _ =>
                let (v, m) := fresh acc.2; (acc.1 ++ [v], m)) ([], n1)
            .ok (trueA, ge ++ [Goal.eq te (chainOf slots)], n2)
        | _ => .error "==: size-atom vs non-literal"
    | "=", [a, b] => do
        -- Boolean unification predicate [SPEC metta.pl registers `=/3`]:
        -- success returns True with bindings, failure returns False.
        let (ta, ga, n1) ← compileExprFuel fuel env n a
        let (tb, gb, n2) ← compileExprFuel fuel env n1 b
        let (r, n3) := fresh n2
        let carry := bindingTemplate (chainOf [ta, tb]) [a, b]
        .ok (r, [Goal.softcut carry (ga ++ gb ++ [Goal.eq ta tb])
                  [Goal.eq r trueA] [Goal.eq r falseA]], n3)
    | "add-atom", [sp, a] => do
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
    | "remove-atom", [sp, a] => do
        let (tsp, gsp, n0) ← compileExprFuel fuel env n sp
        match a with
        | Atom.expr (Atom.sym "=" :: _) =>
            let (r, n1) := fresh n0
            .ok (r, gsp ++ [Goal.wact "remove-atom" [tsp, chainify a] r], n1)
        | _ =>
            let (r, n1) := fresh n0
            .ok (r, gsp ++ [Goal.wact "remove-atom" [tsp, chainify a] r], n1)
    | "bind!", [name, Atom.expr [Atom.sym "new-state", e]] => do
        -- [SPEC metta.pl:240] bind!(A, [new-state,B], C) :- change-state!(A,B,C)
        compileAppFuel fuel env n "change-state!" [name, e]
    | "bind!", [_name, _value] =>
        -- [SPEC metta.pl:240,303] `bind!` is registered, but native PeTTa only
        -- defines the `(new-state ...)` clause; other values fail as calls.
        .ok (trueA, [Goal.eq trueA falseA], n)
    | "get-state", [name] => do
        let (tn, gn, n1) ← compileExprFuel fuel env n name
        let (r, n2) := fresh n1
        .ok (r, gn ++ [Goal.wact "get-state" [tn] r], n2)
    | "change-state!", [name, e] => do
        let (tn, gn, n1) ← compileExprFuel fuel env n name
        let (te, ge, n2) ← compileExprFuel fuel env n1 e
        let (r, n3) := fresh n2
        .ok (r, gn ++ ge ++ [Goal.wact "change-state!" [tn, te] r], n3)
    | _, _ =>
        if env.prologFunctions.contains h then do
          let (ts, gs, n1) ← compileArgsAtFuel fuel env n h 0 args
          let (r, n2) := fresh n1
          let (ok, n3) := fresh n2
          let predicate := chainify (Atom.expr (Atom.sym h :: ts ++ [r]))
          .ok (r, gs ++ [Goal.bin "translatePredicate" [predicate] ok], n3)
        else if env.defined.contains h then do
          let chains0 := env.typeChains h
          let hasCompoundParam : List Atom → Bool := fun chain =>
            chain.dropLast.any (fun ty =>
              match ty with
              | Atom.expr _ => true
              | _ => false)
          let useTypedDispatch :=
            match chains0 with
            | [] => false
            | [_] => chains0.any hasCompoundParam
            | _ :: _ :: _ => true
          if useTypedDispatch then do
            let chains := chains0
            -- typed dispatch [SPEC translator.pl:310-317, 341-363]: one branch
            -- per declared arrow chain; each argument type-checks via
            -- `get-type(V,T) *-> true ; get-metatype(V,T)` (softcut), so does
            -- the OUTPUT unless the type is %Undefined%/Atom;
            -- Expression-typed args pass syntactically.
            let (r, n0) := fresh n
            let checkable : Atom → Bool := fun ty => match ty with
              | Atom.sym s => s != "%Undefined%" && s != "Atom" &&
                              s != "Expression"
              | _ => true
            let mkCheck : Atom → Atom → Nat → (List Goal × Nat) := fun v ty m =>
              if !checkable ty then ([], m) else
              let (g1, m1) := fresh m
              let (g2, m2) := fresh m1
              ([Goal.softcut (Atom.sym "#u")
                 [Goal.bin "get-type" [v] g1, Goal.eq g1 (chainify ty)]
                 []
                 [Goal.bin "get-metatype" [v] g2, Goal.eq g2 ty]], m2)
            let (branches, n3) ← chains.foldlM
              (fun (acc : List (Atom × List Goal) × Nat) chain => do
                match chain.dropLast, chain.getLast? with
                | ptys, some rty => do
                  if ptys.length != args.length then pure acc else do
                  let (ts, gs, m1) ← args.zip ptys |>.foldlM
                    (fun (a2 : List Atom × List Goal × Nat) (arg, ty) => do
                      if ty == Atom.sym "Expression" then
                        pure (a2.1 ++ [chainify arg], a2.2.1, a2.2.2)
                      else do
                        let (t, g, m) ← compileExprFuel fuel env a2.2.2 arg
                        let (chk, m') := mkCheck t ty m
                        pure (a2.1 ++ [t], a2.2.1 ++ g ++ chk, m'))
                    (([], [], acc.2))
                  let (outChk, m2) := mkCheck r rty m1
                  pure (acc.1 ++ [(r, gs ++ [Goal.call h ts r] ++ outChk)], m2)
                | _, none => pure acc)
              (([], n0))
            if branches.isEmpty then do
              let (ts, gs, n1) ← compileArgsAtFuel fuel env n h 0 args
              if (env.arities h).contains ts.length then
                let (r2, n2) := fresh n1
                .ok (r2, gs ++ [Goal.call h ts r2], n2)
              else
                .ok (partialValue h ts, gs, n1)
            else
              .ok (r, [Goal.amb branches r], n3)
          else do
            let (ts, gs, n1) ← compileArgsAtFuel fuel env n h 0 args
            if (env.arities h).contains ts.length then
              let (r, n2) := fresh n1
              .ok (r, gs ++ [Goal.call h ts r], n2)
            else
              .ok (partialValue h ts, gs, n1)
        else if env.isBin h then do
          let (ts, gs, n1) ← compileArgsAtFuel fuel env n h 0 args
          match compileBinArity h with
          | some ar =>
              if ar == ts.length then
                let (r, n2) := fresh n1
                .ok (r, gs ++ [Goal.bin h ts r], n2)
              else
                .ok (partialValue h ts, gs, n1)
          | none =>
              let (r, n2) := fresh n1
              .ok (r, gs ++ [Goal.bin h ts r], n2)
        else do
          let (ts, gs, n1) ← compileListFuel fuel env n args
          if env.dynamicUnknown && dynamicUnknownHead h then
            -- Unknown lowercase heads in a bang may be functions introduced by
            -- earlier top-level `add-atom` effects; resolve them at run time.
            -- Unregistered constructor-like heads stay data, matching native.
            let (r, n2) := fresh n1
            .ok (r, gs ++ [Goal.callDyn (Atom.sym h) ts r], n2)
          else
            -- Unknown non-function heads are data at this translation point
            -- [SPEC translator.pl:318-326].
            .ok (chainOf (Atom.sym h :: ts), gs, n1)
termination_by structural fuel _ _ _ _ => fuel

/-- Compile the ordered arms of `case`.  Giving this traversal its own fuelled
equations keeps both the list recursion and its calls back into expression
compilation visible to the kernel. -/
def compileCaseArmsFuel : Nat → CEnv → Atom → Atom → Nat → List Atom →
    CompileM (List Goal × Nat)
  | 0, _, _, _, _, _ => .error "compiler fuel exhausted"
  | _ + 1, _, _, _, m, [] =>
      .ok ([Goal.eq trueA falseA], m)
  | fuel + 1, env, scrutinee, result, m,
      Atom.expr [Atom.sym "Empty", _] :: more =>
      compileCaseArmsFuel fuel env scrutinee result m more
  | fuel + 1, env, scrutinee, result, m,
      Atom.expr [pattern, body] :: more => do
      let (compiledPattern, patternGoals, m1) ←
        compilePatternFuel fuel env m pattern
      let (compiledBody, bodyGoals, m2) ←
        compileExprFuel fuel env m1 body
      let (elseGoals, m3) ←
        compileCaseArmsFuel fuel env scrutinee result m2 more
      let carry := bindingTemplate compiledPattern [pattern]
      .ok ([Goal.softcut carry
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

/-- Publicly named fuelled argument traversal, starting at argument zero. -/
def compileArgsFuel (fuel : Nat) (env : CEnv) (counter : Nat)
    (head : String) (arguments : List Atom) :
    CompileM (List Atom × List Goal × Nat) :=
  compileArgsAtFuel fuel env counter head 0 arguments

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
/-- Negative sequencing example: native `progn` requires at least one
expression, so the empty form is rejected explicitly. -/
theorem compileExprFuel_progn_empty_eq (fuel counter : Nat) (env : CEnv)
    (noHook : env.translatorRules.contains "progn" = false) :
    compileExprFuel (fuel + 3) env counter (.expr [.sym "progn"]) =
      .error "progn: empty" := by
  rw [show fuel + 3 = (fuel + 2) + 1 by omega]
  rw [compileExprFuel.eq_7 (x_4 := by simp)]
  rw [show fuel + 2 = (fuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_36]
  rfl

set_option maxHeartbeats 2000000 in
/-- Negative sequencing example: native `prog1` requires at least one
expression, so the empty form is rejected explicitly. -/
theorem compileExprFuel_prog1_empty_eq (fuel counter : Nat) (env : CEnv)
    (noHook : env.translatorRules.contains "prog1" = false) :
    compileExprFuel (fuel + 3) env counter (.expr [.sym "prog1"]) =
      .error "prog1: empty" := by
  rw [show fuel + 3 = (fuel + 2) + 1 by omega]
  rw [compileExprFuel.eq_7 (x_4 := by simp)]
  rw [show fuel + 2 = (fuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_37]
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
  rw [compileExprFuel.eq_7 (x_4 := by simp)]
  rw [show listFuel + 2 = (listFuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_36]
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
  rw [compileExprFuel.eq_7 (x_4 := by simp)]
  rw [show listFuel + 2 = (listFuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_37]
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
  rw [compileExprFuel.eq_7 (x_4 := by simp)]
  rw [show bodyFuel + 3 = (bodyFuel + 2) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [show bodyFuel + 2 = (bodyFuel + 1) + 1 by omega]
  rw [compileAppCoreFuel.eq_36]
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
  rw [compileExprFuel.eq_7 (x_4 := by simp)]
  rw [show bodyFuel + 3 = (bodyFuel + 2) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [show bodyFuel + 2 = (bodyFuel + 1) + 1 by omega]
  rw [compileAppCoreFuel.eq_37]
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
  rw [compileExprFuel.eq_7 (x_4 := by simp)]
  rw [show bodyFuel + 2 = (bodyFuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_26, body]
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
  rw [compileExprFuel.eq_7 (x_4 := by simp)]
  rw [show bodyFuel + 2 = (bodyFuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_27, body]
  rfl

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
  rw [compileExprFuel.eq_7 (x_4 := by simp)]
  rw [show childFuel + 2 = (childFuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  exact compileAppCoreFuel_let_eq childFuel env counter pattern value
    bodySource patternTerm valueTerm bodyTerm patternGoals valueGoals
    bodyGoals patternCounter valueCounter nextCounter patternCompiled
    valueCompiled bodyCompiled

set_option maxHeartbeats 2000000 in
/-- `chain` follows the same pinned translation clause as `let`: source order
is value, pattern, body, while translation traverses pattern, value, body.  Its
own hook check is the only dispatch guard; a `let` hook cannot capture it. -/
theorem compileExprFuel_chain_eq (childFuel : Nat) (env : CEnv)
    (counter : Nat) (value pattern bodySource : Atom)
    (patternTerm valueTerm bodyTerm : Atom)
    (patternGoals valueGoals bodyGoals : List Goal)
    (patternCounter valueCounter nextCounter : Nat)
    (noHook : env.translatorRules.contains "chain" = false)
    (patternCompiled : compileExprFuel childFuel env counter pattern =
      .ok (patternTerm, patternGoals, patternCounter))
    (valueCompiled : compileExprFuel childFuel env patternCounter value =
      .ok (valueTerm, valueGoals, valueCounter))
    (bodyCompiled : compileExprFuel childFuel env valueCounter bodySource =
      .ok (bodyTerm, bodyGoals, nextCounter)) :
    compileExprFuel (childFuel + 4) env counter
        (.expr [.sym "chain", value, pattern, bodySource]) =
      .ok (bodyTerm,
        [Goal.eq patternTerm valueTerm] ++ patternGoals ++ valueGoals ++
          bodyGoals,
        nextCounter) := by
  rw [show childFuel + 4 = (childFuel + 3) + 1 by omega]
  rw [compileExprFuel.eq_7 (x_4 := by simp)]
  rw [show childFuel + 3 = (childFuel + 2) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [show childFuel + 2 = (childFuel + 1) + 1 by omega]
  rw [compileAppCoreFuel.eq_33]
  exact compileAppCoreFuel_let_eq childFuel env counter pattern value
    bodySource patternTerm valueTerm bodyTerm patternGoals valueGoals
    bodyGoals patternCounter valueCounter nextCounter patternCompiled
    valueCompiled bodyCompiled

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
  rw [compileExprFuel.eq_7 (x_4 := by simp)]
  rw [show bodyFuel + 2 = (bodyFuel + 1) + 1 by omega]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_38]
  exact bodyCompiled

set_option maxHeartbeats 2000000 in
/-- The implementation equation for the zero-argument `cut` form when no
translator hook shadows that head.  This small exported equation prevents
downstream proofs from unfolding the complete application compiler. -/
theorem compileExprFuel_cut_eq (fuel counter : Nat) (env : CEnv)
    (noHook : env.translatorRules.contains "cut" = false) :
    compileExprFuel (fuel + 3) env counter (.expr [.sym "cut"]) =
      .ok (.sym "True", [Goal.cut], counter) := by
  rw [compileExprFuel.eq_7 (x_4 := by simp)]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_13]
  rfl

set_option maxHeartbeats 2000000 in
/-- The implementation equation for syntactic quotation when no translator
hook shadows the `quote` head. -/
theorem compileExprFuel_quote_eq (fuel counter : Nat) (env : CEnv)
    (source : Atom)
    (noHook : env.translatorRules.contains "quote" = false) :
    compileExprFuel (fuel + 3) env counter (.expr [.sym "quote", source]) =
      .ok (chainify source, [], counter) := by
  rw [compileExprFuel.eq_7 (x_4 := by simp)]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_2]

set_option maxHeartbeats 2000000 in
/-- The implementation equation for zero-argument `empty` when no translator
hook shadows the pinned built-in.  The executable represents guaranteed
branch failure by an impossible equality. -/
theorem compileExprFuel_empty_eq (fuel counter : Nat) (env : CEnv)
    (noHook : env.translatorRules.contains "empty" = false) :
    compileExprFuel (fuel + 3) env counter (.expr [.sym "empty"]) =
      .ok (.sym "True",
        [Goal.eq (.sym "True") (.sym "False")], counter) := by
  rw [compileExprFuel.eq_7 (x_4 := by simp)]
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_12]
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

/-- Surface desugaring: HE-style binder forms become synthesized rules plus
    the function-value form —
    `(map-atom l $x body)`       → `(map-atom l #lamK)`  + `(= (#lamK $x) body)`
    `(filter-atom l $x body)`    → likewise
    `(foldl-atom l i $a $x body)`→ `(foldl-atom l i #lamK)` + 2-param rule;
    `(|-> params body)` closure-converts to a synthesized rule whose value is
    the bare `#lam` symbol or the partially applied `(#lam captures…)`. -/
private def _desugarDoc : Unit := ()

/-- Collect the $-variables of a surface atom (order-preserving). -/
partial def surfaceVars (a : Atom) (acc : List String := []) : List String :=
  match a with
  | Atom.var v => if acc.contains v then acc else acc ++ [v]
  | Atom.expr es => es.foldl (fun ac e => surfaceVars e ac) acc
  | _ => acc

partial def desugarBinders (a : Atom) (k : Nat) :
    Atom × List Atom × Nat :=
  match a with
  | Atom.expr [Atom.sym "|->", Atom.expr ps, body] =>
      -- λ closure conversion: captured outer vars become leading params;
      -- the VALUE is the bare symbol (no captures) or the partially
      -- applied chain (#lamK cap…), completed by callDyn at application
      let (b', ds, k1) := desugarBinders body k
      let f := s!"#lam{k1}"
      let pvars := ps.foldl (fun ac e => surfaceVars e ac) []
      let caps := (surfaceVars b').filter (fun v => !pvars.contains v)
      let rule := Atom.expr [Atom.sym "=",
        Atom.expr (Atom.sym f :: (caps.map Atom.var) ++ ps), b']
      -- [SPEC translator.pl:253-254] value = F (no captures) or
      -- partial(F, FreeVars)
      let value := if caps.isEmpty then Atom.sym f
        else partialValue f (caps.map Atom.var)
      (value, ds ++ [rule], k1 + 1)
  | Atom.expr [Atom.sym "|->", Atom.var pv, body] =>
      desugarBinders (Atom.expr [Atom.sym "|->", Atom.expr [Atom.var pv], body]) k
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
  | Atom.expr es =>
      let (es', ds, k') := es.foldl
        (fun (acc : List Atom × List Atom × Nat) e =>
          let (e', d, k2) := desugarBinders e acc.2.2
          (acc.1 ++ [e'], acc.2.1 ++ d, k2)) ([], [], k)
      (Atom.expr es', ds, k')
  | other => (other, [], k)

/-- Partition and compile a parsed program; bangs become queries
    `(goals, resultVar)`. -/
def compileProgram (isBin : String → Bool) (atoms0 : List Atom) :
    CompileM (Prog × List (List Goal × Atom)) := do
  let (atoms, _) := atoms0.foldl
    (fun (acc : List Atom × Nat) a =>
      let (a', ds, k') := desugarBinders a acc.2
      (acc.1 ++ ds ++ [a'], k')) ([], 0)
  -- pass 1: collect rule heads, type decls, facts, bangs
  let mut heads : List String := []
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
          if !heads.contains f then heads := heads ++ [f]
      | Atom.expr [Atom.sym ":", subj, ty] => decls := decls ++ [(subj, ty)]
      | other => facts := facts ++ [other]
  -- [SPEC translator.pl:354-363] only `Expression`-typed argument positions
  -- stay syntactic; `Atom`/`%Undefined%` translate unchecked; other types
  -- translate with a get-type post-check (the check is a v2 item, ledgered)
  let arities := rules.map (fun (f, ps, _) => (f, ps.length))
  let env : CEnv := mkEnv isBin heads arities decls
  let mut n := 0
  let mut clauses : List (String × Clause) := []
  for (f, ps, rhs) in rules do
    let (c, n') ← compileRule env n ps rhs
    clauses := clauses ++ [(f, c)]; n := n'
  let queryEnv : CEnv := mkEnv isBin heads
    (arities ++ clauses.map (fun (f, c) => (f, c.params.length))) decls
  let mut queries : List (List Goal × Atom) := []
  for q in bangs do
    let (t, gs, n') ← compileExpr queryEnv n q
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
  let (forms, _) := forms0.foldl
    (fun (acc : List SourceForm × Nat) form =>
      match form with
      | .hostImport moduleName observable =>
          (acc.1 ++ [.hostImport moduleName observable], acc.2)
      | .prologRegister functions observable =>
          (acc.1 ++ [.prologRegister functions observable], acc.2)
      | .importBegin => (acc.1 ++ [.importBegin], acc.2)
      | .importEnd observable =>
          (acc.1 ++ [.importEnd observable], acc.2)
      | .atom a observable =>
          let (a', ds, k') := desugarBinders a acc.2
          (acc.1 ++ ds.map (SourceForm.atom · observable) ++
            [.atom a' observable], k')) ([], 0)
  let mut heads : List String := []
  let mut arities : List (String × Nat) := []
  for form in forms do
    match form with
    | .hostImport _ _ => pure ()
    | .prologRegister _ _ => pure ()
    | .importBegin | .importEnd _ => pure ()
    | .atom a _ =>
        match a with
        | Atom.expr [Atom.sym "=", Atom.expr (Atom.sym f :: ps), _] =>
            if !heads.contains f then heads := heads ++ [f]
            arities := arities ++ [(f, ps.length)]
        | _ => pure ()
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
            events := events ++ [TopEvent.query [] trueA pendingObservable]
            pendingBang := false
            continue
        | Atom.expr [Atom.sym "remove-translator-rule!", Atom.sym f] =>
            translatorRules := translatorRules.erase f
            events := events ++ [TopEvent.query [] trueA pendingObservable]
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
        let (t, gs, n') ← compileExpr env n a
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
            events := events ++ [TopEvent.query [] trueA observable]
        | Atom.expr [Atom.sym "!",
            Atom.expr [Atom.sym "remove-translator-rule!", Atom.sym f]] =>
            translatorRules := translatorRules.erase f
            events := events ++ [TopEvent.query [] trueA observable]
        | Atom.expr [Atom.sym "!", q] =>
            let liveArities := arities ++ clauses.map (fun (f, c) =>
              (f, c.params.length))
            let env := { mkEnv isBin heads liveArities decls with
              translatorRules, prologFunctions }
            let (t, gs, n') ← compileExpr env n q
            events := events ++ [TopEvent.query gs t observable]
            n := n'
        | Atom.expr [Atom.sym "=", Atom.expr (Atom.sym f :: ps), rhs] =>
            let env := { mkEnv isBin heads arities decls with
              translatorRules, prologFunctions }
            let (c, n') ← compileRule env n ps rhs
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
