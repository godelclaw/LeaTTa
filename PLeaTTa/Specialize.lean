-- SPDX-License-Identifier: Apache-2.0

/-
PLeaTTa's compiler-profile specialization pass.

The generic compiler and `Goal.callDyn` remain the reference path.  A
specialized clause is obtained by applying the concrete higher-order binding
to the already-compiled clause and lowering only a now-concrete dynamic head
to the existing direct-call IR.  The stateful discovery/commit lifecycle is
deliberately layered above these pure equations.

[SPEC specializer.pl:14-58, translator.pl:18-24]
-/
import PLeaTTa.Compile
import MettaHyperonFull.Core.Unification

namespace PLeaTTa

open Metta (Atom Subst)

/-- Recover the source metadata paired with a generically compiled rule.
    Sequential and dynamically asserted clauses use this same constructor. -/
def MetaClause.ofRule? (source : Atom) (compiled : Clause) : Option MetaClause :=
  match source with
  | Atom.expr [Atom.sym "=", Atom.expr (Atom.sym parent :: params), body] =>
      some { parent, sourceParams := params, sourceBody := body, compiled }
  | _ => none

def partialHeadView? (a : Atom) : Option (String × List Atom) :=
  match chainListM a with
  | some [Atom.sym "partial", Atom.sym base, bound] =>
      (chainListM bound).map (base, ·)
  | _ => none

mutual

/-- Lower a concrete dynamic function head to the existing direct-call IR.
    Unknown symbols retain the generic `callDyn` fallback. -/
def lowerConcreteGoal (isDefined : String → Bool) : Goal → Goal
  | .callDyn (Atom.sym f) args res =>
      if isDefined f then .call f args res else .callDyn (Atom.sym f) args res
  | .catchg tmpl sub res =>
      .catchg tmpl (lowerConcreteGoals isDefined sub) res
  | .softcut tmpl sub thn els =>
      .softcut tmpl (lowerConcreteGoals isDefined sub)
        (lowerConcreteGoals isDefined thn) (lowerConcreteGoals isDefined els)
  | .findall tmpl sub res =>
      .findall tmpl (lowerConcreteGoals isDefined sub) res
  | .onceg tmpl sub res =>
      .onceg tmpl (lowerConcreteGoals isDefined sub) res
  | .transactiong tmpl sub =>
      .transactiong tmpl (lowerConcreteGoals isDefined sub)
  | .amb branches res =>
      .amb (lowerConcreteBranches isDefined branches) res
  | .ite cond thn els res =>
      .ite cond (thn.1, lowerConcreteGoals isDefined thn.2)
        (els.1, lowerConcreteGoals isDefined els.2) res
  | g => g

/-- Lower concrete dynamic heads in a goal sequence. -/
def lowerConcreteGoals (isDefined : String → Bool) : List Goal → List Goal
  | [] => []
  | g :: gs =>
      lowerConcreteGoal isDefined g :: lowerConcreteGoals isDefined gs

/-- Lower concrete dynamic heads inside nondeterministic branches. -/
def lowerConcreteBranches (isDefined : String → Bool) :
    List (Atom × List Goal) → List (Atom × List Goal)
  | [] => []
  | (tmpl, goals) :: rest =>
      (tmpl, lowerConcreteGoals isDefined goals) ::
        lowerConcreteBranches isDefined rest

end


/-- The pure base specialization equation: instantiate one captured clause,
    then lower dynamic calls whose heads became known functions. -/
def specializeClauseBase (isDefined : String → Bool) (binding : Subst)
    (clause : Clause) : Clause :=
  { params := clause.params.map (Metta.Subst.apply binding)
    result := Metta.Subst.apply binding clause.result
    body := lowerConcreteGoals isDefined (instantiateGoals binding clause.body) }

mutual

/-- Full profile lowering: concrete function heads become `call`, builtins
    become `bin`, and concrete partials append their bound arguments. -/
def lowerProfileGoal (isDefined isBin : String → Bool) : Goal → Goal
  | .callDyn head args res =>
      match head with
      | Atom.sym f =>
          if isDefined f then .call f args res
          else if isBin f then .bin f args res
          else .callDyn head args res
      | other =>
          match partialHeadView? other with
          | some (base, bound) =>
              if isDefined base then .call base (bound ++ args) res
              else if isBin base then .bin base (bound ++ args) res
              else .callDyn head args res
          | none => .callDyn head args res
  | .catchg tmpl sub res =>
      .catchg tmpl (lowerProfileGoals isDefined isBin sub) res
  | .softcut tmpl sub thn els =>
      .softcut tmpl (lowerProfileGoals isDefined isBin sub)
        (lowerProfileGoals isDefined isBin thn)
        (lowerProfileGoals isDefined isBin els)
  | .findall tmpl sub res =>
      .findall tmpl (lowerProfileGoals isDefined isBin sub) res
  | .onceg tmpl sub res =>
      .onceg tmpl (lowerProfileGoals isDefined isBin sub) res
  | .transactiong tmpl sub =>
      .transactiong tmpl (lowerProfileGoals isDefined isBin sub)
  | .amb branches res =>
      .amb (lowerProfileBranches isDefined isBin branches) res
  | .ite cond thn els res =>
      .ite cond (thn.1, lowerProfileGoals isDefined isBin thn.2)
        (els.1, lowerProfileGoals isDefined isBin els.2) res
  | goal => goal

def lowerProfileGoals (isDefined isBin : String → Bool) : List Goal → List Goal
  | [] => []
  | goal :: rest =>
      lowerProfileGoal isDefined isBin goal ::
        lowerProfileGoals isDefined isBin rest

def lowerProfileBranches (isDefined isBin : String → Bool) :
    List (Atom × List Goal) → List (Atom × List Goal)
  | [] => []
  | (tmpl, goals) :: rest =>
      (tmpl, lowerProfileGoals isDefined isBin goals) ::
        lowerProfileBranches isDefined isBin rest

end


def specializeClauseProfile (isDefined isBin : String → Bool)
    (binding : Subst) (clause : Clause) : Clause :=
  { params := clause.params.map (Metta.Subst.apply binding)
    result := Metta.Subst.apply binding clause.result
    body := lowerProfileGoals isDefined isBin
      (instantiateGoals binding clause.body) }

/-! ## Guarded executable normal form -/

/-- Pure, effect-free guards that make a specialization binding explicit in
    the executable clause.  They are always a strict body prefix, so a call
    inconsistent with the native-concrete visible head fails before any
    observable operation. -/
def specializationGuards (binding : Subst) : List Goal :=
  binding.map (fun entry => Goal.eq entry.2 (Atom.var entry.1))

mutual

/-- Decide a dynamic callable head using the specialization binding while
    preserving every non-head atom verbatim.  This proof-oriented IR form is
    observationally the native eager substitution: generic clause-head
    resolution remains unchanged, the binding guards enforce the concrete
    call, and only the dispatch constructor is shortened. -/
def specializeCallableHeadGoal (isDefined isBin : String → Bool)
    (binding : Subst) : Goal → Goal
  | .callDyn head args res =>
      match Metta.Subst.apply binding head with
      | Atom.sym f =>
          if isDefined f then .call f args res
          else if isBin f then .bin f args res
          else .callDyn head args res
      | concrete =>
          match partialHeadView? concrete with
          | some (base, bound) =>
              if isDefined base then .call base (bound ++ args) res
              else if isBin base then .bin base (bound ++ args) res
              else .callDyn head args res
          | none => .callDyn head args res
  | .catchg tmpl sub res =>
      .catchg tmpl (specializeCallableHeadGoals isDefined isBin binding sub) res
  | .softcut tmpl sub thn els =>
      .softcut tmpl
        (specializeCallableHeadGoals isDefined isBin binding sub)
        (specializeCallableHeadGoals isDefined isBin binding thn)
        (specializeCallableHeadGoals isDefined isBin binding els)
  | .findall tmpl sub res =>
      .findall tmpl (specializeCallableHeadGoals isDefined isBin binding sub) res
  | .onceg tmpl sub res =>
      .onceg tmpl (specializeCallableHeadGoals isDefined isBin binding sub) res
  | .transactiong tmpl sub =>
      .transactiong tmpl
        (specializeCallableHeadGoals isDefined isBin binding sub)
  | .amb branches res =>
      .amb (specializeCallableHeadBranches isDefined isBin binding branches) res
  | .ite cond thn els res =>
      .ite cond
        (thn.1, specializeCallableHeadGoals isDefined isBin binding thn.2)
        (els.1, specializeCallableHeadGoals isDefined isBin binding els.2) res
  | goal => goal

def specializeCallableHeadGoals (isDefined isBin : String → Bool)
    (binding : Subst) : List Goal → List Goal
  | [] => []
  | goal :: rest =>
      specializeCallableHeadGoal isDefined isBin binding goal ::
        specializeCallableHeadGoals isDefined isBin binding rest

def specializeCallableHeadBranches (isDefined isBin : String → Bool)
    (binding : Subst) : List (Atom × List Goal) → List (Atom × List Goal)
  | [] => []
  | (tmpl, goals) :: rest =>
      (tmpl, specializeCallableHeadGoals isDefined isBin binding goals) ::
        specializeCallableHeadBranches isDefined isBin binding rest

end

/-- Executable specialization normal form.  The generic head and all payload
    atoms are retained exactly; concrete binding is represented by a pure
    guard prefix, followed by callable-head lowering only. -/
def specializeClauseGuarded (isDefined isBin : String → Bool)
    (binding : Subst) (clause : Clause) : Clause :=
  { params := clause.params
    result := clause.result
    body := specializationGuards binding ++
      specializeCallableHeadGoals isDefined isBin binding clause.body }

/-! ## Proof-facing validation of installed rewrites -/

/-- Reflexive structural equality used only by the provenance checker.
    Runtime `BEq Atom` deliberately follows IEEE equality and is therefore
    false on NaN; provenance instead compares float payload bits so an
    unchanged goal is always recognized as unchanged. -/
def proofGroundEq : Metta.Ground → Metta.Ground → Bool
  | .int x, .int y => x == y
  | .float x, .float y => x.toBits == y.toBits
  | .str x, .str y => x == y
  | .bool x, .bool y => x == y
  | .unit, .unit => true
  | .error x, .error y => x == y
  | .external tx px, .external ty py => tx == ty && px == py
  | _, _ => false

mutual

def proofAtomEq : Atom → Atom → Bool
  | .sym x, .sym y => x == y
  | .var x, .var y => x == y
  | .gnd x, .gnd y => proofGroundEq x y
  | .expr xs, .expr ys => proofAtomsEq xs ys
  | _, _ => false

def proofAtomsEq : List Atom → List Atom → Bool
  | [], [] => true
  | x :: xs, y :: ys => proofAtomEq x y && proofAtomsEq xs ys
  | _, _ => false

end


mutual

def proofGoalEq : Goal → Goal → Bool
  | .call f args res, .call g args' res' =>
      f == g && proofAtomsEq args args' && proofAtomEq res res'
  | .bin f args res, .bin g args' res' =>
      f == g && proofAtomsEq args args' && proofAtomEq res res'
  | .callDyn head args res, .callDyn head' args' res' =>
      proofAtomEq head head' && proofAtomsEq args args' && proofAtomEq res res'
  | .evalg val res, .evalg val' res' =>
      proofAtomEq val val' && proofAtomEq res res'
  | .catchg tmpl sub res, .catchg tmpl' sub' res' =>
      proofAtomEq tmpl tmpl' && proofGoalsEq sub sub' && proofAtomEq res res'
  | .softcut tmpl sub thn els, .softcut tmpl' sub' thn' els' =>
      proofAtomEq tmpl tmpl' && proofGoalsEq sub sub' &&
        proofGoalsEq thn thn' && proofGoalsEq els els'
  | .eq a b, .eq a' b' => proofAtomEq a a' && proofAtomEq b b'
  | .compileAlias a b, .compileAlias a' b' =>
      proofAtomEq a a' && proofAtomEq b b'
  | .cut, .cut => true
  | .cutAt n, .cutAt m => n == m
  | .findall tmpl sub res, .findall tmpl' sub' res'
  | .onceg tmpl sub res, .onceg tmpl' sub' res' =>
      proofAtomEq tmpl tmpl' && proofGoalsEq sub sub' && proofAtomEq res res'
  | .transactiong tmpl sub, .transactiong tmpl' sub' =>
      proofAtomEq tmpl tmpl' && proofGoalsEq sub sub'
  | .amb branches res, .amb branches' res' =>
      proofBranchesEq branches branches' && proofAtomEq res res'
  | .spread val res, .spread val' res' =>
      proofAtomEq val val' && proofAtomEq res res'
  | .ite cond thn els res, .ite cond' thn' els' res' =>
      proofAtomEq cond cond' && proofAtomEq thn.1 thn'.1 &&
        proofGoalsEq thn.2 thn'.2 && proofAtomEq els.1 els'.1 &&
        proofGoalsEq els.2 els'.2 && proofAtomEq res res'
  | .smatch pat, .smatch pat' => proofAtomEq pat pat'
  | .wact op args res, .wact op' args' res' =>
      op == op' && proofAtomsEq args args' && proofAtomEq res res'
  | _, _ => false

def proofGoalsEq : List Goal → List Goal → Bool
  | [], [] => true
  | goal :: rest, goal' :: rest' =>
      proofGoalEq goal goal' && proofGoalsEq rest rest'
  | _, _ => false

def proofBranchesEq : List (Atom × List Goal) →
    List (Atom × List Goal) → Bool
  | [], [] => true
  | (tmpl, goals) :: rest, (tmpl', goals') :: rest' =>
      proofAtomEq tmpl tmpl' && proofGoalsEq goals goals' &&
        proofBranchesEq rest rest'
  | _, _ => false

end

def proofClauseEq (left right : Clause) : Bool :=
  proofAtomsEq left.params right.params &&
    proofAtomEq left.result right.result && proofGoalsEq left.body right.body

def proofClausesEq : List Clause → List Clause → Bool
  | [], [] => true
  | clause :: rest, clause' :: rest' =>
      proofClauseEq clause clause' && proofClausesEq rest rest'
  | _, _ => false

/-! ## Static support for recursive child specializations -/

mutual

/-- Whether a clause-head atom contains the named specialization variable.
    Specialization variables remain ordinary MeTTa variables at runtime. -/
def specializationVarOccurs (name : String) : Atom → Bool
  | .var other => other == name
  | .expr atoms => specializationVarOccursList name atoms
  | _ => false

def specializationVarOccursList (name : String) : List Atom → Bool
  | [] => false
  | atom :: rest =>
      specializationVarOccurs name atom ||
        specializationVarOccursList name rest

end


mutual

/-- Check every occurrence of one selected formal variable against the
    corresponding static actual.  A shape mismatch is irrelevant when the
    selected variable does not occur below it: ordinary clause-head matching
    will reject that clause independently. -/
def specializationEntryAgrees (name : String) (value : Atom) :
    Atom → Atom → Bool
  | .var other, actual =>
      if other == name then Metta.Atom.equiv value actual else true
  | .expr formals, .expr actuals =>
      if formals.length == actuals.length then
        specializationEntryAgreesList name value formals actuals
      else !specializationVarOccursList name formals
  | formal, _ => !specializationVarOccurs name formal

def specializationEntryAgreesList (name : String) (value : Atom) :
    List Atom → List Atom → Bool
  | [], [] => true
  | formal :: formals, actual :: actuals =>
      specializationEntryAgrees name value formal actual &&
        specializationEntryAgreesList name value formals actuals
  | formals, _ => !specializationVarOccursList name formals

end

/- Exact proof-facing counterpart of `specializationEntryAgrees`.  Selected
    formals must retain the literal call-site atom, so numeric runtime
    equivalence (`1` versus `1.0`) cannot masquerade as alpha-copy origin. -/
mutual

def specializationEntryExactlyAgrees (name : String) (value : Atom) :
    Atom → Atom → Bool
  | .var other, actual =>
      if other == name then proofAtomEq value actual else true
  | .expr formals, .expr actuals =>
      if formals.length == actuals.length then
        specializationEntryExactlyAgreesList name value formals actuals
      else !specializationVarOccursList name formals
  | formal, _ => !specializationVarOccurs name formal

def specializationEntryExactlyAgreesList (name : String) (value : Atom) :
    List Atom → List Atom → Bool
  | [], [] => true
  | formal :: formals, actual :: actuals =>
      specializationEntryExactlyAgrees name value formal actual &&
        specializationEntryExactlyAgreesList name value formals actuals
  | formals, _ => !specializationVarOccursList name formals

end

/-- Exact constructional alignment retained by a discovered source binding.
    Empty bindings are vacuous sibling clauses and remain governed by normal
    clause-head resolution. -/
def specializationSourceBindingExact (binding : Subst)
    (formals actuals : List Atom) : Bool :=
  binding.isEmpty ||
    (formals.length == actuals.length &&
      binding.all (fun entry =>
        formals.any (specializationVarOccurs entry.1) &&
          specializationEntryExactlyAgreesList entry.1 entry.2
            formals actuals))


/-- A discovered binding is supported by this exact call site when applying
    it to the complete parent head produces one pattern that unifies with the
    complete actual tuple.  Checking the tuple in one unification preserves
    sharing between residual variables in different arguments. -/
def specializationBindingSupported (binding : Subst)
    (formals actuals : List Atom) : Bool :=
  binding.isEmpty ||
    (formals.length == actuals.length &&
      binding.all (fun entry =>
        formals.any (specializationVarOccurs entry.1)) &&
      (Metta.Unify.unifyTop
        (Atom.expr (formals.map (Metta.Subst.apply binding)))
        (Atom.expr actuals)).isSome)

/-- Every generated guard must be reflexive under the runtime unifier.  IEEE
    NaN is intentionally non-reflexive there; a partial value containing NaN
    therefore stays on the generic correctness path. -/
def specializationBindingRuntimeSafe (binding : Subst) : Bool :=
  binding.all (fun entry => Metta.Atom.equiv entry.2 entry.2)

mutual

/-- Decidable, predicate-independent envelope of callable-head lowering.
    It permits exactly the generic goal or the direct function/builtin form
    selected from the binding-applied head, while requiring every payload
    atom and nested constructor to remain unchanged. -/
def callableHeadRewriteValid (binding : Subst) : Goal → Goal → Bool
  | .callDyn head args res, rewritten =>
      let same := proofGoalEq rewritten (Goal.callDyn head args res)
      match Metta.Subst.apply binding head with
      | Atom.sym f =>
          same || proofGoalEq rewritten (Goal.call f args res) ||
            proofGoalEq rewritten (Goal.bin f args res)
      | concrete =>
          match partialHeadView? concrete with
          | some (base, bound) =>
              same || proofGoalEq rewritten (Goal.call base (bound ++ args) res) ||
                proofGoalEq rewritten (Goal.bin base (bound ++ args) res)
          | none => same
  | .catchg tmpl sub res, .catchg tmpl' sub' res' =>
      proofAtomEq tmpl tmpl' && proofAtomEq res res' &&
        callableHeadsRewriteValid binding sub sub'
  | .softcut tmpl sub thn els, .softcut tmpl' sub' thn' els' =>
      proofAtomEq tmpl tmpl' && callableHeadsRewriteValid binding sub sub' &&
        callableHeadsRewriteValid binding thn thn' &&
        callableHeadsRewriteValid binding els els'
  | .findall tmpl sub res, .findall tmpl' sub' res'
  | .onceg tmpl sub res, .onceg tmpl' sub' res' =>
      proofAtomEq tmpl tmpl' && proofAtomEq res res' &&
        callableHeadsRewriteValid binding sub sub'
  | .transactiong tmpl sub, .transactiong tmpl' sub' =>
      proofAtomEq tmpl tmpl' && callableHeadsRewriteValid binding sub sub'
  | .amb branches res, .amb branches' res' =>
      proofAtomEq res res' &&
        callableHeadBranchesRewriteValid binding branches branches'
  | .ite cond thn els res, .ite cond' thn' els' res' =>
      proofAtomEq cond cond' && proofAtomEq thn.1 thn'.1 &&
        proofAtomEq els.1 els'.1 && proofAtomEq res res' &&
        callableHeadsRewriteValid binding thn.2 thn'.2 &&
        callableHeadsRewriteValid binding els.2 els'.2
  | original, rewritten => proofGoalEq original rewritten

def callableHeadsRewriteValid (binding : Subst) : List Goal → List Goal → Bool
  | [], [] => true
  | goal :: rest, rewritten :: rewrittenRest =>
      callableHeadRewriteValid binding goal rewritten &&
        callableHeadsRewriteValid binding rest rewrittenRest
  | _, _ => false

def callableHeadBranchesRewriteValid (binding : Subst) :
    List (Atom × List Goal) → List (Atom × List Goal) → Bool
  | [], [] => true
  | (tmpl, goals) :: rest, (tmpl', rewritten) :: rewrittenRest =>
      proofAtomEq tmpl tmpl' &&
        callableHeadsRewriteValid binding goals rewritten &&
        callableHeadBranchesRewriteValid binding rest rewrittenRest
  | _, _ => false

end

/-- Check the exact guarded-clause envelope independently of the lowering
    predicates: identical head, exact pure guard prefix, and only permitted
    callable-head rewrites in the remaining body. -/
def guardedClauseShapeValid (binding : Subst) (parent guarded : Clause) :
    Bool :=
  proofAtomsEq guarded.params parent.params &&
    proofAtomEq guarded.result parent.result &&
    proofGoalsEq (guarded.body.take binding.length)
      (specializationGuards binding) &&
    callableHeadsRewriteValid binding parent.body
      (guarded.body.drop binding.length)

private def registeredChildRewrite (records : List SpecRecord)
    (parent child : String) : Bool :=
  parent == child || records.any (fun record =>
    record.name == child && record.key.parent == parent)

mutual

/-- Exact validation of the second profile layer: only an ordinary direct
    call may be retargeted to a registered specialization of that same
    parent; every argument, result, and nested payload is retained. -/
def childCallRewriteValid (records : List SpecRecord) : Goal → Goal → Bool
  | .call parent args res, .call child args' res' =>
      proofAtomsEq args args' && proofAtomEq res res' &&
        registeredChildRewrite records parent child
  | .catchg tmpl sub res, .catchg tmpl' sub' res' =>
      proofAtomEq tmpl tmpl' && proofAtomEq res res' &&
        childCallsRewriteValid records sub sub'
  | .softcut tmpl sub thn els, .softcut tmpl' sub' thn' els' =>
      proofAtomEq tmpl tmpl' && childCallsRewriteValid records sub sub' &&
        childCallsRewriteValid records thn thn' &&
        childCallsRewriteValid records els els'
  | .findall tmpl sub res, .findall tmpl' sub' res'
  | .onceg tmpl sub res, .onceg tmpl' sub' res' =>
      proofAtomEq tmpl tmpl' && proofAtomEq res res' &&
        childCallsRewriteValid records sub sub'
  | .transactiong tmpl sub, .transactiong tmpl' sub' =>
      proofAtomEq tmpl tmpl' && childCallsRewriteValid records sub sub'
  | .amb branches res, .amb branches' res' =>
      proofAtomEq res res' &&
        childCallBranchesRewriteValid records branches branches'
  | .ite cond thn els res, .ite cond' thn' els' res' =>
      proofAtomEq cond cond' && proofAtomEq thn.1 thn'.1 &&
        proofAtomEq els.1 els'.1 && proofAtomEq res res' &&
        childCallsRewriteValid records thn.2 thn'.2 &&
        childCallsRewriteValid records els.2 els'.2
  | original, rewritten => proofGoalEq original rewritten

def childCallsRewriteValid (records : List SpecRecord) :
    List Goal → List Goal → Bool
  | [], [] => true
  | goal :: rest, rewritten :: rewrittenRest =>
      childCallRewriteValid records goal rewritten &&
        childCallsRewriteValid records rest rewrittenRest
  | _, _ => false

def childCallBranchesRewriteValid (records : List SpecRecord) :
    List (Atom × List Goal) → List (Atom × List Goal) → Bool
  | [], [] => true
  | (tmpl, goals) :: rest, (tmpl', rewritten) :: rewrittenRest =>
      proofAtomEq tmpl tmpl' &&
        childCallsRewriteValid records goals rewritten &&
        childCallBranchesRewriteValid records rest rewrittenRest
  | _, _ => false

end

/-! ## Structural discovery and stable public names -/

/-- The internal representation of PeTTa's `partial(Base, Bound)` value. -/
def specPartialView? (a : Atom) : Option (String × List Atom) :=
  partialHeadView? a

/-- Replace residual variables as native `replace_vars_with_var` does before
    constructing the stable specialization name [SPEC specializer.pl:8-11]. -/
def cleanSpecAtom : Atom → Atom
  | Atom.var _ => Atom.sym "VAR"
  | Atom.expr xs => Atom.expr (xs.map cleanSpecAtom)
  | a => a

private def renderSpecAtomFuel : Nat → Atom → String
  | 0, a => Metta.Pretty.atom a
  | _ + 1, Atom.var _ => "VAR"
  | fuel + 1, Atom.expr
      [Atom.sym "partial", Atom.sym base, Atom.expr bound] =>
      s!"partial({base},[{String.intercalate "," (bound.map
        (renderSpecAtomFuel fuel))}])"
  | fuel + 1, Atom.expr xs =>
      s!"[{String.intercalate "," (xs.map (renderSpecAtomFuel fuel))}]"
  | _, a => Metta.Pretty.atom a

/-- Canonical PeTTa/Prolog rendering used only for the public function name;
    registry identity remains the structural `SpecKey`. -/
def renderSpecBinding (a : Atom) : String :=
  renderSpecAtomFuel 1000 (unchainify 1000 (cleanSpecAtom a))

def specializationName (key : SpecKey) : String :=
  s!"{key.parent}_Spec_[{String.intercalate ","
    (key.bindings.map renderSpecBinding)}]"

/-- A function symbol or partial application that native PeTTa may use as a
    concrete higher-order specialization value [SPEC specializer.pl:90-92]. -/
def specializableValue (isDefined : String → Bool) (a : Atom) : Bool :=
  match a with
  | Atom.sym f => isDefined f
  | other =>
      match specPartialView? other with
      | some (base, _) => isDefined base
      | none => false

/-- A specialization binding depends on a function when the bound callable
    value is that function or a partial application rooted at it.  This edge
    remains relevant even when lowering chose the builtin constructor, which
    carries no ordinary `.call` edge for invalidation to discover. -/
def specializationValueDependsOn (parent : String) (a : Atom) : Bool :=
  match a with
  | Atom.sym f => f == parent
  | other =>
      match specPartialView? other with
      | some (base, _) => base == parent
      | none => false

def specializationBindingDependsOn (binding : Subst) (parent : String) :
    Bool :=
  binding.any (fun entry => specializationValueDependsOn parent entry.2)

mutual

/-- Does `v` occur as a dynamic call head in this compiled goal? -/
def directHeadUseGoal (v : String) : Goal → Bool
  | .callDyn head _ _ => head == Atom.var v
  | .catchg _ sub _ => directHeadUseGoals v sub
  | .softcut _ sub thn els =>
      directHeadUseGoals v sub || directHeadUseGoals v thn ||
        directHeadUseGoals v els
  | .findall _ sub _ => directHeadUseGoals v sub
  | .onceg _ sub _ => directHeadUseGoals v sub
  | .transactiong _ sub => directHeadUseGoals v sub
  | .amb branches _ => directHeadUseBranches v branches
  | .ite _ thn els _ =>
      directHeadUseGoals v thn.2 || directHeadUseGoals v els.2
  | _ => false

def directHeadUseGoals (v : String) : List Goal → Bool
  | [] => false
  | g :: rest => directHeadUseGoal v g || directHeadUseGoals v rest

def directHeadUseBranches (v : String) : List (Atom × List Goal) → Bool
  | [] => false
  | (_, goals) :: rest =>
      directHeadUseGoals v goals || directHeadUseBranches v rest

end

mutual

/-- Does `v` flow into an ordinary function call that itself has captured
    source metadata and can therefore specialize recursively? -/
def propagatedUseGoal (hasMeta : String → Bool) (v : String) : Goal → Bool
  | .call f args _ =>
      (hasMeta f && args.any (fun a => a.vars.contains v))
  | .catchg _ sub _ => propagatedUseGoals hasMeta v sub
  | .softcut _ sub thn els =>
      propagatedUseGoals hasMeta v sub || propagatedUseGoals hasMeta v thn ||
        propagatedUseGoals hasMeta v els
  | .findall _ sub _ => propagatedUseGoals hasMeta v sub
  | .onceg _ sub _ => propagatedUseGoals hasMeta v sub
  | .transactiong _ sub => propagatedUseGoals hasMeta v sub
  | .amb branches _ => propagatedUseBranches hasMeta v branches
  | .ite _ thn els _ =>
      propagatedUseGoals hasMeta v thn.2 ||
        propagatedUseGoals hasMeta v els.2
  | _ => false

def propagatedUseGoals (hasMeta : String → Bool) (v : String) :
    List Goal → Bool
  | [] => false
  | g :: rest =>
      propagatedUseGoal hasMeta v g || propagatedUseGoals hasMeta v rest

def propagatedUseBranches (hasMeta : String → Bool) (v : String) :
    List (Atom × List Goal) → Bool
  | [] => false
  | (_, goals) :: rest =>
      propagatedUseGoals hasMeta v goals ||
        propagatedUseBranches hasMeta v rest

end

def relevantSpecializationVar (hasMeta : String → Bool) (body : List Goal)
    (v : String) : Bool :=
  directHeadUseGoals v body || propagatedUseGoals hasMeta v body

mutual

/-- A dynamic head that the current base rewrite will turn into a direct call. -/
def concreteDynamicUseGoal (isDefined : String → Bool) : Goal → Bool
  | .callDyn (Atom.sym f) _ _ => isDefined f
  | .catchg _ sub _ => concreteDynamicUseGoals isDefined sub
  | .softcut _ sub thn els =>
      concreteDynamicUseGoals isDefined sub ||
        concreteDynamicUseGoals isDefined thn ||
        concreteDynamicUseGoals isDefined els
  | .findall _ sub _ => concreteDynamicUseGoals isDefined sub
  | .onceg _ sub _ => concreteDynamicUseGoals isDefined sub
  | .transactiong _ sub => concreteDynamicUseGoals isDefined sub
  | .amb branches _ => concreteDynamicUseBranches isDefined branches
  | .ite _ thn els _ =>
      concreteDynamicUseGoals isDefined thn.2 ||
        concreteDynamicUseGoals isDefined els.2
  | _ => false

def concreteDynamicUseGoals (isDefined : String → Bool) : List Goal → Bool
  | [] => false
  | g :: rest =>
      concreteDynamicUseGoal isDefined g ||
        concreteDynamicUseGoals isDefined rest

def concreteDynamicUseBranches (isDefined : String → Bool) :
    List (Atom × List Goal) → Bool
  | [] => false
  | (_, goals) :: rest =>
      concreteDynamicUseGoals isDefined goals ||
        concreteDynamicUseBranches isDefined rest

end

mutual

def profileDynamicUseGoal (isDefined isBin : String → Bool) : Goal → Bool
  | .callDyn head _ _ =>
      match head with
      | Atom.sym f => isDefined f || isBin f
      | other =>
          match partialHeadView? other with
          | some (base, _) => isDefined base || isBin base
          | none => false
  | .catchg _ sub _ => profileDynamicUseGoals isDefined isBin sub
  | .softcut _ sub thn els =>
      profileDynamicUseGoals isDefined isBin sub ||
        profileDynamicUseGoals isDefined isBin thn ||
        profileDynamicUseGoals isDefined isBin els
  | .findall _ sub _ => profileDynamicUseGoals isDefined isBin sub
  | .onceg _ sub _ => profileDynamicUseGoals isDefined isBin sub
  | .transactiong _ sub => profileDynamicUseGoals isDefined isBin sub
  | .amb branches _ => profileDynamicUseBranches isDefined isBin branches
  | .ite _ thn els _ =>
      profileDynamicUseGoals isDefined isBin thn.2 ||
        profileDynamicUseGoals isDefined isBin els.2
  | _ => false

def profileDynamicUseGoals (isDefined isBin : String → Bool) :
    List Goal → Bool
  | [] => false
  | goal :: rest =>
      profileDynamicUseGoal isDefined isBin goal ||
        profileDynamicUseGoals isDefined isBin rest

def profileDynamicUseBranches (isDefined isBin : String → Bool) :
    List (Atom × List Goal) → Bool
  | [] => false
  | (_, goals) :: rest =>
      profileDynamicUseGoals isDefined isBin goals ||
        profileDynamicUseBranches isDefined isBin rest

end

/-- Internal state of structural specialization discovery.  Kept public so
    the constructional proof can follow the executable alignment rather than
    inverting a Boolean equality check. -/
structure Alignment where
  binding : Subst := []
  values : List Atom := []
  compatible : Bool := true

def Alignment.add (st : Alignment) (v : String) (actual : Atom) :
    Alignment :=
  match Metta.Subst.lookup st.binding v with
  | some prior => { st with compatible := st.compatible && prior == actual }
  | none =>
      { st with binding := st.binding ++ [(v, actual)]
                values := st.values ++ [cleanSpecAtom actual] }

mutual

/-- All variables occurring in a compiled goal, including nested goals. -/
def specializationGoalVars : Goal → List String
  | .call _ args res | .bin _ args res | .wact _ args res =>
      args.flatMap Atom.vars ++ res.vars
  | .callDyn head args res =>
      head.vars ++ args.flatMap Atom.vars ++ res.vars
  | .evalg val res | .spread val res => val.vars ++ res.vars
  | .catchg tmpl sub res | .findall tmpl sub res | .onceg tmpl sub res =>
      tmpl.vars ++ specializationGoalsVars sub ++ res.vars
  | .softcut tmpl sub thn els =>
      tmpl.vars ++ specializationGoalsVars sub ++
        specializationGoalsVars thn ++ specializationGoalsVars els
  | .eq left right | .compileAlias left right => left.vars ++ right.vars
  | .cut | .cutAt _ => []
  | .transactiong tmpl sub => tmpl.vars ++ specializationGoalsVars sub
  | .amb branches res => specializationBranchVars branches ++ res.vars
  | .ite cond thn els res =>
      cond.vars ++ thn.1.vars ++ specializationGoalsVars thn.2 ++
        els.1.vars ++ specializationGoalsVars els.2 ++ res.vars
  | .smatch pat => pat.vars

/-- All variables occurring in a compiled goal sequence. -/
def specializationGoalsVars : List Goal → List String
  | [] => []
  | goal :: rest =>
      specializationGoalVars goal ++ specializationGoalsVars rest

/-- All variables occurring in nondeterministic compiled branches. -/
def specializationBranchVars : List (Atom × List Goal) → List String
  | [] => []
  | (tmpl, goals) :: rest =>
      tmpl.vars ++ specializationGoalsVars goals ++
        specializationBranchVars rest

end

/-- Every variable in a compiled clause, including compiler temporaries and
    variables nested under control-flow goals. -/
def specializationClauseVars (clause : Clause) : List String :=
  (clause.params.flatMap Atom.vars ++ clause.result.vars ++
    specializationGoalsVars clause.body).eraseDups

/-- Deterministically allocate names longer than every occupied name.  This
    makes freshness independent of reserved-prefix conventions. -/
def residualFreshName : Nat → String
  | 0 => ""
  | length + 1 => "_" ++ residualFreshName length

def residualFreshNames : Nat → Nat → List String → Subst
  | _, _, [] => []
  | maxLength, index, source :: rest =>
      (source, Atom.var (residualFreshName (maxLength + index + 1))) ::
        residualFreshNames maxLength (index + 1) rest

/-- Residual variables shared by the complete discovered binding. -/
def specializationResiduals (binding : Subst) : List String :=
  (binding.flatMap (fun entry => entry.2.vars)).eraseDups

/-- The one shared alpha-renaming used at PeTTa's clause-copy boundary. -/
def specializationCopySubst (clause : Clause) (binding : Subst) : Subst :=
  let residuals := specializationResiduals binding
  let occupied := specializationClauseVars clause ++ residuals
  let maxLength := occupied.foldl
    (fun current name => max current name.length) 0
  residualFreshNames maxLength 0 residuals

/-- PeTTa's `copy_term` boundary for a generated clause: alpha-copy every
    residual call-site variable in one pass, preserving sharing, and choose
    targets fresh from the complete compiled callee clause. -/
def freshenSpecializationBinding (clause : Clause) (binding : Subst) : Subst :=
  binding.map (fun entry =>
    (entry.1, Metta.Subst.apply
      (specializationCopySubst clause binding) entry.2))

/-- Structurally align one formal parameter with its call-site value.  A
    repeated formal variable must align with the same value; constants and
    expression shapes retain the generic clause when they do not match. -/
def alignSpecializable (isDefined : String → Bool)
    (relevant : String → Bool) : Nat → Atom → Atom → Alignment → Alignment
  | 0, _, _, st => st
  | _ + 1, Atom.var v, actual, st =>
      if relevant v && specializableValue isDefined actual
      then st.add v actual
      else st
  | _ + 1, Atom.sym f, Atom.sym g, st =>
      { st with compatible := st.compatible && f == g }
  | _ + 1, Atom.gnd x, Atom.gnd y, st =>
      { st with compatible := st.compatible && Atom.gnd x == Atom.gnd y }
  | fuel + 1, Atom.expr fs, Atom.expr actuals, st =>
      if fs.length == actuals.length then
        (fs.zip actuals).foldl
          (fun acc pair =>
            alignSpecializable isDefined relevant fuel pair.1 pair.2 acc) st
      else { st with compatible := false }
  | _ + 1, _, _, st => { st with compatible := false }

structure SpecClauseCandidate where
  captured : MetaClause
  /-- Alignment before residual variables are clause-locally alpha-copied. -/
  sourceBinding : Subst := []
  /-- Exact static actual tuple used for this discovery. -/
  discoveryActuals : List Atom := []
deriving Repr, Inhabited, BEq

/-- The executable binding is definitionally the clause-local alpha-copy of
    the retained discovery binding; malformed candidates cannot separate the
    two views. -/
def SpecClauseCandidate.binding (candidate : SpecClauseCandidate) : Subst :=
  freshenSpecializationBinding candidate.captured.compiled
    candidate.sourceBinding

/-- Admission condition for one discovered clause: its generated guards are
    runtime-reflexive and the retained discovery tuple supports the complete
    guarded parent head. -/
def SpecClauseCandidate.safe (candidate : SpecClauseCandidate) : Bool :=
  specializationBindingRuntimeSafe candidate.binding &&
    specializationSourceBindingExact candidate.sourceBinding
      candidate.captured.compiled.params candidate.discoveryActuals &&
    specializationBindingSupported candidate.binding
      candidate.captured.compiled.params candidate.discoveryActuals

structure SpecCandidate where
  key : SpecKey
  clauses : List SpecClauseCandidate
deriving Repr, Inhabited, BEq

/-- Clause-local alignment used by whole-family discovery.  Kept public so
    the constructional proof can relate candidate order back to captured
    metadata without reimplementing the algorithm. -/
def discoverClause (isDefined hasMeta : String → Bool)
    (actuals : List Atom) (captured : MetaClause) :
    SpecClauseCandidate × List Atom :=
  let relevant := relevantSpecializationVar hasMeta captured.compiled.body
  let aligned :=
    if captured.compiled.params.length == actuals.length then
      (captured.compiled.params.zip actuals).foldl
        (fun st pair =>
          alignSpecializable isDefined relevant (pair.1.size + 1)
            pair.1 pair.2 st) {}
    else { compatible := false : Alignment }
  if aligned.compatible then
    ({ captured := captured
       sourceBinding := aligned.binding
       discoveryActuals := actuals },
      aligned.values)
  else ({ captured := captured
          sourceBinding := []
          discoveryActuals := actuals }, [])

/-- Discover a specialization structurally across every captured parent
    clause in native newest-first metadata order.  `none` is the exact generic
    fallback: no higher-order binding was relevant and concrete. -/
def discoverSpecialization (isDefined hasMeta : String → Bool)
    (parent : String) (actuals : List Atom) (captured : List MetaClause) :
    Option SpecCandidate :=
  let parentClauses := captured.filter (fun mc => mc.parent == parent)
  let found := parentClauses.map (discoverClause isDefined hasMeta actuals)
  let values := found.flatMap (·.2)
  if values.isEmpty then none
  else some
    { key := { parent, bindings := values }
      clauses := found.map (·.1) }

end PLeaTTa
