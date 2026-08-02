-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologGoalControlCarryBridge
Purpose: Record every exact post-substitution soft-cut control packet,
  separately from the stronger type-check closure law
Trusted boundary: none
Main exports: MaterializedSoftCutControl,
  materializedSoftCutControlsGoals, MaterializedControlAgrees,
  CanonicalTypeCheckClosure
-/
import PLeaTTa.Proofs.PrologGoalTermForestBridge

namespace PLeaTTa.PrologGoalControlCarryBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.OpenSubstitution
open PrologFindallBagAlphaBridge
open PrologGoalTermForestBridge
open PrologOrdinaryStepBridge
open PrologRecursiveCallPayloadBridge

/-!
The compiler-generated type-check soft-cut contains executable control fields
which have no independent source-term peer.  Applying a runtime substitution
to those already-emitted atoms is not the same as recomputing them from the
substituted raw expected atom.  The counterexamples in
`CompilerSubstitutionAdequacy` make both failures observable.

Two claims must consequently stay separate:

* `materializedSoftCutControlsGoals` records exactly what the executable
  emits.  It traverses executable syntax directly, records every soft-cut,
  and never moves substitution through `chainify` or
  `typeCheckBindingTemplate`.  Because it is a function of syntax rather than
  an agreement proof, overlapping `AlphaGoalAgrees` constructors cannot omit
  or replace a control packet.
* `CanonicalTypeCheckClosure` is the stronger representation law needed to
  reconstruct the old post-substitution type-check agreement.  Producers may
  establish it when their substitution discipline justifies reconstruction;
  exact-emission adequacy never assumes it.

The traversal is ordered and duplicate-sensitive.  A parent soft-cut appears
before its nested controls, and every nested goal list is visited left to
right.
-/

/-- One complete soft-cut packet before and after the executable's current
substitution.  Storing whole ordered branches makes omission of a hidden
template or repeated expected-value occurrence structurally impossible. -/
structure MaterializedSoftCutControl where
  beforeTemplate : Atom
  beforeCondition : List PLeaTTa.Goal
  beforeThen : List PLeaTTa.Goal
  beforeElse : List PLeaTTa.Goal
  afterTemplate : Atom
  afterCondition : List PLeaTTa.Goal
  afterThen : List PLeaTTa.Goal
  afterElse : List PLeaTTa.Goal
deriving Repr

namespace MaterializedSoftCutControl

/-- Exact bounded materialization of one already-emitted soft-cut packet. -/
def ofEmitted (runtime : Subst) (template : Atom)
    (condition thenGoals elseGoals : List PLeaTTa.Goal) :
    MaterializedSoftCutControl :=
  { beforeTemplate := template
    beforeCondition := condition
    beforeThen := thenGoals
    beforeElse := elseGoals
    afterTemplate := PLeaTTa.subst runtime template
    afterCondition := PLeaTTa.substCompiledGoals runtime condition
    afterThen := PLeaTTa.substCompiledGoals runtime thenGoals
    afterElse := PLeaTTa.substCompiledGoals runtime elseGoals }

end MaterializedSoftCutControl

mutual

/-- Preorder traversal of every soft-cut control packet in one executable
goal.  Non-control term fields stay in the separately certified term forest. -/
def materializedSoftCutControlsGoal (runtime : Subst) :
    PLeaTTa.Goal → List MaterializedSoftCutControl
  | .catchg _ goals _ => materializedSoftCutControlsGoals runtime goals
  | .catchExit _ _ => []
  | .softcut template condition thenGoals elseGoals =>
      MaterializedSoftCutControl.ofEmitted runtime template condition thenGoals
          elseGoals ::
        (materializedSoftCutControlsGoals runtime condition ++
          (materializedSoftCutControlsGoals runtime thenGoals ++
            materializedSoftCutControlsGoals runtime elseGoals))
  | .softcutExit _ => []
  | .findall _ goals _ => materializedSoftCutControlsGoals runtime goals
  | .onceg _ goals _ => materializedSoftCutControlsGoals runtime goals
  | .transactiong _ goals => materializedSoftCutControlsGoals runtime goals
  | .amb branches _ => materializedSoftCutControlsBranches runtime branches
  | .ite _ thenBranch elseBranch _ =>
      materializedSoftCutControlsGoals runtime thenBranch.2 ++
        materializedSoftCutControlsGoals runtime elseBranch.2
  | .call _ _ _ => []
  | .bin _ _ _ => []
  | .callDyn _ _ _ => []
  | .evalg _ _ => []
  | .eq _ _ => []
  | .compileAlias _ _ => []
  | .cut => []
  | .cutAt _ => []
  | .spread _ _ => []
  | .smatch _ => []
  | .wact _ _ _ => []

/-- Ordered traversal over an executable continuation. -/
def materializedSoftCutControlsGoals (runtime : Subst) :
    List PLeaTTa.Goal → List MaterializedSoftCutControl
  | [] => []
  | goal :: goals =>
      materializedSoftCutControlsGoal runtime goal ++
        materializedSoftCutControlsGoals runtime goals

/-- Ordered traversal over branch templates and their nested bodies. -/
def materializedSoftCutControlsBranches (runtime : Subst) :
    List (Atom × List PLeaTTa.Goal) → List MaterializedSoftCutControl
  | [] => []
  | branch :: branches =>
      materializedSoftCutControlsGoals runtime branch.2 ++
        materializedSoftCutControlsBranches runtime branches

end

@[simp] theorem materializedSoftCutControlsGoals_append
    (runtime : Subst) (left right : List PLeaTTa.Goal) :
    materializedSoftCutControlsGoals runtime (left ++ right) =
      materializedSoftCutControlsGoals runtime left ++
        materializedSoftCutControlsGoals runtime right := by
  induction left with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [materializedSoftCutControlsGoals, inductionHypothesis,
        List.append_assoc]

/-- The traversal is preorder and duplicate-sensitive: the enclosing packet
precedes nested packets, and condition/then/else remain left-to-right. -/
theorem nested_softcut_preorder_is_exact :
    let runtime : Subst := []
    let condition : List PLeaTTa.Goal :=
      [.softcut (.sym "condition") [] [] []]
    let thenGoals : List PLeaTTa.Goal :=
      [.softcut (.sym "then") [] [] []]
    let elseGoals : List PLeaTTa.Goal :=
      [.softcut (.sym "else") [] [] []]
    materializedSoftCutControlsGoals runtime
        [.softcut (.sym "parent") condition thenGoals elseGoals] =
      [MaterializedSoftCutControl.ofEmitted runtime (.sym "parent")
          condition thenGoals elseGoals,
       MaterializedSoftCutControl.ofEmitted runtime (.sym "condition")
          [] [] [],
       MaterializedSoftCutControl.ofEmitted runtime (.sym "then") [] [] [],
       MaterializedSoftCutControl.ofEmitted runtime (.sym "else") [] [] []] := by
  rfl

/-- Every current executable constructor containing nested goals participates
in the traversal.  The explicit nonrecursive constructor cases above ensure
that adding a future constructor cannot silently inherit an empty result. -/
theorem nested_control_containers_are_exhaustive :
    let runtime : Subst := []
    let control (name : String) : PLeaTTa.Goal :=
      .softcut (.sym name) [] [] []
    let packet (name : String) : MaterializedSoftCutControl :=
      MaterializedSoftCutControl.ofEmitted runtime (.sym name) [] [] []
    materializedSoftCutControlsGoals runtime
        [.catchg (.sym "catch-template") [control "catch"] (.sym "catch-result"),
         .findall (.sym "findall-template") [control "findall"]
           (.sym "findall-result"),
         .onceg (.sym "once-template") [control "once"] (.sym "once-result"),
         .transactiong (.sym "transaction-template") [control "transaction"],
         .amb [(.sym "branch", [control "amb"])] (.sym "amb-result"),
         .ite (.sym "condition")
           (.sym "then-template", [control "ite-then"])
           (.sym "else-template", [control "ite-else"])
           (.sym "ite-result")] =
      [packet "catch", packet "findall", packet "once", packet "transaction",
       packet "amb", packet "ite-then", packet "ite-else"] := by
  rfl

/-- Stronger canonical closure for one compiler type-check packet.  This is
the old specialized reconstruction obligation stated without conflating it
with the atoms actually executed. -/
def CanonicalTypeCheckClosure (runtime : Subst)
    (expected template : Atom) : Prop :=
  PLeaTTa.subst runtime template =
      typeCheckBindingTemplate (PLeaTTa.subst runtime expected) ∧
    PLeaTTa.subst runtime (chainify expected) =
      chainify (PLeaTTa.subst runtime expected)

/-- One existential owns the exact term forest and the deterministic control
traversal.  A client cannot replace the recorded controls by choosing another
proof of the intentionally overlapping goal-agreement relation. -/
def NormalizedAlphaGoalsAgree.ControlSupported
    {alpha : List (LogicVar × String)}
    (support : List (LogicVar × String)) (runtime : Subst)
    {barrier : Nat} {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement : NormalizedAlphaGoalsAgree alpha barrier references
      executables) : Prop :=
  ∃ (forest : AlphaTermForest alpha)
      (controls : List MaterializedSoftCutControl),
    NormalizedAlphaGoalsTermForest alpha barrier agreement forest ∧
      AlphaTermsSupported alpha support forest.references ∧
      controls = materializedSoftCutControlsGoals runtime executables

/-- Exact post-substitution continuation relation.  The goal-list equalities
identify the actual source and executable control, the shared runtime-alpha
certificate interprets every ordinary term leaf, and `controls` is definitionally
the complete traversal of the actual executable continuation.

Canonical type-check closure is deliberately not a field: it is a stronger
optional property and is false for some substitutions represented here. -/
def MaterializedControlAgrees
    {alpha : List (LogicVar × String)} (barrier : Nat)
    (current : PeTTaSpec.PrologCore.OpenSubstitution.Substitution)
    (runtime : Subst)
    (references : List PeTTaSpec.PrologCore.Goal)
    (executables : List PLeaTTa.Goal)
    (agreement : NormalizedAlphaGoalsAgree alpha barrier references
      executables)
    (materializedReferences : List PeTTaSpec.PrologCore.Goal)
    (materializedExecutables : List PLeaTTa.Goal) : Prop :=
  materializedReferences = current.applyGoals references ∧
    materializedExecutables = PLeaTTa.substCompiledGoals runtime executables ∧
    ∃ (forest : AlphaTermForest alpha)
        (controls : List MaterializedSoftCutControl)
        (referenceSupport : List LogicVar)
        (executableSupport : List String),
      NormalizedAlphaGoalsTermForest alpha barrier agreement forest ∧
        controls = materializedSoftCutControlsGoals runtime executables ∧
        RuntimeTermsAgreesWith referenceSupport executableSupport
          (current.applyTerms forest.references)
          (forest.executables.map (PLeaTTa.subst runtime))

/-- One frozen combined support packet materializes the exact source and
executable continuation without reconstructing generated control from its
post-substitution variables. -/
theorem TaskPayloadAgrees.materializeControl
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : PeTTaSpec.PrologCore.Canonical.TreeSubstitution}
    {referenceBase current :
      PeTTaSpec.PrologCore.OpenSubstitution.Substitution}
    {runtime : Subst}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (payload : TaskPayloadAgrees alpha support barrier canonical referenceBase
      current runtime references executables)
    (supported :
      NormalizedAlphaGoalsAgree.ControlSupported support runtime
        payload.control) :
    MaterializedControlAgrees barrier current runtime references executables
      payload.control (current.applyGoals references)
      (PLeaTTa.substCompiledGoals runtime executables) := by
  refine ⟨rfl, rfl, ?_⟩
  obtain ⟨forest, controls, forestRel, forestSupported, controlsExact⟩ :=
    supported
  obtain ⟨referenceSupport, executableSupport, materialized⟩ :=
    PLeaTTa.PrologResidualForestBridge.TaskDataAgrees.runtimeTermsAgreesWith
      payload.data forest.agreement forestSupported
  exact ⟨forest, controls, referenceSupport, executableSupport, forestRel,
    controlsExact, materialized⟩

/-! ## Anti-vacuity witnesses -/

/-- A real compiler-shaped type-check packet whose expected variable becomes
a compound is recorded exactly as one soft-cut packet.  The traversal does
not silently replace the executed atoms by a reconstructed packet. -/
theorem variable_to_compound_typecheck_is_recorded_exactly :
    let runtime : Subst := [("_q0", .expr [.sym "a"])]
    let expected : Atom := .var "_q0"
    let template := typeCheckBindingTemplate expected
    let condition : List PLeaTTa.Goal :=
      [.bin "get-type" [.gnd (.int 0)] (.gnd (.int 1)),
       .eq (.gnd (.int 1)) (chainify expected)]
    let otherwise : List PLeaTTa.Goal :=
      [.bin "get-metatype" [.gnd (.int 0)] (.gnd (.int 2)),
       .eq (.gnd (.int 2)) (chainify expected)]
    materializedSoftCutControlsGoals runtime
        [.softcut template condition [] otherwise] =
      [MaterializedSoftCutControl.ofEmitted runtime template condition []
        otherwise] := by
  intros
  rfl

/-- The compound-binding witness is outside canonical closure.  Exact
emission remains true, while the invalid `subst`/`chainify` reconstruction is
rejected explicitly. -/
theorem variable_to_compound_typecheck_is_not_closed :
    ¬ CanonicalTypeCheckClosure
      [("_q0", .expr [.sym "a"])] (.var "_q0")
        (typeCheckBindingTemplate (.var "_q0")) := by
  intro closed
  exact CompilerSubstitutionAdequacy.subst_chainify_counterexample closed.2

/-- A forged canonicalized packet is not the packet emitted for the compound
binding.  Acceptance of the non-closed execution therefore does not make
control values arbitrary. -/
theorem variable_to_compound_forged_control_is_rejected :
    let runtime : Subst := [("_q0", .expr [.sym "a"])]
    let expected : Atom := .var "_q0"
    let template := typeCheckBindingTemplate expected
    let condition : List PLeaTTa.Goal :=
      [.eq (.gnd (.int 1)) (chainify expected)]
    let emitted := MaterializedSoftCutControl.ofEmitted runtime template
      condition [] []
    let forged : MaterializedSoftCutControl :=
      { emitted with
        afterTemplate := typeCheckBindingTemplate
          (PLeaTTa.subst runtime expected)
        afterCondition :=
          [.eq (.gnd (.int 1))
            (chainify (PLeaTTa.subst runtime expected))] }
    emitted ≠ forged := by
  intro runtime expected template condition emitted forged equal
  simp only [emitted, forged, condition, template, expected, runtime,
    MaterializedSoftCutControl.ofEmitted] at equal
  have conditionEqual := congrArg MaterializedSoftCutControl.afterCondition
    equal
  simp only [PLeaTTa.substCompiledGoals,
    PLeaTTa.substCompiledGoal] at conditionEqual
  have goalEqual := (List.cons.inj conditionEqual).1
  exact CompilerSubstitutionAdequacy.subst_chainify_counterexample
    (PLeaTTa.Goal.eq.inj goalEqual).2

/-- Alias merge is another genuine failure of canonical closure, even though
the exact duplicated template is valid executable control. -/
theorem alias_merge_typecheck_is_not_closed :
    ¬ CanonicalTypeCheckClosure
      [("_q0", .var "_q1")]
      (.expr [.var "_q0", .var "_q1"])
      (typeCheckBindingTemplate (.expr [.var "_q0", .var "_q1"])) := by
  intro closed
  have templateClosed := closed.1
  simp [typeCheckBindingTemplate,
    bindingTemplate, Atom.vars, PLeaTTa.subst, PLeaTTa.substN,
    Metta.Subst.lookup, List.eraseDups_cons, chainOf, consC, nilA] at templateClosed

/-- Canonical closure has a non-vacuous open inhabitant: an injective
variable renaming preserves both generated fields. -/
theorem variable_renaming_typecheck_is_closed :
    CanonicalTypeCheckClosure [("_q0", .var "_q1")] (.var "_q0")
      (typeCheckBindingTemplate (.var "_q0")) := by
  simp [CanonicalTypeCheckClosure, typeCheckBindingTemplate,
    bindingTemplate, Atom.vars, PLeaTTa.subst, PLeaTTa.substN,
    Metta.Subst.lookup, List.eraseDups_cons, chainify, canonBool,
    chainOf, consC, nilA]

end PLeaTTa.PrologGoalControlCarryBridge
