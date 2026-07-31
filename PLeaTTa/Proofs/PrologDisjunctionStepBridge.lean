-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologDisjunctionStepBridge
Purpose: Exact source/executable one-step correspondence for literal amb
  disjunction scheduling and its first leftmost branch activation
Trusted boundary: none
Main exports: TaskChoiceActivationAgrees,
  literal_disjunction_step_correspondence,
  literal_selected_unify_failure_two_step_correspondence
-/
import PLeaTTa.Proofs.PrologAnswerResourceBridge

namespace PLeaTTa.PrologDisjunctionStepBridge

open Metta (Atom Subst GroundingTable)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PrologAnswerResourceBridge
open PrologGoalAlpha
open PrologMguBridge
open PrologMguComposition
open PrologOrdinaryStepBridge
open PrologStateBridge
open DemandDrivenStep

/-!
# Literal disjunction scheduling

The independent semantics exposes `taskDisjunction` as one silent step into
`Search.disjoin`.  The sealed executable's `Step.amb` performs two operations
atomically: it appends every branch to the alternative bank and immediately
pulls the first branch.  The relation below describes that post-pull state
structurally.  In particular, the first source task is active, the remaining
source choice owns exactly the newly prepended executable alternatives, and
the older executable bank is a literal untouched suffix.

Only literal amb branches are covered here.  Their executable bodies are
empty and `ambBranchGoals` reverses the equality from source `value = output`
to executable `output = value`; `TaskChoicePayloadAgrees.symmetricUnify`
records precisely that one equation symmetry.  No answer, effect, cursor, or
scheduling decision can be supplied by the relation.
-/

/-- Post-pull agreement for one nonempty source disjunction and the exact
active/current-plus-residual executable control it produces.

`last` consumes the sole branch and leaves the older bank unchanged.  `more`
activates the left branch and prefixes the exact same-order alternatives for
the remaining source choice.  Thus order and duplicate multiplicity are
indices, not set-valued side conditions. -/
inductive TaskChoiceActivationAgrees
    (alpha support : List (LogicVar × String))
    (scope : CutScopeId) (barrier : Nat)
    (canonical : TreeSubstitution)
    (referenceBase current : Substitution) (runtime : Metta.Subst)
    (olderAlts : List PLeaTTa.Alt) :
    Search -> Option (List PLeaTTa.Goal × Metta.Subst) ->
      List PLeaTTa.Alt -> Prop where
  | last (referenceHead : PeTTaSpec.PrologCore.Goal)
      (referenceTail : List PeTTaSpec.PrologCore.Goal)
      (executableGoals : List PLeaTTa.Goal)
      (payload :
        TaskChoicePayloadAgrees alpha support barrier canonical referenceBase
          current runtime (referenceHead :: referenceTail) executableGoals) :
      TaskChoiceActivationAgrees alpha support scope barrier canonical
        referenceBase current runtime olderAlts
        (.task scope (referenceHead :: referenceTail) current)
        (some (executableGoals, runtime)) olderAlts
  | more (referenceHead : PeTTaSpec.PrologCore.Goal)
      (referenceTail : List PeTTaSpec.PrologCore.Goal)
      (executableGoals : List PLeaTTa.Goal)
      (right : Search) (tailAlts : List PLeaTTa.Alt)
      (payload :
        TaskChoicePayloadAgrees alpha support barrier canonical referenceBase
          current runtime (referenceHead :: referenceTail) executableGoals)
      (tail :
        TaskChoiceAlternativeRegionAgrees alpha support scope barrier canonical
          referenceBase current runtime right tailAlts) :
      TaskChoiceActivationAgrees alpha support scope barrier canonical
        referenceBase current runtime olderAlts
        (.choice scope (.task scope (referenceHead :: referenceTail) current)
          right)
        (some (executableGoals, runtime)) (tailAlts ++ olderAlts)

namespace TaskChoiceAlternativeRegionAgrees

/-- Pulling the head of an exact task-choice alternative region produces the
corresponding exact active source branch and preserves an arbitrary older
alternative suffix literally. -/
theorem activate
    {alpha support : List (LogicVar × String)}
    {scope : CutScopeId} {barrier : Nat}
    {canonical : TreeSubstitution}
    {referenceBase current : Substitution} {runtime : Metta.Subst}
    {source : Search} {alts olderAlts : List PLeaTTa.Alt}
    (agreement :
      TaskChoiceAlternativeRegionAgrees alpha support scope barrier canonical
        referenceBase current runtime source alts) :
    ∃ executableGoals : List PLeaTTa.Goal,
      ∃ tailAlts : List PLeaTTa.Alt,
        alts = .br executableGoals runtime :: tailAlts ∧
        TaskChoiceActivationAgrees alpha support scope barrier canonical
          referenceBase current runtime olderAlts source
          (some (executableGoals, runtime)) (tailAlts ++ olderAlts) := by
  cases agreement with
  | last referenceHead referenceTail executableGoals payload =>
      exact ⟨executableGoals, [], rfl, by simpa using
        (TaskChoiceActivationAgrees.last referenceHead referenceTail
          executableGoals payload :
          TaskChoiceActivationAgrees alpha support scope barrier canonical
            referenceBase current runtime olderAlts
            (.task scope (referenceHead :: referenceTail) current)
            (some (executableGoals, runtime)) olderAlts)⟩
  | more referenceHead referenceTail executableGoals right tailAlts payload tail =>
      exact ⟨executableGoals, tailAlts, rfl,
        TaskChoiceActivationAgrees.more referenceHead referenceTail
          executableGoals right tailAlts payload tail⟩

end TaskChoiceAlternativeRegionAgrees

/-- Ready-state certificate for one literal amb head.  It fixes the source
and executable goal payloads, the exact runtime binding, and the persistent
state relation while leaving the preexisting alternative bank and enclosing
typed frames unconstrained. -/
structure ReadyLiteralDisjunctionRelates
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String)) (barrier : Nat)
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (session : Session) (current : Substitution)
    (referenceOutput : Term)
    (referenceBranches referenceTail : List PeTTaSpec.PrologCore.Goal)
    (runtime : Metta.Subst) (executableOutput : Metta.Atom)
    (executableBranches : List (Metta.Atom × List PLeaTTa.Goal))
    (executableTail : List PLeaTTa.Goal)
    (state : OpenConf) : Prop where
  persistent :
    SessionRelatesPersistent freshFrontier session state.persistent
  current_exact :
    state.control.cur =
      some (.amb executableBranches executableOutput :: executableTail,
        runtime)
  data :
    TaskDataAgrees alpha support canonical referenceBase current runtime
  branches :
    AlphaLiteralAmbBranchesAgree alpha referenceOutput executableOutput
      referenceBranches executableBranches
  tail :
    NormalizedAlphaGoalsAgree alpha barrier referenceTail executableTail
  nonempty : referenceBranches ≠ []

/-- Exact sealed successor after a nonempty amb installs its same-order bank
and pulls the first branch.  This helper names an already-existing `Conf`;
it does not define a second evaluator. -/
def literalAmbPulledSuccessor
    (state : OpenConf) (executableOutput executableValue : Metta.Atom)
    (remainingBranches : List (Metta.Atom × List PLeaTTa.Goal))
    (executableTail : List PLeaTTa.Goal) (runtime : Metta.Subst) : OpenConf :=
  state.stepOpen
    { state.toConf with
      cur := some
        (PLeaTTa.ambBranchGoals executableOutput (executableValue, []) ++
          executableTail, runtime)
      alts := remainingBranches.map (fun branch =>
          PLeaTTa.Alt.br
            (PLeaTTa.ambBranchGoals executableOutput branch ++ executableTail)
            runtime) ++ state.toConf.alts }

@[simp] theorem literalAmbPulledSuccessor_persistent
    (state : OpenConf) (executableOutput executableValue : Metta.Atom)
    (remainingBranches : List (Metta.Atom × List PLeaTTa.Goal))
    (executableTail : List PLeaTTa.Goal) (runtime : Metta.Subst) :
    (literalAmbPulledSuccessor state executableOutput executableValue
      remainingBranches executableTail runtime).persistent =
      state.persistent := by
  rfl

@[simp] theorem literalAmbPulledSuccessor_current
    (state : OpenConf) (executableOutput executableValue : Metta.Atom)
    (remainingBranches : List (Metta.Atom × List PLeaTTa.Goal))
    (executableTail : List PLeaTTa.Goal) (runtime : Metta.Subst) :
    (literalAmbPulledSuccessor state executableOutput executableValue
      remainingBranches executableTail runtime).control.cur =
      some
        (PLeaTTa.ambBranchGoals executableOutput (executableValue, []) ++
          executableTail, runtime) := by
  rfl

@[simp] theorem literalAmbPulledSuccessor_alts
    (state : OpenConf) (executableOutput executableValue : Metta.Atom)
    (remainingBranches : List (Metta.Atom × List PLeaTTa.Goal))
    (executableTail : List PLeaTTa.Goal) (runtime : Metta.Subst) :
    (literalAmbPulledSuccessor state executableOutput executableValue
      remainingBranches executableTail runtime).control.alts =
      remainingBranches.map (fun branch =>
          PLeaTTa.Alt.br
            (PLeaTTa.ambBranchGoals executableOutput branch ++ executableTail)
            runtime) ++ state.control.alts := by
  rfl

@[simp] theorem literalAmbPulledSuccessor_qterm
    (state : OpenConf) (executableOutput executableValue : Metta.Atom)
    (remainingBranches : List (Metta.Atom × List PLeaTTa.Goal))
    (executableTail : List PLeaTTa.Goal) (runtime : Metta.Subst) :
    (literalAmbPulledSuccessor state executableOutput executableValue
      remainingBranches executableTail runtime).control.qterm =
      state.control.qterm := by
  rfl

/-- Literal scheduling changes only the active branch and alternative bank;
the private answer accumulator remains owned by the surrounding collector. -/
@[simp] theorem literalAmbPulledSuccessor_answers
    (state : OpenConf) (executableOutput executableValue : Metta.Atom)
    (remainingBranches : List (Metta.Atom × List PLeaTTa.Goal))
    (executableTail : List PLeaTTa.Goal) (runtime : Metta.Subst) :
    (literalAmbPulledSuccessor state executableOutput executableValue
      remainingBranches executableTail runtime).control.answers =
      state.control.answers := by
  rfl

@[simp] theorem literalAmbPulledSuccessor_frames
    (state : OpenConf) (executableOutput executableValue : Metta.Atom)
    (remainingBranches : List (Metta.Atom × List PLeaTTa.Goal))
    (executableTail : List PLeaTTa.Goal) (runtime : Metta.Subst) :
    (literalAmbPulledSuccessor state executableOutput executableValue
      remainingBranches executableTail runtime).frames = state.frames := by
  rfl

@[simp] theorem literalAmbPulledSuccessor_scopes
    (state : OpenConf) (executableOutput executableValue : Metta.Atom)
    (remainingBranches : List (Metta.Atom × List PLeaTTa.Goal))
    (executableTail : List PLeaTTa.Goal) (runtime : Metta.Subst) :
    (literalAmbPulledSuccessor state executableOutput executableValue
      remainingBranches executableTail runtime).scopes = state.scopes := by
  rfl

/-- One literal source disjunction step and the executable `amb` step agree
on the exact leftmost activation.

The conclusion exposes both branch-list decompositions, so nonemptiness is
not hidden behind an existential scheduler.  The independent side takes its
actual silent `taskDisjunction` step.  The executable side takes the sealed
`Step.amb`, lifted through both fine lanes, and reaches the named post-pull
state.  `TaskChoiceActivationAgrees` then pins its current branch and residual
bank against `Search.disjoin`; the preexisting alternative bank is the exact
suffix.  Persistent world/allocation, typed frames, and all three open scope
frontiers are unchanged. -/
theorem literal_disjunction_step_correspondence
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {session : Session} {scope : CutScopeId} {current : Substitution}
    {referenceOutput : Term}
    {referenceBranches referenceTail : List PeTTaSpec.PrologCore.Goal}
    {runtime : Metta.Subst} {executableOutput : Metta.Atom}
    {executableBranches : List (Metta.Atom × List PLeaTTa.Goal)}
    {executableTail : List PLeaTTa.Goal} {state : OpenConf}
    (agreement :
      ReadyLiteralDisjunctionRelates freshFrontier alpha support barrier
        canonical referenceBase session current referenceOutput
        referenceBranches referenceTail runtime executableOutput
        executableBranches executableTail state) :
    ∃ referenceValue : Term,
      ∃ remainingReferences : List PeTTaSpec.PrologCore.Goal,
        ∃ executableValue : Metta.Atom,
          ∃ remainingExecutables :
              List (Metta.Atom × List PLeaTTa.Goal),
            referenceBranches =
                .unify referenceValue referenceOutput ::
                  remainingReferences ∧
              executableBranches =
                (executableValue, []) :: remainingExecutables ∧
              let next := literalAmbPulledSuccessor state executableOutput
                executableValue remainingExecutables executableTail runtime
              RawStep session
                  (.task scope
                    (.disjunction referenceBranches :: referenceTail) current)
                  [] .none session
                  (.running
                    (Search.disjoin scope referenceBranches referenceTail
                      current)) ∧
                DemandDrivenCallStep.Step prog gt (.ready state)
                  (.ready next) ∧
                TaskChoiceActivationAgrees alpha support scope barrier
                  canonical referenceBase current runtime state.control.alts
                  (Search.disjoin scope referenceBranches referenceTail current)
                  next.control.cur next.control.alts ∧
                SessionRelatesPersistent freshFrontier session
                  next.persistent ∧
                next.frames = state.frames ∧
                next.scopes = state.scopes := by
  rcases agreement with
    ⟨persistent, currentExact, data, branches, tailControl, nonempty⟩
  cases branches with
  | nil outputAgreement =>
      simp at nonempty
  | @cons referenceValue executableValue remainingReferences
      remainingExecutables valueAgreement outputAgreement tailBranches =>
      refine
        ⟨referenceValue, remainingReferences, executableValue,
          remainingExecutables, rfl, rfl, ?_⟩
      let next := literalAmbPulledSuccessor state executableOutput
        executableValue remainingExecutables executableTail runtime
      have sealedHead :
          state.toConf.cur =
            some
              (.amb ((executableValue, []) :: remainingExecutables)
                  executableOutput :: executableTail,
                runtime) := by
        simpa [OpenConf.toConf, Control.toConf] using currentExact
      have sealedStep : PLeaTTa.Step prog gt state.toConf next.toConf := by
        simpa [next, literalAmbPulledSuccessor] using
          (PLeaTTa.Step.amb state.toConf
            ((executableValue, []) :: remainingExecutables)
            executableOutput executableTail runtime sealedHead)
      have notFindall : ¬ PLeaTTa.findallRunHead state.toConf := by
        simp [PLeaTTa.findallRunHead, sealedHead]
      have notLocalCall :
          ¬ DemandDrivenCallStep.LocalResolveHead state := by
        simp [DemandDrivenCallStep.LocalResolveHead, sealedHead]
      have executableStep :
          DemandDrivenCallStep.Step prog gt (.ready state) (.ready next) := by
        apply DemandDrivenCallStep.Step.ordinary state next notLocalCall
        apply DemandDrivenStep.Step.ordinary state next.toConf notFindall
        simpa [next] using sealedStep
      have ordered :
          OrderedTaskChoicePayloadsAgree alpha support barrier canonical
            referenceBase current runtime referenceTail
            (.unify referenceValue referenceOutput :: remainingReferences)
            (((executableValue, []) :: remainingExecutables).map fun branch =>
              PLeaTTa.ambBranchGoals executableOutput branch ++
                executableTail) :=
        PLeaTTa.PrologAnswerResourceBridge.AlphaLiteralAmbBranchesAgree.toOrderedTaskChoicePayloads
            (AlphaLiteralAmbBranchesAgree.cons valueAgreement outputAgreement
              tailBranches)
            data referenceTail executableTail tailControl
      have region := ordered.toTaskChoiceAlternativeRegion
        (scope := scope) (by simp)
      obtain ⟨firstGoals, tailAlts, fullEq, activated⟩ :=
        PrologDisjunctionStepBridge.TaskChoiceAlternativeRegionAgrees.activate
          (olderAlts := state.control.alts) region
      simp only [List.map_cons] at fullEq
      injection fullEq with firstAltEq tailAltsEq
      have firstGoalsEq :
          PLeaTTa.ambBranchGoals executableOutput (executableValue, []) ++
              executableTail = firstGoals := by
        injection firstAltEq
      rw [← firstGoalsEq, ← tailAltsEq] at activated
      have activation :
          TaskChoiceActivationAgrees alpha support scope barrier canonical
            referenceBase current runtime state.control.alts
            (Search.disjoin scope
              (.unify referenceValue referenceOutput :: remainingReferences)
              referenceTail current)
            next.control.cur next.control.alts := by
        change
          TaskChoiceActivationAgrees alpha support scope barrier canonical
            referenceBase current runtime state.control.alts
            (Search.disjoin scope
              (.unify referenceValue referenceOutput :: remainingReferences)
              referenceTail current)
            (literalAmbPulledSuccessor state executableOutput executableValue
              remainingExecutables executableTail runtime).control.cur
            (literalAmbPulledSuccessor state executableOutput executableValue
              remainingExecutables executableTail runtime).control.alts
        rw [literalAmbPulledSuccessor_current,
          literalAmbPulledSuccessor_alts]
        simpa [List.map_map, Function.comp_def] using activated
      exact
        ⟨RawStep.taskDisjunction scope
            (.unify referenceValue referenceOutput :: remainingReferences)
            referenceTail current session,
          executableStep, activation,
          by
            change SessionRelatesPersistent freshFrontier session
              state.persistent
            exact persistent,
          by rfl, by rfl⟩

/-- Fixed-head specialization of the scheduler theorem.  This is the API
used by the selected-branch MGU correspondence: no existential branch can be
silently chosen in place of the literal first branch supplied by the caller. -/
theorem literal_disjunction_step_correspondence_cons
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {session : Session} {scope : CutScopeId} {current : Substitution}
    {referenceValue referenceOutput : Term}
    {remainingReferences referenceTail :
      List PeTTaSpec.PrologCore.Goal}
    {runtime : Metta.Subst} {executableValue executableOutput : Metta.Atom}
    {remainingExecutables : List (Metta.Atom × List PLeaTTa.Goal)}
    {executableTail : List PLeaTTa.Goal} {state : OpenConf}
    (agreement :
      ReadyLiteralDisjunctionRelates freshFrontier alpha support barrier
        canonical referenceBase session current referenceOutput
        (.unify referenceValue referenceOutput :: remainingReferences)
        referenceTail runtime executableOutput
        ((executableValue, []) :: remainingExecutables)
        executableTail state) :
    let next := literalAmbPulledSuccessor state executableOutput
      executableValue remainingExecutables executableTail runtime
    RawStep session
        (.task scope
          (.disjunction
              (.unify referenceValue referenceOutput :: remainingReferences) ::
            referenceTail)
          current)
        [] .none session
        (.running
          (Search.disjoin scope
            (.unify referenceValue referenceOutput :: remainingReferences)
            referenceTail current)) ∧
      DemandDrivenCallStep.Step prog gt (.ready state) (.ready next) ∧
      TaskChoiceActivationAgrees alpha support scope barrier canonical
        referenceBase current runtime state.control.alts
        (Search.disjoin scope
          (.unify referenceValue referenceOutput :: remainingReferences)
          referenceTail current)
        next.control.cur next.control.alts ∧
      SessionRelatesPersistent freshFrontier session next.persistent ∧
      next.frames = state.frames ∧ next.scopes = state.scopes := by
  obtain
    ⟨foundReference, foundReferences, foundExecutable, foundExecutables,
      referenceShape, executableShape, result⟩ :=
    literal_disjunction_step_correspondence
      (prog := prog) (gt := gt) (scope := scope) agreement
  injection referenceShape with referenceValueEq remainingReferencesEq
  injection referenceValueEq with referenceTermEq referenceOutputEq
  injection executableShape with executableHeadEq remainingExecutablesEq
  injection executableHeadEq with executableValueEq executableBodyEq
  subst foundReference
  subst foundReferences
  subst foundExecutable
  subst foundExecutables
  exact result

/-- Source control after the selected branch's first equality succeeds.
The inactive right disjunction retains the entry binding; only the active
left task advances to the resulting binding. -/
def selectedUnifySourceSuccessor (scope : CutScopeId)
    (remainingReferences referenceTail : List PeTTaSpec.PrologCore.Goal)
    (entry result : Substitution) : Search :=
  match remainingReferences with
  | [] => .task scope referenceTail result
  | head :: tail =>
      .choice scope (.task scope referenceTail result)
        (Search.disjoin scope (head :: tail) referenceTail entry)

/-- The independent leftmost scheduler takes exactly one successful equality
step in the selected branch.  With siblings the child transition is lifted
by `choiceProgress`; with no sibling the task itself advances. -/
theorem source_selected_unify_step
    {scope : CutScopeId} {session : Session}
    {referenceValue referenceOutput : Term}
    {remainingReferences referenceTail :
      List PeTTaSpec.PrologCore.Goal}
    {entry result : Substitution}
    (resolved :
      UnifyResolution entry referenceValue referenceOutput result) :
    RawStep session
      (Search.disjoin scope
        (.unify referenceValue referenceOutput :: remainingReferences)
        referenceTail entry)
      [] .none session
      (.running
        (selectedUnifySourceSuccessor scope remainingReferences referenceTail
          entry result)) := by
  cases remainingReferences with
  | nil =>
      simpa [Search.disjoin, selectedUnifySourceSuccessor] using
        (RawStep.taskUnifySuccess scope referenceValue referenceOutput
          referenceTail entry result session resolved)
  | cons head tail =>
      apply RawStep.choiceProgress
      exact RawStep.taskUnifySuccess scope referenceValue referenceOutput
        referenceTail entry result session resolved

/-- A failed selected equality with at least one residual disjunct switches
to that residual disjunction in one top-level source step.

The failing task's private completion observation is consumed by
`choiceComplete`, so the enclosing scheduler emits no observation.  The
right branch retains the entry binding and the common caller tail exactly. -/
theorem source_selected_unify_failure_step
    {scope : CutScopeId} {session : Session}
    {referenceValue referenceOutput : Term}
    {nextReference : PeTTaSpec.PrologCore.Goal}
    {remainingReferences referenceTail :
      List PeTTaSpec.PrologCore.Goal}
    {current : Substitution}
    (clash :
      ¬ ∃ result,
        UnifyResolution current referenceValue referenceOutput result) :
    RawStep session
      (Search.disjoin scope
        (.unify referenceValue referenceOutput ::
          nextReference :: remainingReferences)
        referenceTail current)
      [] .none session
      (.running
        (Search.disjoin scope (nextReference :: remainingReferences)
          referenceTail current)) := by
  apply RawStep.choiceComplete
  exact RawStep.taskUnifyFailure scope referenceValue referenceOutput
    referenceTail current session clash

/-- The sealed eager pull after one failed literal branch installs exactly
the next literal branch and leaves the exact later/older alternative suffix.

This is equality of the full fine state, not merely its sealed projection:
persistent world/counter, typed frame stack, and all scope high-waters are
carried unchanged by both sides. -/
theorem unifyFailureSuccessor_literalAmbPulledSuccessor_cons
    (state : OpenConf) (executableOutput failedValue nextValue : Metta.Atom)
    (remainingBranches : List (Metta.Atom × List PLeaTTa.Goal))
    (executableTail : List PLeaTTa.Goal) (runtime : Metta.Subst) :
    PrologOrdinaryStepBridge.unifyFailureSuccessor
        (literalAmbPulledSuccessor state executableOutput failedValue
          ((nextValue, []) :: remainingBranches) executableTail runtime) =
      literalAmbPulledSuccessor state executableOutput nextValue
        remainingBranches executableTail runtime := by
  let selected :=
    literalAmbPulledSuccessor state executableOutput failedValue
      ((nextValue, []) :: remainingBranches) executableTail runtime
  let next :=
    literalAmbPulledSuccessor state executableOutput nextValue
      remainingBranches executableTail runtime
  change PrologOrdinaryStepBridge.unifyFailureSuccessor selected = next
  apply OpenConf.eq_of_toConf_eq_of_frames_eq_of_scopes_eq
  · change
      PLeaTTa.pull { selected.toConf with cur := none } = next.toConf
    have alts :
        ({ selected.toConf with cur := none }).alts =
          .br (PLeaTTa.Goal.eq executableOutput nextValue :: executableTail)
              runtime ::
            (remainingBranches.map (fun branch =>
                PLeaTTa.Alt.br
                  (PLeaTTa.ambBranchGoals executableOutput branch ++
                    executableTail)
                  runtime) ++ state.toConf.alts) := by
      simp [selected, literalAmbPulledSuccessor]
    rw [PLeaTTa.pull_of_alts_branch _ _ _ _ alts]
    simp [selected, next, literalAmbPulledSuccessor]
  · simp [PrologOrdinaryStepBridge.unifyFailureSuccessor, selected, next]
  · simp [PrologOrdinaryStepBridge.unifyFailureSuccessor, selected, next]

namespace ReadyLiteralDisjunctionRelates

/-- Inversion for a caller-indexed nonempty literal branch list.  The
relation cannot replace the requested first branch with another value or a
nested executable body. -/
theorem literal_cons_components
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {session : Session} {current : Substitution}
    {referenceValue referenceOutput : Term}
    {remainingReferences referenceTail :
      List PeTTaSpec.PrologCore.Goal}
    {runtime : Metta.Subst} {executableValue executableOutput : Metta.Atom}
    {remainingExecutables : List (Metta.Atom × List PLeaTTa.Goal)}
    {executableTail : List PLeaTTa.Goal} {state : OpenConf}
    (agreement :
      ReadyLiteralDisjunctionRelates freshFrontier alpha support barrier
        canonical referenceBase session current referenceOutput
        (.unify referenceValue referenceOutput :: remainingReferences)
        referenceTail runtime executableOutput
        ((executableValue, []) :: remainingExecutables)
        executableTail state) :
    AlphaTermAgrees alpha referenceValue executableValue ∧
      AlphaTermAgrees alpha referenceOutput executableOutput ∧
      AlphaLiteralAmbBranchesAgree alpha referenceOutput executableOutput
        remainingReferences remainingExecutables := by
  cases agreement.branches with
  | cons value output tail => exact ⟨value, output, tail⟩

end ReadyLiteralDisjunctionRelates

/-- Exact two-step prefix for a nonempty literal disjunction whose selected
equality succeeds.

Step one is the actual source `taskDisjunction` paired with sealed/fine
`Step.amb`; step two is the selected source unification (lifted through
`choiceProgress` when siblings exist) paired with sealed/fine `eq_ok`.
The source and executable ordered MGU association lists may differ, but the
post-state task data records their proved cumulative variant relation.

Inactive siblings deliberately retain the entry binding and old canonical
state.  Their exact same-order payload relation is returned separately from
the selected branch's new payload, preventing successful left-branch
bindings from leaking into backtrackable rights. -/
theorem literal_selected_unify_two_step_correspondence
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {session : Session} {scope : CutScopeId} {current result : Substitution}
    {referenceValue referenceOutput : Term}
    {remainingReferences referenceTail :
      List PeTTaSpec.PrologCore.Goal}
    {runtime : Metta.Subst} {executableValue executableOutput : Metta.Atom}
    {remainingExecutables : List (Metta.Atom × List PLeaTTa.Goal)}
    {executableTail : List PLeaTTa.Goal} {state : OpenConf}
    (agreement :
      ReadyLiteralDisjunctionRelates freshFrontier alpha support barrier
        canonical referenceBase session current referenceOutput
        (.unify referenceValue referenceOutput :: remainingReferences)
        referenceTail runtime executableOutput
        ((executableValue, []) :: remainingExecutables)
        executableTail state)
    (valueSupported :
      AlphaTreeSupported alpha support (Term.denote referenceValue))
    (outputSupported :
      AlphaTreeSupported alpha support (Term.denote referenceOutput))
    (supportIncluded : ∀ pair, pair ∈ support → pair ∈ alpha)
    (runtimeAvoids : AlphaRuntimeNamesAvoid support runtime)
    (live :
      AlphaRuntimeNamesLive support executableTail state.control.qterm)
    (resolved :
      UnifyResolution current referenceValue referenceOutput result) :
    ∃ sourceExtension : TreeSubstitution,
      ∃ installed : Metta.Subst,
        let selected := literalAmbPulledSuccessor state executableOutput
          executableValue remainingExecutables executableTail runtime
        let after := PrologOrdinaryStepBridge.unifySuccessor selected
          executableTail installed
        PLeaTTa.unifyB runtime executableOutput executableValue =
            some installed ∧
          RawStep session
            (.task scope
              (.disjunction
                  (.unify referenceValue referenceOutput ::
                    remainingReferences) :: referenceTail)
              current)
            [] .none session
            (.running
              (Search.disjoin scope
                (.unify referenceValue referenceOutput ::
                  remainingReferences)
                referenceTail current)) ∧
          DemandDrivenCallStep.Step prog gt (.ready state)
            (.ready selected) ∧
          RawStep session
            (Search.disjoin scope
              (.unify referenceValue referenceOutput :: remainingReferences)
              referenceTail current)
            [] .none session
            (.running
              (selectedUnifySourceSuccessor scope remainingReferences
                referenceTail current result)) ∧
          DemandDrivenCallStep.Step prog gt (.ready selected)
            (.ready after) ∧
          TaskPayloadAgrees alpha support barrier
            (sourceExtension ++ canonical) referenceBase result
            (PLeaTTa.trimFor executableTail state.control.qterm installed)
            referenceTail executableTail ∧
          OrderedTaskChoicePayloadsAgree alpha support barrier canonical
            referenceBase current runtime referenceTail remainingReferences
            (remainingExecutables.map fun branch =>
              PLeaTTa.ambBranchGoals executableOutput branch ++
                executableTail) ∧
          after.control.alts =
            remainingExecutables.map (fun branch =>
              PLeaTTa.Alt.br
                (PLeaTTa.ambBranchGoals executableOutput branch ++
                  executableTail)
                runtime) ++ state.control.alts ∧
          SessionRelatesPersistent freshFrontier session after.persistent ∧
          after.frames = state.frames ∧ after.scopes = state.scopes := by
  rcases agreement.literal_cons_components with
    ⟨valueAgreement, outputAgreement, remainingAgreement⟩
  let selected := literalAmbPulledSuccessor state executableOutput
    executableValue remainingExecutables executableTail runtime
  have selectedHead :
      selected.control.cur =
        some (.eq executableOutput executableValue :: executableTail,
          runtime) := by
    simp [selected, PLeaTTa.ambBranchGoals]
  let selectedPayload :
      TaskChoicePayloadAgrees alpha support barrier canonical referenceBase
        current runtime
        (.unify referenceValue referenceOutput :: referenceTail)
        (.eq executableOutput executableValue :: executableTail) :=
    .symmetricUnify agreement.data valueAgreement outputAgreement
      agreement.tail
  obtain ⟨sourceExtension, installed, installedExact, nextData⟩ :=
    selectedPayload.afterUnifySuccessData valueSupported outputSupported
      supportIncluded runtimeAvoids resolved
  have nextPayload :
      TaskPayloadAgrees alpha support barrier
        (sourceExtension ++ canonical) referenceBase result
        (PLeaTTa.trimFor executableTail state.control.qterm installed)
        referenceTail executableTail :=
    (nextData.trimFor live).withControl agreement.tail
  have residualPayloads :
      OrderedTaskChoicePayloadsAgree alpha support barrier canonical
        referenceBase current runtime referenceTail remainingReferences
        (remainingExecutables.map fun branch =>
          PLeaTTa.ambBranchGoals executableOutput branch ++
            executableTail) :=
    PLeaTTa.PrologAnswerResourceBridge.AlphaLiteralAmbBranchesAgree.toOrderedTaskChoicePayloads
      remainingAgreement agreement.data referenceTail executableTail
        agreement.tail
  have scheduling := literal_disjunction_step_correspondence_cons
    (prog := prog) (gt := gt) (scope := scope) agreement
  change
    RawStep session
        (.task scope
          (.disjunction
              (.unify referenceValue referenceOutput :: remainingReferences) ::
            referenceTail)
          current)
        [] .none session
        (.running
          (Search.disjoin scope
            (.unify referenceValue referenceOutput :: remainingReferences)
            referenceTail current)) ∧
      DemandDrivenCallStep.Step prog gt (.ready state) (.ready selected) ∧
      _ at scheduling
  have executableUnify :
      DemandDrivenCallStep.Step prog gt (.ready selected)
        (.ready
          (PrologOrdinaryStepBridge.unifySuccessor selected executableTail
            installed)) :=
    PrologOrdinaryStepBridge.executable_unify_step selected .equality
      executableOutput executableValue executableTail runtime installed
      selectedHead installedExact
  refine ⟨sourceExtension, installed, installedExact,
    scheduling.1, scheduling.2.1,
    source_selected_unify_step resolved, executableUnify,
    nextPayload, residualPayloads, ?_, ?_, ?_, ?_⟩
  · calc
      (PrologOrdinaryStepBridge.unifySuccessor selected executableTail
          installed).control.alts = selected.control.alts :=
        PrologOrdinaryStepBridge.unifySuccessor_alts selected executableTail
          installed
      _ = remainingExecutables.map (fun branch =>
            PLeaTTa.Alt.br
              (PLeaTTa.ambBranchGoals executableOutput branch ++
                executableTail)
              runtime) ++ state.control.alts := by
        simp [selected]
  · change SessionRelatesPersistent freshFrontier session state.persistent
    exact agreement.persistent
  · rfl
  · rfl

/-- Exact two-step prefix for a literal disjunction whose selected equality
fails while at least one residual branch remains.

The source first expands `disjunction`, then consumes the selected leaf's
private completion through `choiceComplete`.  The fine machine first executes
`amb`, then performs its atomic `eq_fail → pull`; the latter endpoint is
proved equal to the next literal activation, including the older alternative
suffix and all open-only resources.  Runtime failure is derived through the
operand-reversed task-choice certificate rather than assumed. -/
theorem literal_selected_unify_failure_two_step_correspondence
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {session : Session} {scope : CutScopeId} {current : Substitution}
    {referenceValue referenceOutput : Term}
    {nextReference : PeTTaSpec.PrologCore.Goal}
    {remainingReferences referenceTail :
      List PeTTaSpec.PrologCore.Goal}
    {runtime : Metta.Subst}
    {executableValue executableOutput nextExecutable : Metta.Atom}
    {remainingExecutables : List (Metta.Atom × List PLeaTTa.Goal)}
    {executableTail : List PLeaTTa.Goal} {state : OpenConf}
    (agreement :
      ReadyLiteralDisjunctionRelates freshFrontier alpha support barrier
        canonical referenceBase session current referenceOutput
        (.unify referenceValue referenceOutput ::
          nextReference :: remainingReferences)
        referenceTail runtime executableOutput
        ((executableValue, []) ::
          (nextExecutable, []) :: remainingExecutables)
        executableTail state)
    (valueSupported :
      AlphaTreeSupported alpha support (Term.denote referenceValue))
    (outputSupported :
      AlphaTreeSupported alpha support (Term.denote referenceOutput))
    (aliasSafe :
      CurrentUnifyOperandsAliasSafe current referenceValue referenceOutput)
    (clash :
      ¬ ∃ result,
        UnifyResolution current referenceValue referenceOutput result) :
    let selected :=
      literalAmbPulledSuccessor state executableOutput executableValue
        ((nextExecutable, []) :: remainingExecutables)
        executableTail runtime
    let next :=
      literalAmbPulledSuccessor state executableOutput nextExecutable
        remainingExecutables executableTail runtime
    PLeaTTa.unifyB runtime executableOutput executableValue = none ∧
      RawStep session
        (.task scope
          (.disjunction
              (.unify referenceValue referenceOutput ::
                nextReference :: remainingReferences) ::
            referenceTail)
          current)
        [] .none session
        (.running
          (Search.disjoin scope
            (.unify referenceValue referenceOutput ::
              nextReference :: remainingReferences)
            referenceTail current)) ∧
      DemandDrivenCallStep.Step prog gt (.ready state) (.ready selected) ∧
      RawStep session
        (Search.disjoin scope
          (.unify referenceValue referenceOutput ::
            nextReference :: remainingReferences)
          referenceTail current)
        [] .none session
        (.running
          (Search.disjoin scope (nextReference :: remainingReferences)
            referenceTail current)) ∧
      DemandDrivenCallStep.Step prog gt (.ready selected) (.ready next) ∧
      TaskChoiceActivationAgrees alpha support scope barrier canonical
        referenceBase current runtime state.control.alts
        (Search.disjoin scope (nextReference :: remainingReferences)
          referenceTail current)
        next.control.cur next.control.alts ∧
      SessionRelatesPersistent freshFrontier session next.persistent ∧
      next.frames = state.frames ∧ next.scopes = state.scopes := by
  rcases agreement.literal_cons_components with
    ⟨valueAgreement, outputAgreement, residualAgreement⟩
  let selected :=
    literalAmbPulledSuccessor state executableOutput executableValue
      ((nextExecutable, []) :: remainingExecutables) executableTail runtime
  let next :=
    literalAmbPulledSuccessor state executableOutput nextExecutable
      remainingExecutables executableTail runtime
  have selectedHead :
      selected.control.cur =
        some (.eq executableOutput executableValue :: executableTail,
          runtime) := by
    simp [selected, PLeaTTa.ambBranchGoals]
  let selectedPayload :
      TaskChoicePayloadAgrees alpha support barrier canonical referenceBase
        current runtime
        (.unify referenceValue referenceOutput :: referenceTail)
        (.eq executableOutput executableValue :: executableTail) :=
    .symmetricUnify agreement.data valueAgreement outputAgreement
      agreement.tail
  have failed :
      PLeaTTa.unifyB runtime executableOutput executableValue = none :=
    selectedPayload.unifyB_eq_none_of_no_resolution
      valueSupported outputSupported aliasSafe clash
  have scheduling := literal_disjunction_step_correspondence_cons
    (prog := prog) (gt := gt) (scope := scope) agreement
  have sourceFailure :
      RawStep session
        (Search.disjoin scope
          (.unify referenceValue referenceOutput ::
            nextReference :: remainingReferences)
          referenceTail current)
        [] .none session
        (.running
          (Search.disjoin scope (nextReference :: remainingReferences)
            referenceTail current)) :=
    source_selected_unify_failure_step clash
  have endpoint :
      PrologOrdinaryStepBridge.unifyFailureSuccessor selected = next := by
    simpa [selected, next] using
      (unifyFailureSuccessor_literalAmbPulledSuccessor_cons state
        executableOutput executableValue nextExecutable remainingExecutables
        executableTail runtime)
  have executableFailure :
      DemandDrivenCallStep.Step prog gt (.ready selected) (.ready next) := by
    rw [← endpoint]
    exact
      PrologOrdinaryStepBridge.executable_unify_failure_step selected
        .equality executableOutput executableValue executableTail runtime
        selectedHead failed
  have orderedResidual :
      OrderedTaskChoicePayloadsAgree alpha support barrier canonical
        referenceBase current runtime referenceTail
        (nextReference :: remainingReferences)
        (((nextExecutable, []) :: remainingExecutables).map fun branch =>
          PLeaTTa.ambBranchGoals executableOutput branch ++ executableTail) :=
    PLeaTTa.PrologAnswerResourceBridge.AlphaLiteralAmbBranchesAgree.toOrderedTaskChoicePayloads
      residualAgreement agreement.data referenceTail executableTail
        agreement.tail
  have region := orderedResidual.toTaskChoiceAlternativeRegion
    (scope := scope) (by simp)
  obtain ⟨firstGoals, tailAlts, fullEq, activated⟩ :=
    PrologDisjunctionStepBridge.TaskChoiceAlternativeRegionAgrees.activate
      (olderAlts := state.control.alts) region
  simp only [List.map_cons] at fullEq
  injection fullEq with firstAltEq tailAltsEq
  have firstGoalsEq :
      PLeaTTa.ambBranchGoals executableOutput (nextExecutable, []) ++
          executableTail = firstGoals := by
    injection firstAltEq
  rw [← firstGoalsEq, ← tailAltsEq] at activated
  have nextActivation :
      TaskChoiceActivationAgrees alpha support scope barrier canonical
        referenceBase current runtime state.control.alts
        (Search.disjoin scope (nextReference :: remainingReferences)
          referenceTail current)
        next.control.cur next.control.alts := by
    change
      TaskChoiceActivationAgrees alpha support scope barrier canonical
        referenceBase current runtime state.control.alts
        (Search.disjoin scope (nextReference :: remainingReferences)
          referenceTail current)
        (literalAmbPulledSuccessor state executableOutput nextExecutable
          remainingExecutables executableTail runtime).control.cur
        (literalAmbPulledSuccessor state executableOutput nextExecutable
          remainingExecutables executableTail runtime).control.alts
    rw [literalAmbPulledSuccessor_current,
      literalAmbPulledSuccessor_alts]
    simpa [List.map_map, Function.comp_def] using activated
  refine ⟨failed, scheduling.1, ?_, sourceFailure, executableFailure,
    nextActivation, ?_, ?_, ?_⟩
  · simpa [selected] using scheduling.2.1
  · change SessionRelatesPersistent freshFrontier session state.persistent
    exact agreement.persistent
  · rfl
  · rfl

/-! ## Residual-versus-exhausted failure discriminators -/

/-- The same selected equality clash has observably different source control
depending only on whether a later disjunct exists.

With one residual branch, `choiceComplete` consumes the leaf completion and
silently activates the right branch.  With no residual branch there is no
choice wrapper: the task publishes completion and becomes terminal.  Both
halves are actual `RawStep` derivations, so the nonempty premise of the main
correspondence cannot be weakened away. -/
theorem source_selected_failure_residual_exhaustion_discriminator
    {scope : CutScopeId} {session : Session}
    {referenceValue referenceOutput : Term}
    {nextReference : PeTTaSpec.PrologCore.Goal}
    {referenceTail : List PeTTaSpec.PrologCore.Goal}
    {current : Substitution}
    (clash :
      ¬ ∃ result,
        UnifyResolution current referenceValue referenceOutput result) :
    RawStep session
        (Search.disjoin scope
          [.unify referenceValue referenceOutput, nextReference]
          referenceTail current)
        [] .none session
        (.running
          (Search.disjoin scope [nextReference] referenceTail current)) ∧
      RawStep session
        (Search.disjoin scope [.unify referenceValue referenceOutput]
          referenceTail current)
        [.completed] .none session (.terminal .completed) := by
  constructor
  · simpa using
      (source_selected_unify_failure_step
        (scope := scope) (session := session)
        (nextReference := nextReference)
        (remainingReferences := []) (referenceTail := referenceTail) clash)
  · simpa [Search.disjoin] using
      (RawStep.taskUnifyFailure scope referenceValue referenceOutput
        referenceTail current session clash)

/-- Fine failure likewise distinguishes a residual literal branch from
exhaustion when the older alternative bank is empty, as it is inside a newly
entered `findall` generator.

The residual run installs `nextValue` immediately.  The exhausted run keeps
the collector frame and typed scope chronology but has no current goal; it is
therefore an intermediate generator terminal awaiting a later `findallExit`,
not the residual successor and not an already exited collector. -/
theorem executable_selected_failure_residual_exhaustion_discriminator
    (state : OpenConf) (executableOutput failedValue nextValue : Metta.Atom)
    (executableTail : List PLeaTTa.Goal) (runtime : Metta.Subst)
    (olderEmpty : state.control.alts = []) :
    let residualSelected :=
      literalAmbPulledSuccessor state executableOutput failedValue
        [(nextValue, [])] executableTail runtime
    let exhaustedSelected :=
      literalAmbPulledSuccessor state executableOutput failedValue []
        executableTail runtime
    let residualAfter :=
      PrologOrdinaryStepBridge.unifyFailureSuccessor residualSelected
    let exhaustedAfter :=
      PrologOrdinaryStepBridge.unifyFailureSuccessor exhaustedSelected
    residualAfter.control.cur =
        some (.eq executableOutput nextValue :: executableTail, runtime) ∧
      exhaustedAfter.control.cur = none ∧
      residualAfter ≠ exhaustedAfter ∧
      exhaustedAfter.frames = state.frames ∧
      exhaustedAfter.scopes = state.scopes := by
  let residualSelected :=
    literalAmbPulledSuccessor state executableOutput failedValue
      [(nextValue, [])] executableTail runtime
  let exhaustedSelected :=
    literalAmbPulledSuccessor state executableOutput failedValue []
      executableTail runtime
  let residualAfter :=
    PrologOrdinaryStepBridge.unifyFailureSuccessor residualSelected
  let exhaustedAfter :=
    PrologOrdinaryStepBridge.unifyFailureSuccessor exhaustedSelected
  have residualEq :
      residualAfter =
        literalAmbPulledSuccessor state executableOutput nextValue []
          executableTail runtime := by
    simpa [residualAfter, residualSelected] using
      (unifyFailureSuccessor_literalAmbPulledSuccessor_cons state
        executableOutput failedValue nextValue [] executableTail runtime)
  have exhaustedAlts : exhaustedSelected.toConf.alts = [] := by
    change exhaustedSelected.control.alts = []
    simpa [exhaustedSelected] using olderEmpty
  have exhaustedCur : exhaustedAfter.control.cur = none := by
    have projected : exhaustedAfter.toConf.cur = none := by
      change
        (PLeaTTa.pull { exhaustedSelected.toConf with cur := none }).cur = none
      cases cache : exhaustedSelected.toConf.barriers <;>
        simp [PLeaTTa.pull, PLeaTTa.pullAux, PLeaTTa.pullAuxTracked,
          PLeaTTa.pullAuxCached, exhaustedAlts, cache]
    simpa [OpenConf.toConf, Control.toConf] using projected
  have residualCur :
      residualAfter.control.cur =
        some (.eq executableOutput nextValue :: executableTail, runtime) := by
    rw [residualEq]
    simp [PLeaTTa.ambBranchGoals]
  have different : residualAfter ≠ exhaustedAfter := by
    intro same
    have currents := congrArg (fun openState => openState.control.cur) same
    rw [residualCur, exhaustedCur] at currents
    contradiction
  exact
    ⟨residualCur, exhaustedCur, different,
      by
        change exhaustedSelected.frames = state.frames
        exact literalAmbPulledSuccessor_frames state executableOutput
          failedValue [] executableTail runtime,
      by
        change exhaustedSelected.scopes = state.scopes
        exact literalAmbPulledSuccessor_scopes state executableOutput
          failedValue [] executableTail runtime⟩

/-! ## The generated-output shape is necessary -/

/-- A nonempty shared-output branch can take the body-only shortcut only if
the executable atom's Boolean equality is reflexive on that value.

This symbolic theorem is paired with two executable characterizations:
`Regression` pins a concrete NaN atom whose raw equality is false, while
`ambBranchGoals_generated_nonempty` proves generated variables take the
shortcut.  Consequently the general superpose bridge must derive generated
output shape at compiler entry; generic `Atom` reflexivity would be an
unsound premise. -/
theorem amb_shared_output_shortcut_implies_beq_true
    (atom : Metta.Atom) (goal : PLeaTTa.Goal)
    (goals : List PLeaTTa.Goal)
    (shortcut :
      PLeaTTa.ambBranchGoals atom (atom, goal :: goals) = goal :: goals) :
    (atom == atom) = true := by
  cases selfEq : (atom == atom) with
  | false =>
      simp [PLeaTTa.ambBranchGoals, selfEq] at shortcut
  | true => rfl

end PLeaTTa.PrologDisjunctionStepBridge
