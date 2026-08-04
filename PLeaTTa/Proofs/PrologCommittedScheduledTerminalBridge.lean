-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologCommittedScheduledTerminalBridge
Purpose: Close a rooted post-cut answer without recreating the consumed
  predicate cursor.
Trusted boundary: none
Main exports:
  RootCommittedScheduledAnswerReady,
  RootCommittedScheduledAnswerReady.complete
-/
import PLeaTTa.Proofs.PrologPersistentFreeCommittedScheduledPayloadBridge

namespace PLeaTTa.PrologCommittedScheduledTerminalBridge

open Metta (Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open DemandDrivenStep
open PrologPersistentFreeCommittedScheduledPayloadBridge

/-! ## Exact exhausted-right source control -/

/-- Source successor after the rooted caller emits its post-cut answer.

The right branch contains only the exhausted predicate boundary.  It owns no
cursor and corresponds to no executable alternative. -/
def committedScheduledAfterAnswerAt
    (callerScope predicateScope : CutScopeId) : Search :=
  .choice callerScope .done
    (.product callerScope (.cutBoundary predicateScope .done) [])

/-- The rooted post-cut caller emits exactly one answer while preserving the
exhausted right branch. -/
theorem committedScheduledSourceProductAt_answer
    (session : Session) (callerScope predicateScope : CutScopeId)
    (current : Substitution) :
    RawStep session
      (committedScheduledSourceProductAt callerScope predicateScope current [])
      [.answer current] .none session
      (.running
        (committedScheduledAfterAnswerAt callerScope predicateScope)) := by
  exact
    .choiceProgress callerScope _ _ _ [.answer current] session session
      (.taskAnswer callerScope current session)

/-- After the answer, leftmost DFS consumes the completed caller leaf and
then propagates completion from the exhausted predicate boundary. -/
theorem committedScheduledAfterAnswerAt_completes
    (session : Session) (callerScope predicateScope : CutScopeId) :
    StepsN 2
      (.running session
        (committedScheduledAfterAnswerAt callerScope predicateScope))
      [.completed] (.terminal session .completed) := by
  let exhausted : Search :=
    .product callerScope (.cutBoundary predicateScope .done) []
  have enterRight :
      Transition
        (.running session
          (committedScheduledAfterAnswerAt callerScope predicateScope))
        [] (.running session exhausted) :=
    .ordinary _ [] session session _
      (.choiceComplete callerScope .done exhausted session session
        (.done session))
  have finish :
      Transition (.running session exhausted) [.completed]
        (.terminal session .completed) :=
    .ordinary _ [.completed] session session _
      (.productComplete callerScope (.cutBoundary predicateScope .done) []
        [.completed] session session
        (.cutBoundaryComplete predicateScope .done session session
          (.done session))
        (by simp [Trace.AnswerFree]))
  simpa [exhausted] using
    (StepsN.succ 1 _ _ _ [] [.completed] enterRight
      (StepsN.succ 0 _ _ _ [.completed] [] finish (.zero _)))

/-- The complete rooted post-cut source trace has one answer followed by one
terminal completion.  The intervening right-switch is a real silent step. -/
theorem committedScheduledSourceProductAt_complete
    (session : Session) (callerScope predicateScope : CutScopeId)
    (current : Substitution) :
    StepsN 3
      (.running session
        (committedScheduledSourceProductAt callerScope predicateScope current []))
      [.answer current, .completed] (.terminal session .completed) := by
  have answer :
      Transition
        (.running session
          (committedScheduledSourceProductAt callerScope predicateScope current []))
        [.answer current]
        (.running session
          (committedScheduledAfterAnswerAt callerScope predicateScope)) :=
    .ordinary _ [.answer current] session session _
      (committedScheduledSourceProductAt_answer session callerScope
        predicateScope current)
  have completion :=
    committedScheduledAfterAnswerAt_completes session callerScope
      predicateScope
  simpa using
    (StepsN.succ 2 _ _ _ [.answer current] [.completed] answer completion)

/-- An empty executable alternative bank has an exact exhausted pull. -/
private theorem pull_empty_fields (conf : PLeaTTa.Conf)
    (empty : conf.alts = []) :
    (PLeaTTa.pull conf).cur = none ∧
      (PLeaTTa.pull conf).alts = [] := by
  unfold PLeaTTa.pull
  rw [empty]
  cases conf.barriers <;>
    simp [PLeaTTa.pullAuxTracked, PLeaTTa.pullAuxCached,
      PLeaTTa.pullAux]

/-! ## Rooted source/fine coupling -/

/-- The exact facts needed to close a post-cut scheduled state at the root.

Every condition is a field of the live carrier.  In particular there is no
replacement clause occurrence or retained cursor. -/
structure RootCommittedScheduledAnswerReady
    (before : RepresentativePersistentFreeCommittedScheduledPayloadState) :
    Prop where
  callerReferencesEmpty : before.carrier.index.callerReferences = []
  contextEmpty : before.carrier.index.context = []
  resourcesEmpty : before.carrier.index.resources = []
  baseAltsEmpty : before.carrier.index.baseAlts = []
  fineHead :
    before.carrier.index.openConf.toConf.cur =
      some ([], before.carrier.index.runtime)
  rootFrames : before.carrier.index.openConf.frames = []

/-- Exact root-to-terminal correspondence for one successful committed
predicate answer.

The independent source needs three transitions because its exhausted right
branch remains explicit.  The fine machine takes one answer-and-pull step;
the empty executable bank makes that successor globally terminal. -/
structure RootCommittedScheduledTerminalRelates
    (prog : Prog) (gt : Metta.GroundingTable)
    (before : RepresentativePersistentFreeCommittedScheduledPayloadState)
    (ready : RootCommittedScheduledAnswerReady before) : Prop where
  sourceRun :
    StepsN 3 before.carrier.sourceState
      [.answer before.carrier.index.current, .completed]
      (.terminal before.carrier.index.session .completed)
  fineStep :
    DemandDrivenCallStep.Step prog gt before.carrier.fineState
      (.ready
        (privateAnswerTarget before.carrier.index.openConf
          before.carrier.index.runtime))
  fineRun :
    DemandDrivenCallStep.StepsN prog gt 1 before.carrier.fineState
      (.ready
        (privateAnswerTarget before.carrier.index.openConf
          before.carrier.index.runtime))
  fineTerminal :
    DemandDrivenStep.Terminal
      (privateAnswerTarget before.carrier.index.openConf
        before.carrier.index.runtime)
  publicAnswerExact :
    publicAnswers
        (privateAnswerTarget before.carrier.index.openConf
          before.carrier.index.runtime) =
      publicAnswers before.carrier.index.openConf ++
        [subst before.carrier.index.runtime
          before.carrier.index.openConf.control.qterm]
  persistentExact :
    (privateAnswerTarget before.carrier.index.openConf
      before.carrier.index.runtime).persistent =
        before.carrier.index.openConf.persistent
  scopesExact :
    (privateAnswerTarget before.carrier.index.openConf
      before.carrier.index.runtime).scopes =
        before.carrier.index.openConf.scopes

namespace RootCommittedScheduledAnswerReady

/-- Construct the exact rooted terminal run from the live post-cut carrier. -/
theorem complete
    {prog : Prog} {gt : Metta.GroundingTable}
    {before : RepresentativePersistentFreeCommittedScheduledPayloadState}
    (ready : RootCommittedScheduledAnswerReady before) :
    RootCommittedScheduledTerminalRelates prog gt before ready := by
  have sourceExact :
      before.carrier.index.source =
        committedScheduledSourceProductAt
          before.carrier.index.callerScope
          before.carrier.index.predicateScope
          before.carrier.index.current [] := by
    rw [before.carrier.agreement.sourceShape, ready.contextEmpty,
      ready.callerReferencesEmpty]
    rfl
  have sourceRun :
      StepsN 3 before.carrier.sourceState
        [.answer before.carrier.index.current, .completed]
        (.terminal before.carrier.index.session .completed) := by
    simpa [PersistentFreeCommittedScheduledPayloadState.sourceState,
      sourceExact] using
      committedScheduledSourceProductAt_complete
        before.carrier.index.session before.carrier.index.callerScope
        before.carrier.index.predicateScope before.carrier.index.current
  have fineAlts : before.carrier.index.openConf.control.alts = [] := by
    rw [before.carrier.agreement.actualAlts, ready.resourcesEmpty,
      ready.baseAltsEmpty]
    rfl
  have publicOwner : PublicAnswerOwner before.carrier.index.openConf.frames := by
    rw [ready.rootFrames]
    exact publicAnswerOwner_nil
  have openStepAndAnswer :=
    answer_is_one_public_step prog gt before.carrier.index.openConf
      before.carrier.index.runtime publicOwner ready.fineHead
  have notLocalCall :
      ¬ DemandDrivenCallStep.LocalResolveHead before.carrier.index.openConf := by
    intro hLocal
    rcases hLocal with
      ⟨f, args, res, rest, binding, head, _nonempty, _arity⟩
    rw [ready.fineHead] at head
    simp at head
  have fineStep :
      DemandDrivenCallStep.Step prog gt before.carrier.fineState
        (.ready
          (privateAnswerTarget before.carrier.index.openConf
            before.carrier.index.runtime)) := by
    exact .ordinary _ _ notLocalCall openStepAndAnswer.1
  have fineRun :
      DemandDrivenCallStep.StepsN prog gt 1 before.carrier.fineState
        (.ready
          (privateAnswerTarget before.carrier.index.openConf
            before.carrier.index.runtime)) := by
    simpa using
      DemandDrivenCallStep.StepsN.succ 0 before.carrier.fineState
        (.ready
          (privateAnswerTarget before.carrier.index.openConf
            before.carrier.index.runtime))
        (.ready
          (privateAnswerTarget before.carrier.index.openConf
            before.carrier.index.runtime))
        fineStep (.zero _)
  have targetEmpty :
      (privateAnswerTarget before.carrier.index.openConf
        before.carrier.index.runtime).control.cur = none ∧
      (privateAnswerTarget before.carrier.index.openConf
        before.carrier.index.runtime).control.alts = [] := by
    let answered : PLeaTTa.Conf :=
      { before.carrier.index.openConf.toConf with
        cur := none
        answers :=
          subst before.carrier.index.runtime
              before.carrier.index.openConf.toConf.qterm ::
            before.carrier.index.openConf.toConf.answers
        answerKeys :=
          PLeaTTa.PersistentSubst.atomExactKey
                (subst before.carrier.index.runtime
                  before.carrier.index.openConf.toConf.qterm) ::
            before.carrier.index.openConf.toConf.answerKeys
        answerKeys_sound := by
          simp only [List.map_cons]
          rw [before.carrier.index.openConf.toConf.answerKeys_sound] }
    have answeredAlts : answered.alts = [] := by
      simpa [answered, OpenConf.toConf, Control.toConf] using fineAlts
    have pulledEmpty := pull_empty_fields answered answeredAlts
    simpa [privateAnswerTarget, answerSuccessor, answered,
      OpenConf.stepOpen, OpenConf.ofConfWith, controlOf] using pulledEmpty
  have fineTerminal :
      DemandDrivenStep.Terminal
        (privateAnswerTarget before.carrier.index.openConf
          before.carrier.index.runtime) := by
    refine ⟨?_, ?_⟩
    · exact targetEmpty
    · simpa using ready.rootFrames
  exact
    { sourceRun := sourceRun
      fineStep := fineStep
      fineRun := fineRun
      fineTerminal := fineTerminal
      publicAnswerExact := openStepAndAnswer.2
      persistentExact := by simp
      scopesExact := by simp }

end RootCommittedScheduledAnswerReady

end PLeaTTa.PrologCommittedScheduledTerminalBridge
