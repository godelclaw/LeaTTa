-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologScheduledAnswerValueBridge
Purpose: Relate one scheduled independent answer's query denotation to the
  exact public executable answer appended by the fine machine
Trusted boundary: none
Main exports: RepresentativePersistentFreeScheduledPayloadState.answerValueAgrees,
  RootClosedPublicAnswerRelates,
  RootClosedLocalLivePublicAnswerRelates,
  RootClosedAnswerReady.withPublicAnswer,
  RootClosedLocalLiveAnswerRelates.withPublicAnswer
-/
import PLeaTTa.Proofs.PrologAnswerValueBridge
import PLeaTTa.Proofs.PrologRootClosedLocalLiveBridge

namespace PLeaTTa.PrologScheduledAnswerValueBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open CompilerAdequacy
open DemandDrivenStep
open PrologAnswerValueBridge
open PrologFindallCopyBridge
open PrologHeterogeneousPrefixBridge
open PrologMguBridge
open PrologMguComposition
open PrologOrdinaryStepBridge
open PrologPersistentFreeScheduledPayloadBridge
open PrologRecursiveCallPayloadBridge
open PrologRootClosedAnswerBridge
open PrologRootClosedLocalLiveBridge
open PrologScheduledPayloadResumeBridge
open PrologStateBridge

namespace RepresentativePersistentFreeScheduledPayloadState

/-- The scheduled representative's existing task invariant, exposed under a
stable name instead of making observation proofs depend on the nested product
payload projection path.  No new existential representative is selected. -/
theorem taskData (state : RepresentativePersistentFreeScheduledPayloadState) :
    TaskDataAgrees state.carrier.index.alpha state.carrier.index.support
      state.carrier.index.canonical state.carrier.index.referenceBase
      state.carrier.index.current state.carrier.index.runtime :=
  state.carrier.headPayload.data

/-- Package an explicit source/runtime query spelling with the task invariant
already carried by the scheduled state. -/
theorem answerValueProducer
    (state : RepresentativePersistentFreeScheduledPayloadState)
    {sourceQuery : Term} {runtimeQuery : Atom}
    (queryAgreement :
      AlphaTermAgrees state.carrier.index.alpha sourceQuery runtimeQuery)
    (querySupported :
      AlphaTermsSupported state.carrier.index.alpha
        state.carrier.index.support [sourceQuery]) :
    AnswerValueProducerAgrees state.carrier.index.alpha
      state.carrier.index.support state.carrier.index.current
      state.carrier.index.runtime sourceQuery runtimeQuery :=
  AnswerValueProducerAgrees.ofTaskData
    (RepresentativePersistentFreeScheduledPayloadState.taskData state) queryAgreement
    querySupported

/-- The live cumulative substitutions materialize an explicitly related query
to runtime-alpha-equivalent source and executable values.  This is a value
theorem only; the public answer step is coupled below. -/
theorem answerValueAgrees
    (state : RepresentativePersistentFreeScheduledPayloadState)
    {sourceQuery : Term} {runtimeQuery : Atom}
    (queryAgreement :
      AlphaTermAgrees state.carrier.index.alpha sourceQuery runtimeQuery)
    (querySupported :
      AlphaTermsSupported state.carrier.index.alpha
        state.carrier.index.support [sourceQuery]) :
    RuntimeTermAgrees
      (state.carrier.index.current.applyTerm sourceQuery)
      (PLeaTTa.subst state.carrier.index.runtime runtimeQuery) :=
  (RepresentativePersistentFreeScheduledPayloadState.answerValueProducer state
    queryAgreement querySupported).runtimeTermAgrees

end RepresentativePersistentFreeScheduledPayloadState

/-- Exact source-answer/value/public-executable coupling at the rooted
pre-pull boundary.

The source first absorbs every empty private caller frame, then emits its
literal current substitution once.  The fine machine takes its real sealed
answer-and-pull step and appends the materialized executable query value to
the public accumulator.  Whether that pull selects another local branch or
falls through is deliberately not part of this relation. -/
structure RootClosedPublicAnswerRelates
    (sourceQuery : Term)
    (prog : Prog) (gt : Metta.GroundingTable)
    (before : RepresentativePersistentFreeScheduledPayloadState)
    (ready : RootClosedAnswerReady before) : Prop where
  sourceBindingExact :
    ready.result.history.bindings = before.carrier.index.current
  sourceRun :
    PeTTaSpec.PrologCore.GoalSemantics.StepsN
      (before.carrier.index.outer.length + 1)
      before.carrier.sourceState
      [.answer before.carrier.index.current]
      (.running before.carrier.index.session ready.result.targetNext)
  fineStep :
    DemandDrivenStep.Step prog gt before.carrier.index.openConf
      (privateAnswerTarget before.carrier.index.openConf
        before.carrier.index.runtime)
  queryAgreement :
    AlphaTermAgrees before.carrier.index.alpha sourceQuery
      before.carrier.index.openConf.control.qterm
  querySupported :
    AlphaTermsSupported before.carrier.index.alpha
      before.carrier.index.support [sourceQuery]
  publicOwner : PublicAnswerOwner before.carrier.index.openConf.frames
  valueAgreement :
    RuntimeTermAgrees
      (before.carrier.index.current.applyTerm sourceQuery)
      (PLeaTTa.subst before.carrier.index.runtime
        before.carrier.index.openConf.control.qterm)
  publicAnswer :
    publicAnswers
        (privateAnswerTarget before.carrier.index.openConf
          before.carrier.index.runtime) =
      publicAnswers before.carrier.index.openConf ++
        [PLeaTTa.subst before.carrier.index.runtime
          before.carrier.index.openConf.control.qterm]

namespace RootClosedAnswerReady

/-- Construct the rooted public answer relation from the existing scheduled
task invariant and structural public-answer ownership. -/
theorem withPublicAnswer
    {sourceQuery : Term}
    {prog : Prog} {gt : Metta.GroundingTable}
    {before : RepresentativePersistentFreeScheduledPayloadState}
    (ready : RootClosedAnswerReady before)
    (queryAgreement :
      AlphaTermAgrees before.carrier.index.alpha sourceQuery
        before.carrier.index.openConf.control.qterm)
    (querySupported :
      AlphaTermsSupported before.carrier.index.alpha
        before.carrier.index.support [sourceQuery])
    (publicOwner : PublicAnswerOwner before.carrier.index.openConf.frames) :
    RootClosedPublicAnswerRelates sourceQuery prog gt before ready := by
  have sourceBindingExact :
      ready.result.history.bindings = before.carrier.index.current := by
    simpa using ready.result.bindingsExact
  have absorption := ready.sourceSteps
  rw [← ready.result.targetSourceExact] at absorption
  have answerTransition :
      Transition
        (.running before.carrier.index.session ready.result.targetSource)
        [.answer ready.result.history.bindings]
        (.running before.carrier.index.session ready.result.targetNext) :=
    .ordinary _ _ _ _ _
      (ready.result.history.sourceStep before.carrier.index.session)
  have answerRun :
      PeTTaSpec.PrologCore.GoalSemantics.StepsN 1
        (.running before.carrier.index.session ready.result.targetSource)
        [.answer ready.result.history.bindings]
        (.running before.carrier.index.session ready.result.targetNext) := by
    simpa using
      (PeTTaSpec.PrologCore.GoalSemantics.StepsN.succ 0 _ _ _
        [.answer ready.result.history.bindings] [] answerTransition
        (.zero _))
  have sourceRunRaw :=
    PeTTaSpec.PrologCore.GoalSemantics.StepsN.trans absorption answerRun
  have sourceRun :
      PeTTaSpec.PrologCore.GoalSemantics.StepsN
        (before.carrier.index.outer.length + 1)
        before.carrier.sourceState
        [.answer before.carrier.index.current]
        (.running before.carrier.index.session ready.result.targetNext) := by
    simpa [sourceBindingExact] using sourceRunRaw
  have publicStep :=
    answer_is_one_public_step prog gt before.carrier.index.openConf
      before.carrier.index.runtime publicOwner ready.fineHead
  exact
    { sourceBindingExact := sourceBindingExact
      sourceRun := sourceRun
      fineStep := publicStep.1
      queryAgreement := queryAgreement
      querySupported := querySupported
      publicOwner := publicOwner
      valueAgreement :=
        RepresentativePersistentFreeScheduledPayloadState.answerValueAgrees before
          queryAgreement querySupported
      publicAnswer := publicStep.2 }

end RootClosedAnswerReady

/-- Exact source-value/public-executable-observation coupling for one rooted
locally live answer.

The independent query is explicit because compiler query production belongs
to the later source-composition theorem, not to the scheduler carrier.  Empty
fine frames are load-bearing: they make this answer public rather than a
private findall-generator answer.  Both the value relation and public append
are derived by `RootClosedLocalLiveAnswerRelates.withObservedAnswer`; callers
do not provide either to that constructor. -/
structure RootClosedLocalLivePublicAnswerRelates
    (sourceQuery : Term)
    (prog : Prog) (gt : Metta.GroundingTable)
    (before : RepresentativePersistentFreeScheduledPayloadState)
    (ready : RootClosedAnswerReady before)
    (selectedGoals : List PLeaTTa.Goal) (selectedBinding : Subst)
    (selectedTail : List PLeaTTa.Alt)
    (count : Nat) (target : Search) : Prop where
  control :
    RootClosedLocalLiveAnswerRelates prog gt before ready selectedGoals
      selectedBinding selectedTail count target
  framesEmpty : before.carrier.index.openConf.frames = []
  rootAnswer : RootClosedPublicAnswerRelates sourceQuery prog gt before ready

namespace RootClosedLocalLiveAnswerRelates

/-- Add exact source-value and public-observation content to an already
coupled rooted control step.  The scheduled task invariant derives the value;
the actual sealed answer step plus an empty frame stack derives the append. -/
theorem withPublicAnswer
    {sourceQuery : Term}
    {prog : Prog} {gt : Metta.GroundingTable}
    {before : RepresentativePersistentFreeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
    {selectedTail : List PLeaTTa.Alt}
    {count : Nat} {target : Search}
    (control :
      RootClosedLocalLiveAnswerRelates prog gt before ready selectedGoals
        selectedBinding selectedTail count target)
    (queryAgreement :
      AlphaTermAgrees before.carrier.index.alpha sourceQuery
        before.carrier.index.openConf.control.qterm)
    (querySupported :
      AlphaTermsSupported before.carrier.index.alpha
        before.carrier.index.support [sourceQuery])
    (framesEmpty : before.carrier.index.openConf.frames = []) :
    RootClosedLocalLivePublicAnswerRelates sourceQuery prog gt before ready
      selectedGoals selectedBinding selectedTail count target := by
  have publicOwner :
      PublicAnswerOwner before.carrier.index.openConf.frames := by
    rw [framesEmpty]
    exact publicAnswerOwner_nil
  have publicRelation :=
    PLeaTTa.PrologScheduledAnswerValueBridge.RootClosedAnswerReady.withPublicAnswer
      (prog := prog) (gt := gt) ready queryAgreement querySupported publicOwner
  exact
    { control := control
      framesEmpty := framesEmpty
      rootAnswer := publicRelation }

end RootClosedLocalLiveAnswerRelates

end PLeaTTa.PrologScheduledAnswerValueBridge
