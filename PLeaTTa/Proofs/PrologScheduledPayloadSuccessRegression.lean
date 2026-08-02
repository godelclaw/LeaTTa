-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologScheduledPayloadSuccessRegression
Purpose: Reject stuttering and hidden-head readings of the paired scheduled
  retained-head success transition.
Trusted boundary: none
-/
import PLeaTTa.Proofs.PrologScheduledPayloadSuccessBridge

namespace PLeaTTa.PrologScheduledPayloadSuccessRegression

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PrologActivatedProductStepBridge
open PrologBodyFailureOuterResourceCatchupBridge
open PrologBodyFailureResourceTransitionBridge
open PrologHeterogeneousPrefixBridge
open PrologRootClosedAnswerBridge
open PrologRepresentativeProductActivationBridge
open PrologScheduledHistoryBuildBridge
open PrologScheduledPayloadLandingBridge
open PrologScheduledPayloadPostHeadBridge
open PrologScheduledPayloadRejectionBridge
open PrologScheduledPayloadRejectionBridge.ScheduledSelectedHeadTransition
open PrologScheduledPayloadSuccessBridge
open PrologSourceProductContextBridge

/-- Successful head activation contributes one real source transition after
all scheduled-history, outer-resource, and internal-rejection catch-up. -/
theorem selected_success_cost_is_strictly_additive
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session)
    (partition : RootPayloadPartition before) :
    postAnswerSuccessfulHeadCount ready transition partition =
        ready.result.historyBuild.cells.length +
          (partition.rejectionSteps + partition.crossedFrames.length + 1) +
          transition.frontier.rejectedCount + 1 ∧
      postAnswerSuccessfulHeadCount ready transition partition ≠
        ready.result.historyBuild.cells.length +
          (partition.rejectionSteps + partition.crossedFrames.length + 1) +
          transition.frontier.rejectedCount := by
  constructor
  · rfl
  · simp [postAnswerSuccessfulHeadCount]

/-- The executable success step cannot stutter: it removes the selected
full-head equality from `cur` before installing the cumulative MGU. -/
theorem successful_fine_step_is_not_stutter
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session)
    (installed : Metta.Subst) :
    successfulFineState transition installed ≠ selectedFineState before := by
  intro equality
  have currentEquality :=
    congrArg (fun state : DemandDrivenStep.OpenConf => state.control.cur)
      equality
  have selectedCurrent :=
    PLeaTTa.PrologScheduledPayloadOpenConfBridge.ScheduledSelectedHeadTransition.fineCurrentExact
      transition
  have selectedCurrentAtState :
      (selectedFineState before).control.cur =
        some
          (PLeaTTa.Goal.eq
                (.expr
                  (selection.selected.resource.args ++
                    [selection.selected.resource.res]))
                (.expr
                  (transition.copied.params ++ [transition.copied.result])) ::
              transition.copied.body ++ selection.selected.resource.rest,
            selection.selected.resource.binding) := by
    simpa [selectedFineState] using selectedCurrent
  rw [successfulFineState,
    PrologOrdinaryStepBridge.unifySuccessor_current,
    selectedCurrentAtState] at currentEquality
  have goalsEquality := congrArg (fun item => item.1)
    (Option.some.inj currentEquality)
  have lengths := congrArg List.length goalsEquality
  simp at lengths

/-- The source success step is structurally different from the selected
ready frontier: it installs an active left clause body and retained right
cursor under the predicate cut boundary.  Arbitrary outer frames cannot hide
that change. -/
theorem successful_source_step_is_not_stutter
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session)
    (independentResult : Substitution) :
    successfulSourceFrontier transition independentResult ≠
      sourceFrontier transition transition.finish := by
  intro equality
  have inner :=
    ActiveProductContext.plug_injective transition.postLaterContext equality
  simp [sourceFrame, frameRetainedFrontier, activeSourceProduct,
    selectedOpened] at inner

/-- Any inhabited paired result exposes genuine source and fine transitions
and both literal endpoints reject a stuttering interpretation. -/
theorem paired_success_exposes_both_real_steps
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    {transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session}
    {partition : RootPayloadPartition before}
    {independentResult : Substitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattened : Canonical.TreeSubstitution}
    {installed : Metta.Subst}
    (relation :
      ScheduledSuccessfulHeadRelates prog gt before ready selection scope
        transition partition independentResult nextAlpha sourceCanonical
        flattened installed) :
    RawStep before.carrier.index.session
        (sourceFrontier transition transition.finish) [] .none
        before.carrier.index.session
        (.running (successfulSourceFrontier transition independentResult)) ∧
      DemandDrivenCallStep.Step prog gt (.ready (selectedFineState before))
        (.ready (successfulFineState transition installed)) ∧
      successfulSourceFrontier transition independentResult ≠
        sourceFrontier transition transition.finish ∧
      successfulFineState transition installed ≠ selectedFineState before := by
  exact
    ⟨relation.sourceActivation, relation.fineStep,
      successful_source_step_is_not_stutter transition independentResult,
      successful_fine_step_is_not_stutter transition installed⟩

end PLeaTTa.PrologScheduledPayloadSuccessRegression
