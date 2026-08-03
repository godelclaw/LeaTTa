-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologScheduledPayloadRejectionRegression
Purpose: Reject stuttering and off-by-one readings of the paired scheduled
  retained-head failure transition.
Trusted boundary: none
-/
import PLeaTTa.Proofs.PrologScheduledPayloadRejectionBridge

namespace PLeaTTa.PrologScheduledPayloadRejectionRegression

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.Resolver
open PrologBodyFailureExhaustedResourceTransitionBridge
open PrologBodyFailureOuterResourceCatchupBridge
open PrologBodyFailureResourceTransitionBridge
open PrologHeterogeneousPrefixBridge
open PrologPersistentFreeScheduledPayloadBridge
open PrologRootClosedAnswerBridge
open PrologScheduledHistoryBuildBridge
open PrologScheduledPayloadLandingBridge
open PrologScheduledPayloadPostHeadBridge
open PrologScheduledPayloadRejectionBridge
open PrologScheduledPayloadRejectionBridge.ScheduledSelectedHeadTransition

/-- Consuming the selected head cannot stutter at the same source cursor.
The proof observes the literal remaining-clause list, whose head is removed
by `PreparedCursor.advance`. -/
theorem selected_head_advance_is_not_stutter
    {before : RepresentativePersistentFreeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session) :
    transition.finish.advance transition.branch transition.branchTail ≠
      transition.finish := by
  intro equality
  have remainingEquality :=
    congrArg PreparedCursor.remaining equality
  simp [PreparedCursor.advance, transition.offset.cursorRemaining] at remainingEquality

/-- Nor can an arbitrary outer product stack hide that cursor advance.  This
is the source-endpoint discriminator for the composed theorem. -/
theorem selected_head_advance_changes_source_frontier
    {before : RepresentativePersistentFreeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session) :
    sourceFrontier transition
        (transition.finish.advance transition.branch transition.branchTail) ≠
      sourceFrontier transition transition.finish := by
  intro equality
  have inner :=
    ActiveProductContext.plug_injective transition.postLaterContext equality
  have cursorEquality :
      transition.finish.advance transition.branch transition.branchTail =
        transition.finish := by
    simpa [sourceFrontier, sourceFrame, frameRetainedFrontier] using inner
  exact selected_head_advance_is_not_stutter transition cursorEquality

/-- The selected-head rejection contributes one real source transition in
addition to every pre-selection rejected pull.  Omitting it is a strict
off-by-one error even when every earlier prefix is empty. -/
theorem selected_failure_cost_is_strictly_additive
    {before : RepresentativePersistentFreeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session)
    (partition : RootPayloadPartition before) :
    postAnswerRejectedHeadCount ready transition partition =
        ready.result.historyBuild.cells.length +
          (partition.rejectionSteps + partition.crossedFrames.length + 1) +
          transition.frontier.rejectedCount + 1 ∧
      postAnswerRejectedHeadCount ready transition partition ≠
        ready.result.historyBuild.cells.length +
          (partition.rejectionSteps + partition.crossedFrames.length + 1) +
          transition.frontier.rejectedCount := by
  constructor
  · rfl
  · simp [postAnswerRejectedHeadCount]

/-- Any inhabited paired result therefore contains genuine transitions on
both lanes and ends at the non-stuttering advanced source frontier. -/
theorem paired_rejection_exposes_both_real_steps
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativePersistentFreeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    {transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session}
    {partition : RootPayloadPartition before}
    (relation :
      ScheduledRejectedHeadRelates prog gt before ready selection scope
        transition partition) :
    PeTTaSpec.PrologCore.GoalSemantics.StepsN
        (postAnswerRejectedHeadCount ready transition partition)
        (.running before.carrier.index.session ready.result.targetNext) []
        (.running before.carrier.index.session
          (sourceFrontier transition
            (transition.finish.advance transition.branch
              transition.branchTail))) ∧
      DemandDrivenCallStep.Step prog gt (.ready (selectedFineState before))
        (.ready (rejectedFineState before)) ∧
      sourceFrontier transition
          (transition.finish.advance transition.branch
            transition.branchTail) ≠
        sourceFrontier transition transition.finish := by
  exact
    ⟨relation.postAnswerSourceRun, relation.fineStep,
      selected_head_advance_changes_source_frontier transition⟩

/-- Whenever the second eager pull changes the residual barrier count, its
enabled cache cannot be the stale post-answer cache.  The premise is
deliberately conditional: selecting an adjacent branch need not cross a
barrier, while crossing an exhausted resource does. -/
theorem changed_rejection_barrier_count_rejects_stale_cache
    {before : RepresentativePersistentFreeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session)
    (cache : before.carrier.index.openConf.control.barriers =
      some
        (PLeaTTa.barrierCount
          before.carrier.index.openConf.control.alts))
    (changed :
      PLeaTTa.barrierCount (rejectedFineState before).control.alts ≠
        PLeaTTa.barrierCount (selectedFineState before).control.alts) :
    (rejectedFineState before).control.barriers ≠
      (selectedFineState before).control.barriers := by
  have selectedCache :
      (selectedFineState before).control.barriers =
        some
          (PLeaTTa.barrierCount
            (selectedFineState before).control.alts) := by
    simpa [selectedFineState] using
      (PLeaTTa.PrologScheduledPayloadOpenConfBridge.ScheduledSelectedHeadTransition.fineBarrierCacheExact
        transition cache)
  rw [ScheduledSelectedHeadTransition.rejectedFineBarrierCacheExact
    transition cache]
  rw [selectedCache]
  intro equality
  exact changed (Option.some.inj equality)

end PLeaTTa.PrologScheduledPayloadRejectionRegression
