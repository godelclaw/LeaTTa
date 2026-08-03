-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologScheduledPayloadRejectionBridge
Purpose: Pair the first post-answer retained-head rejection with the exact
  scheduled source frontier and real fine executable transition.
Trusted boundary: none
Main exports:
  ScheduledSelectedHeadTransition.postAnswerToSelectedReady,
  ScheduledRejectedHeadRelates,
  ScheduledSelectedHeadTransition.rejectHead
-/
import PLeaTTa.Proofs.PrologScheduledPayloadOpenConfBridge
import PLeaTTa.Proofs.PrologActivationFailureBridge
import PLeaTTa.Proofs.PrologBodyFailureOuterResourceCatchupBridge
import PLeaTTa.Proofs.PrologOrdinaryStepBridge

namespace PLeaTTa.PrologScheduledPayloadRejectionBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologActivationFailureBridge
open PrologAnswerSourceCatchupBridge
open PrologBodyFailureExhaustedResourceTransitionBridge
open PrologBodyFailureOuterResourceCatchupBridge
open PrologBodyFailureResourceTransitionBridge
open PrologFindallAnswerResourceBridge
open PrologPrefilterScanBridge
open PrologProductResourceContextBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRootClosedAnswerBridge
open PrologScheduledHistoryBuildBridge
open PrologScheduledPayloadLandingBridge
open PrologScheduledPayloadOpenConfBridge
open PrologScheduledPayloadPathBridge
open PrologScheduledPayloadPostHeadBridge
open PrologSourceProductContextBridge

namespace ScheduledSelectedHeadTransition

/-- The exact predicate frame selected by the scheduled payload coordinate,
with an explicitly supplied current cursor.

The delimiter labels and caller continuation come only from the selected
Type-valued payload cell; callers may vary the cursor only. -/
def sourceFrame
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List PrologControlSegmentSpineBridge.ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : ActiveProductContext}
    {payload :
      PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
        alpha support qterm currentBarrier segments resources inner context
        outer}
    {source next : Search}
    {history : PrologScheduledAnswerPropagationBridge.ScheduledAnswerHistory
      alpha source next}
    {build : ScheduledHistoryBuild history}
    {alignment : ScheduledPayloadAlignment payload build}
    {selection : ScheduledLocalSelection build.cells}
    {scope : CutScopeId} {session : Session}
    (transition :
      ScheduledSelectedHeadTransition alignment selection scope session) :
    ActiveProductFrame :=
  { callerScope := transition.selectedPayloadCell.nextScope
    predicateScope := transition.selectedPayloadCell.currentScope
    retained :=
      .clauses transition.selectedPayloadCell.currentScope
        selection.selected.cursor
    callerRest := transition.selectedPayloadCell.segment.references }

/-- Canonical source frontier at the selected scheduled predicate.

Every earlier scheduled cell has been consumed.  The exact later payload
context remains around the selected predicate, and no resource is represented
twice. -/
def sourceFrontier
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List PrologControlSegmentSpineBridge.ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : ActiveProductContext}
    {payload :
      PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
        alpha support qterm currentBarrier segments resources inner context
        outer}
    {source next : Search}
    {history : PrologScheduledAnswerPropagationBridge.ScheduledAnswerHistory
      alpha source next}
    {build : ScheduledHistoryBuild history}
    {alignment : ScheduledPayloadAlignment payload build}
    {selection : ScheduledLocalSelection build.cells}
    {scope : CutScopeId} {session : Session}
    (transition :
      ScheduledSelectedHeadTransition alignment selection scope session)
    (cursor : PreparedCursor) : Search :=
  ActiveProductContext.plug transition.postLaterContext
    (frameRetainedFrontier (sourceFrame transition) cursor)

/-- Exact source-only catch-up from the answer successor to the selected
retained clause occurrence.

The three summands are intentionally not fused:

* `build.cells.length` peels the privately scheduled answer choices;
* the ranked partition crosses earlier empty predicate resources;
* `frontier.rejectedCount` consumes conservative false positives inside the
  selected resource.

This theorem ends *before* consuming the selected head. -/
theorem postAnswerToSelectedReady
    {before :
      PrologHeterogeneousPrefixBridge.RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session)
    {partition :
      OuterResourceCatchupPartition before.carrier.index.alpha
        ({ barrier := before.carrier.index.callerBarrier
           references := before.carrier.index.callerReferences
           executables := before.carrier.index.callerExecutables } ::
          before.carrier.index.outer)
        (before.carrier.index.active :: before.carrier.index.resources)
        ({ callerScope := before.carrier.index.callerScope
           predicateScope := before.carrier.index.predicateScope
           retained :=
             .clauses before.carrier.index.predicateScope
               (before.carrier.index.finish.advance
                 before.carrier.index.branch before.carrier.index.branchTail)
           callerRest := before.carrier.index.callerReferences } ::
          before.carrier.index.context)}
    (partitionExact :
      PrologScheduledPayloadPostHeadBridge.ScheduledSelectedHeadTransition.PartitionAgrees
        transition partition) :
    PeTTaSpec.PrologCore.GoalSemantics.StepsN
      (ready.result.historyBuild.cells.length +
        (partition.rejectionSteps + partition.crossedFrames.length + 1) +
        transition.frontier.rejectedCount)
      (.running before.carrier.index.session ready.result.targetNext)
      []
      (.running before.carrier.index.session
        (sourceFrontier transition transition.finish)) := by
  have historySilent :=
    ready.result.historyBuild.next_to_activeContext_done
      before.carrier.index.session
  have historySteps := historySilent.toStepsN
  have historyContext :
      ready.result.historyBuild.activeContext =
        { callerScope := before.carrier.index.callerScope
          predicateScope := before.carrier.index.predicateScope
          retained :=
            .clauses before.carrier.index.predicateScope
              (before.carrier.index.finish.advance before.carrier.index.branch
                before.carrier.index.branchTail)
          callerRest := before.carrier.index.callerReferences } ::
        before.carrier.index.context :=
    ready.historyContext_eq_fullContext
  have partitionContext :
      ({ callerScope := before.carrier.index.callerScope
         predicateScope := before.carrier.index.predicateScope
         retained :=
           .clauses before.carrier.index.predicateScope
             (before.carrier.index.finish.advance before.carrier.index.branch
               before.carrier.index.branchTail)
         callerRest := before.carrier.index.callerReferences } :
          ActiveProductFrame) ::
          before.carrier.index.context =
        partition.crossedFrames ++
          partition.firstFrame :: partition.survivingContext :=
    partition.contextEq
  have completed :
      RawStep before.carrier.index.session .done [.completed] .none
        before.carrier.index.session (.terminal .completed) :=
    .done before.carrier.index.session
  have crossed :=
    PLeaTTa.PrologBodyFailureOuterResourceCatchupBridge.CrossedEmptyResourceFramesAgrees.sourceCatchupToFrame
      partition.crossedWork
      before.carrier.index.session .done completed partition.firstFrame
      partition.survivingContext partition.firstCursor
      partition.firstRetainedShape
  have historyToCrossed :
      PeTTaSpec.PrologCore.GoalSemantics.StepsN
        (ready.result.historyBuild.cells.length +
          (partition.rejectionSteps + partition.crossedFrames.length + 1))
        (.running before.carrier.index.session ready.result.targetNext)
        []
        (.running before.carrier.index.session
          (firstLiveSourceFrontier partition)) := by
    have historyRewritten :
        StepsN ready.result.historyBuild.cells.length
          (.running before.carrier.index.session ready.result.targetNext) []
          (.running before.carrier.index.session
            (ActiveProductContext.plug
              (partition.crossedFrames ++
                partition.firstFrame :: partition.survivingContext)
              .done)) := by
      simpa [historyContext, partitionContext] using historySteps
    exact historyRewritten.trans crossed
  have rejected :=
    PLeaTTa.PrologBodyFailureOuterResourceCatchupBridge.RejectedPullsN.frameRetainedFrontierContextStepsN
      transition.frontier.rejectedPulls
      partition.survivingContext partition.firstFrame
      before.carrier.index.session
  have rejectedExact :
      PeTTaSpec.PrologCore.GoalSemantics.StepsN
        transition.frontier.rejectedCount
        (.running before.carrier.index.session
          (firstLiveSourceFrontier partition)) []
        (.running before.carrier.index.session
          (sourceFrontier transition transition.finish)) := by
    simpa [firstLiveSourceFrontier, sourceFrontier,
      partitionExact.firstFrameExact, partitionExact.firstCursorExact,
      partitionExact.survivingContextExact, sourceFrame] using rejected
  exact historyToCrossed.trans rejectedExact

end ScheduledSelectedHeadTransition

/-! ## One real scheduled rejected-head transition -/

/-- The source catch-up partition indexed by a rooted scheduled payload.

Naming this dependent type once keeps the actual active cell in the
partition: current caller references, selected resource, and selected frame
are not erased to the older-only context. -/
abbrev RootPayloadPartition
    (before :
      PrologHeterogeneousPrefixBridge.RepresentativeScheduledPayloadState) :=
  OuterResourceCatchupPartition before.carrier.index.alpha
    ({ barrier := before.carrier.index.callerBarrier
       references := before.carrier.index.callerReferences
       executables := before.carrier.index.callerExecutables } ::
      before.carrier.index.outer)
    (before.carrier.index.active :: before.carrier.index.resources)
    ({ callerScope := before.carrier.index.callerScope
       predicateScope := before.carrier.index.predicateScope
       retained :=
         .clauses before.carrier.index.predicateScope
           (before.carrier.index.finish.advance before.carrier.index.branch
             before.carrier.index.branchTail)
       callerRest := before.carrier.index.callerReferences } ::
      before.carrier.index.context)

/-- Exact number of source transitions after the answer observation and
through rejection of the selected retained head. -/
def postAnswerRejectedHeadCount
    {before :
      PrologHeterogeneousPrefixBridge.RepresentativeScheduledPayloadState}
    (ready : RootClosedAnswerReady before)
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session)
    (partition : RootPayloadPartition before) : Nat :=
  ready.result.historyBuild.cells.length +
    (partition.rejectionSteps + partition.crossedFrames.length + 1) +
    transition.frontier.rejectedCount + 1

/-- The fine state after the real answer transition has eagerly selected the
next locally owned clause occurrence. -/
def selectedFineState
    (before :
      PrologHeterogeneousPrefixBridge.RepresentativeScheduledPayloadState) :
    OpenConf :=
  privateAnswerTarget before.carrier.index.openConf before.carrier.index.runtime

/-- The real fine successor of rejecting that selected occurrence. -/
def rejectedFineState
    (before :
      PrologHeterogeneousPrefixBridge.RepresentativeScheduledPayloadState) :
    OpenConf :=
  PrologOrdinaryStepBridge.unifyFailureSuccessor (selectedFineState before)

/-- Full paired operational result for the first selected post-answer clause
whose complete head equality fails.

The independent lane has already emitted the previous answer.  It then
performs every administrative catch-up step and consumes exactly the selected
source occurrence.  The fine lane starts at the *actual* answer-and-pull
successor and takes the sealed equality-failure step. -/
structure ScheduledRejectedHeadRelates
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (before :
      PrologHeterogeneousPrefixBridge.RepresentativeScheduledPayloadState)
    (ready : RootClosedAnswerReady before)
    (selection : ScheduledLocalSelection ready.result.historyBuild.cells)
    (scope : CutScopeId)
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session)
    (partition : RootPayloadPartition before) : Prop where
  partitionExact :
    PrologScheduledPayloadPostHeadBridge.ScheduledSelectedHeadTransition.PartitionAgrees
      transition partition
  failure :
    RetainedHeadFailureAgrees transition.branch
      selection.selected.resource.args selection.selected.resource.res
      selection.selected.resource.rest selection.selected.resource.binding
      selection.selected.resource.qterm selection.selected.resource.counter
      selection.selected.resource.barrier transition.clause
  postAnswerSourceRun :
    PeTTaSpec.PrologCore.GoalSemantics.StepsN
      (postAnswerRejectedHeadCount ready transition partition)
      (.running before.carrier.index.session ready.result.targetNext) []
      (.running before.carrier.index.session
        (PrologScheduledPayloadRejectionBridge.ScheduledSelectedHeadTransition.sourceFrontier
          transition
          (transition.finish.advance transition.branch
            transition.branchTail)))
  fullSourceRun :
    PeTTaSpec.PrologCore.GoalSemantics.StepsN
      (before.carrier.index.outer.length + 1 +
        postAnswerRejectedHeadCount ready transition partition)
      before.carrier.sourceState
      [.answer before.carrier.index.current]
      (.running before.carrier.index.session
        (PrologScheduledPayloadRejectionBridge.ScheduledSelectedHeadTransition.sourceFrontier
          transition
          (transition.finish.advance transition.branch
            transition.branchTail)))
  fineStep :
    DemandDrivenCallStep.Step prog gt (.ready (selectedFineState before))
      (.ready (rejectedFineState before))
  finePersistent :
    (rejectedFineState before).persistent =
      (selectedFineState before).persistent
  fineFrames :
    (rejectedFineState before).frames = (selectedFineState before).frames
  fineScopes :
    (rejectedFineState before).scopes = (selectedFineState before).scopes
  fineAnswers :
    (rejectedFineState before).control.answers =
      (selectedFineState before).control.answers

namespace ScheduledSelectedHeadTransition

/-- If the original answer state uses the enabled exact barrier cache, the
selected-answer pull and the subsequent selected-head rejection each update
that cache to their own literal residual banks.

The conclusion names the actual `unifyFailureSuccessor`; it does not inherit
the post-answer depth or choose a compatible alternative suffix. -/
theorem rejectedFineBarrierCacheExact
    {before :
      PrologHeterogeneousPrefixBridge.RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session)
    (cache : before.carrier.index.openConf.control.barriers =
      some
        (PLeaTTa.barrierCount
          before.carrier.index.openConf.control.alts)) :
    (rejectedFineState before).control.barriers =
      some (PLeaTTa.barrierCount (rejectedFineState before).control.alts) := by
  apply PrologOrdinaryStepBridge.unifyFailureSuccessor_barrierCacheExact
  exact
    PLeaTTa.PrologScheduledPayloadOpenConfBridge.ScheduledSelectedHeadTransition.fineBarrierCacheExact
      transition cache

/-- Consume the exact selected post-answer head when both independent and
executable full-head unification reject it.

The partition is generated from the same Type-valued payload path as
`transition`; it is existential only because source catch-up evidence lives
in `Prop`.  No runtime state is chosen by eliminating that evidence. -/
theorem rejectHead
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before :
      PrologHeterogeneousPrefixBridge.RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session)
    (failure :
      RetainedHeadFailureAgrees transition.branch
        selection.selected.resource.args selection.selected.resource.res
        selection.selected.resource.rest selection.selected.resource.binding
        selection.selected.resource.qterm selection.selected.resource.counter
        selection.selected.resource.barrier transition.clause) :
    ∃ partition : RootPayloadPartition before,
      ScheduledRejectedHeadRelates prog gt before ready selection scope
        transition partition := by
  obtain ⟨partition, partitionExact⟩ :=
    PLeaTTa.PrologScheduledPayloadPostHeadBridge.ScheduledSelectedHeadTransition.partitionExact
      transition
  have readyRun :=
    PrologScheduledPayloadRejectionBridge.ScheduledSelectedHeadTransition.postAnswerToSelectedReady
      transition partitionExact
  have oneRejected :
      RejectedPullsN 1 transition.finish
        (transition.finish.advance transition.branch transition.branchTail) := by
    simpa using
      (RejectedPullsN.succ 0 transition.finish transition.branch
        transition.branchTail
        (transition.finish.advance transition.branch transition.branchTail)
        transition.offset.cursorRemaining failure.independentRejected
        (.zero
          (transition.finish.advance transition.branch
            transition.branchTail)))
  have rejectedSource :=
    PLeaTTa.PrologBodyFailureOuterResourceCatchupBridge.RejectedPullsN.frameRetainedFrontierContextStepsN
      oneRejected transition.postLaterContext (sourceFrame transition)
      before.carrier.index.session
  have postAnswerSourceRun :
      PeTTaSpec.PrologCore.GoalSemantics.StepsN
        (postAnswerRejectedHeadCount ready transition partition)
        (.running before.carrier.index.session ready.result.targetNext) []
        (.running before.carrier.index.session
          (sourceFrontier transition
            (transition.finish.advance transition.branch
              transition.branchTail))) := by
    have combined := readyRun.trans rejectedSource
    simpa [postAnswerRejectedHeadCount, sourceFrontier] using combined
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
        [.answer ready.result.history.bindings] [] answerTransition (.zero _))
  have fullRaw := absorption.trans (answerRun.trans postAnswerSourceRun)
  have sourceBindingExact :
      ready.result.history.bindings = before.carrier.index.current := by
    simpa using ready.result.bindingsExact
  have fullSourceRun :
      PeTTaSpec.PrologCore.GoalSemantics.StepsN
        (before.carrier.index.outer.length + 1 +
          postAnswerRejectedHeadCount ready transition partition)
        before.carrier.sourceState [.answer before.carrier.index.current]
        (.running before.carrier.index.session
          (sourceFrontier transition
            (transition.finish.advance transition.branch
              transition.branchTail))) := by
    simpa [Nat.add_assoc, sourceBindingExact] using fullRaw
  have failed :
      PLeaTTa.unifyB selection.selected.resource.binding
          (.expr
            (selection.selected.resource.args ++
              [selection.selected.resource.res]))
          (.expr (transition.copied.params ++ [transition.copied.result])) =
        none := by
    rw [transition.offset.copiedExact, transition.offset.substitutedArgs]
    exact failure.executableRejected
  have current :=
    PLeaTTa.PrologScheduledPayloadOpenConfBridge.ScheduledSelectedHeadTransition.fineCurrentExact
      transition
  have fineStep :
      DemandDrivenCallStep.Step prog gt (.ready (selectedFineState before))
        (.ready (rejectedFineState before)) := by
    exact
      PrologOrdinaryStepBridge.executable_unify_failure_step
        (selectedFineState before) .equality
        (.expr
          (selection.selected.resource.args ++
            [selection.selected.resource.res]))
        (.expr (transition.copied.params ++ [transition.copied.result]))
        (transition.copied.body ++ selection.selected.resource.rest)
        selection.selected.resource.binding current failed
  exact
    ⟨partition,
      { partitionExact := partitionExact
        failure := failure
        postAnswerSourceRun := postAnswerSourceRun
        fullSourceRun := fullSourceRun
        fineStep := fineStep
        finePersistent := by
          exact
            PrologOrdinaryStepBridge.unifyFailureSuccessor_persistent
              (selectedFineState before)
        fineFrames := by
          exact
            PrologOrdinaryStepBridge.unifyFailureSuccessor_frames
              (selectedFineState before)
        fineScopes := by
          exact
            PrologOrdinaryStepBridge.unifyFailureSuccessor_scopes
              (selectedFineState before)
        fineAnswers := by
          exact
            PrologOrdinaryStepBridge.unifyFailureSuccessor_answers
              (selectedFineState before) }⟩

end ScheduledSelectedHeadTransition

end PLeaTTa.PrologScheduledPayloadRejectionBridge
