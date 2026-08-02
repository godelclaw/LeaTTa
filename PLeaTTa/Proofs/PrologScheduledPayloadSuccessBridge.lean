-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologScheduledPayloadSuccessBridge
Purpose: Pair one successful scheduled selected-head resolution across the
  independent source semantics and the fine executable machine.
Trusted boundary: none
Main exports:
  ScheduledSuccessfulHeadRelates,
  ScheduledSelectedHeadTransition.resolveHead
-/
import PLeaTTa.Proofs.PrologScheduledPayloadRejectionBridge
import PLeaTTa.Proofs.PrologRetainedPayloadActivationBridge

namespace PLeaTTa.PrologScheduledPayloadSuccessBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologActivatedProductStepBridge
open PrologAlphaFreshFrontierBridge
open PrologBodyFailureOuterResourceCatchupBridge
open PrologBodyFailureResourceTransitionBridge
open PrologControlSegmentSpineBridge
open PrologHeterogeneousPrefixBridge
open PrologMguBridge
open PrologMguComposition
open PrologOrdinaryStepBridge
open PrologProductResourceContextBridge
open PrologRetainedPayloadActivationBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRootClosedAnswerBridge
open PrologScheduledAnswerPropagationBridge
open PrologScheduledHistoryBuildBridge
open PrologScheduledPayloadLandingBridge
open PrologScheduledPayloadOpenConfBridge
open PrologScheduledPayloadPathBridge
open PrologScheduledPayloadPostHeadBridge
open PrologScheduledPayloadRejectionBridge
open PrologScheduledPayloadRejectionBridge.ScheduledSelectedHeadTransition
open PrologSourceProductContextBridge
open PrologStateBridge

/-!
The scheduled answer step has already pulled one executable clause head into
`cur`, while the independent lane still has to traverse its exact private
history and conservative rejection prefix.  The rejection bridge closes the
`unifyB = none` half.  This module closes the successful mirror without
choosing another clause occurrence, another runtime state, or an
association-list spelling of the MGU.
-/

/-- Exact number of source transitions after the answer observation and
through successful activation of the selected retained head. -/
def postAnswerSuccessfulHeadCount
    {before : RepresentativeScheduledPayloadState}
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

/-- Proof-local opened-call packet for the exact selected predicate scope.

Only `scope` is semantically consumed by `activeSourceProduct`; retaining the
literal finish cursor and current session prevents a compatible historical
opener from entering the statement. -/
def selectedOpened
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    {build : ScheduledHistoryBuild history}
    {alignment : ScheduledPayloadAlignment payload build}
    {selection : ScheduledLocalSelection build.cells}
    {scope : CutScopeId} {session : Session}
    (transition :
      ScheduledSelectedHeadTransition alignment selection scope session) :
    OpenedCall :=
  { scope := transition.selectedPayloadCell.currentScope
    cursor := transition.finish
    session := session }

/-- Exact source focus after the selected clause head has unified.

The selected clause body is the left DFS branch.  The same advanced cursor is
the right branch at the predicate cut scope, and the selected caller tail is
outside that cut boundary.  Every still-outer payload frame remains literal.
-/
def successfulSourceFrontier
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    {build : ScheduledHistoryBuild history}
    {alignment : ScheduledPayloadAlignment payload build}
    {selection : ScheduledLocalSelection build.cells}
    {scope : CutScopeId} {session : Session}
    (transition :
      ScheduledSelectedHeadTransition alignment selection scope session)
    (independentResult : Substitution) : Search :=
  ActiveProductContext.plug transition.postLaterContext
    (activeSourceProduct transition.selectedPayloadCell.nextScope
      (selectedOpened transition) transition.finish transition.branch
      transition.branchTail independentResult transition.branch.body
      transition.selectedPayloadCell.segment.references)

/-- Exact fine successor of successful full-head unification. -/
def successfulFineState
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session)
    (installed : Subst) : OpenConf :=
  unifySuccessor (selectedFineState before)
    (transition.copied.body ++ selection.selected.resource.rest) installed

namespace ScheduledSelectedHeadTransition

/-- Lift the local matched-clause source step through the selected predicate's
cut boundary, caller product, and every exact older payload frame.

This is the control half of successful activation.  It adds no observation
and does not rebuild the retained cursor: `activeSourceProduct` receives the
same `finish`, `branch`, and `branchTail` as the selected occurrence. -/
theorem liftMatchedSourceStep
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    {build : ScheduledHistoryBuild history}
    {alignment : ScheduledPayloadAlignment payload build}
    {selection : ScheduledLocalSelection build.cells}
    {scope : CutScopeId} {session : Session}
    (transition :
      ScheduledSelectedHeadTransition alignment selection scope session)
    {independentResult : Substitution}
    (child :
      RawStep session (.clauses scope transition.finish) [] .none session
        (.running
          (.choice scope
            (.task scope transition.branch.body independentResult)
            (.clauses scope
              (transition.finish.advance transition.branch
                transition.branchTail))))) :
    RawStep session (sourceFrontier transition transition.finish) [] .none
      session (.running (successfulSourceFrontier transition independentResult)) := by
  have childAtSelected :
      RawStep session
        (.clauses transition.selectedPayloadCell.currentScope
          transition.finish)
        [] .none session
        (.running
          (.choice transition.selectedPayloadCell.currentScope
            (.task transition.selectedPayloadCell.currentScope
              transition.branch.body independentResult)
            (.clauses transition.selectedPayloadCell.currentScope
              (transition.finish.advance transition.branch
                transition.branchTail)))) := by
    simpa only [transition.sourceScopeExact] using child
  have boundary :
      RawStep session
        (.cutBoundary transition.selectedPayloadCell.currentScope
          (.clauses transition.selectedPayloadCell.currentScope
            transition.finish))
        [] .none session
        (.running
          (.cutBoundary transition.selectedPayloadCell.currentScope
            (.choice transition.selectedPayloadCell.currentScope
              (.task transition.selectedPayloadCell.currentScope
                transition.branch.body independentResult)
              (.clauses transition.selectedPayloadCell.currentScope
                (transition.finish.advance transition.branch
                  transition.branchTail))))) :=
    .cutBoundaryProgress transition.selectedPayloadCell.currentScope _ _ []
      session session childAtSelected
  have product :
      RawStep session
        (frameRetainedFrontier (sourceFrame transition) transition.finish)
        [] .none session
        (.running
          (activeSourceProduct transition.selectedPayloadCell.nextScope
            (selectedOpened transition) transition.finish transition.branch
            transition.branchTail independentResult transition.branch.body
            transition.selectedPayloadCell.segment.references)) := by
    simpa [frameRetainedFrontier, sourceFrame, activeSourceProduct,
      selectedOpened] using
      (RawStep.productProgress transition.selectedPayloadCell.nextScope _ _
        transition.selectedPayloadCell.segment.references [] .none session
        session boundary (by simp [Trace.AnswerFree]))
  have lifted :=
    ActiveProductContext.liftProgress transition.postLaterContext product
      (by simp [Trace.AnswerFree])
  simpa [sourceFrontier, successfulSourceFrontier] using lifted

end ScheduledSelectedHeadTransition

/-- Full exact paired result for one selected post-answer clause whose head
unification succeeds.

The source and fine lanes consume the same scheduled payload occurrence.  A
single source `HeadResolution` produces both the ordered canonical MGU and
the actual executable `unifyB` result; the conclusion compares their
denotations through one extended alpha graph rather than requiring equal
association-list orientation. -/
structure ScheduledSuccessfulHeadRelates
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (before : RepresentativeScheduledPayloadState)
    (ready : RootClosedAnswerReady before)
    (selection : ScheduledLocalSelection ready.result.historyBuild.cells)
    (scope : CutScopeId)
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session)
    (partition : RootPayloadPartition before)
    (independentResult : Substitution)
    (nextAlpha : List (LogicVar × String))
    (sourceCanonical flattened : TreeSubstitution)
    (installed : Subst) : Prop where
  partitionExact :
    PrologScheduledPayloadPostHeadBridge.ScheduledSelectedHeadTransition.PartitionAgrees
      transition partition
  resolved : HeadResolution transition.branch independentResult
  nextShared : SharedRuntimeAlpha nextAlpha
  alphaIncluded :
    ∀ pair, pair ∈ before.carrier.index.alpha → pair ∈ nextAlpha
  extensionAbove :
    AlphaExtendsAbove before.carrier.index.alpha nextAlpha
      transition.branch.firstFresh selection.selected.resource.counter
  freshFrontier :
    AlphaFreshFrontier nextAlpha
      before.carrier.index.session.resolver.nextFresh
      (selectedFineState before).persistent.counter
  independentShape :
    independentResult =
      TreeSubstitution.reify
          (sourceCanonical ++ transition.selectedSnapshotAtFinish.canonical) ++
        transition.selectedSnapshotAtFinish.referenceBase
  sourceOrdered :
    OrderedTreeMgu
      (denoteEquations transition.branch.normalizedHeadEquations)
      sourceCanonical
  sourceActivation :
    RawStep before.carrier.index.session
      (sourceFrontier transition transition.finish) [] .none
      before.carrier.index.session
      (.running (successfulSourceFrontier transition independentResult))
  postAnswerSourceRun :
    StepsN (postAnswerSuccessfulHeadCount ready transition partition)
      (.running before.carrier.index.session ready.result.targetNext) []
      (.running before.carrier.index.session
        (successfulSourceFrontier transition independentResult))
  fullSourceRun :
    StepsN
      (before.carrier.index.outer.length + 1 +
        postAnswerSuccessfulHeadCount ready transition partition)
      before.carrier.sourceState [.answer before.carrier.index.current]
      (.running before.carrier.index.session
        (successfulSourceFrontier transition independentResult))
  sealedStep :
    PLeaTTa.Step prog gt (selectedFineState before).toConf
      (successfulFineState transition installed).toConf
  fineStep :
    DemandDrivenCallStep.Step prog gt (.ready (selectedFineState before))
      (.ready (successfulFineState transition installed))
  successorCumulative :
    AlphaCumulativeResidualVariantAgreesOnWith nextAlpha
      before.carrier.index.support
      (sourceCanonical ++ transition.selectedSnapshotAtFinish.canonical)
      transition.selectedSnapshotAtFinish.referenceBase
      (PLeaTTa.trimFor
        (transition.copied.body ++ selection.selected.resource.rest)
        selection.selected.resource.qterm installed)
      (flattened ++
        transition.selectedSnapshotAtFinish.residualRepresentative)
  successorTask :
    TaskPayloadAgrees nextAlpha before.carrier.index.support
      selection.selected.resource.barrier
      (sourceCanonical ++ transition.selectedSnapshotAtFinish.canonical)
      transition.selectedSnapshotAtFinish.referenceBase independentResult
      (PLeaTTa.trimFor
        (transition.copied.body ++ selection.selected.resource.rest)
        selection.selected.resource.qterm installed)
      transition.branch.body transition.copied.body
  nextSnapshot :
    ∃ snapshot :
      RetainedCallPayloadSnapshot nextAlpha before.carrier.index.support
        (afterPulledHead selection.selected.resource selection.localTail)
        (transition.finish.advance transition.branch transition.branchTail)
        transition.selectedPayloadCell.segment
        transition.selectedPayloadCell.outerSegments,
      snapshot.controlOrigin =
        transition.selectedSnapshotAtFinish.controlOrigin
  successorBelow :
    ConfBelowResolutionCounter
      (successfulFineState transition installed).toConf
  finePersistent :
    (successfulFineState transition installed).persistent =
      (selectedFineState before).persistent
  fineFrames :
    (successfulFineState transition installed).frames =
      (selectedFineState before).frames
  fineScopes :
    (successfulFineState transition installed).scopes =
      (selectedFineState before).scopes
  fineAlts :
    (successfulFineState transition installed).control.alts =
      (selectedFineState before).control.alts
  fineBarriers :
    (successfulFineState transition installed).control.barriers =
      (selectedFineState before).control.barriers
  fineAnswers :
    (successfulFineState transition installed).control.answers =
      (selectedFineState before).control.answers

namespace ScheduledSelectedHeadTransition

/-- Resolve the exact selected post-answer head on both lanes.

Only two current-state facts are supplied beyond the proof-relevant carrier:

* `belowBefore` is the global executable resolution-name invariant before the
  real answer step;
* `live` identifies the observable alpha support retained by the exact clause
  body and caller continuation.

Alpha functionality, persistent-state agreement, both allocator bounds,
query identity, clause occurrence, copied body, and cumulative MGU state are
all derived from the carrier and selected payload path. -/
theorem resolveHead
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session)
    (freshFrontierExact :
      before.carrier.index.freshFrontier =
        AlphaFreshFrontier before.carrier.index.alpha)
    (belowBefore :
      ConfBelowResolutionCounter before.carrier.index.openConf.toConf)
    (live :
      AlphaRuntimeNamesLive before.carrier.index.support
        (transition.copied.body ++ selection.selected.resource.rest)
        selection.selected.resource.qterm)
    {independentResult : Substitution}
    (resolved : HeadResolution transition.branch independentResult) :
    ∃ partition : RootPayloadPartition before,
      ∃ nextAlpha sourceCanonical flattened installed,
        ScheduledSuccessfulHeadRelates prog gt before ready selection scope
          transition partition independentResult nextAlpha sourceCanonical
          flattened installed := by
  obtain ⟨partition, partitionExact⟩ :=
    PLeaTTa.PrologScheduledPayloadPostHeadBridge.ScheduledSelectedHeadTransition.partitionExact
      transition
  have catchup :=
    PrologScheduledPayloadRejectionBridge.ScheduledSelectedHeadTransition.postAnswerToSelectedReady
      transition partitionExact
  have currentHead :=
    PLeaTTa.PrologScheduledPayloadOpenConfBridge.ScheduledSelectedHeadTransition.fineCurrentExact
      transition
  have currentQuery :
      (selectedFineState before).control.qterm =
        selection.selected.resource.qterm := by
    calc
      (selectedFineState before).control.qterm =
          before.carrier.index.openConf.control.qterm := by
        simp [selectedFineState]
      _ = before.carrier.index.qterm :=
        before.carrier.agreement.core.control.ready.2.2.1
      _ = selection.selected.resource.qterm :=
        transition.selectedResourceQueryExact.symm
  have currentShared : SharedRuntimeAlpha before.carrier.index.alpha :=
    before.carrier.agreement.core.control.ready.2.2.2.data.alphaShared
  have persistentBefore :
      SessionRelatesPersistent
        (AlphaFreshFrontier before.carrier.index.alpha)
        before.carrier.index.session
        before.carrier.index.openConf.persistent := by
    simpa only [freshFrontierExact] using
      before.carrier.agreement.core.control.ready.1
  have currentPersistent :
      SessionRelatesPersistent
        (AlphaFreshFrontier before.carrier.index.alpha)
        before.carrier.index.session
        (selectedFineState before).persistent := by
    simpa [selectedFineState] using persistentBefore
  have endpointBounds :=
    transition.selectedEndpointBounds
      before.carrier.agreement.endpointsCurrent
  have cursorDominated :
      transition.finish.reservedUntil ≤
        before.carrier.index.session.resolver.nextFresh :=
    endpointBounds.1
  have resourceDominated :
      selection.selected.resource.finalCounter ≤
        (selectedFineState before).persistent.counter := by
    simpa [selectedFineState] using endpointBounds.2
  have answerSealed :
      PLeaTTa.Step prog gt before.carrier.index.openConf.toConf
        (answerSuccessor before.carrier.index.openConf.toConf
          before.carrier.index.runtime) :=
    .answer before.carrier.index.openConf.toConf
      before.carrier.index.runtime ready.fineHead
  have belowAfterAnswer :=
    answerSealed.preserves_belowResolutionCounter belowBefore
  have belowSelected :
      ConfBelowResolutionCounter (selectedFineState before).toConf := by
    simpa [selectedFineState, privateAnswerTarget] using belowAfterAnswer
  obtain
    ⟨nextAlpha, sourceCanonical, flattened, installed,
      nextShared, alphaIncluded, extensionAbove, freshFrontier,
      independentShape, sourceOrdered, sourceStep, sealedStep, fineStep,
      successorCumulative, successorTask, nextSnapshot, successorBelow,
      finePersistent, fineFrames, fineAlts⟩ :=
    RetainedCallPayloadSnapshot.activateSelectedHead
      (prog := prog) (gt := gt) (scope := scope)
      transition.selectedSnapshotAtFinish transition.offset currentHead
      currentQuery currentShared currentPersistent cursorDominated
      resourceDominated belowSelected live resolved
  have sourceActivation :=
    PLeaTTa.PrologScheduledPayloadSuccessBridge.ScheduledSelectedHeadTransition.liftMatchedSourceStep
      transition sourceStep
  have oneSourceRun :
      StepsN 1
        (.running before.carrier.index.session
          (sourceFrontier transition transition.finish)) []
        (.running before.carrier.index.session
          (successfulSourceFrontier transition independentResult)) := by
    have oneTransition :
        Transition
          (.running before.carrier.index.session
            (sourceFrontier transition transition.finish)) []
          (.running before.carrier.index.session
            (successfulSourceFrontier transition independentResult)) :=
      .ordinary _ _ _ _ _ sourceActivation
    simpa using
      (StepsN.succ 0
        (.running before.carrier.index.session
          (sourceFrontier transition transition.finish))
        (.running before.carrier.index.session
          (successfulSourceFrontier transition independentResult))
        (.running before.carrier.index.session
          (successfulSourceFrontier transition independentResult))
        [] [] oneTransition (.zero _))
  have postAnswerSourceRun :
      StepsN (postAnswerSuccessfulHeadCount ready transition partition)
        (.running before.carrier.index.session ready.result.targetNext) []
        (.running before.carrier.index.session
          (successfulSourceFrontier transition independentResult)) := by
    have combined := catchup.trans oneSourceRun
    simpa [postAnswerSuccessfulHeadCount, Nat.add_assoc] using combined
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
      StepsN 1
        (.running before.carrier.index.session ready.result.targetSource)
        [.answer ready.result.history.bindings]
        (.running before.carrier.index.session ready.result.targetNext) := by
    simpa using
      (StepsN.succ 0 _ _ _ [.answer ready.result.history.bindings] []
        answerTransition (.zero _))
  have fullRaw := absorption.trans (answerRun.trans postAnswerSourceRun)
  have sourceBindingExact :
      ready.result.history.bindings = before.carrier.index.current := by
    simpa using ready.result.bindingsExact
  have fullSourceRun :
      StepsN
        (before.carrier.index.outer.length + 1 +
          postAnswerSuccessfulHeadCount ready transition partition)
        before.carrier.sourceState [.answer before.carrier.index.current]
        (.running before.carrier.index.session
          (successfulSourceFrontier transition independentResult)) := by
    simpa [Nat.add_assoc, sourceBindingExact] using fullRaw
  exact
    ⟨partition, nextAlpha, sourceCanonical, flattened, installed,
      { partitionExact := partitionExact
        resolved := resolved
        nextShared := nextShared
        alphaIncluded := alphaIncluded
        extensionAbove := extensionAbove
        freshFrontier := freshFrontier
        independentShape := independentShape
        sourceOrdered := sourceOrdered
        sourceActivation := sourceActivation
        postAnswerSourceRun := postAnswerSourceRun
        fullSourceRun := fullSourceRun
        sealedStep := sealedStep
        fineStep := fineStep
        successorCumulative := successorCumulative
        successorTask := successorTask
        nextSnapshot := nextSnapshot
        successorBelow := successorBelow
        finePersistent := finePersistent
        fineFrames := fineFrames
        fineScopes := rfl
        fineAlts := fineAlts
        fineBarriers := rfl
        fineAnswers := rfl }⟩

end ScheduledSelectedHeadTransition

end PLeaTTa.PrologScheduledPayloadSuccessBridge
