-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologScheduledPayloadPostHeadBridge
Purpose: Apply one exact scheduled local-head selection to the dependent
  retained payload zipper.
Trusted boundary: none
Main exports:
  SourceControlResourcePayloadContextAgrees.afterRejectedPullsAndPulledHead,
  ScheduledSelectedHeadTransition,
  ScheduledPayloadAlignment.selectAndAdvanceHead
-/
import PLeaTTa.Proofs.PrologScheduledPayloadLandingBridge
import PLeaTTa.Proofs.PrologAnswerSelectedHeadOffsetBridge
import PLeaTTa.Proofs.PrologRetainedPayloadActivationBridge
import PLeaTTa.Proofs.PrologRetainedPayloadSnapshotBridge

namespace PLeaTTa.PrologScheduledPayloadPostHeadBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.Resolver
open PLeaTTa.PrologAnswerSelectedHeadOffsetBridge
open PLeaTTa.PrologAnswerSourceCatchupBridge
open PLeaTTa.PrologBodyFailureExhaustedResourceTransitionBridge
open PLeaTTa.PrologBodyFailureResourceTransitionBridge
open PLeaTTa.PrologControlSegmentSpineBridge
open PLeaTTa.PrologPrefilterScanBridge
open PLeaTTa.PrologProductResourceContextBridge
open PLeaTTa.PrologRetainedPayloadActivationBridge
open PLeaTTa.PrologRetainedPayloadSnapshotBridge
open PLeaTTa.PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
open PLeaTTa.PrologScheduledAnswerPropagationBridge
open PLeaTTa.PrologScheduledHistoryBuildBridge
open PLeaTTa.PrologScheduledPayloadLandingBridge
open PLeaTTa.PrologScheduledPayloadPathBridge
open PLeaTTa.PrologSourceProductContextBridge
open PLeaTTa.PrologSupportedCallFrontierBridge
open PLeaTTa.PrologSupportedCursorAlternativeBridge

/-! ## A generic one-cell dependent zipper transform -/

namespace SourceControlResourcePayloadContextAgrees

/-- Transport exactly the head payload cell through a counted rejected
source prefix and one retained-head consumption.

The tail payload object is reused literally.  Persistent state is absent from
this operation: only the immutable call snapshot, its exact source cursor,
and the corresponding executable resource are transformed. -/
def afterRejectedPullsAndPulledHead
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {before finish : PreparedCursor}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    {branchTail : List ClauseBranch} {copied : PLeaTTa.Clause}
    {remainingAlts : List PLeaTTa.Alt}
    {currentScope nextScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    (payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier (segment :: segments) (resource :: resources)
        currentScope
        ({ callerScope := nextScope
           predicateScope := currentScope
           retained := .clauses currentScope before
           callerRest := segment.references } :: context)
        outerScope)
    (beforeWellFormed : before.WellFormed)
    {count : Nat}
    (pulls : RejectedPullsN count before finish)
    (offset :
      PulledHeadOffsetAgrees alpha finish branch clause branchTail copied
        resource remainingAlts) :
    SourceControlResourcePayloadContextAgrees alpha support qterm
      currentBarrier (segment :: segments)
      (afterPulledHead resource remainingAlts :: resources)
      currentScope
      ({ callerScope := nextScope
         predicateScope := currentScope
         retained :=
           .clauses currentScope (finish.advance branch branchTail)
         callerRest := segment.references } :: context)
      outerScope := by
  cases payload with
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees =>
      let nextSnapshot :=
        RetainedCallPayloadSnapshot.afterRejectedPullsAndPulledHead snapshot
          beforeWellFormed pulls offset
      exact
        .cons currentBarrier currentScope nextScope outerScope segment segments
          (afterPulledHead resource remainingAlts) resources
          (finish.advance branch branchTail) context segmentAgrees
          (by simpa [afterPulledHead] using resourceRest)
          (by simpa [afterPulledHead] using resourceQuery)
          (by simpa [afterPulledHead] using resourceBarrier)
          offset.tailOwnership nextSnapshot outerAgrees

/-- The generic head transform preserves the literal dependent tail. -/
@[simp] theorem tail_afterRejectedPullsAndPulledHead
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {before finish : PreparedCursor}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    {branchTail : List ClauseBranch} {copied : PLeaTTa.Clause}
    {remainingAlts : List PLeaTTa.Alt}
    {currentScope nextScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    (payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier (segment :: segments) (resource :: resources)
        currentScope
        ({ callerScope := nextScope
           predicateScope := currentScope
           retained := .clauses currentScope before
           callerRest := segment.references } :: context)
        outerScope)
    (beforeWellFormed : before.WellFormed)
    {count : Nat}
    (pulls : RejectedPullsN count before finish)
    (offset :
      PulledHeadOffsetAgrees alpha finish branch clause branchTail copied
        resource remainingAlts) :
    SourceControlResourcePayloadContextAgrees.tail
        (afterRejectedPullsAndPulledHead payload beforeWellFormed pulls offset) =
      SourceControlResourcePayloadContextAgrees.tail payload := by
  cases payload
  simp [afterRejectedPullsAndPulledHead,
    SourceControlResourcePayloadContextAgrees.tail]

end SourceControlResourcePayloadContextAgrees

/-! ## Exact scheduled transition package -/

namespace PayloadCell

/-- Replace only the operational resource/cursor/snapshot of one immutable
payload cell.  All typed delimiter and caller-segment labels are inherited
from the selected occurrence itself. -/
def afterSelectedHead
    {alpha support : List (LogicVar × String)}
    (cell : PayloadCell alpha support)
    (resource : RetainedAlternativeSegment) (cursor : PreparedCursor)
    (ownership : resource.HasIndexedOwnershipAt alpha cursor)
    (snapshot :
      RetainedCallPayloadSnapshot alpha support resource cursor cell.segment
        cell.outerSegments) :
    PayloadCell alpha support :=
  { currentBarrier := cell.currentBarrier
    currentScope := cell.currentScope
    nextScope := cell.nextScope
    outerScope := cell.outerScope
    segment := cell.segment
    outerSegments := cell.outerSegments
    resource := resource
    cursor := cursor
    ownership := ownership
    snapshot := snapshot }

end PayloadCell

/-- Complete proof-relevant result of selecting and consuming one local head
at an exact scheduled payload coordinate.

The carrier is Type-valued because it retains the transformed dependent
payload zipper.  Its producer returns `Nonempty`, so no Prop-valued source
proof is eliminated to compute runtime data. -/
structure ScheduledSelectedHeadTransition
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
    (alignment : ScheduledPayloadAlignment payload build)
    (selection : ScheduledLocalSelection build.cells)
    (scope : CutScopeId) (session : Session) : Type where
  route : ScheduledPayloadAlignment.SelectionRoute alignment selection
  selectedPayloadCell : PayloadCell alpha support
  selectedPayloadCellExact :
    selectedPayloadCell = (alignment.payloadPath selection.path).cell
  sourceScopeExact : scope = selectedPayloadCell.currentScope
  callStart : PreparedCursor
  startPosition : Nat
  finish : PreparedCursor
  readyClauses : List PLeaTTa.Clause
  frontier :
    SelectedReadyFrontier alpha selection.selected.resource selection.goals
      selection.binding selection.localTail callStart selection.selected.cursor
      finish startPosition readyClauses
  sourceSteps :
    SilentStepsN session frontier.rejectedCount
      (.clauses scope selection.selected.cursor) (.clauses scope finish)
  branch : ClauseBranch
  clause : PLeaTTa.Clause
  branchTail : List ClauseBranch
  copied : PLeaTTa.Clause
  offset :
    PulledHeadOffsetAgrees alpha finish branch clause branchTail copied
      selection.selected.resource selection.localTail
  tailOwnershipExact :
    (afterPulledHead selection.selected.resource selection.localTail).Owns
      alpha callStart (finish.advance branch branchTail)
      ((startPosition + frontier.rejectedCount) + 1)
  consumedSnapshot :
    RetainedCallPayloadSnapshot alpha support
      (afterPulledHead selection.selected.resource selection.localTail)
      (finish.advance branch branchTail)
      selectedPayloadCell.segment selectedPayloadCell.outerSegments
  /-- The exact pre-pull allocation chronology intentionally weakened by
  `consumedSnapshot`.

  This proof-only token is produced from the same selected occurrence,
  rejected prefix, and eager pull as `consumedSnapshot`.  It carries no
  world, session, frame, or alternative bank; retaining it prevents later
  reactivation from attempting to reconstruct historical relative bounds
  from current high-water domination, which is insufficient. -/
  activationChronology :
    SelectedHeadActivationChronology consumedSnapshot
  /-- Rejection transport and eager head consumption preserve the compact
  call-control origin of this exact occurrence.  This equality is retained
  explicitly because the post-pull snapshot weakens other indexed fields and
  consumers must not recover an outer call origin by value search. -/
  controlOriginExact :
    consumedSnapshot.controlOrigin =
      selectedPayloadCell.snapshot.controlOrigin
  postLaterResources : List RetainedAlternativeSegment
  postLaterContext : ActiveProductContext
  postLaterContextExact :
    postLaterContext = route.route.head.data.laterContext
  postPayload :
    SourceControlResourcePayloadContextAgrees alpha support qterm
      selectedPayloadCell.currentBarrier
      (selectedPayloadCell.segment :: selectedPayloadCell.outerSegments)
      (afterPulledHead selection.selected.resource selection.localTail ::
        postLaterResources)
      selectedPayloadCell.currentScope
      ({ callerScope := selectedPayloadCell.nextScope
         predicateScope := selectedPayloadCell.currentScope
         retained :=
           .clauses selectedPayloadCell.currentScope
             (finish.advance branch branchTail)
         callerRest := selectedPayloadCell.segment.references } ::
        postLaterContext)
      selectedPayloadCell.outerScope
  postSegmentsExact :
    selectedPayloadCell.segment :: selectedPayloadCell.outerSegments =
      segments.drop selection.path.position.val
  postLaterResourcesExact :
    postLaterResources =
      selection.suffix.map ScheduledHistoryCell.resource
  postOuterExact : selectedPayloadCell.outerScope = outer
  /-- The rebuilt zipper head contains the newly derived occurrence
  ownership and transported snapshot.  This is an equality of uniform
  `PayloadCell` values, rather than a cast between dependently indexed
  snapshots. -/
  postHeadCellExact :
    payloadCells postPayload =
      PayloadCell.afterSelectedHead selectedPayloadCell
          (afterPulledHead selection.selected.resource selection.localTail)
          (finish.advance branch branchTail)
          ⟨callStart, (startPosition + frontier.rejectedCount) + 1,
            tailOwnershipExact⟩
          consumedSnapshot ::
        payloadCells
          (SourceControlResourcePayloadContextAgrees.tail postPayload)
  postLaterCellsExact :
    payloadCells (SourceControlResourcePayloadContextAgrees.tail postPayload) =
      (payloadCells payload).drop (selection.path.position.val + 1)

namespace ScheduledSelectedHeadTransition

/-- The selected dependent payload cell erases to the exact scheduled-history
occurrence chosen by the executable pull.

This projection is intentionally occurrence-sensitive: it follows the typed
payload path and never searches for an equal resource or cursor. -/
theorem selectedHistoryCellExact
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
    transition.selectedPayloadCell.historyCell = selection.selected := by
  exact
    (congrArg PayloadCell.historyCell
      transition.selectedPayloadCellExact).trans
      transition.route.selectedExact

/-- Resource identity at the selected payload coordinate. -/
theorem selectedResourceExact
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
    transition.selectedPayloadCell.resource = selection.selected.resource :=
  congrArg ScheduledHistoryCell.resource transition.selectedHistoryCellExact

/-- Cursor identity at the selected payload coordinate. -/
theorem selectedCursorExact
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
    transition.selectedPayloadCell.cursor = selection.selected.cursor :=
  congrArg ScheduledHistoryCell.cursor transition.selectedHistoryCellExact

/-- The immutable snapshot immediately before the selected resource's
conservative rejection prefix.

Both dependent resource and cursor indices are transported from the same
typed payload occurrence; neither can be supplied independently. -/
def selectedSnapshot
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
    RetainedCallPayloadSnapshot alpha support selection.selected.resource
      selection.selected.cursor transition.selectedPayloadCell.segment
      transition.selectedPayloadCell.outerSegments := by
  simpa only [transition.selectedResourceExact,
    transition.selectedCursorExact] using
    transition.selectedPayloadCell.snapshot

/-- The selected source cursor is well formed before its counted conservative
rejection prefix. -/
theorem selectedCursorWellFormed
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
    selection.selected.cursor.WellFormed := by
  rcases transition.frontier.ownership.scan with
    ⟨_candidates, wellFormed, _query, _substitutedArgs, _supported,
      _arities, _scan⟩
  exact wellFormed

/-- The immutable payload transported through exactly the rejected prefix,
stopping immediately before the selected head is consumed. -/
def selectedSnapshotAtFinish
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
    RetainedCallPayloadSnapshot alpha support selection.selected.resource
      transition.finish transition.selectedPayloadCell.segment
      transition.selectedPayloadCell.outerSegments :=
  RetainedCallPayloadSnapshot.afterRejectedPulls transition.selectedSnapshot
    transition.selectedCursorWellFormed transition.frontier.rejectedPulls

/-- The selected resource retains the payload zipper's observable query. -/
theorem selectedResourceQueryExact
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
    selection.selected.resource.qterm = qterm := by
  let head := transition.route.route.head.data
  have headCellExact : head.cell = transition.selectedPayloadCell :=
    transition.route.route.headCell_exact.trans
      transition.selectedPayloadCellExact.symm
  have headResourceExact :
      head.resource = selection.selected.resource := by
    calc
      head.resource = transition.selectedPayloadCell.resource := by
        simpa [PayloadHeadData.cell] using
          congrArg PayloadCell.resource headCellExact
      _ = selection.selected.resource := transition.selectedResourceExact
  calc
    selection.selected.resource.qterm = head.resource.qterm := by
      rw [headResourceExact]
    _ = qterm := head.resourceQuery

/-- Persistent allocator domination for the exact selected occurrence,
transported through its counted rejected prefix.

The proof starts from the complete pre-answer dependent zipper and uses the
typed selection path, so duplicate-shaped resources cannot borrow each
other's high-water bounds. -/
theorem selectedEndpointBounds
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
    {referenceFloor executableFloor : Nat}
    (below :
      SourceControlResourcePayloadContextAgrees.endpointsBelow payload
        referenceFloor executableFloor) :
    transition.finish.reservedUntil ≤ referenceFloor ∧
      selection.selected.resource.finalCounter ≤ executableFloor := by
  have pathBounds :=
    (alignment.payloadPath selection.path).endpointsBelow below
  have cellBounds :
      transition.selectedPayloadCell.cursor.reservedUntil ≤ referenceFloor ∧
        transition.selectedPayloadCell.resource.finalCounter ≤
          executableFloor := by
    simpa only [transition.selectedPayloadCellExact] using pathBounds
  constructor
  · calc
      transition.finish.reservedUntil =
          selection.selected.cursor.reservedUntil :=
        PLeaTTa.PrologSupportedCallFrontierBridge.RejectedPullsN.preserves_reservedUntil
          transition.frontier.rejectedPulls
      _ = transition.selectedPayloadCell.cursor.reservedUntil := by
        rw [transition.selectedCursorExact]
      _ ≤ referenceFloor := cellBounds.1
  · simpa only [← transition.selectedResourceExact] using cellBounds.2

/-- Exact source catch-up partition at the same typed payload occurrence as a
selected-head transition.

The older classifier supplies the ranked source work in `Prop`; it does not
choose runtime data.  These equations force its crossed prefix, selected
frame, cursor, segment, and surviving context to be the literal positional
suffix already selected by the Type-valued payload route. -/
structure PartitionAgrees
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
    (partition :
      OuterResourceCatchupPartition alpha segments resources context) :
    Prop where
  crossedResourcesExact :
    partition.crossedResources =
      selection.earlier.map ScheduledHistoryCell.resource
  firstResourceExact :
    partition.first = selection.selected.resource
  survivingResourcesExact :
    partition.survivingResources =
      selection.suffix.map ScheduledHistoryCell.resource
  tailExact : partition.tail = selection.localTail
  crossedFramesExact :
    partition.crossedFrames =
      context.take selection.path.position.val
  firstFrameExact :
    partition.firstFrame =
      { callerScope := transition.selectedPayloadCell.nextScope
        predicateScope := transition.selectedPayloadCell.currentScope
        retained :=
          .clauses transition.selectedPayloadCell.currentScope
            selection.selected.cursor
        callerRest := transition.selectedPayloadCell.segment.references }
  survivingContextExact :
    partition.survivingContext = transition.postLaterContext
  firstCursorExact : partition.firstCursor = selection.selected.cursor
  crossedSegmentsExact :
    partition.crossedSegments =
      segments.take selection.path.position.val
  firstSegmentExact :
    partition.firstSegment = transition.selectedPayloadCell.segment
  survivingSegmentsExact :
    partition.survivingSegments =
      transition.selectedPayloadCell.outerSegments

/-- The generic first-live source classifier is positionally identical to
the already-selected payload route.  In particular, duplicate-shaped
resources cannot move the source transition under another delimiter frame. -/
theorem partitionExact
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
    ∃ partition :
        OuterResourceCatchupPartition alpha segments resources context,
      PartitionAgrees transition partition := by
  obtain
    ⟨partition, crossedResourcesExact, firstResourceExact,
      survivingResourcesExact, tailExact⟩ :=
    PLeaTTa.PrologScheduledPayloadLandingBridge.ScheduledPayloadAlignment.selection_partition
      alignment selection
  let head := transition.route.route.head.data
  have headCellExact :
      head.cell = transition.selectedPayloadCell :=
    transition.route.route.headCell_exact.trans
      transition.selectedPayloadCellExact.symm
  have crossedFramesLength :
      partition.crossedFrames.length =
        selection.path.position.val := by
    calc
      partition.crossedFrames.length =
          partition.crossedResources.length :=
        partition.crossedWork.length_eq.symm
      _ =
          (selection.earlier.map
            ScheduledHistoryCell.resource).length := by
        rw [crossedResourcesExact]
      _ = selection.path.position.val := by
        simp [ScheduledLocalSelection.path,
          ScheduledLocalSelection.position]
  have partitionContextDrop :
      context.drop selection.path.position.val =
        partition.firstFrame :: partition.survivingContext := by
    calc
      context.drop selection.path.position.val =
          (partition.crossedFrames ++
            partition.firstFrame :: partition.survivingContext).drop
              selection.path.position.val :=
        congrArg (List.drop selection.path.position.val)
          partition.contextEq
      _ = partition.firstFrame :: partition.survivingContext := by
        rw [← crossedFramesLength]
        simp
  have headContextDrop :
      context.drop selection.path.position.val =
        ({ callerScope := head.nextScope
           predicateScope := head.currentScope
           retained := .clauses head.currentScope head.cursor
           callerRest := head.segment.references } : ActiveProductFrame) ::
          head.laterContext := by
    exact head.contextExact
  have frameAndContext :=
    List.cons.inj (partitionContextDrop.symm.trans headContextDrop)
  have headFrameSelected :
      ({ callerScope := head.nextScope
         predicateScope := head.currentScope
         retained := .clauses head.currentScope head.cursor
         callerRest := head.segment.references } : ActiveProductFrame) =
        { callerScope := transition.selectedPayloadCell.nextScope
          predicateScope := transition.selectedPayloadCell.currentScope
          retained :=
            .clauses transition.selectedPayloadCell.currentScope
              selection.selected.cursor
          callerRest :=
            transition.selectedPayloadCell.segment.references } := by
    have cursorExact :
        head.cursor = selection.selected.cursor := by
      have selectedHistory :
          head.cell.historyCell = selection.selected := by
        exact
          (congrArg PayloadCell.historyCell headCellExact).trans
            ((congrArg PayloadCell.historyCell
                transition.selectedPayloadCellExact).trans
              transition.route.selectedExact)
      exact congrArg ScheduledHistoryCell.cursor selectedHistory
    have nextScopeExact :
        head.nextScope = transition.selectedPayloadCell.nextScope := by
      simpa [PayloadHeadData.cell] using
        congrArg PayloadCell.nextScope headCellExact
    have currentScopeExact :
        head.currentScope = transition.selectedPayloadCell.currentScope := by
      simpa [PayloadHeadData.cell] using
        congrArg PayloadCell.currentScope headCellExact
    have referencesExact :
        head.segment.references =
          transition.selectedPayloadCell.segment.references := by
      simpa [PayloadHeadData.cell] using
        congrArg (fun cell => cell.segment.references) headCellExact
    rw [nextScopeExact, currentScopeExact, cursorExact, referencesExact]
  have firstFrameExact :
      partition.firstFrame =
        { callerScope := transition.selectedPayloadCell.nextScope
          predicateScope := transition.selectedPayloadCell.currentScope
          retained :=
            .clauses transition.selectedPayloadCell.currentScope
              selection.selected.cursor
          callerRest :=
            transition.selectedPayloadCell.segment.references } :=
    frameAndContext.1.trans headFrameSelected
  have survivingContextExact :
      partition.survivingContext = transition.postLaterContext :=
    frameAndContext.2.trans transition.postLaterContextExact.symm
  have firstCursorExact :
      partition.firstCursor = selection.selected.cursor := by
    have retained := partition.firstRetainedShape
    rw [firstFrameExact] at retained
    have cursorExact :=
      congrArg
        (fun search =>
          match search with
          | .clauses _ cursor => some cursor
          | _ => none)
        retained
    simpa using cursorExact.symm
  have crossedFramesExact :
      partition.crossedFrames =
        context.take selection.path.position.val := by
    calc
      partition.crossedFrames =
          (partition.crossedFrames ++
              partition.firstFrame :: partition.survivingContext).take
            partition.crossedFrames.length := by simp
      _ = context.take selection.path.position.val := by
        rw [← partition.contextEq, crossedFramesLength]
  have crossedSegmentsLength :
      partition.crossedSegments.length =
        selection.path.position.val := by
    calc
      partition.crossedSegments.length =
          partition.crossedResources.length :=
        partition.crossedSegmentDepth
      _ =
          (selection.earlier.map
            ScheduledHistoryCell.resource).length := by
        rw [crossedResourcesExact]
      _ = selection.path.position.val := by
        simp [ScheduledLocalSelection.path,
          ScheduledLocalSelection.position]
  have partitionSegmentsDrop :
      segments.drop selection.path.position.val =
        partition.firstSegment :: partition.survivingSegments := by
    calc
      segments.drop selection.path.position.val =
          (partition.crossedSegments ++
            partition.firstSegment :: partition.survivingSegments).drop
              selection.path.position.val :=
        congrArg (List.drop selection.path.position.val)
          partition.segmentsEq
      _ = partition.firstSegment :: partition.survivingSegments := by
        rw [← crossedSegmentsLength]
        simp
  have headSegmentsDrop :
      segments.drop selection.path.position.val =
        head.segment :: head.laterSegments :=
    head.segmentsExact
  have segmentAndTail :=
    List.cons.inj (partitionSegmentsDrop.symm.trans headSegmentsDrop)
  have firstSegmentExact :
      partition.firstSegment =
        transition.selectedPayloadCell.segment :=
    segmentAndTail.1.trans
      (congrArg PayloadCell.segment headCellExact)
  have survivingSegmentsExact :
      partition.survivingSegments =
        transition.selectedPayloadCell.outerSegments :=
    segmentAndTail.2.trans
      (congrArg PayloadCell.outerSegments headCellExact)
  have crossedSegmentsExact :
      partition.crossedSegments =
        segments.take selection.path.position.val := by
    calc
      partition.crossedSegments =
          (partition.crossedSegments ++
              partition.firstSegment :: partition.survivingSegments).take
            partition.crossedSegments.length := by simp
      _ = segments.take selection.path.position.val := by
        rw [← partition.segmentsEq, crossedSegmentsLength]
  exact
    ⟨partition,
      { crossedResourcesExact := crossedResourcesExact
        firstResourceExact := firstResourceExact
        survivingResourcesExact := survivingResourcesExact
        tailExact := tailExact
        crossedFramesExact := crossedFramesExact
        firstFrameExact := firstFrameExact
        survivingContextExact := survivingContextExact
        firstCursorExact := firstCursorExact
        crossedSegmentsExact := crossedSegmentsExact
        firstSegmentExact := firstSegmentExact
        survivingSegmentsExact := survivingSegmentsExact }⟩

/-- The transformed dependent zipper preserves every later payload cell
literally, including its immutable snapshot. -/
theorem laterCellsExact
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
    payloadCells
        (SourceControlResourcePayloadContextAgrees.tail
          transition.postPayload) =
      (payloadCells payload).drop (selection.path.position.val + 1) := by
  exact transition.postLaterCellsExact

/-- The transformed head followed by the literal old suffix is the complete
ordinary-cell view of the rebuilt dependent zipper.  This is a corollary of
the dependently indexed carrier, not the definition of the carrier. -/
theorem postCellSpineExact
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
    payloadCells transition.postPayload =
      PayloadCell.afterSelectedHead transition.selectedPayloadCell
          (afterPulledHead selection.selected.resource selection.localTail)
          (transition.finish.advance transition.branch transition.branchTail)
          ⟨transition.callStart,
            (transition.startPosition + transition.frontier.rejectedCount) + 1,
            transition.tailOwnershipExact⟩
          transition.consumedSnapshot ::
        (payloadCells payload).drop (selection.path.position.val + 1) := by
  rw [transition.postHeadCellExact, transition.postLaterCellsExact]

/-- The executable resource spine of the rebuilt payload is exactly the
selection's operational post-pull spine. -/
theorem postResourcesExact
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
    (payloadCells transition.postPayload).map PayloadCell.resource =
      selection.postResources := by
  calc
    (payloadCells transition.postPayload).map PayloadCell.resource =
        afterPulledHead selection.selected.resource selection.localTail ::
          transition.postLaterResources :=
      payloadCells_map_resource transition.postPayload
    _ = selection.postResources := by
      simp [ScheduledLocalSelection.postResources,
        transition.postLaterResourcesExact]

/-- The selected path's earlier cells are explicitly the erased prefix of
the original dependent zipper.  Together with `postCellSpineExact`, this
accounts for every pre-state cell: earlier cells are dropped, the selected
cell is transformed once, and later cells are reused. -/
theorem earlierCellsExact
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
    selection.earlier =
      ((payloadCells payload).take selection.path.position.val).map
        PayloadCell.historyCell :=
  transition.route.earlierExact

/-- Each dropped empty cell removes exactly its owned barrier marker; the
selected marker remains in the post-resource spine.  This is the payload
level cache equation consumed by the later OpenConf transition bridge. -/
theorem barrierMarkersDroppedExact
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
    (_transition :
      ScheduledSelectedHeadTransition alignment selection scope session) :
    PLeaTTa.barrierCount
        (flattenOwnedAlts
          ((payloadCells payload).map PayloadCell.resource) []) =
      PLeaTTa.barrierCount
          (flattenOwnedAlts selection.postResources []) +
        selection.earlier.length := by
  have dropped := selection.barrierCount_drop_exact
  have post := selection.rest_eq_flatten_postResources
  rw [post] at dropped
  simpa [alignment.cellsExact, List.map_map, Function.comp_def,
    PayloadCell.historyCell]
    using dropped

end ScheduledSelectedHeadTransition

namespace ScheduledPayloadAlignment

/-- Select the exact dependent payload occurrence, consume its real source
rejection prefix and retained head, and rebuild the dependent suffix with
only that head transformed.

Earlier empty cells are absent from `postPayload`; every later cell is the
literal old payload value.  The source coordinate is fixed at
`startPosition + rejectedCount + 1`. -/
theorem selectAndAdvanceHead
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
    (alignment : ScheduledPayloadAlignment payload build)
    (selection : ScheduledLocalSelection build.cells)
    (session : Session) :
    Nonempty
      (ScheduledSelectedHeadTransition alignment selection
        (alignment.payloadPath selection.path).cell.currentScope session) := by
  let route :=
    PLeaTTa.PrologScheduledPayloadLandingBridge.ScheduledPayloadAlignment.selectionRoute
      alignment selection
  let head := route.route.head.data
  have cellsAtSuffix :
      ({ currentBarrier := route.route.suffixBarrier
         currentScope := head.currentScope
         nextScope := head.nextScope
         outerScope := outer
         segment := head.segment
         outerSegments := head.laterSegments
         resource := head.resource
         cursor := head.cursor
         ownership := head.resourceOwnership
         snapshot := head.snapshot } : PayloadCell alpha support) ::
          payloadCells head.outerAgrees =
        (alignment.payloadPath selection.path).cell ::
          (payloadCells payload).drop
            (selection.path.position.val + 1) :=
    head.cellsExact.symm.trans route.route.cellsExact
  have headCellExact :
      ({ currentBarrier := route.route.suffixBarrier
         currentScope := head.currentScope
         nextScope := head.nextScope
         outerScope := outer
         segment := head.segment
         outerSegments := head.laterSegments
         resource := head.resource
         cursor := head.cursor
         ownership := head.resourceOwnership
         snapshot := head.snapshot } : PayloadCell alpha support) =
        (alignment.payloadPath selection.path).cell :=
    (List.cons.inj cellsAtSuffix).1
  have laterCellsExact :
      payloadCells head.outerAgrees =
        (payloadCells payload).drop
          (selection.path.position.val + 1) :=
    (List.cons.inj cellsAtSuffix).2
  have segmentExact :
      head.segment = (alignment.payloadPath selection.path).cell.segment :=
    congrArg PayloadCell.segment headCellExact
  have outerSegmentsExact :
      head.laterSegments =
        (alignment.payloadPath selection.path).cell.outerSegments :=
    congrArg PayloadCell.outerSegments headCellExact
  have headHistoryExact :
      ({ resource := head.resource
         cursor := head.cursor
         ownership := head.resourceOwnership } : ScheduledHistoryCell alpha) =
        selection.selected := by
    exact
      (congrArg PayloadCell.historyCell headCellExact).trans
        route.selectedExact
  have resourceExact : head.resource = selection.selected.resource :=
    congrArg ScheduledHistoryCell.resource headHistoryExact
  have cursorExact : head.cursor = selection.selected.cursor :=
    congrArg ScheduledHistoryCell.cursor headHistoryExact
  obtain ⟨selectedSnapshot, selectedSnapshotOriginExact⟩ :
      ∃ selectedSnapshot :
          RetainedCallPayloadSnapshot alpha support
            selection.selected.resource selection.selected.cursor head.segment
            head.laterSegments,
        selectedSnapshot.controlOrigin = head.snapshot.controlOrigin := by
    rw [← resourceExact, ← cursorExact]
    exact ⟨head.snapshot, rfl⟩
  let selectedPayloadCell : PayloadCell alpha support :=
    { currentBarrier := route.route.suffixBarrier
      currentScope := head.currentScope
      nextScope := head.nextScope
      outerScope := outer
      segment := head.segment
      outerSegments := head.laterSegments
      resource := head.resource
      cursor := head.cursor
      ownership := head.resourceOwnership
      snapshot := head.snapshot }
  have selectedPayloadCellExact :
      selectedPayloadCell =
        (alignment.payloadPath selection.path).cell := by
    simpa [selectedPayloadCell] using headCellExact
  have selectedResourceRest :
      selection.selected.resource.rest =
        head.segment.executables ++ flattenExecutables head.laterSegments := by
    simpa only [resourceExact] using head.resourceRest
  have selectedResourceQuery : selection.selected.resource.qterm = qterm := by
    simpa only [resourceExact] using head.resourceQuery
  have selectedResourceBarrier :
      selection.selected.resource.barrier = route.route.suffixBarrier := by
    simpa only [resourceExact] using head.resourceBarrier
  rcases selection.selected.ownership with
    ⟨callStart, startPosition, exactOwnership⟩
  obtain ⟨finish, readyClauses, frontier, sourceSteps, _positioned⟩ :=
    PLeaTTa.PrologAnswerSourceCatchupBridge.RetainedAlternativeSegment.catchupSelectedAt
      exactOwnership selection.selectedHead
        (alignment.payloadPath selection.path).cell.currentScope session
  obtain
    ⟨branch, clause, branchTail, copied, offset, tailOwnershipExact⟩ :=
    PLeaTTa.PrologAnswerSelectedHeadOffsetBridge.SelectedReadyFrontier.pulledHeadOffsetExact
      frontier
  have beforeWellFormed : selection.selected.cursor.WellFormed := by
    rcases exactOwnership.scan with
      ⟨_candidates, wellFormed, _query, _substitutedArgs, _supported,
        _arities, _scan⟩
    exact wellFormed
  let consumedSnapshot :=
    RetainedCallPayloadSnapshot.afterRejectedPullsAndPulledHead
      selectedSnapshot beforeWellFormed frontier.rejectedPulls offset
  let oldSuffix :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        route.route.suffixBarrier (head.segment :: head.laterSegments)
        (selection.selected.resource :: head.laterResources)
        head.currentScope
        ({ callerScope := head.nextScope
           predicateScope := head.currentScope
           retained :=
             .clauses head.currentScope selection.selected.cursor
           callerRest := head.segment.references } :: head.laterContext)
        outer :=
    .cons route.route.suffixBarrier head.currentScope head.nextScope outer
      head.segment head.laterSegments selection.selected.resource
      head.laterResources selection.selected.cursor head.laterContext
      head.segmentAgrees selectedResourceRest selectedResourceQuery
      selectedResourceBarrier selection.selected.ownership selectedSnapshot
      head.outerAgrees
  let postPayload :=
    SourceControlResourcePayloadContextAgrees.afterRejectedPullsAndPulledHead
      oldSuffix beforeWellFormed frontier.rejectedPulls offset
  have laterResourcesExact :
      head.laterResources =
        selection.suffix.map ScheduledHistoryCell.resource := by
    calc
      head.laterResources =
          (payloadCells head.outerAgrees).map PayloadCell.resource :=
        (payloadCells_map_resource head.outerAgrees).symm
      _ =
          ((payloadCells payload).drop
            (selection.path.position.val + 1)).map
              PayloadCell.resource := by
        rw [laterCellsExact]
      _ =
          (((payloadCells payload).drop
            (selection.path.position.val + 1)).map
              PayloadCell.historyCell).map
                ScheduledHistoryCell.resource := by
        rw [List.map_map]
        rfl
      _ = selection.suffix.map ScheduledHistoryCell.resource := by
        rw [← route.suffixExact]
  have postSegmentsExact :
      selectedPayloadCell.segment :: selectedPayloadCell.outerSegments =
        segments.drop selection.path.position.val := by
    simpa [selectedPayloadCell] using head.segmentsExact.symm
  have postHeadCellExact :
      payloadCells postPayload =
        PayloadCell.afterSelectedHead
            selectedPayloadCell
            (afterPulledHead selection.selected.resource selection.localTail)
            (finish.advance branch branchTail)
            ⟨callStart, (startPosition + frontier.rejectedCount) + 1,
              tailOwnershipExact⟩
            consumedSnapshot ::
          payloadCells
            (SourceControlResourcePayloadContextAgrees.tail postPayload) := by
    simp [postPayload, oldSuffix,
      SourceControlResourcePayloadContextAgrees.afterRejectedPullsAndPulledHead,
      SourceControlResourcePayloadContextAgrees.tail, payloadCells,
      PayloadCell.afterSelectedHead, selectedPayloadCell, consumedSnapshot]
  have postLaterCellsExact :
      payloadCells
          (SourceControlResourcePayloadContextAgrees.tail postPayload) =
        (payloadCells payload).drop
          (selection.path.position.val + 1) := by
    calc
      payloadCells
          (SourceControlResourcePayloadContextAgrees.tail postPayload) =
          payloadCells
            (SourceControlResourcePayloadContextAgrees.tail oldSuffix) := by
        rw [SourceControlResourcePayloadContextAgrees.tail_afterRejectedPullsAndPulledHead]
      _ = payloadCells head.outerAgrees := by
        rfl
      _ =
          (payloadCells payload).drop
            (selection.path.position.val + 1) := laterCellsExact
  exact
    ⟨{ route := route
       selectedPayloadCell := selectedPayloadCell
       selectedPayloadCellExact := selectedPayloadCellExact
       sourceScopeExact := by
         exact
           (congrArg PayloadCell.currentScope
              selectedPayloadCellExact).symm
       callStart := callStart
       startPosition := startPosition
       finish := finish
       readyClauses := readyClauses
       frontier := frontier
       sourceSteps := sourceSteps
       branch := branch
       clause := clause
       branchTail := branchTail
       copied := copied
       offset := offset
       tailOwnershipExact := tailOwnershipExact
       consumedSnapshot := by
         simpa [selectedPayloadCell] using consumedSnapshot
       activationChronology := by
         simpa [selectedPayloadCell, consumedSnapshot] using
           (SelectedHeadActivationChronology.ofRejectedPullsAndBeforePull
             selectedSnapshot beforeWellFormed frontier.rejectedPulls offset)
       controlOriginExact := by
         simpa [selectedPayloadCell, consumedSnapshot,
           RetainedCallPayloadSnapshot.afterRejectedPullsAndPulledHead,
           RetainedCallPayloadSnapshot.afterRejectedPulls,
           RetainedCallPayloadSnapshot.transportCursor,
           RetainedCallPayloadSnapshot.afterPulledHead] using
             selectedSnapshotOriginExact
       postLaterResources := head.laterResources
       postLaterContext := head.laterContext
       postLaterContextExact := rfl
       postPayload := by
         simpa [selectedPayloadCell] using postPayload
       postSegmentsExact := postSegmentsExact
       postLaterResourcesExact := laterResourcesExact
       postOuterExact := by rfl
       postHeadCellExact := by
         simpa [selectedPayloadCell] using postHeadCellExact
       postLaterCellsExact := by
         simpa [selectedPayloadCell] using postLaterCellsExact }⟩

end ScheduledPayloadAlignment

end PLeaTTa.PrologScheduledPayloadPostHeadBridge
