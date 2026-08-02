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
import PLeaTTa.Proofs.PrologRetainedPayloadSnapshotBridge

namespace PLeaTTa.PrologScheduledPayloadPostHeadBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.Resolver
open PLeaTTa.PrologAnswerSelectedHeadOffsetBridge
open PLeaTTa.PrologAnswerSourceCatchupBridge
open PLeaTTa.PrologBodyFailureResourceTransitionBridge
open PLeaTTa.PrologControlSegmentSpineBridge
open PLeaTTa.PrologPrefilterScanBridge
open PLeaTTa.PrologProductResourceContextBridge
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
  postLaterResources : List RetainedAlternativeSegment
  postLaterContext : ActiveProductContext
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
    (scope : CutScopeId) (session : Session) :
    Nonempty (ScheduledSelectedHeadTransition alignment selection scope session) := by
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
  have selectedSnapshot :
      RetainedCallPayloadSnapshot alpha support selection.selected.resource
        selection.selected.cursor head.segment head.laterSegments := by
    simpa only [resourceExact, cursorExact] using head.snapshot
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
      exactOwnership selection.selectedHead scope session
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
       postLaterResources := head.laterResources
       postLaterContext := head.laterContext
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
