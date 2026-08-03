-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologPersistentFreeScheduledRejectionCatchupBridge
Purpose: Relate a literal post-rejection payload selection to exact ranked
  source catch-up without recovering historical persistent packets.
Trusted boundary: none
Main exports:
  PayloadLocalPartitionAgrees,
  PayloadLocalSelection.partitionExact
-/
import PLeaTTa.Proofs.PrologPersistentFreeScheduledRejectionPullBridge
import PLeaTTa.Proofs.PrologBodyFailureOuterResourceActivationBridge

namespace PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologActivationMacro
open PrologAnswerSourceCatchupBridge
open PrologBodyFailureExhaustedResourceTransitionBridge
open PrologBodyFailureOuterResourceActivationBridge
open PrologBodyFailureOuterResourceCatchupBridge
open PrologBodyFailureResourceTransitionBridge
open PrologControlSegmentSpineBridge
open PrologPersistentFreeScheduledRejectionPullBridge
open PrologPrefilterScanBridge
open PrologProductResourceContextBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
open PrologScheduledPayloadLandingBridge
open PrologScheduledPayloadPathBridge
open PrologScheduledPayloadPostHeadBridge
open PrologScheduledPayloadRejectionBridge
open PrologSourceProductContextBridge

/-!
# Literal payload partition

The generic owned-resource classifier already constructs all ranked source
work needed to cross empty resources.  The structure below proves that its
existential first-live partition is exactly the occurrence selected by the
Type-valued payload path: same ordinal, frame, cursor, control segment, and
suffix.  Resource equality is used only after both decompositions have been
derived from the same literal spine; it never chooses the occurrence.
-/

/-- Cross a nonempty ranked prefix after its first predicate frame has
already been entered.

`sourceCatchupToFrame` starts from a completed inner focus and therefore
counts one promotion into every crossed frame.  After a selected head has
been rejected, the source is already at the first crossed frame's retained
cursor.  This theorem consumes that cursor's stored rejection work directly
and delegates only the remaining frames to `sourceCatchupToFrame`.  Its exact
count is therefore `rejectionSteps + crossedFrames.length`, with no extra
entry step at the active frame. -/
theorem CrossedEmptyResourceFramesAgrees.sourceCatchupToFrameFromEnteredHead
    {alpha : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {frame : ActiveProductFrame} {frames : ActiveProductContext}
    {rejectionSteps : Nat}
    (agreement :
      CrossedEmptyResourceFramesAgrees alpha (resource :: resources)
        (frame :: frames) rejectionSteps)
    (session : Session)
    (enteredCursor : PreparedCursor)
    (enteredShape :
      frame.retained = .clauses frame.predicateScope enteredCursor)
    (destination : ActiveProductFrame)
    (surviving : ActiveProductContext)
    (destinationCursor : PreparedCursor)
    (destinationShape :
      destination.retained =
        .clauses destination.predicateScope destinationCursor) :
    StepsN (rejectionSteps + (frame :: frames).length)
      (.running session
        (ActiveProductContext.plug
          (frames ++ destination :: surviving)
          (frameRetainedFrontier frame enteredCursor)))
      []
      (.running session
        (ActiveProductContext.plug surviving
          (frameRetainedFrontier destination destinationCursor))) := by
  cases agreement with
  | cons _resource _resources frame frames cursor finish count tailCount
      retainedShape ownership empty pulls finishEmpty tail =>
      have cursorExact : cursor = enteredCursor := by
        have retainedExact := retainedShape.symm.trans enteredShape
        injection retainedExact
      subst enteredCursor
      have rejected :
          StepsN count
            (.running session
              (ActiveProductContext.plug
                (frames ++ destination :: surviving)
                (frameRetainedFrontier frame cursor)))
            []
            (.running session
              (ActiveProductContext.plug
                (frames ++ destination :: surviving)
                (frameRetainedFrontier frame finish))) :=
        PLeaTTa.PrologBodyFailureOuterResourceCatchupBridge.RejectedPullsN.frameRetainedFrontierContextStepsN
          pulls (frames ++ destination :: surviving) frame session
      have finishCompleted :
          RawStep session (frameRetainedFrontier frame finish)
            [.completed] .none session (.terminal .completed) :=
        frameRetainedFrontier_exhausted session frame finish finishEmpty
      have rest :=
        PLeaTTa.PrologBodyFailureOuterResourceCatchupBridge.CrossedEmptyResourceFramesAgrees.sourceCatchupToFrame
          tail session (frameRetainedFrontier frame finish) finishCompleted
          destination surviving destinationCursor destinationShape
      have combined := rejected.trans rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using combined

/-- An empty crossed-frame spine has neither a hidden resource nor hidden
rejection work. -/
theorem CrossedEmptyResourceFramesAgrees.indicesOfFramesNil
    {alpha : List (LogicVar × String)}
    {resources : List RetainedAlternativeSegment}
    {rejectionSteps : Nat}
    (agreement :
      CrossedEmptyResourceFramesAgrees alpha resources [] rejectionSteps) :
    resources = [] ∧ rejectionSteps = 0 := by
  cases agreement
  exact ⟨rfl, rfl⟩

/-- A nonempty crossed-frame spine exposes the exact entered head cursor and
the ranked tail without eliminating a proof whose indices are structure
projections. -/
theorem CrossedEmptyResourceFramesAgrees.decomposeFramesCons
    {alpha : List (LogicVar × String)}
    {crossedResources : List RetainedAlternativeSegment}
    {frame : ActiveProductFrame} {frames : ActiveProductContext}
    {rejectionSteps : Nat}
    (agreement :
      CrossedEmptyResourceFramesAgrees alpha crossedResources
        (frame :: frames) rejectionSteps) :
    ∃ (resource : RetainedAlternativeSegment)
        (resources : List RetainedAlternativeSegment)
        (cursor finish : PreparedCursor) (count tailCount : Nat),
      crossedResources = resource :: resources ∧
      rejectionSteps = count + tailCount ∧
      frame.retained = .clauses frame.predicateScope cursor ∧
      resource.HasIndexedOwnershipAt alpha cursor ∧
      resource.alts = [] ∧
      RejectedPullsN count cursor finish ∧
      finish.remaining = [] ∧
      CrossedEmptyResourceFramesAgrees alpha resources frames tailCount := by
  cases agreement with
  | cons resource resources frame frames cursor finish count tailCount
      retainedShape ownership empty pulls finishEmpty tail =>
      exact
        ⟨resource, resources, cursor, finish, count, tailCount, rfl, rfl,
          retainedShape, ownership, empty, pulls, finishEmpty, tail⟩

/-- Exact positional agreement between a dependent payload selection and the
generic first-live source partition. -/
structure PayloadLocalPartitionAgrees
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (selection : PayloadLocalSelection payload)
    (partition :
      OuterResourceCatchupPartition alpha segments resources context) :
    Prop where
  crossedResourcesExact :
    partition.crossedResources =
      ((payloadCells payload).take selection.path.position.val).map
        PayloadCell.resource
  firstResourceExact :
    partition.first = selection.path.cell.resource
  survivingResourcesExact :
    partition.survivingResources =
      ((payloadCells payload).drop
        (selection.path.position.val + 1)).map PayloadCell.resource
  tailExact : partition.tail = selection.erased.localTail
  crossedFramesExact :
    partition.crossedFrames = context.take selection.path.position.val
  crossedDepthExact :
    partition.crossedFrames.length = selection.path.position.val
  firstFrameExact :
    partition.firstFrame =
      { callerScope := selection.path.cell.nextScope
        predicateScope := selection.path.cell.currentScope
        retained :=
          .clauses selection.path.cell.currentScope selection.path.cell.cursor
        callerRest := selection.path.cell.segment.references }
  survivingContextExact :
    partition.survivingContext = selection.route.head.data.laterContext
  firstCursorExact : partition.firstCursor = selection.path.cell.cursor
  crossedSegmentsExact :
    partition.crossedSegments = segments.take selection.path.position.val
  firstSegmentExact :
    partition.firstSegment = selection.path.cell.segment
  survivingSegmentsExact :
    partition.survivingSegments = selection.path.cell.outerSegments

namespace PayloadLocalSelection

/-- Exact constructor data at the head of the payload containing a live
selection.  Existence of the selection supplies the nonempty proof; no
resource comparison or Prop-valued classifier chooses the head. -/
def payloadHead
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (selection : PayloadLocalSelection payload) : PayloadHeadData payload :=
  (payloadHeadViewOfCellsNonempty payload (by
      intro empty
      have within := selection.path.position.isLt
      have lengthExact := congrArg List.length empty
      simp only [List.length_nil] at lengthExact
      omega)).data

/-- Source frontier after the literal payload head's predicate frame has
already been entered.  This is the phase reached after rejecting a selected
head: the active cursor is live, while every later frame remains outside it. -/
def enteredSourceFrontier
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (selection : PayloadLocalSelection payload) : Search :=
  let head :=
    PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.PayloadLocalSelection.payloadHead
      selection
  ActiveProductContext.plug head.laterContext
    (frameRetainedFrontier
      { callerScope := head.nextScope
        predicateScope := head.currentScope
        retained := .clauses head.currentScope head.cursor
        callerRest := head.segment.references }
      head.cursor)

end PayloadLocalSelection

/-- The generic first-live classifier selects the exact dependent payload
coordinate found by `classifyPayloadBank`.

The theorem is independent of scheduled history and executable persistent
state.  Ranked rejection work comes from indexed source ownership; the
Type-valued path supplies only the literal ordinal and selected payload cell. -/
theorem PayloadLocalSelection.partitionExact
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (selection : PayloadLocalSelection payload) :
    ∃ partition :
        OuterResourceCatchupPartition alpha segments resources context,
      PayloadLocalPartitionAgrees selection partition := by
  have resourcesExact :
      ((payloadCells payload).take selection.path.position.val).map
            PayloadCell.resource ++
          selection.path.cell.resource ::
            ((payloadCells payload).drop
              (selection.path.position.val + 1)).map PayloadCell.resource =
        resources := by
    calc
      _ =
          ((payloadCells payload).take selection.path.position.val ++
            selection.path.cell ::
              (payloadCells payload).drop
                (selection.path.position.val + 1)).map
            PayloadCell.resource := by simp
      _ = (payloadCells payload).map PayloadCell.resource := by
        rw [← selection.cells_exact]
      _ = resources := payloadCells_map_resource payload
  have earlierEmpty :
      ∀ resource ∈
          ((payloadCells payload).take selection.path.position.val).map
            PayloadCell.resource,
        resource.alts = [] := by
    intro resource member
    rcases List.mem_map.mp member with ⟨cell, cellMember, rfl⟩
    exact selection.earlier_empty cell cellMember
  have selectedLive : selection.path.cell.resource.alts ≠ [] := by
    rw [selection.selected_head]
    simp
  cases
      PrologBodyFailureExhaustedResourceTransitionBridge.SourceControlResourceContextAgrees.classifyLocal
        payload.alignment with
  | firstLive partition =>
      have partitionEmpty := partition.crossedWork.all_empty
      have partitionLive : partition.first.alts ≠ [] := by
        rw [partition.firstHead]
        simp
      have same :
          ((payloadCells payload).take selection.path.position.val).map
                PayloadCell.resource ++
              selection.path.cell.resource ::
                ((payloadCells payload).drop
                  (selection.path.position.val + 1)).map
                    PayloadCell.resource =
            partition.crossedResources ++
              partition.first :: partition.survivingResources :=
        resourcesExact.trans partition.resourcesEq
      obtain ⟨crossedEq, firstEq, survivingEq⟩ :=
        PLeaTTa.PrologScheduledPayloadLandingBridge.ScheduledPayloadAlignment.first_live_resource_decomposition_unique
          (((payloadCells payload).take selection.path.position.val).map
            PayloadCell.resource)
          selection.path.cell.resource
          (((payloadCells payload).drop
              (selection.path.position.val + 1)).map PayloadCell.resource)
          partition.crossedResources partition.first
          partition.survivingResources same earlierEmpty partitionEmpty
          selectedLive partitionLive
      have tailEq : partition.tail = selection.erased.localTail := by
        have heads :
            PLeaTTa.Alt.br partition.goals partition.binding ::
                partition.tail =
              PLeaTTa.Alt.br selection.erased.goals
                  selection.erased.binding :: selection.erased.localTail := by
          calc
            _ = partition.first.alts := partition.firstHead.symm
            _ = selection.path.cell.resource.alts := by rw [firstEq]
            _ = _ := selection.selected_head
        exact (List.cons.inj heads).2
      let head := selection.route.head.data
      have headCellExact : head.cell = selection.path.cell :=
        selection.route.headCell_exact
      have crossedFramesLength :
          partition.crossedFrames.length =
            selection.path.position.val := by
        calc
          partition.crossedFrames.length =
              partition.crossedResources.length :=
            partition.crossedWork.length_eq.symm
          _ =
              (((payloadCells payload).take selection.path.position.val).map
                PayloadCell.resource).length := by rw [crossedEq]
          _ = selection.path.position.val := by
            rw [List.length_map, List.length_take,
              Nat.min_eq_left (Nat.le_of_lt selection.path.position.isLt)]
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
               callerRest := head.segment.references } :
              ActiveProductFrame) :: head.laterContext :=
        head.contextExact
      have frameAndContext :=
        List.cons.inj (partitionContextDrop.symm.trans headContextDrop)
      have headFrameSelected :
          ({ callerScope := head.nextScope
             predicateScope := head.currentScope
             retained := .clauses head.currentScope head.cursor
             callerRest := head.segment.references } :
            ActiveProductFrame) =
          { callerScope := selection.path.cell.nextScope
            predicateScope := selection.path.cell.currentScope
            retained :=
              .clauses selection.path.cell.currentScope
                selection.path.cell.cursor
            callerRest := selection.path.cell.segment.references } := by
        simpa [PayloadHeadData.cell] using
          congrArg
            (fun cell : PayloadCell alpha support =>
              ({ callerScope := cell.nextScope
                 predicateScope := cell.currentScope
                 retained := .clauses cell.currentScope cell.cursor
                 callerRest := cell.segment.references } :
                ActiveProductFrame))
            headCellExact
      have firstFrameExact :
          partition.firstFrame =
            { callerScope := selection.path.cell.nextScope
              predicateScope := selection.path.cell.currentScope
              retained :=
                .clauses selection.path.cell.currentScope
                  selection.path.cell.cursor
              callerRest := selection.path.cell.segment.references } :=
        frameAndContext.1.trans headFrameSelected
      have survivingContextExact :
          partition.survivingContext = head.laterContext :=
        frameAndContext.2
      have firstCursorExact :
          partition.firstCursor = selection.path.cell.cursor := by
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
              (((payloadCells payload).take selection.path.position.val).map
                PayloadCell.resource).length := by rw [crossedEq]
          _ = selection.path.position.val := by
            rw [List.length_map, List.length_take,
              Nat.min_eq_left (Nat.le_of_lt selection.path.position.isLt)]
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
          partition.firstSegment = selection.path.cell.segment :=
        segmentAndTail.1.trans
          (congrArg PayloadCell.segment headCellExact)
      have survivingSegmentsExact :
          partition.survivingSegments =
            selection.path.cell.outerSegments :=
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
          { crossedResourcesExact := crossedEq.symm
            firstResourceExact := firstEq.symm
            survivingResourcesExact := survivingEq.symm
            tailExact := tailEq
            crossedFramesExact := crossedFramesExact
            crossedDepthExact := crossedFramesLength
            firstFrameExact := firstFrameExact
            survivingContextExact := survivingContextExact
            firstCursorExact := firstCursorExact
            crossedSegmentsExact := crossedSegmentsExact
            firstSegmentExact := firstSegmentExact
            survivingSegmentsExact := survivingSegmentsExact }⟩
  | allEmpty partition =>
      have selectedMember : selection.path.cell.resource ∈ resources := by
        apply
          (congrArg
            (fun bank => selection.path.cell.resource ∈ bank)
            resourcesExact).mp
        simp
      have selectedEmpty :=
        partition.crossedWork.all_empty selection.path.cell.resource
          selectedMember
      exact False.elim (selectedLive selectedEmpty)

/-- Catch the source up from an already-entered literal payload head to the
first live resource of a ranked partition over the same payload context.

The exact count is uniform across both shapes:

* at position zero, no frame is entered or crossed and both summands are zero;
* at a later position, the active crossed cursor is consumed in place and
  only the remaining frames perform promotion steps.

Thus there is no inherited body-failure `+1`, and every conservative source
rejection hidden by a fine-empty bank remains explicitly counted. -/
theorem PayloadLocalSelection.catchupToFirstLive
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (selection : PayloadLocalSelection payload)
    (partition :
      OuterResourceCatchupPartition alpha segments resources context)
    (session : Session) :
    StepsN (partition.rejectionSteps + partition.crossedFrames.length)
      (.running session
        (PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.PayloadLocalSelection.enteredSourceFrontier
          selection))
      []
      (.running session (firstLiveSourceFrontier partition)) := by
  let head :=
    PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.PayloadLocalSelection.payloadHead
      selection
  let enteredFrame : ActiveProductFrame :=
    { callerScope := head.nextScope
      predicateScope := head.currentScope
      retained := .clauses head.currentScope head.cursor
      callerRest := head.segment.references }
  have headContext :
      context = enteredFrame :: head.laterContext := by
    simpa [enteredFrame] using head.contextExact
  cases crossedFramesEq : partition.crossedFrames with
  | nil =>
      have work :
          CrossedEmptyResourceFramesAgrees alpha partition.crossedResources
            [] partition.rejectionSteps := by
        simpa [crossedFramesEq] using partition.crossedWork
      obtain ⟨crossedResourcesEq, rejectionStepsEq⟩ :=
        PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.CrossedEmptyResourceFramesAgrees.indicesOfFramesNil
          work
      have partitionContext :
          context = partition.firstFrame :: partition.survivingContext := by
        simpa [crossedFramesEq] using partition.contextEq
      have frameAndContext :=
        List.cons.inj (headContext.symm.trans partitionContext)
      have cursorExact : head.cursor = partition.firstCursor := by
        have retained := partition.firstRetainedShape
        rw [← frameAndContext.1] at retained
        dsimp [enteredFrame] at retained
        injection retained
      have sourceExact :
          PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.PayloadLocalSelection.enteredSourceFrontier
              selection =
            firstLiveSourceFrontier partition := by
        change
          ActiveProductContext.plug head.laterContext
              (frameRetainedFrontier enteredFrame head.cursor) =
            ActiveProductContext.plug partition.survivingContext
              (frameRetainedFrontier partition.firstFrame
                partition.firstCursor)
        rw [frameAndContext.1, frameAndContext.2, cursorExact]
      simpa [crossedFramesEq, rejectionStepsEq, sourceExact] using
        (StepsN.zero
          (.running session (firstLiveSourceFrontier partition)))
  | cons frame frames =>
      have work :
          CrossedEmptyResourceFramesAgrees alpha partition.crossedResources
            (frame :: frames) partition.rejectionSteps := by
        simpa [crossedFramesEq] using partition.crossedWork
      obtain
        ⟨resource, resources, cursor, finish, count, tailCount,
          crossedResourcesEq, rejectionStepsEq, retainedShape, ownership,
          empty, pulls, finishEmpty, tail⟩ :=
        PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.CrossedEmptyResourceFramesAgrees.decomposeFramesCons
          work
      have partitionContext :
          context =
            frame ::
              (frames ++ partition.firstFrame ::
                partition.survivingContext) := by
        simpa [crossedFramesEq, List.append_assoc] using partition.contextEq
      have frameAndContext :=
        List.cons.inj (headContext.symm.trans partitionContext)
      have cursorExact : head.cursor = cursor := by
        have retained := retainedShape
        rw [← frameAndContext.1] at retained
        dsimp [enteredFrame] at retained
        injection retained
      have crossed :=
        PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.CrossedEmptyResourceFramesAgrees.sourceCatchupToFrameFromEnteredHead
          (CrossedEmptyResourceFramesAgrees.cons resource resources frame
            frames cursor finish count tailCount retainedShape ownership empty
            pulls finishEmpty tail)
          session cursor retainedShape partition.firstFrame
          partition.survivingContext partition.firstCursor
          partition.firstRetainedShape
      have sourceExact :
          PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.PayloadLocalSelection.enteredSourceFrontier
              selection =
            ActiveProductContext.plug
              (frames ++ partition.firstFrame :: partition.survivingContext)
              (frameRetainedFrontier frame cursor) := by
        change
          ActiveProductContext.plug head.laterContext
              (frameRetainedFrontier enteredFrame head.cursor) = _
        rw [frameAndContext.1, frameAndContext.2, cursorExact]
      rw [sourceExact]
      simpa [crossedFramesEq, rejectionStepsEq, firstLiveSourceFrontier]
        using crossed

/-- Full source-only catch-up to the exact retained head chosen by the
dependent fine payload classifier.

The first phase crosses the classifier's ranked empty prefix from an already
entered head; the second consumes the conservative rejection prefix inside
the selected live resource.  Both phases are silent, share the current
session literally, and expose the certified clause occurrence immediately
before source selection. -/
theorem PayloadLocalSelection.catchupToSelectedReady
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (selection : PayloadLocalSelection payload)
    (session : Session) :
    ∃ (partition :
          OuterResourceCatchupPartition alpha segments resources context)
        (count : Nat)
        (skippedBranches : List ClauseBranch)
        (skippedClauses candidates : List PLeaTTa.Clause)
        (finish : PreparedCursor)
        (branch : ClauseBranch) (clause : PLeaTTa.Clause)
        (branchTail : List ClauseBranch)
        (clauseTail : List PLeaTTa.Clause)
        (copied : PLeaTTa.Clause),
      PayloadLocalPartitionAgrees selection partition ∧
      partition.firstCursor.remaining =
        skippedBranches ++ (branch :: branchTail) ∧
      candidates = skippedClauses ++ (clause :: clauseTail) ∧
      skippedBranches.length = count ∧
      skippedClauses.length = count ∧
      StepsN
        (partition.rejectionSteps + partition.crossedFrames.length + count)
        (.running session
          (PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.PayloadLocalSelection.enteredSourceFrontier
            selection))
        []
        (.running session
          (firstLiveReadySourceFrontier partition finish)) ∧
      RejectedPrefixPulledHeadOffsetAgrees alpha partition.firstCursor finish
        count branch clause branchTail copied partition.first partition.tail ∧
      resolutionAlt partition.first.argsv partition.first.args
          partition.first.res partition.first.rest partition.first.binding
          partition.first.qterm partition.first.barrier
          partition.first.counter clause =
        .br partition.goals partition.binding := by
  obtain ⟨partition, partitionExact⟩ :=
    PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.PayloadLocalSelection.partitionExact
      selection
  obtain
    ⟨count, skippedBranches, skippedClauses, candidates, finish, branch,
      clause, branchTail, clauseTail, copied, cursorSplit, candidatesSplit,
      branchCount, clauseCount, prefixSteps, rejectedPrefix, headExact⟩ :=
    PLeaTTa.PrologBodyFailureOuterResourceActivationBridge.OuterResourceCatchupPartition.consumeRejectedPrefix
      partition session
  have crossed :=
    PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.PayloadLocalSelection.catchupToFirstLive
      selection partition session
  have combined := crossed.trans prefixSteps
  refine
    ⟨partition, count, skippedBranches, skippedClauses, candidates, finish,
      branch, clause, branchTail, clauseTail, copied, partitionExact,
      cursorSplit, candidatesSplit, branchCount, clauseCount, ?_,
      rejectedPrefix, headExact⟩
  simpa [Nat.add_assoc] using combined

/-- Provenance-preserving form of `catchupToSelectedReady`.

The older theorem exposes the pulled-head offset consumed by downstream
execution.  This companion retains the stronger `SelectedReadyFrontier`,
including the original supported candidate spine and the exact maximal
prefilter-rejected prefix.  That information is necessary to distinguish
duplicate-valued occurrences and to prove exact source-only catch-up counts;
it is derived from the same owned resource and scan, never reconstructed from
the selected result. -/
theorem PayloadLocalSelection.catchupToSelectedFrontier
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (selection : PayloadLocalSelection payload)
    (session : Session) :
    ∃ (partition :
          OuterResourceCatchupPartition alpha segments resources context)
        (callStart : PreparedCursor) (startPosition : Nat)
        (finish : PreparedCursor) (readyClauses : List PLeaTTa.Clause)
        (frontier :
          SelectedReadyFrontier alpha partition.first
            partition.goals partition.binding partition.tail
            callStart partition.firstCursor finish
            startPosition readyClauses),
      PayloadLocalPartitionAgrees selection partition ∧
      StepsN
        (partition.rejectionSteps + partition.crossedFrames.length +
          frontier.rejectedCount)
        (.running session
          (PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.PayloadLocalSelection.enteredSourceFrontier
            selection))
        []
        (.running session
          (firstLiveReadySourceFrontier partition finish)) := by
  obtain ⟨partition, partitionExact⟩ :=
    PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.PayloadLocalSelection.partitionExact
      selection
  rcases partition.firstOwnership with
    ⟨callStart, startPosition, ownership⟩
  obtain ⟨finish, readyClauses, frontier, _sourceSteps, _positioned⟩ :=
    PLeaTTa.PrologAnswerSourceCatchupBridge.RetainedAlternativeSegment.catchupSelectedAt
      ownership partition.firstHead partition.firstFrame.predicateScope
      session
  have crossed :=
    PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.PayloadLocalSelection.catchupToFirstLive
      selection partition session
  have rejected :=
    PLeaTTa.PrologBodyFailureOuterResourceCatchupBridge.RejectedPullsN.frameRetainedFrontierContextStepsN
      frontier.rejectedPulls partition.survivingContext partition.firstFrame
      session
  have combined := crossed.trans rejected
  exact
    ⟨partition, callStart, startPosition, finish, readyClauses, frontier,
      partitionExact,
      by
        simpa [Nat.add_assoc, firstLiveReadySourceFrontier] using combined⟩

/-! ## Instantiation at the real scheduled rejection frontier -/

namespace ScheduledSelectedHeadTransition

/-- Ranked source partition for the literal payload after one selected head
has been consumed and rejected. -/
abbrev PostRejectedPayloadPartition
    {before :
      PrologPersistentFreeScheduledPayloadBridge.RepresentativePersistentFreeScheduledPayloadState}
    {ready : PrologRootClosedAnswerBridge.RootClosedAnswerReady before}
    {selection :
      ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session) :=
  OuterResourceCatchupPartition before.carrier.index.alpha
    (transition.selectedPayloadCell.segment ::
      transition.selectedPayloadCell.outerSegments)
    (afterPulledHead selection.selected.resource selection.localTail ::
      transition.postLaterResources)
    ({ callerScope := transition.selectedPayloadCell.nextScope
       predicateScope := transition.selectedPayloadCell.currentScope
       retained :=
         .clauses transition.selectedPayloadCell.currentScope
           (transition.finish.advance transition.branch transition.branchTail)
       callerRest := transition.selectedPayloadCell.segment.references } ::
      transition.postLaterContext)

/-- The independent source state immediately after rejecting the previously
selected occurrence is exactly the entered head of `postPayload`.

The equality follows from the constructor-indexed payload context.  It does
not search for the consumed resource or recover any historical session. -/
theorem rejectedSourceFrontier_eq_entered
    {before :
      PrologPersistentFreeScheduledPayloadBridge.RepresentativePersistentFreeScheduledPayloadState}
    {ready : PrologRootClosedAnswerBridge.RootClosedAnswerReady before}
    {selection :
      ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session)
    (next : PayloadLocalSelection transition.postPayload) :
    PrologScheduledPayloadRejectionBridge.ScheduledSelectedHeadTransition.sourceFrontier
        transition
        (transition.finish.advance transition.branch transition.branchTail) =
      PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.PayloadLocalSelection.enteredSourceFrontier
        next := by
  let head :=
    PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.PayloadLocalSelection.payloadHead
      next
  let enteredFrame : ActiveProductFrame :=
    { callerScope := head.nextScope
      predicateScope := head.currentScope
      retained := .clauses head.currentScope head.cursor
      callerRest := head.segment.references }
  let postFrame : ActiveProductFrame :=
    { callerScope := transition.selectedPayloadCell.nextScope
      predicateScope := transition.selectedPayloadCell.currentScope
      retained :=
        .clauses transition.selectedPayloadCell.currentScope
          (transition.finish.advance transition.branch transition.branchTail)
      callerRest := transition.selectedPayloadCell.segment.references }
  have contextExact :
      postFrame :: transition.postLaterContext =
        enteredFrame :: head.laterContext := by
    simpa [postFrame, enteredFrame] using head.contextExact
  have frameAndContext := List.cons.inj contextExact
  have cursorExact :
      transition.finish.advance transition.branch transition.branchTail =
        head.cursor := by
    have retainedExact :=
      congrArg ActiveProductFrame.retained frameAndContext.1
    dsimp [postFrame, enteredFrame] at retainedExact
    injection retainedExact
  change
    ActiveProductContext.plug transition.postLaterContext
        (frameRetainedFrontier
          (PrologScheduledPayloadRejectionBridge.ScheduledSelectedHeadTransition.sourceFrame
            transition)
          (transition.finish.advance transition.branch
            transition.branchTail)) =
      ActiveProductContext.plug head.laterContext
        (frameRetainedFrontier enteredFrame head.cursor)
  have focusExact :
      frameRetainedFrontier
          (PrologScheduledPayloadRejectionBridge.ScheduledSelectedHeadTransition.sourceFrame
            transition)
          (transition.finish.advance transition.branch
            transition.branchTail) =
        frameRetainedFrontier enteredFrame head.cursor := by
    calc
      _ = frameRetainedFrontier postFrame
            (transition.finish.advance transition.branch
              transition.branchTail) := rfl
      _ = frameRetainedFrontier enteredFrame
            (transition.finish.advance transition.branch
              transition.branchTail) :=
        congrArg
          (fun frame =>
            frameRetainedFrontier frame
              (transition.finish.advance transition.branch
                transition.branchTail))
          frameAndContext.1
      _ = frameRetainedFrontier enteredFrame head.cursor :=
        congrArg (frameRetainedFrontier enteredFrame) cursorExact
  calc
    _ = ActiveProductContext.plug transition.postLaterContext
          (frameRetainedFrontier enteredFrame head.cursor) :=
      congrArg (ActiveProductContext.plug transition.postLaterContext)
        focusExact
    _ = _ :=
      congrArg
        (fun frames =>
          ActiveProductContext.plug frames
            (frameRetainedFrontier enteredFrame head.cursor))
        frameAndContext.2

/-- Continue the independent source from the real rejected-head frontier to
the exact next clause head already selected by the fine payload pull.

This is the live arm of the post-rejection correspondence.  It retains the
ranked partition and the selected clause offset, so a later composition can
identify the fine installed head without comparing resource values. -/
theorem catchupAfterRejectedHead
    {before :
      PrologPersistentFreeScheduledPayloadBridge.RepresentativePersistentFreeScheduledPayloadState}
    {ready : PrologRootClosedAnswerBridge.RootClosedAnswerReady before}
    {selection :
      ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session)
    (next : PayloadLocalSelection transition.postPayload) :
    ∃ (partition : PostRejectedPayloadPartition transition)
        (count : Nat) (finish : PreparedCursor)
        (branch : ClauseBranch) (clause : PLeaTTa.Clause)
        (branchTail : List ClauseBranch) (copied : PLeaTTa.Clause),
      PayloadLocalPartitionAgrees next partition ∧
      StepsN
        (partition.rejectionSteps + partition.crossedFrames.length + count)
        (.running before.carrier.index.session
          (PrologScheduledPayloadRejectionBridge.ScheduledSelectedHeadTransition.sourceFrontier
            transition
            (transition.finish.advance transition.branch
              transition.branchTail)))
        []
        (.running before.carrier.index.session
          (firstLiveReadySourceFrontier partition finish)) ∧
      RejectedPrefixPulledHeadOffsetAgrees before.carrier.index.alpha
        partition.firstCursor finish count branch clause branchTail copied
        partition.first partition.tail ∧
      resolutionAlt partition.first.argsv partition.first.args
          partition.first.res partition.first.rest partition.first.binding
          partition.first.qterm partition.first.barrier
          partition.first.counter clause =
        .br partition.goals partition.binding := by
  obtain
    ⟨partition, count, skippedBranches, skippedClauses, candidates, finish,
      branch, clause, branchTail, clauseTail, copied, partitionExact,
      cursorSplit, candidatesSplit, branchCount, clauseCount, sourceRun,
      rejectedPrefix, headExact⟩ :=
    PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.PayloadLocalSelection.catchupToSelectedReady
      next before.carrier.index.session
  have startExact :=
    PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.ScheduledSelectedHeadTransition.rejectedSourceFrontier_eq_entered
      transition next
  have actualRun :
      StepsN
        (partition.rejectionSteps + partition.crossedFrames.length + count)
        (.running before.carrier.index.session
          (PrologScheduledPayloadRejectionBridge.ScheduledSelectedHeadTransition.sourceFrontier
            transition
            (transition.finish.advance transition.branch
              transition.branchTail)))
        []
        (.running before.carrier.index.session
          (firstLiveReadySourceFrontier partition finish)) := by
    rw [startExact]
    exact sourceRun
  exact
    ⟨partition, count, finish, branch, clause, branchTail, copied,
      partitionExact, actualRun, rejectedPrefix, headExact⟩

end ScheduledSelectedHeadTransition

namespace ScheduledRejectedHeadRelates

/-- Compose the already-proved post-answer rejected-head run with the live
source catch-up to the fine classifier's next selected occurrence. -/
theorem continueToNextSelectedReady
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before :
      PrologPersistentFreeScheduledPayloadBridge.RepresentativePersistentFreeScheduledPayloadState}
    {ready : PrologRootClosedAnswerBridge.RootClosedAnswerReady before}
    {selection :
      ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    {transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session}
    {oldPartition :
      PrologScheduledPayloadRejectionBridge.RootPayloadPartition before}
    (agreement :
      ScheduledRejectedHeadRelates prog gt before ready selection scope
        transition oldPartition)
    (next : PayloadLocalSelection transition.postPayload) :
    ∃ (partition :
          ScheduledSelectedHeadTransition.PostRejectedPayloadPartition
            transition)
        (count : Nat) (finish : PreparedCursor)
        (branch : ClauseBranch) (clause : PLeaTTa.Clause)
        (branchTail : List ClauseBranch) (copied : PLeaTTa.Clause),
      PayloadLocalPartitionAgrees next partition ∧
      StepsN
        (PrologScheduledPayloadRejectionBridge.postAnswerRejectedHeadCount
            ready transition oldPartition +
          (partition.rejectionSteps +
            partition.crossedFrames.length + count))
        (.running before.carrier.index.session ready.result.targetNext)
        []
        (.running before.carrier.index.session
          (firstLiveReadySourceFrontier partition finish)) ∧
      RejectedPrefixPulledHeadOffsetAgrees before.carrier.index.alpha
        partition.firstCursor finish count branch clause branchTail copied
        partition.first partition.tail ∧
      resolutionAlt partition.first.argsv partition.first.args
          partition.first.res partition.first.rest partition.first.binding
          partition.first.qterm partition.first.barrier
          partition.first.counter clause =
        .br partition.goals partition.binding := by
  obtain
    ⟨partition, count, finish, branch, clause, branchTail, copied,
      partitionExact, catchup, rejectedPrefix, headExact⟩ :=
    PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.ScheduledSelectedHeadTransition.catchupAfterRejectedHead
      transition next
  have combined := agreement.postAnswerSourceRun.trans catchup
  exact
    ⟨partition, count, finish, branch, clause, branchTail, copied,
      partitionExact, combined, rejectedPrefix, headExact⟩

end ScheduledRejectedHeadRelates

/-- Proof-only certificate attached to a constructively selected live payload
successor.  Its existential source partition remains in `Prop`; the dependent
`next` selection is an explicit input and therefore remains available to the
next executable correspondence step.  The `_agreement` index is intentionally
retained: it pins `ready`, `scope`, and `oldPartition` for the exact run count
without exposing or inspecting the proof value. -/
def ScheduledRejectedLiveCatchupCertificate
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before :
      PrologPersistentFreeScheduledPayloadBridge.RepresentativePersistentFreeScheduledPayloadState}
    {ready : PrologRootClosedAnswerBridge.RootClosedAnswerReady before}
    {selection :
      ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    {transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session}
    {oldPartition :
      PrologScheduledPayloadRejectionBridge.RootPayloadPartition before}
    (_agreement :
      ScheduledRejectedHeadRelates prog gt before ready selection scope
        transition oldPartition)
    (next : PayloadLocalSelection transition.postPayload) : Prop :=
  ∃ (partition :
        ScheduledSelectedHeadTransition.PostRejectedPayloadPartition
          transition)
      (count : Nat) (finish : PreparedCursor)
      (branch : ClauseBranch) (clause : PLeaTTa.Clause)
      (branchTail : List ClauseBranch) (copied : PLeaTTa.Clause),
    PayloadLocalPartitionAgrees next partition ∧
    StepsN
      (PrologScheduledPayloadRejectionBridge.postAnswerRejectedHeadCount
          ready transition oldPartition +
        (partition.rejectionSteps +
          partition.crossedFrames.length + count))
      (.running before.carrier.index.session ready.result.targetNext)
      []
      (.running before.carrier.index.session
        (firstLiveReadySourceFrontier partition finish)) ∧
    RejectedPrefixPulledHeadOffsetAgrees before.carrier.index.alpha
      partition.firstCursor finish count branch clause branchTail copied
      partition.first partition.tail ∧
    (PLeaTTa.Goal.eq
          (.expr (partition.first.args ++ [partition.first.res]))
          (.expr (copied.params ++ [copied.result])) ::
        copied.body ++ partition.first.rest =
      next.erased.goals) ∧
    partition.first.binding = next.erased.binding

namespace ScheduledRejectedHeadRelates

/-- Construct the complete source certificate for an already selected live
fine successor.  This theorem may eliminate source existentials because its
result remains in `Prop`; no runtime successor data is recovered from them. -/
theorem liveCatchupCertificate
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before :
      PrologPersistentFreeScheduledPayloadBridge.RepresentativePersistentFreeScheduledPayloadState}
    {ready : PrologRootClosedAnswerBridge.RootClosedAnswerReady before}
    {selection :
      ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    {transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session}
    {oldPartition :
      PrologScheduledPayloadRejectionBridge.RootPayloadPartition before}
    (agreement :
      ScheduledRejectedHeadRelates prog gt before ready selection scope
        transition oldPartition)
    (next : PayloadLocalSelection transition.postPayload) :
    ScheduledRejectedLiveCatchupCertificate agreement next := by
  obtain
    ⟨partition, count, finish, branch, clause, branchTail, copied,
      partitionExact, sourceRun, rejectedPrefix, headExact⟩ :=
    PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.ScheduledRejectedHeadRelates.continueToNextSelectedReady
      agreement next
  have banksEqual :
      PLeaTTa.Alt.br partition.goals partition.binding :: partition.tail =
        PLeaTTa.Alt.br next.erased.goals next.erased.binding ::
          next.erased.localTail := by
    calc
      _ = partition.first.alts := partition.firstHead.symm
      _ = next.path.cell.resource.alts := by
        rw [partitionExact.firstResourceExact]
      _ = _ := next.selected_head
  have selectedFields := List.cons.inj banksEqual
  have goalsBinding := PLeaTTa.Alt.br.inj selectedFields.1
  have selectedHead :
      PLeaTTa.Alt.br
          (PLeaTTa.Goal.eq
                (.expr (partition.first.args ++ [partition.first.res]))
                (.expr (copied.params ++ [copied.result])) ::
              copied.body ++ partition.first.rest)
          partition.first.binding =
        PLeaTTa.Alt.br partition.goals partition.binding := by
    rw [rejectedPrefix.offset.copiedExact]
    simpa [resolutionAlt] using headExact
  have sourceFields := PLeaTTa.Alt.br.inj selectedHead
  exact
    ⟨partition, count, finish, branch, clause, branchTail, copied,
      partitionExact, sourceRun, rejectedPrefix,
      sourceFields.1.trans goalsBinding.1,
      sourceFields.2.trans goalsBinding.2⟩

end ScheduledRejectedHeadRelates

/-- Joint classification of the real fine successor and the independent
source catch-up after a scheduled selected-head rejection.

The `Type`-valued live constructor exposes the classifier's dependent
successor directly.  Its source derivation is attached as a proof-only
certificate, so no `Prop` existential is eliminated to manufacture runtime
data.  The exhausted constructor is deliberately fine-only: source termination
after total payload exhaustion remains a separate obligation rather than being
inferred from an empty executable bank. -/
inductive ScheduledRejectedFineSourceCatchupOutcome
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before :
      PrologPersistentFreeScheduledPayloadBridge.RepresentativePersistentFreeScheduledPayloadState}
    {ready : PrologRootClosedAnswerBridge.RootClosedAnswerReady before}
    {selection :
      ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    {transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session}
    {oldPartition :
      PrologScheduledPayloadRejectionBridge.RootPayloadPartition before}
    (agreement :
      ScheduledRejectedHeadRelates prog gt before ready selection scope
        transition oldPartition) : Type where
  | localLive
      (next : PayloadLocalSelection transition.postPayload)
      (fineCurrentExact :
        (rejectedFineState before).control.cur =
          some (next.erased.goals, next.erased.binding))
      (fineAltsExact :
        (rejectedFineState before).control.alts =
          next.erased.localTail ++ PLeaTTa.Alt.barrier ::
            flattenOwnedAlts
              (((payloadCells transition.postPayload).drop
                  (next.path.position.val + 1)).map
                PayloadCell.resource) [])
      (fineBarriersExact :
        (rejectedFineState before).control.barriers =
          PLeaTTa.pushBarrierCache
            next.path.cell.snapshot.controlOrigin.outerBarriers)
      (certificate : ScheduledRejectedLiveCatchupCertificate agreement next) :
      ScheduledRejectedFineSourceCatchupOutcome agreement
  | exhausted
      (allEmpty :
        ∀ cell ∈ payloadCells transition.postPayload,
          cell.resource.alts = [])
      (fineCurrentExact : (rejectedFineState before).control.cur = none)
      (fineAltsExact : (rejectedFineState before).control.alts = [])
      (fineTerminal : PLeaTTa.Terminal (rejectedFineState before).toConf) :
      ScheduledRejectedFineSourceCatchupOutcome agreement

namespace ScheduledRejectedHeadRelates

/-- Classify the actual fine rejected-head successor.  The classifier itself
supplies the `Type`-valued successor; the source theorem supplies only its
proof certificate. -/
def classifyFineAndCatchup
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before :
      PrologPersistentFreeScheduledPayloadBridge.RepresentativePersistentFreeScheduledPayloadState}
    {ready : PrologRootClosedAnswerBridge.RootClosedAnswerReady before}
    {selection :
      ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    {transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session}
    {oldPartition :
      PrologScheduledPayloadRejectionBridge.RootPayloadPartition before}
    (agreement :
      ScheduledRejectedHeadRelates prog gt before ready selection scope
        transition oldPartition) :
    ScheduledRejectedFineSourceCatchupOutcome agreement :=
  match
      PLeaTTa.PrologPersistentFreeScheduledRejectionPullBridge.ScheduledSelectedHeadTransition.classifyRejectedFinePull
        (transition := transition) with
  | .localLive next fineCurrent fineAlts fineBarriers =>
      .localLive next fineCurrent fineAlts fineBarriers
        (liveCatchupCertificate agreement next)
  | .exhausted allEmpty fineCurrent fineAlts terminal =>
      .exhausted allEmpty fineCurrent fineAlts terminal

end ScheduledRejectedHeadRelates

end PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge
