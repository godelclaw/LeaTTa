-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologScheduledPayloadPathBridge
Purpose: Select one immutable retained-call payload by a coordinate indexed
  by the literal dependent payload zipper
Trusted boundary: none
Main exports:
  PayloadCell,
  SourceControlResourcePayloadContextAgrees.payloadCells,
  PayloadPath,
  PayloadPath.cell
-/
import PLeaTTa.Proofs.PrologNestedCallChainBridge
import PLeaTTa.Proofs.PrologScheduledHistoryBuildBridge

namespace PLeaTTa.PrologScheduledPayloadPathBridge

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.Resolver
open PrologControlSegmentSpineBridge
open PrologNestedCallChainBridge
open PrologProductResourceContextBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
open PrologScheduledHistoryBuildBridge
open PrologSourceProductContextBridge

/-!
# Exact paths through the retained payload zipper

Executable resources are not occurrence identifiers: two distinct source
clauses may own extensionally equal alternative banks.  A later scheduled
answer therefore must not recover its immutable payload snapshot by comparing
resources.  The coordinate below is indexed by the literal Type-valued
payload zipper.  A coordinate made for another zipper, even one with the same
length and equal resources, is a different type.
-/

/-- One selected cell of the retained payload zipper, including the exact
immutable snapshot whose dependent indices prevent cursor/resource mixing. -/
structure PayloadCell (alpha support : List (LogicVar × String)) where
  currentBarrier : Nat
  currentScope : CutScopeId
  nextScope : CutScopeId
  outerScope : CutScopeId
  segment : ControlSegment
  outerSegments : List ControlSegment
  resource : RetainedAlternativeSegment
  cursor : PreparedCursor
  ownership : resource.HasIndexedOwnershipAt alpha cursor
  snapshot :
    RetainedCallPayloadSnapshot alpha support resource cursor segment
      outerSegments

namespace PayloadCell

/-- Runtime identity retained by the existing heterogeneous phase carrier.
The snapshot stays available in `PayloadCell`; this projection erases it only
for comparison with the already-audited identity spine. -/
def identity
    {alpha support : List (LogicVar × String)}
    (cell : PayloadCell alpha support) : PayloadCellIdentity :=
  { currentBarrier := cell.currentBarrier
    currentScope := cell.currentScope
    nextScope := cell.nextScope
    outerScope := cell.outerScope
    segment := cell.segment
    resource := cell.resource
    cursor := cell.cursor }

/-- Erase only the immutable snapshot and typed control labels while retaining
the local occurrence identity used by a scheduled-history build. -/
def historyCell
    {alpha support : List (LogicVar × String)}
    (cell : PayloadCell alpha support) : ScheduledHistoryCell alpha :=
  { resource := cell.resource
    cursor := cell.cursor
    ownership := cell.ownership }

@[simp] theorem historyCell_resource
    {alpha support : List (LogicVar × String)}
    (cell : PayloadCell alpha support) :
    cell.historyCell.resource = cell.resource := rfl

@[simp] theorem historyCell_cursor
    {alpha support : List (LogicVar × String)}
    (cell : PayloadCell alpha support) :
    cell.historyCell.cursor = cell.cursor := rfl

end PayloadCell

/-- Preserve every dependent snapshot while exposing the payload zipper as an
ordinary ordered list.  This function eliminates Type-valued payload data,
not a Prop-valued agreement proof. -/
def payloadCells
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext} :
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer) →
      List (PayloadCell alpha support)
  | .nil _ _ => []
  | .cons currentBarrier currentScope nextScope outerScope segment segments
      resource _resources cursor _context _segmentAgrees _resourceRest
      _resourceQuery _resourceBarrier resourceOwnership snapshot outerAgrees =>
      { currentBarrier := currentBarrier
        currentScope := currentScope
        nextScope := nextScope
        outerScope := outerScope
        segment := segment
        outerSegments := segments
        resource := resource
        cursor := cursor
        ownership := resourceOwnership
        snapshot := snapshot } ::
        payloadCells outerAgrees

/-- Snapshot-preserving cells erase to exactly the existing ordered runtime
identity spine. -/
theorem payloadCells_map_identity
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer) :
    (payloadCells agreement).map PayloadCell.identity =
      PrologNestedCallChainBridge.SourceControlResourcePayloadContextAgrees.cellIdentities
        agreement := by
  induction agreement with
  | nil => rfl
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      simp only [payloadCells, List.map_cons, PayloadCell.identity,
        PrologNestedCallChainBridge.SourceControlResourcePayloadContextAgrees.cellIdentities]
      rw [inductionHypothesis]

/-- The snapshot-preserving cells expose exactly the executable resource
spine indexed by the dependent zipper. -/
theorem payloadCells_map_resource
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer) :
    (payloadCells agreement).map PayloadCell.resource = resources := by
  induction agreement with
  | nil => rfl
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      simp only [payloadCells, List.map_cons]
      rw [inductionHypothesis]

/-- The snapshot-preserving list and the dependent zipper have the same
number of cells. -/
theorem payloadCells_length
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer) :
    (payloadCells agreement).length =
      PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount
        agreement := by
  induction agreement with
  | nil => rfl
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      simp only [payloadCells, List.length_cons,
        PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount]
      omega

/-- The snapshot-preserving cells are one-for-one with the literal source
control segments and executable resources. -/
theorem payloadCells_length_eq_spines
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer) :
    (payloadCells agreement).length = segments.length ∧
      (payloadCells agreement).length = resources.length := by
  induction agreement with
  | nil => exact ⟨rfl, rfl⟩
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      simpa [payloadCells] using
        And.intro (congrArg Nat.succ inductionHypothesis.1)
          (congrArg Nat.succ inductionHypothesis.2)

/-- Every snapshot-preserving cell inherits the allocator domination carried
by the exact dependent zipper which contains that occurrence.

The membership premise is over `payloadCells agreement`, not over a separate
resource or cursor list.  Consequently the two endpoint inequalities cannot
be paired with a duplicate-shaped occurrence at another payload depth. -/
theorem SourceControlResourcePayloadContextAgrees.cell_endpointsBelow
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer)
    {referenceFloor executableFloor : Nat}
    (below :
      SourceControlResourcePayloadContextAgrees.endpointsBelow agreement
        referenceFloor executableFloor)
    {cell : PayloadCell alpha support}
    (member : cell ∈ payloadCells agreement) :
    cell.cursor.reservedUntil ≤ referenceFloor ∧
      cell.resource.finalCounter ≤ executableFloor := by
  induction agreement with
  | nil =>
      simp [payloadCells] at member
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      simp only [payloadCells, List.mem_cons] at member
      have headBounds :=
        SourceControlResourcePayloadContextAgrees.endpointsBelow_head
          (.cons currentBarrier currentScope nextScope outerScope segment
            segments resource resources cursor context segmentAgrees
            resourceRest resourceQuery resourceBarrier resourceOwnership
            snapshot outerAgrees)
          below
      rcases member with rfl | member
      · exact ⟨headBounds.1, headBounds.2.1⟩
      · exact inductionHypothesis headBounds.2.2 member

/-- A position whose type names the literal payload zipper it indexes.

The payload value is an explicit type parameter, not merely a length proof.
Consequently a coordinate cannot be reused after a payload transformation or
against a shape-compatible historical zipper without transporting the whole
dependent zipper first. -/
structure PayloadPath
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer) where
  position : Fin (payloadCells payload).length

namespace PayloadPath

/-- Select the exact dependent cell at this path.  No equality search over
resources or cursors occurs. -/
def cell
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (path : PayloadPath payload) : PayloadCell alpha support :=
  (payloadCells payload).get path.position

/-- The exact ordinal payload coordinate inherits both persistent allocator
bounds from its containing dependent zipper.

This is the occurrence-indexed form consumed by scheduled head activation:
the path chooses the cell, while `endpointsBelow` supplies chronology for the
same zipper. -/
theorem endpointsBelow
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (path : PayloadPath payload)
    {referenceFloor executableFloor : Nat}
    (below :
      SourceControlResourcePayloadContextAgrees.endpointsBelow payload
        referenceFloor executableFloor) :
    path.cell.cursor.reservedUntil ≤ referenceFloor ∧
      path.cell.resource.finalCounter ≤ executableFloor := by
  apply
    SourceControlResourcePayloadContextAgrees.cell_endpointsBelow payload below
  exact List.get_mem (payloadCells payload) path.position

/-- The selected runtime identity is literally the same-position entry in the
existing identity spine. -/
theorem identity_exact
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (path : PayloadPath payload) :
    path.cell.identity =
      (PrologNestedCallChainBridge.SourceControlResourcePayloadContextAgrees.cellIdentities
        payload).get
        ⟨path.position.val, by
          rw [← payloadCells_map_identity, List.length_map]
          exact path.position.isLt⟩ := by
  change
    PayloadCell.identity ((payloadCells payload).get path.position) = _
  simp only [← payloadCells_map_identity, List.get_eq_getElem,
    List.getElem_map]

/-- The literal head coordinate of a nonempty payload zipper. -/
def atHead
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {cursor : PreparedCursor} {currentScope nextScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {segmentAgrees : segment.Agrees alpha}
    {resourceRest :
      resource.rest = segment.executables ++ flattenExecutables segments}
    {resourceQuery : resource.qterm = qterm}
    {resourceBarrier : resource.barrier = currentBarrier}
    {resourceOwnership : resource.HasIndexedOwnershipAt alpha cursor}
    {snapshot :
      RetainedCallPayloadSnapshot alpha support resource cursor segment
        segments}
    {outerAgrees :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        segment.barrier segments resources nextScope context outerScope} :
    PayloadPath
      (.cons currentBarrier currentScope nextScope outerScope segment segments
        resource resources cursor context segmentAgrees resourceRest
        resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees) :=
  ⟨⟨0, by simp [payloadCells]⟩⟩

/-- Lift a coordinate of the exact tail into the exact enclosing zipper. -/
def inTail
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {cursor : PreparedCursor} {currentScope nextScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {segmentAgrees : segment.Agrees alpha}
    {resourceRest :
      resource.rest = segment.executables ++ flattenExecutables segments}
    {resourceQuery : resource.qterm = qterm}
    {resourceBarrier : resource.barrier = currentBarrier}
    {resourceOwnership : resource.HasIndexedOwnershipAt alpha cursor}
    {snapshot :
      RetainedCallPayloadSnapshot alpha support resource cursor segment
        segments}
    {outerAgrees :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        segment.barrier segments resources nextScope context outerScope}
    (path : PayloadPath outerAgrees) :
    PayloadPath
      (.cons currentBarrier currentScope nextScope outerScope segment segments
        resource resources cursor context segmentAgrees resourceRest
        resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees) :=
  ⟨⟨path.position.val + 1, by
      simp [payloadCells]⟩⟩

@[simp] theorem atHead_cell
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {cursor : PreparedCursor} {currentScope nextScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {segmentAgrees : segment.Agrees alpha}
    {resourceRest :
      resource.rest = segment.executables ++ flattenExecutables segments}
    {resourceQuery : resource.qterm = qterm}
    {resourceBarrier : resource.barrier = currentBarrier}
    {resourceOwnership : resource.HasIndexedOwnershipAt alpha cursor}
    {snapshot :
      RetainedCallPayloadSnapshot alpha support resource cursor segment
        segments}
    {outerAgrees :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        segment.barrier segments resources nextScope context outerScope} :
    (atHead (currentBarrier := currentBarrier) (currentScope := currentScope)
      (nextScope := nextScope) (outerScope := outerScope)
      (segmentAgrees := segmentAgrees) (resourceRest := resourceRest)
      (resourceQuery := resourceQuery) (resourceBarrier := resourceBarrier)
      (resourceOwnership := resourceOwnership) (snapshot := snapshot)
      (outerAgrees := outerAgrees)).cell =
      { currentBarrier := currentBarrier
        currentScope := currentScope
        nextScope := nextScope
        outerScope := outerScope
        segment := segment
        outerSegments := segments
        resource := resource
        cursor := cursor
        ownership := resourceOwnership
        snapshot := snapshot } := rfl

@[simp] theorem inTail_cell
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {cursor : PreparedCursor} {currentScope nextScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {segmentAgrees : segment.Agrees alpha}
    {resourceRest :
      resource.rest = segment.executables ++ flattenExecutables segments}
    {resourceQuery : resource.qterm = qterm}
    {resourceBarrier : resource.barrier = currentBarrier}
    {resourceOwnership : resource.HasIndexedOwnershipAt alpha cursor}
    {snapshot :
      RetainedCallPayloadSnapshot alpha support resource cursor segment
        segments}
    {outerAgrees :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        segment.barrier segments resources nextScope context outerScope}
    (path : PayloadPath outerAgrees) :
    (inTail (currentBarrier := currentBarrier) (currentScope := currentScope)
      (nextScope := nextScope) (outerScope := outerScope)
      (segmentAgrees := segmentAgrees) (resourceRest := resourceRest)
      (resourceQuery := resourceQuery) (resourceBarrier := resourceBarrier)
      (resourceOwnership := resourceOwnership) (snapshot := snapshot)
      path).cell = path.cell := by
  simp [inTail, cell, payloadCells, List.get_eq_getElem]

@[simp] theorem head_position
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {cursor : PreparedCursor} {currentScope nextScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {segmentAgrees : segment.Agrees alpha}
    {resourceRest :
      resource.rest = segment.executables ++ flattenExecutables segments}
    {resourceQuery : resource.qterm = qterm}
    {resourceBarrier : resource.barrier = currentBarrier}
    {resourceOwnership : resource.HasIndexedOwnershipAt alpha cursor}
    {snapshot :
      RetainedCallPayloadSnapshot alpha support resource cursor segment
        segments}
    {outerAgrees :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        segment.barrier segments resources nextScope context outerScope} :
    (atHead (currentBarrier := currentBarrier) (currentScope := currentScope)
      (nextScope := nextScope) (outerScope := outerScope)
      (segmentAgrees := segmentAgrees) (resourceRest := resourceRest)
      (resourceQuery := resourceQuery) (resourceBarrier := resourceBarrier)
      (resourceOwnership := resourceOwnership) (snapshot := snapshot)
      (outerAgrees := outerAgrees)).position.val = 0 := rfl

@[simp] theorem tail_position
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {cursor : PreparedCursor} {currentScope nextScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {segmentAgrees : segment.Agrees alpha}
    {resourceRest :
      resource.rest = segment.executables ++ flattenExecutables segments}
    {resourceQuery : resource.qterm = qterm}
    {resourceBarrier : resource.barrier = currentBarrier}
    {resourceOwnership : resource.HasIndexedOwnershipAt alpha cursor}
    {snapshot :
      RetainedCallPayloadSnapshot alpha support resource cursor segment
        segments}
    {outerAgrees :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        segment.barrier segments resources nextScope context outerScope}
    (path : PayloadPath outerAgrees) :
    (inTail (currentBarrier := currentBarrier) (currentScope := currentScope)
      (nextScope := nextScope) (outerScope := outerScope)
      (segmentAgrees := segmentAgrees) (resourceRest := resourceRest)
      (resourceQuery := resourceQuery) (resourceBarrier := resourceBarrier)
      (resourceOwnership := resourceOwnership) (snapshot := snapshot)
      path).position.val = path.position.val + 1 := rfl

/-- Distinct selected cursors force distinct paths even if the executable
resource values happen to be equal. -/
theorem ne_of_cursor_ne
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (left right : PayloadPath payload)
    (different : left.cell.cursor ≠ right.cell.cursor) :
    left ≠ right := by
  intro pathsEqual
  apply different
  simp [pathsEqual]

/-- Resource equality is insufficient to identify a retained payload path.
If two selected cells share the same executable resource but retain different
source cursors, their exact paths are necessarily distinct. -/
theorem same_resource_distinct_paths_of_cursor_ne
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (left right : PayloadPath payload)
    (sameResource : left.cell.resource = right.cell.resource)
    (differentCursor : left.cell.cursor ≠ right.cell.cursor) :
    left.cell.resource = right.cell.resource ∧ left ≠ right :=
  ⟨sameResource, ne_of_cursor_ne left right differentCursor⟩

end PayloadPath

/-! ## Structural dependent suffix at an exact path -/

/-- A dependent payload is structurally nonempty exactly when its value is a
`cons` cell.  Indexing the view by the payload value makes the head's
`outerAgrees` available without an equality search or a cast through an
ordinary resource list. -/
inductive PayloadHeadView
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom} :
    {currentBarrier : Nat} →
    {segments : List ControlSegment} →
    {resources : List RetainedAlternativeSegment} →
    {inner outer : CutScopeId} →
    {context : ActiveProductContext} →
    SourceControlResourcePayloadContextAgrees alpha support qterm
      currentBarrier segments resources inner context outer → Type where
  | cons
      (currentBarrier : Nat)
      (currentScope nextScope outerScope : CutScopeId)
      (segment : ControlSegment) (segments : List ControlSegment)
      (resource : RetainedAlternativeSegment)
      (resources : List RetainedAlternativeSegment)
      (cursor : PreparedCursor) (context : ActiveProductContext)
      (segmentAgrees : segment.Agrees alpha)
      (resourceRest :
        resource.rest = segment.executables ++ flattenExecutables segments)
      (resourceQuery : resource.qterm = qterm)
      (resourceBarrier : resource.barrier = currentBarrier)
      (resourceOwnership : resource.HasIndexedOwnershipAt alpha cursor)
      (snapshot :
        RetainedCallPayloadSnapshot alpha support resource cursor segment
          segments)
      (outerAgrees :
        SourceControlResourcePayloadContextAgrees alpha support qterm
          segment.barrier segments resources nextScope context outerScope) :
      PayloadHeadView
        (.cons currentBarrier currentScope nextScope outerScope segment
          segments resource resources cursor context segmentAgrees
          resourceRest resourceQuery resourceBarrier resourceOwnership
          snapshot outerAgrees)

/-- Constructor data exposed from a nonempty dependent payload without
requiring a consumer to eliminate equations between computed list drops.

The three spine equalities and `cellsExact` are part of the data package, so
the extracted tail cannot be paired with a different segment/resource/frame
suffix. -/
structure PayloadHeadData
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer) : Type where
  currentScope : CutScopeId
  nextScope : CutScopeId
  segment : ControlSegment
  laterSegments : List ControlSegment
  resource : RetainedAlternativeSegment
  laterResources : List RetainedAlternativeSegment
  cursor : PreparedCursor
  laterContext : ActiveProductContext
  segmentAgrees : segment.Agrees alpha
  resourceRest :
    resource.rest = segment.executables ++ flattenExecutables laterSegments
  resourceQuery : resource.qterm = qterm
  resourceBarrier : resource.barrier = currentBarrier
  resourceOwnership : resource.HasIndexedOwnershipAt alpha cursor
  snapshot :
    RetainedCallPayloadSnapshot alpha support resource cursor segment
      laterSegments
  outerAgrees :
    SourceControlResourcePayloadContextAgrees alpha support qterm
      segment.barrier laterSegments laterResources nextScope laterContext outer
  segmentsExact : segments = segment :: laterSegments
  resourcesExact : resources = resource :: laterResources
  innerExact : inner = currentScope
  contextExact :
    context =
      { callerScope := nextScope
        predicateScope := currentScope
        retained := .clauses currentScope cursor
        callerRest := segment.references } :: laterContext
  cellsExact :
    payloadCells payload =
      { currentBarrier := currentBarrier
        currentScope := currentScope
        nextScope := nextScope
        outerScope := outer
        segment := segment
        outerSegments := laterSegments
        resource := resource
        cursor := cursor
        ownership := resourceOwnership
        snapshot := snapshot } :: payloadCells outerAgrees

namespace PayloadHeadData

/-- The literal payload cell named by a dependent head view.

Unlike `PayloadCell.historyCell`, this projection retains every delimiter
label and the immutable snapshot. -/
def cell
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (head : PayloadHeadData payload) : PayloadCell alpha support :=
  { currentBarrier := currentBarrier
    currentScope := head.currentScope
    nextScope := head.nextScope
    outerScope := outer
    segment := head.segment
    outerSegments := head.laterSegments
    resource := head.resource
    cursor := head.cursor
    ownership := head.resourceOwnership
    snapshot := head.snapshot }

end PayloadHeadData

namespace PayloadHeadView

/-- Eliminate an indexed head view into explicit constructor data.  The
eliminator's payload index is a variable, so callers never need to solve
dependent equations for computed `drop` expressions. -/
def data
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (view : PayloadHeadView payload) : PayloadHeadData payload := by
  cases view with
  | cons currentBarrier nextScope _ segment laterSegments
      resource laterResources cursor laterContext segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees =>
      exact
        { currentScope := inner
          nextScope := nextScope
          segment := segment
          laterSegments := laterSegments
          resource := resource
          laterResources := laterResources
          cursor := cursor
          laterContext := laterContext
          segmentAgrees := segmentAgrees
          resourceRest := resourceRest
          resourceQuery := resourceQuery
          resourceBarrier := resourceBarrier
          resourceOwnership := resourceOwnership
          snapshot := snapshot
          outerAgrees := outerAgrees
          segmentsExact := rfl
          resourcesExact := rfl
          innerExact := rfl
          contextExact := rfl
          cellsExact := rfl }

end PayloadHeadView

/-- Compute the exact constructor view of any payload whose cell list is
nonempty.  The impossible nil case is discharged from the supplied list fact;
no proposition is used to choose any payload data. -/
def payloadHeadViewOfCellsNonempty
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer)
    (nonempty : payloadCells payload ≠ []) : PayloadHeadView payload := by
  cases payload with
  | nil currentBarrier scope =>
      exact False.elim (nonempty rfl)
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees =>
      exact .cons currentBarrier inner nextScope outer segment
        segments resource resources cursor context segmentAgrees resourceRest
        resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees

/-- Dropping an aligned dependent prefix drops exactly the same number of
snapshot-preserving cells.

The returned suffix is the one computed by the existing dependent zipper
eliminator.  This theorem rules out a proof-compatible reconstruction whose
ordinary cell spelling differs from the literal dropped suffix. -/
theorem payloadCells_dropAlignedPrefix
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer)
    (count : Nat) (within : count ≤ segments.length) :
    let dropped :=
      SourceControlResourcePayloadContextAgrees.dropAlignedPrefix payload
        count within
    payloadCells dropped.2.2 = (payloadCells payload).drop count := by
  induction count generalizing currentBarrier segments resources inner
      context with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      cases payload with
      | nil currentBarrier scope =>
          simp at within
      | cons currentBarrier currentScope nextScope outerScope segment
          segments resource resources cursor context segmentAgrees
          resourceRest resourceQuery resourceBarrier resourceOwnership
          snapshot outerAgrees =>
          have withinTail : count ≤ segments.length := by
            simpa using Nat.le_of_succ_le_succ within
          simpa [SourceControlResourcePayloadContextAgrees.dropAlignedPrefix,
            payloadCells] using
            inductionHypothesis outerAgrees withinTail

/-- A structural route from an ordinal payload path to the exact dependent
zipper suffix beginning at that path.

`cellsExact` couples all three views at once: the original path's selected
cell is the suffix head, the rest of the dependent zipper is the literal list
drop after that coordinate, and there is no second independently supplied
position which could drift. -/
structure PayloadRoute
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer)
    (path : PayloadPath payload) : Type where
  suffixBarrier : Nat
  suffixInner : CutScopeId
  suffix :
    SourceControlResourcePayloadContextAgrees alpha support qterm
      suffixBarrier (segments.drop path.position.val)
      (resources.drop path.position.val) suffixInner
      (context.drop path.position.val) outer
  cellsExact :
    payloadCells suffix =
      path.cell ::
        (payloadCells payload).drop (path.position.val + 1)
  head : PayloadHeadView suffix

namespace PayloadPath

/-- Convert the exact ordinal to its exact dependent suffix.  The conversion
uses the already-audited aligned-prefix eliminator; it does not search for an
equal resource or cursor. -/
def route
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (path : PayloadPath payload) : PayloadRoute payload path := by
  have within : path.position.val ≤ segments.length := by
    have cellsSpines := payloadCells_length_eq_spines payload
    omega
  let dropped :=
    SourceControlResourcePayloadContextAgrees.dropAlignedPrefix payload
      path.position.val within
  have cellsExact :
      payloadCells dropped.2.2 =
        path.cell ::
          (payloadCells payload).drop (path.position.val + 1) := by
    calc
      payloadCells dropped.2.2 =
        (payloadCells payload).drop path.position.val :=
        payloadCells_dropAlignedPrefix payload path.position.val within
      _ =
        path.cell ::
          (payloadCells payload).drop (path.position.val + 1) := by
        simp [PayloadPath.cell]
  refine
    { suffixBarrier := dropped.1
      suffixInner := dropped.2.1
      suffix := dropped.2.2
      cellsExact := cellsExact
      head := payloadHeadViewOfCellsNonempty dropped.2.2 (by
        rw [cellsExact]
        simp) }

end PayloadPath

namespace PayloadRoute

/-- The dependent route head is exactly the selected payload occurrence,
including all typed delimiters and its immutable snapshot. -/
theorem headCell_exact
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    {path : PayloadPath payload}
    (route : PayloadRoute payload path) :
    route.head.data.cell = path.cell := by
  have cellsAtHead :=
    route.head.data.cellsExact.symm.trans route.cellsExact
  simpa [PayloadHeadData.cell] using (List.cons.inj cellsAtHead).1

/-- A route suffix is structurally nonempty: its head is the exact selected
cell rather than a postulated compatible occurrence. -/
theorem suffix_ne_nil
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    {path : PayloadPath payload}
    (route : PayloadRoute payload path) :
    payloadCells route.suffix ≠ [] := by
  rw [route.cellsExact]
  simp

/-- Removing the selected head from the dependent route leaves exactly the
ordinary payload cells after the original ordinal. -/
theorem laterCells_exact
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    {path : PayloadPath payload}
    (route : PayloadRoute payload path) :
    (payloadCells route.suffix).drop 1 =
      (payloadCells payload).drop (path.position.val + 1) := by
  rw [route.cellsExact]
  simp

/-- A route has no independently chosen coordinate; projecting it back
returns its index path definitionally. -/
def toPath
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    {path : PayloadPath payload}
    (_route : PayloadRoute payload path) : PayloadPath payload :=
  path

@[simp] theorem toPath_position
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    {path : PayloadPath payload}
    (route : PayloadRoute payload path) :
    route.toPath.position.val = path.position.val := rfl

end PayloadRoute

/-! ## Exact alignment with local scheduled-history construction -/

/-- One literal payload zipper and one literal local scheduled-history build
contain the same occurrence cells in the same order.

This is Type-valued and both structures are indices.  It is stronger than
resource-list equality: cursor identity is preserved, while each payload path
still carries the immutable snapshot omitted from the history layer. -/
structure ScheduledPayloadAlignment
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer)
    {source next : Search}
    {history : PrologScheduledAnswerPropagationBridge.ScheduledAnswerHistory
      alpha source next}
    (build : ScheduledHistoryBuild history) : Type where
  cellsExact :
    build.cells = (payloadCells payload).map PayloadCell.historyCell

namespace ScheduledPayloadAlignment

/-- The aligned history and payload coordinates have the same finite
cardinality. -/
theorem lengths_eq
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    {source next : Search}
    {history : PrologScheduledAnswerPropagationBridge.ScheduledAnswerHistory
      alpha source next}
    {build : ScheduledHistoryBuild history}
    (alignment : ScheduledPayloadAlignment payload build) :
    build.cells.length = (payloadCells payload).length := by
  have exact := congrArg List.length alignment.cellsExact
  simpa using exact

/-- Convert a history coordinate to the same ordinal in the exact payload
zipper.  The selected snapshot is therefore chosen by position, never by
resource equality. -/
def payloadPath
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    {source next : Search}
    {history : PrologScheduledAnswerPropagationBridge.ScheduledAnswerHistory
      alpha source next}
    {build : ScheduledHistoryBuild history}
    (alignment : ScheduledPayloadAlignment payload build)
    (path : ScheduledHistoryBuild.Path build) : PayloadPath payload :=
  ⟨⟨path.position.val, by
      have within := path.position.isLt
      have lengthExact := alignment.lengths_eq
      omega⟩⟩

/-- Mapping a history coordinate back to the payload preserves the exact
resource and source cursor, while additionally recovering the immutable
snapshot at that occurrence. -/
theorem selected_history_cell_exact
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    {source next : Search}
    {history : PrologScheduledAnswerPropagationBridge.ScheduledAnswerHistory
      alpha source next}
    {build : ScheduledHistoryBuild history}
    (alignment : ScheduledPayloadAlignment payload build)
    (path : ScheduledHistoryBuild.Path build) :
    (alignment.payloadPath path).cell.historyCell = path.cell := by
  change
    PayloadCell.historyCell
        ((payloadCells payload).get
          ⟨path.position.val, by
            have within := path.position.isLt
            have lengthExact := alignment.lengths_eq
            omega⟩) =
      build.cells.get path.position
  simp only [alignment.cellsExact, List.get_eq_getElem, List.getElem_map]

@[simp] theorem payloadPath_position
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    {source next : Search}
    {history : PrologScheduledAnswerPropagationBridge.ScheduledAnswerHistory
      alpha source next}
    {build : ScheduledHistoryBuild history}
    (alignment : ScheduledPayloadAlignment payload build)
    (path : ScheduledHistoryBuild.Path build) :
    (alignment.payloadPath path).position.val = path.position.val := rfl

end ScheduledPayloadAlignment

end PLeaTTa.PrologScheduledPayloadPathBridge
