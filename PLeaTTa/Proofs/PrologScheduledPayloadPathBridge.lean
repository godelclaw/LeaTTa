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
      simpa [payloadCells, Nat.succ_eq_add_one] using
        Nat.succ_lt_succ path.position.isLt⟩⟩

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
