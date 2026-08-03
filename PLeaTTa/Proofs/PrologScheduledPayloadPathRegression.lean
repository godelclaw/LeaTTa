-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologScheduledPayloadPathRegression
Purpose: Inhabit exact zipper-indexed payload selection at nested depth two
Trusted boundary: none
-/
import PLeaTTa.Proofs.PrologNestedCallReadyRegression
import PLeaTTa.Proofs.PrologScheduledPayloadPathBridge
import PLeaTTa.Proofs.PrologScheduledPayloadResumeRegression

namespace PLeaTTa.PrologScheduledPayloadPathRegression

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PrologHeterogeneousPrefixBridge
open PrologNestedCallChainBridge
open PrologNestedCallReadyBridge
open PrologProductResourceContextBridge
open PrologScheduledPayloadPathBridge
open PrologScheduledHistoryBuildBridge
open PrologRootClosedAnswerBridge

/-- The real ground `p -> q -> r` nested-call carrier has three exact payload
coordinates: the active `r` cell and two older cells.  Reading those paths in
order reproduces the complete already-audited identity spine.

This is deliberately a depth-two fixture.  A singleton payload would not
exercise stale-coordinate or outer-cell selection. -/
theorem ground_depth_two_payload_paths_are_exact
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ state : ActivePayloadState,
      ∃ first second third : PayloadPath state.payloadContext,
        state.index.outer.length = 2 ∧
          first.position.val = 0 ∧
          second.position.val = 1 ∧
          third.position.val = 2 ∧
          [first.cell.identity, second.cell.identity, third.cell.identity] =
            state.cellIdentities := by
  obtain
    ⟨_root, _qHead, _middle, _qReady, _qPredicate, _qPayload,
      _rootReferences, _rootExecutables, _rootSourceSteps, _rootFineSteps,
      _qCertificate, _rHead, state, _rReady, _rPredicate, _rPayload,
      _rCertificate, _bodyReferencesEmpty, _bodyExecutablesEmpty,
      _callerReferencesEmpty, _baseAltsEmpty, _afterActiveAlts,
      _afterResources, _middleActiveAlts, _rootActiveAlts, outerLength,
      _outerAllEmpty⟩ :=
    PrologNestedCallReadyRegression.ground_p_q_r_two_nested_pushes
      (prog := prog) (gt := gt)
  have cellsLength :
      (payloadCells state.payloadContext).length = 3 := by
    rw [(payloadCells_length_eq_spines state.payloadContext).1]
    simp [outerLength]
  let first : PayloadPath state.payloadContext :=
    ⟨⟨0, by omega⟩⟩
  let second : PayloadPath state.payloadContext :=
    ⟨⟨1, by omega⟩⟩
  let third : PayloadPath state.payloadContext :=
    ⟨⟨2, by omega⟩⟩
  refine ⟨state, first, second, third, outerLength, rfl, rfl, rfl, ?_⟩
  obtain ⟨firstCell, secondCell, thirdCell, cellsExact⟩ :=
    List.length_eq_three.mp cellsLength
  change
    [first.cell.identity, second.cell.identity, third.cell.identity] =
      PrologNestedCallChainBridge.SourceControlResourcePayloadContextAgrees.cellIdentities
        state.payloadContext
  rw [← payloadCells_map_identity]
  simp [first, second, third, PayloadPath.cell, cellsExact]

/-- The same reachable depth-two carrier forces the structural-route
conversion to expose dependent suffixes of lengths three, two, and one.

This is the anti-drift witness for the route layer: a conversion which reused
the full zipper, dropped the selected cell, or closed over an equal resource
at another occurrence would fail at least one exact suffix length. -/
theorem ground_depth_two_payload_routes_drop_exact_prefixes
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ state : ActivePayloadState,
      ∃ first second third : PayloadPath state.payloadContext,
        let firstRoute := first.route
        let secondRoute := second.route
        let thirdRoute := third.route
        (payloadCells firstRoute.suffix).length = 3 ∧
          (payloadCells secondRoute.suffix).length = 2 ∧
          (payloadCells thirdRoute.suffix).length = 1 ∧
          payloadCells firstRoute.suffix =
            first.cell ::
              (payloadCells state.payloadContext).drop
                (first.position.val + 1) ∧
          payloadCells secondRoute.suffix =
            second.cell ::
              (payloadCells state.payloadContext).drop
                (second.position.val + 1) ∧
          payloadCells thirdRoute.suffix =
            third.cell ::
              (payloadCells state.payloadContext).drop
                (third.position.val + 1) := by
  obtain
    ⟨state, first, second, third, _outerLength, firstPosition,
      secondPosition, thirdPosition, identities⟩ :=
    ground_depth_two_payload_paths_are_exact (prog := prog) (gt := gt)
  have payloadLength : (payloadCells state.payloadContext).length = 3 := by
    have cellListExact :
        [first.cell.identity, second.cell.identity, third.cell.identity] =
          (payloadCells state.payloadContext).map PayloadCell.identity := by
      rw [payloadCells_map_identity]
      exact identities
    have exactLength := congrArg List.length cellListExact
    simpa using exactLength.symm
  refine ⟨state, first, second, third, ?_⟩
  dsimp only
  constructor
  · rw [first.route.cellsExact, firstPosition]
    simp [payloadLength]
  constructor
  · rw [second.route.cellsExact, secondPosition]
    simp [payloadLength]
  constructor
  · rw [third.route.cellsExact, thirdPosition]
    simp [payloadLength]
  exact
    ⟨first.route.cellsExact, second.route.cellsExact,
      third.route.cellsExact⟩

/-- The path abstraction refuses the known unsound replacement of occurrence
identity by resource equality.  Whenever two cells share one executable bank
but retain different source cursors, their zipper-indexed paths differ. -/
theorem duplicate_resource_cannot_identify_payload_path
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat}
    {segments : List PrologControlSegmentSpineBridge.ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : PrologSourceProductContextBridge.ActiveProductContext}
    {payload :
      PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
        alpha support qterm currentBarrier segments resources inner context
        outer}
    (left right : PayloadPath payload)
    (sameResource : left.cell.resource = right.cell.resource)
    (differentCursor : left.cell.cursor ≠ right.cell.cursor) :
    left.cell.resource = right.cell.resource ∧ left ≠ right :=
  PayloadPath.same_resource_distinct_paths_of_cursor_ne left right
    sameResource differentCursor

/-- The same real depth-two carrier exercises the complete positional bridge:
its closed local history has three construction cells, and all three history
coordinates recover the same-occurrence payload cell (including its immutable
snapshot) at positions 0, 1, and 2. -/
theorem ground_root_closed_history_paths_recover_exact_payload_cells
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ before : RepresentativeScheduledPayloadState,
      ∃ ready : RootClosedAnswerReady before,
        ∃ first second third :
            ScheduledHistoryBuild.Path ready.result.historyBuild,
          before.carrier.index.outer.length = 2 ∧
            first.position.val = 0 ∧
            second.position.val = 1 ∧
            third.position.val = 2 ∧
            (ready.payloadAlignment.payloadPath first).cell.historyCell =
              first.cell ∧
            (ready.payloadAlignment.payloadPath second).cell.historyCell =
              second.cell ∧
            (ready.payloadAlignment.payloadPath third).cell.historyCell =
              third.cell := by
  obtain ⟨before, ready, outerLength, _events, _outcome, _classified⟩ :=
    PrologScheduledPayloadResumeRegression.ground_two_frame_root_closed_pull_is_inhabited
      (prog := prog) (gt := gt)
  have payloadLength :
      (payloadCells before.carrier.payloadContext).length = 3 := by
    rw [(payloadCells_length_eq_spines before.carrier.payloadContext).1]
    simp [outerLength]
  have historyLength : ready.result.historyBuild.cells.length = 3 := by
    rw [ready.payloadAlignment.lengths_eq, payloadLength]
  let first : ScheduledHistoryBuild.Path ready.result.historyBuild :=
    ⟨⟨0, by omega⟩⟩
  let second : ScheduledHistoryBuild.Path ready.result.historyBuild :=
    ⟨⟨1, by omega⟩⟩
  let third : ScheduledHistoryBuild.Path ready.result.historyBuild :=
    ⟨⟨2, by omega⟩⟩
  exact
    ⟨before, ready, first, second, third, outerLength, rfl, rfl, rfl,
      ready.payloadAlignment.selected_history_cell_exact first,
      ready.payloadAlignment.selected_history_cell_exact second,
      ready.payloadAlignment.selected_history_cell_exact third⟩

end PLeaTTa.PrologScheduledPayloadPathRegression
