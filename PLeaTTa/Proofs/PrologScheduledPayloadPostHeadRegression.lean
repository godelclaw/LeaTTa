-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologScheduledPayloadPostHeadRegression
Purpose: Discriminate collapsed path/source offsets in the exact post-head
  dependent payload transition
Trusted boundary: none
-/
import PLeaTTa.Proofs.PrologRootRejectedPrefixRegression
import PLeaTTa.Proofs.PrologScheduledPayloadPathRegression
import PLeaTTa.Proofs.PrologScheduledPayloadPostHeadBridge

namespace PLeaTTa.PrologScheduledPayloadPostHeadRegression

open Metta (Atom)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PLeaTTa.PrologControlSegmentSpineBridge
open PLeaTTa.PrologNestedCallChainBridge
open PLeaTTa.PrologPrefilterScanBridge
open PLeaTTa.PrologProductResourceContextBridge
open PLeaTTa.PrologRetainedPayloadSnapshotBridge
open PLeaTTa.PrologScheduledAnswerPropagationBridge
open PLeaTTa.PrologScheduledHistoryBuildBridge
open PLeaTTa.PrologScheduledPayloadLandingBridge
open PLeaTTa.PrologScheduledPayloadPathBridge
open PLeaTTa.PrologScheduledPayloadPostHeadBridge
open PLeaTTa.PrologScheduledPayloadPostHeadBridge.ScheduledSelectedHeadTransition
open PLeaTTa.PrologSourceProductContextBridge

/-! ## Three independent coordinates cannot be collapsed -/

/-- In a genuinely nondegenerate transition, replacing the counted source
offset by one, deleting the transformed head, or retaining the old selected
head changes an observable list length or absolute position.

This theorem deliberately requires all three axes at once: at least one
earlier scheduled cell, at least one rejected source occurrence, and at
least one later payload cell.  It is a negative discriminator for the three
shortcuts most likely to pass singleton/zero-prefix fixtures. -/
theorem nondegenerate_transition_rejects_collapsed_offsets
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List
      PLeaTTa.PrologControlSegmentSpineBridge.ControlSegment}
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
    (earlierNonempty : selection.earlier ≠ [])
    (rejectedPositive : 0 < transition.frontier.rejectedCount)
    (laterNonempty : selection.suffix ≠ []) :
    transition.startPosition + transition.frontier.rejectedCount + 1 ≠
        transition.startPosition + 1 ∧
      payloadCells transition.postPayload ≠
        (payloadCells payload).drop (selection.path.position.val + 1) ∧
      payloadCells
          (SourceControlResourcePayloadContextAgrees.tail
            transition.postPayload) ≠
        (payloadCells payload).drop selection.path.position.val ∧
      (payloadCells payload).take selection.path.position.val ≠ [] ∧
      payloadCells
          (SourceControlResourcePayloadContextAgrees.tail
            transition.postPayload) ≠ [] := by
  have sourceOffsetWrong :
      transition.startPosition + transition.frontier.rejectedCount + 1 ≠
        transition.startPosition + 1 := by
    omega
  have postSpine := transition.postCellSpineExact
  have droppedHeadWrong :
      payloadCells transition.postPayload ≠
        (payloadCells payload).drop (selection.path.position.val + 1) := by
    intro same
    have lengths := congrArg List.length same
    rw [postSpine] at lengths
    simp at lengths
  have oldHeadWrong :
      payloadCells
          (SourceControlResourcePayloadContextAgrees.tail
            transition.postPayload) ≠
        (payloadCells payload).drop selection.path.position.val := by
    intro same
    have selectedDecomposition :=
      List.cons_get_drop_succ
        (l := payloadCells payload)
        (n := alignment.payloadPath selection.path |>.position)
    have selectedDecomposition' :
        (alignment.payloadPath selection.path).cell ::
            (payloadCells payload).drop
              (selection.path.position.val + 1) =
          (payloadCells payload).drop selection.path.position.val := by
      change
        ((alignment.payloadPath selection.path).cell ::
            (payloadCells payload).drop
              (selection.path.position.val + 1) =
          (payloadCells payload).drop selection.path.position.val) at selectedDecomposition
      exact selectedDecomposition
    have later := transition.postLaterCellsExact
    rw [later] at same
    rw [← selectedDecomposition'] at same
    have lengths := congrArg List.length same
    simp at lengths
  have earlierCells := transition.earlierCellsExact
  have earlierPayloadNonempty :
      (payloadCells payload).take selection.path.position.val ≠ [] := by
    intro empty
    rw [empty] at earlierCells
    simp at earlierCells
    exact earlierNonempty earlierCells
  have laterPayloadNonempty :
      payloadCells
          (SourceControlResourcePayloadContextAgrees.tail
            transition.postPayload) ≠ [] := by
    intro empty
    have laterCells := transition.postLaterCellsExact
    have suffix := transition.route.suffixExact
    have dropEmpty :
        (payloadCells payload).drop
            (selection.path.position.val + 1) = [] := by
      rw [← laterCells]
      exact empty
    rw [dropEmpty] at suffix
    simp at suffix
    exact laterNonempty suffix
  exact
    ⟨sourceOffsetWrong, droppedHeadWrong, oldHeadWrong,
      earlierPayloadNonempty, laterPayloadNonempty⟩

/-! ## The path and rejected-prefix axes are concretely inhabited -/

/-- The reachable `p -> q -> r` payload has a middle coordinate with both a
nonempty earlier prefix and a nonempty later suffix.  Thus the path-axis
premises above are not singleton artifacts. -/
theorem depth_two_middle_path_has_both_sides
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ state :
        PLeaTTa.PrologNestedCallChainBridge.ActivePayloadState,
      ∃ path : PayloadPath state.payloadContext,
        path.position.val = 1 ∧
          (payloadCells state.payloadContext).take path.position.val ≠ [] ∧
          (payloadCells state.payloadContext).drop
              (path.position.val + 1) ≠ [] := by
  obtain
    ⟨state, _first, second, _third, outerLength, _firstPosition,
      secondPosition, _thirdPosition, _identities⟩ :=
    PLeaTTa.PrologScheduledPayloadPathRegression.ground_depth_two_payload_paths_are_exact
      (prog := prog) (gt := gt)
  have cellsLength : (payloadCells state.payloadContext).length = 3 := by
    rw [(payloadCells_length_eq_spines state.payloadContext).1]
    simp [outerLength]
  obtain ⟨firstCell, secondCell, thirdCell, cellsExact⟩ :=
    List.length_eq_three.mp cellsLength
  refine ⟨state, second, secondPosition, ?_, ?_⟩
  · rw [secondPosition]
    simp [cellsExact]
  · rw [secondPosition]
    simp [cellsExact]

/-- The source resolver's literal four-clause fixture contains an actual
two-step rejected prefix.  Thus the source-offset premise above is not a
zero-count artifact.

[SPEC metta.pl:251-256, translator.pl:320-321] -/
theorem two_rejected_source_occurrences_are_inhabited
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ finish,
      RejectedPullsN 2
        (openedFor
          PLeaTTa.PrologRootRejectedPrefixRegression.initialSession "p"
          [PLeaTTa.PrologRootRejectedPrefixRegression.queryTerm] []).cursor
        finish := by
  obtain
    ⟨finish, _representative, _nextAlpha, _sourceCanonical, _flattened,
      _installed, _after, facts, _finishRemaining, _bodyReferences,
      _bodyExecutables, _sourceSteps, _fineSteps⟩ :=
    PLeaTTa.PrologRootRejectedPrefixRegression.two_rigid_rejections_then_selected_retained_exact
      (prog := prog) (gt := gt)
  exact ⟨finish, facts.pulls⟩

end PLeaTTa.PrologScheduledPayloadPostHeadRegression
