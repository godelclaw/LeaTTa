-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologPersistentFreeScheduledRejectionPullRegression
Purpose: Inhabit persistent-free payload pull classification at a nonzero
  dependent occurrence using one reachable nested local-resolution prefix.
Trusted boundary: none
-/
import PLeaTTa.Proofs.PrologNestedCallReadyRegression
import PLeaTTa.Proofs.PrologPersistentFreeScheduledRejectionPullBridge

namespace PLeaTTa.PrologPersistentFreeScheduledRejectionPullRegression

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open DemandDrivenStep
open PrologNestedCallChainBridge
open PrologPersistentFreeScheduledRejectionPullBridge
open PrologProductResourceContextBridge
open PrologScheduledPayloadPathBridge

/-!
# Reachable nonzero payload selection

The generic classifier is useful only if a real local run can force it past
exhausted inner banks.  The duplicate-`p/1` fixture supplies exactly that
shape: `r` and `q` are exhausted, while the second `p/1` clause remains live
at dependent payload position two.
-/

/-- A reachable `p -> q -> r` prefix with a duplicate outer `p/1` clause
forces the persistent-free classifier to select the third dependent cell.

The conclusion pins both sides of the selection: the chosen cell is live and
every earlier cell is empty.  Thus a classifier that always chose position
zero, selected by resource equality, or skipped an exhausted prefix would
falsify this theorem.

[SPEC metta.pl:251-256] -/
theorem reachable_outer_sibling_classifies_at_position_two
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ after : ActivePayloadState,
      ∃ selection : PayloadLocalSelection after.payloadContext,
        StepsN 6
            (.running
              PrologNestedCallReadyRegression.siblingInitialSession
              (.task PrologNestedCallReadyRegression.rootScope
                [.call "p" [PrologNestedCallReadyRegression.resultTerm]] []))
            [.opened
                (requestFor "p"
                  [PrologNestedCallReadyRegression.resultTerm] []),
              .opened
                (requestFor "q"
                  [PrologNestedCallReadyRegression.resultTerm] []),
              .opened
                (requestFor "r"
                  [PrologNestedCallReadyRegression.resultTerm] [])]
            after.sourceState ∧
          DemandDrivenCallStep.StepsN prog gt 9
            (.ready PrologNestedCallReadyRegression.siblingInitialOpenConf)
            after.fineState ∧
          classifyPayloadBank after.payloadContext = .localLive selection ∧
          (payloadCells after.payloadContext).length = 3 ∧
          selection.path.position.val = 2 ∧
          selection.path.cell.resource.alts ≠ [] ∧
          (∀ cell ∈
              (payloadCells after.payloadContext).take
                selection.path.position.val,
            cell.resource.alts = []) := by
  obtain
    ⟨after, middle, outer, _alphaNil, _supportNil, activeEmpty,
      resourcesExact, middleEmpty, outerLive, _bodyReferencesEmpty,
      _bodyExecutablesEmpty, sourceSteps, fineSteps⟩ :=
    PrologNestedCallReadyRegression.ground_p_q_r_outer_sibling_resources_are_reachable
      (prog := prog) (gt := gt)
  have resourceSpine :
      (payloadCells after.payloadContext).map PayloadCell.resource =
        [after.index.active, middle, outer] := by
    simpa [resourcesExact] using
      (payloadCells_map_resource after.payloadContext)
  have cellsLength : (payloadCells after.payloadContext).length = 3 := by
    have exact := congrArg List.length resourceSpine
    simpa using exact
  obtain ⟨first, second, third, cellsExact⟩ :=
    List.length_eq_three.mp cellsLength
  have exactResources :
      [first.resource, second.resource, third.resource] =
        [after.index.active, middle, outer] := by
    simpa [cellsExact] using resourceSpine
  have firstResource : first.resource = after.index.active :=
    (List.cons.inj exactResources).1
  have exactResourceTail := (List.cons.inj exactResources).2
  have secondResource : second.resource = middle :=
    (List.cons.inj exactResourceTail).1
  have exactResourceLast := (List.cons.inj exactResourceTail).2
  have thirdResource : third.resource = outer :=
    (List.cons.inj exactResourceLast).1
  have firstEmpty : first.resource.alts = [] := by
    rw [firstResource, activeEmpty]
  have secondEmpty : second.resource.alts = [] := by
    rw [secondResource, middleEmpty]
  have thirdLive : third.resource.alts ≠ [] := by
    rw [thirdResource]
    exact outerLive
  cases classified : classifyPayloadBank after.payloadContext with
  | exhausted allEmpty _pullNone =>
      have thirdMember : third ∈ payloadCells after.payloadContext := by
        rw [cellsExact]
        simp
      exact False.elim (thirdLive (allEmpty third thirdMember))
  | localLive selection =>
      have selectedLive : selection.path.cell.resource.alts ≠ [] := by
        rw [selection.selected_head]
        simp
      have selectedSome :
          (payloadCells after.payloadContext)[selection.path.position.val]? =
            some selection.path.cell := by
        rw [List.getElem?_eq_getElem selection.path.position.isLt]
        rfl
      have positionLt : selection.path.position.val < 3 := by
        simpa [cellsExact] using selection.path.position.isLt
      have positionNeZero : selection.path.position.val ≠ 0 := by
        intro positionZero
        have selectedFirst : selection.path.cell = first := by
          rw [positionZero, cellsExact] at selectedSome
          exact (Option.some.inj selectedSome).symm
        rw [selectedFirst, firstEmpty] at selectedLive
        exact selectedLive rfl
      have positionNeOne : selection.path.position.val ≠ 1 := by
        intro positionOne
        have selectedSecond : selection.path.cell = second := by
          rw [positionOne, cellsExact] at selectedSome
          exact (Option.some.inj selectedSome).symm
        rw [selectedSecond, secondEmpty] at selectedLive
        exact selectedLive rfl
      have positionTwo : selection.path.position.val = 2 := by omega
      have selectedThird : selection.path.cell = third := by
        rw [positionTwo, cellsExact] at selectedSome
        exact (Option.some.inj selectedSome).symm
      refine
        ⟨after, selection, sourceSteps, fineSteps, classified, cellsLength,
          positionTwo, ?_, selection.earlier_empty⟩
      rw [selectedThird]
      exact thirdLive

/-- The corresponding single-clause `p -> q -> r` run reaches the same
three-cell depth with every local bank exhausted, forcing the classifier's
terminal arm.

This is the opposite anti-vacuity witness to
`reachable_outer_sibling_classifies_at_position_two`: both constructors of
`PayloadBankPull` occur on source/fine reachable payloads of the same nested
shape.

[SPEC metta.pl:251-256] -/
theorem reachable_single_clause_payload_classifies_exhausted
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ after : ActivePayloadState,
      StepsN 6
          (.running PrologNestedCallReadyRegression.initialSession
            (.task PrologNestedCallReadyRegression.rootScope
              [.call "p" [PrologNestedCallReadyRegression.resultTerm]] []))
          [.opened
              (requestFor "p"
                [PrologNestedCallReadyRegression.resultTerm] []),
            .opened
              (requestFor "q"
                [PrologNestedCallReadyRegression.resultTerm] []),
            .opened
              (requestFor "r"
                [PrologNestedCallReadyRegression.resultTerm] [])]
          after.sourceState ∧
        DemandDrivenCallStep.StepsN prog gt 9
          (.ready PrologNestedCallReadyRegression.initialOpenConf)
          after.fineState ∧
        (payloadCells after.payloadContext).length = 3 ∧
        ∃ allEmpty :
            ∀ cell ∈ payloadCells after.payloadContext,
              cell.resource.alts = [],
          ∃ pullNone :
              PLeaTTa.pullAux
                  (flattenOwnedAlts
                    ((payloadCells after.payloadContext).map
                      PayloadCell.resource) []) = none,
            classifyPayloadBank after.payloadContext =
              .exhausted allEmpty pullNone := by
  obtain
    ⟨before, _qHead, middle, _qReady, _qPredicate, _qPayload,
      _beforeReferences, _beforeExecutables, rootSourceSteps, rootFineSteps,
      qCertificate, _rHead, after, _rReady, _rPredicate, _rPayload,
      rCertificate, _afterBodyReferences, _afterBodyExecutables,
      _afterCallerReferences, _afterBaseAlts, afterActiveEmpty,
      afterResourcesExact, middleActiveEmpty, beforeActiveEmpty,
      _afterOuterLength, _afterOuterAllEmpty⟩ :=
    PrologNestedCallReadyRegression.ground_p_q_r_two_nested_pushes
      (prog := prog) (gt := gt)
  have resourceSpine :
      (payloadCells after.payloadContext).map PayloadCell.resource =
        [after.index.active, middle.index.active, before.index.active] := by
    simpa [afterResourcesExact] using
      (payloadCells_map_resource after.payloadContext)
  have cellsLength : (payloadCells after.payloadContext).length = 3 := by
    have exact := congrArg List.length resourceSpine
    simpa using exact
  obtain ⟨first, second, third, cellsExact⟩ :=
    List.length_eq_three.mp cellsLength
  have exactResources :
      [first.resource, second.resource, third.resource] =
        [after.index.active, middle.index.active, before.index.active] := by
    simpa [cellsExact] using resourceSpine
  have firstResource : first.resource = after.index.active :=
    (List.cons.inj exactResources).1
  have exactResourceTail := (List.cons.inj exactResources).2
  have secondResource : second.resource = middle.index.active :=
    (List.cons.inj exactResourceTail).1
  have exactResourceLast := (List.cons.inj exactResourceTail).2
  have thirdResource : third.resource = before.index.active :=
    (List.cons.inj exactResourceLast).1
  have firstEmpty : first.resource.alts = [] := by
    rw [firstResource, afterActiveEmpty]
  have secondEmpty : second.resource.alts = [] := by
    rw [secondResource, middleActiveEmpty]
  have thirdEmpty : third.resource.alts = [] := by
    rw [thirdResource, beforeActiveEmpty]
  have everyEmpty :
      ∀ cell ∈ payloadCells after.payloadContext,
        cell.resource.alts = [] := by
    intro cell member
    rw [cellsExact] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact firstEmpty
    · exact secondEmpty
    · exact thirdEmpty
  have sourceSteps :=
    StepsN.trans rootSourceSteps
      (StepsN.trans qCertificate.sourceSteps rCertificate.sourceSteps)
  have fineSteps :=
    DemandDrivenCallStep.StepsN.trans rootFineSteps
      (DemandDrivenCallStep.StepsN.trans qCertificate.fineSteps
        rCertificate.fineSteps)
  cases classified : classifyPayloadBank after.payloadContext with
  | localLive selection =>
      have selectedMember :
          selection.path.cell ∈ payloadCells after.payloadContext :=
        List.get_mem _ selection.path.position
      have selectedEmpty := everyEmpty selection.path.cell selectedMember
      have selectedLive : selection.path.cell.resource.alts ≠ [] := by
        rw [selection.selected_head]
        simp
      exact False.elim (selectedLive selectedEmpty)
  | exhausted allEmpty pullNone =>
      exact
        ⟨after, by simpa using sourceSteps, by simpa using fineSteps,
          cellsLength, allEmpty, pullNone, classified⟩

end PLeaTTa.PrologPersistentFreeScheduledRejectionPullRegression
