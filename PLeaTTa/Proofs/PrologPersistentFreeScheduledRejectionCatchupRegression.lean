-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologPersistentFreeScheduledRejectionCatchupRegression
Purpose: Exercise zero-depth and nonzero-depth source catch-up on payloads
  produced by reachable local-resolution prefixes.
Trusted boundary: none
-/
import PLeaTTa.Proofs.PrologPersistentFreeScheduledRejectionCatchupBridge
import PLeaTTa.Proofs.PrologPersistentFreeScheduledRejectionPullRegression

namespace PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupRegression

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open DemandDrivenStep
open PrologBodyFailureExhaustedResourceTransitionBridge
open PrologBodyFailureOuterResourceActivationBridge
open PrologBodyFailureOuterResourceCatchupBridge
open PrologNestedCallChainBridge
open PrologPersistentFreeScheduledRejectionCatchupBridge
open PrologPersistentFreeScheduledRejectionPullBridge
open PrologProductResourceContextBridge
open PrologScheduledPayloadPathBridge

/-!
# Reachable count discriminators

The two fixtures have the same locally owned `p/q/r` origin but select at
opposite depths.  The first still owns an adjacent duplicate `p/1` clause and
therefore selects at payload position zero.  The second has exhausted `r/1`
and `q/1`, so the same duplicate is selected at position two.
-/

/-- A reachable duplicate-`p/1` activation selects the payload head.  Its
ranked crossing phase is exactly zero steps: no predicate frame is re-entered
and no body-failure `+1` can be inserted.  Only the selected resource's own
conservative rejected prefix remains in the resulting source run.

[SPEC metta.pl:251-256] -/
theorem reachable_position_zero_has_no_frame_entry_cost
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ (state : ActivePayloadState)
        (selection : PayloadLocalSelection state.payloadContext)
        (partition :
          OuterResourceCatchupPartition state.index.alpha
            ({ barrier := state.index.callerBarrier
               references := state.index.callerReferences
               executables := state.index.callerExecutables } ::
              state.index.outer)
            (state.index.active :: state.index.resources)
            ({ callerScope := state.index.callerScope
               predicateScope := state.index.opened.scope
               retained :=
                 .clauses state.index.opened.scope
                   (state.index.finish.advance state.index.branch
                     state.index.branchTail)
               callerRest := state.index.callerReferences } ::
              state.index.context))
        (count : Nat)
        (finish : PeTTaSpec.PrologCore.Resolver.PreparedCursor)
        (branch : PeTTaSpec.PrologCore.Resolver.ClauseBranch)
        (clause : PLeaTTa.Clause)
        (branchTail : List PeTTaSpec.PrologCore.Resolver.ClauseBranch)
        (copied : PLeaTTa.Clause),
      PeTTaSpec.PrologCore.GoalSemantics.StepsN 2
          (.running PrologNestedCallReadyRegression.siblingInitialSession
            (.task PrologNestedCallReadyRegression.rootScope
              [.call "p" [PrologNestedCallReadyRegression.resultTerm]] []))
          [.opened
            (requestFor "p" [PrologNestedCallReadyRegression.resultTerm] [])]
          state.sourceState ∧
      DemandDrivenCallStep.StepsN prog gt 3
          (.ready PrologNestedCallReadyRegression.siblingInitialOpenConf)
          state.fineState ∧
      classifyPayloadBank state.payloadContext = .localLive selection ∧
      selection.path.position.val = 0 ∧
      PayloadLocalPartitionAgrees selection partition ∧
      partition.crossedFrames = [] ∧
      partition.rejectionSteps = 0 ∧
      PeTTaSpec.PrologCore.GoalSemantics.StepsN count
        (.running state.index.session
          (PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.PayloadLocalSelection.enteredSourceFrontier
            selection))
        []
        (.running state.index.session
          (firstLiveReadySourceFrontier partition finish)) ∧
      RejectedPrefixPulledHeadOffsetAgrees state.index.alpha
        partition.firstCursor finish count branch clause branchTail copied
        partition.first partition.tail := by
  obtain
    ⟨state, _bodyReferences, _bodyExecutables, _alpha, _freshFrontier,
      _support, _current, _runtime, _qterm, _callerReferences, _outer,
      resourcesEmpty, _baseAlts, activeAlts, _database, _nextFresh, _world,
      _below, sourceSteps, fineSteps, _representative⟩ :=
    PrologNestedCallReadyRegression.siblingPActive
      (prog := prog) (gt := gt)
  have resourceSpine :
      (payloadCells state.payloadContext).map PayloadCell.resource =
        [state.index.active] := by
    simpa [resourcesEmpty] using
      (payloadCells_map_resource state.payloadContext)
  have cellsLength : (payloadCells state.payloadContext).length = 1 := by
    have exact := congrArg List.length resourceSpine
    simpa using exact
  obtain ⟨only, cellsExact⟩ :=
    List.length_eq_one_iff.mp cellsLength
  have onlyResource : only.resource = state.index.active := by
    have exactResources : [only.resource] = [state.index.active] := by
      simpa [cellsExact] using resourceSpine
    exact (List.cons.inj exactResources).1
  have onlyLive : only.resource.alts ≠ [] := by
    rw [onlyResource, activeAlts]
    simp
  cases classified : classifyPayloadBank state.payloadContext with
  | exhausted allEmpty _pullNone =>
      have member : only ∈ payloadCells state.payloadContext := by
        rw [cellsExact]
        simp
      exact False.elim (onlyLive (allEmpty only member))
  | localLive selection =>
      have positionZero : selection.path.position.val = 0 := by
        have positionLt := selection.path.position.isLt
        exact Nat.lt_one_iff.mp (lt_of_lt_of_eq positionLt cellsLength)
      obtain
        ⟨partition, count, skippedBranches, skippedClauses, candidates,
          finish, branch, clause, branchTail, clauseTail, copied,
          partitionExact, cursorSplit, candidatesSplit, branchCount,
          clauseCount, catchup, rejectedPrefix, headExact⟩ :=
        PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.PayloadLocalSelection.catchupToSelectedReady
          selection state.index.session
      have crossedLength : partition.crossedFrames.length = 0 := by
        rw [partitionExact.crossedDepthExact, positionZero]
      have crossedFrames : partition.crossedFrames = [] :=
        List.length_eq_zero_iff.mp crossedLength
      have work :
          CrossedEmptyResourceFramesAgrees state.index.alpha
            partition.crossedResources [] partition.rejectionSteps := by
        simpa [crossedFrames] using partition.crossedWork
      have rejectionZero : partition.rejectionSteps = 0 :=
        (PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.CrossedEmptyResourceFramesAgrees.indicesOfFramesNil
          work).2
      have exactCatchup :
          PeTTaSpec.PrologCore.GoalSemantics.StepsN count
            (.running state.index.session
              (PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.PayloadLocalSelection.enteredSourceFrontier
                selection))
            []
            (.running state.index.session
              (firstLiveReadySourceFrontier partition finish)) := by
        simpa [crossedFrames, rejectionZero] using catchup
      exact
        ⟨state, selection, partition, count, finish, branch, clause,
          branchTail, copied, sourceSteps, fineSteps, classified,
          positionZero, partitionExact, crossedFrames, rejectionZero,
          exactCatchup, rejectedPrefix⟩

/-- The reachable nested sibling fixture selects at position two, and the
source catch-up therefore contains exactly two frame crossings in addition to
all hidden conservative rejections.  A zero-step or position-only quotient
cannot satisfy the exact count.

[SPEC metta.pl:251-256] -/
theorem reachable_position_two_counts_both_crossed_frames
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ (after : ActivePayloadState)
        (selection : PayloadLocalSelection after.payloadContext)
        (partition :
          OuterResourceCatchupPartition after.index.alpha
            ({ barrier := after.index.callerBarrier
               references := after.index.callerReferences
               executables := after.index.callerExecutables } ::
              after.index.outer)
            (after.index.active :: after.index.resources)
            ({ callerScope := after.index.callerScope
               predicateScope := after.index.opened.scope
               retained :=
                 .clauses after.index.opened.scope
                   (after.index.finish.advance after.index.branch
                     after.index.branchTail)
               callerRest := after.index.callerReferences } ::
              after.index.context))
        (count : Nat)
        (finish : PeTTaSpec.PrologCore.Resolver.PreparedCursor),
      selection.path.position.val = 2 ∧
      PayloadLocalPartitionAgrees selection partition ∧
      partition.crossedFrames.length = 2 ∧
      PeTTaSpec.PrologCore.GoalSemantics.StepsN
        (partition.rejectionSteps + 2 + count)
        (.running after.index.session
          (PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.PayloadLocalSelection.enteredSourceFrontier
            selection))
        []
        (.running after.index.session
          (firstLiveReadySourceFrontier partition finish)) := by
  obtain
    ⟨after, selection, _sourceSteps, _fineSteps, _classified, _cellsLength,
      positionTwo, _selectedLive, _earlierEmpty⟩ :=
    PrologPersistentFreeScheduledRejectionPullRegression.reachable_outer_sibling_classifies_at_position_two
      (prog := prog) (gt := gt)
  obtain
    ⟨partition, count, skippedBranches, skippedClauses, candidates, finish,
      branch, clause, branchTail, clauseTail, copied, partitionExact,
      cursorSplit, candidatesSplit, branchCount, clauseCount, catchup,
      rejectedPrefix, headExact⟩ :=
    PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.PayloadLocalSelection.catchupToSelectedReady
      selection after.index.session
  have crossedLength : partition.crossedFrames.length = 2 := by
    rw [partitionExact.crossedDepthExact, positionTwo]
  have exactCatchup :
      PeTTaSpec.PrologCore.GoalSemantics.StepsN
        (partition.rejectionSteps + 2 + count)
        (.running after.index.session
          (PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.PayloadLocalSelection.enteredSourceFrontier
            selection))
        []
        (.running after.index.session
          (firstLiveReadySourceFrontier partition finish)) := by
    simpa [crossedLength] using catchup
  exact
    ⟨after, selection, partition, count, finish, positionTwo,
      partitionExact, crossedLength, exactCatchup⟩

/-- The ranked source-only catch-up genuinely counts hidden work inside
fine-empty crossed resources.  Two crossed cells each reject one source clause,
so the entered-head catch-up takes exactly four steps: two silent rejected
pulls plus two frame crossings.

This is the nonzero discriminator for `rejectionSteps`; a proof that counted
only payload depth would produce two rather than four.

[SPEC metta.pl:251-256] -/
theorem two_hidden_rejections_plus_two_crossings_take_four_steps :
    ∃ (segments : List PrologControlSegmentSpineBridge.ControlSegment)
        (resources : List RetainedAlternativeSegment)
        (context : PrologSourceProductContextBridge.ActiveProductContext)
        (partition : OuterResourceCatchupPartition [] segments resources context)
        (firstFrame secondFrame :
          PrologSourceProductContextBridge.ActiveProductFrame)
        (cursor : PeTTaSpec.PrologCore.Resolver.PreparedCursor),
      partition.crossedFrames = [firstFrame, secondFrame] ∧
      partition.rejectionSteps = 2 ∧
      PeTTaSpec.PrologCore.GoalSemantics.StepsN 4
        (.running PrologNestedCallReadyRegression.initialSession
          (PrologSourceProductContextBridge.ActiveProductContext.plug
            ([secondFrame] ++
              partition.firstFrame :: partition.survivingContext)
            (frameRetainedFrontier firstFrame cursor)))
        []
        (.running PrologNestedCallReadyRegression.initialSession
          (firstLiveSourceFrontier partition)) := by
  obtain ⟨partition, crossedResourcesLength, rejectionSteps, _firstLive⟩ :=
    two_crossed_then_live_partition_is_inhabited
  have crossedFramesLength : partition.crossedFrames.length = 2 := by
    calc
      partition.crossedFrames.length = partition.crossedResources.length :=
        partition.crossedWork.length_eq.symm
      _ = 2 := crossedResourcesLength
  obtain ⟨firstFrame, secondFrame, framesExact⟩ :=
    List.length_eq_two.mp crossedFramesLength
  have work :
      CrossedEmptyResourceFramesAgrees [] partition.crossedResources
        [firstFrame, secondFrame] 2 := by
    simpa [framesExact, rejectionSteps] using partition.crossedWork
  obtain
    ⟨resource, remainingResources, cursor, _finish, _count, _tailCount,
      resourcesExact, _stepsExact, retainedShape, _ownership, _empty,
      _pulls, _finishEmpty, _tail⟩ :=
    PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.CrossedEmptyResourceFramesAgrees.decomposeFramesCons
      work
  have workCons :
      CrossedEmptyResourceFramesAgrees []
        (resource :: remainingResources) [firstFrame, secondFrame] 2 := by
    simpa [resourcesExact] using work
  have catchup :=
    PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupBridge.CrossedEmptyResourceFramesAgrees.sourceCatchupToFrameFromEnteredHead
      workCons PrologNestedCallReadyRegression.initialSession cursor
      retainedShape
      partition.firstFrame partition.survivingContext partition.firstCursor
      partition.firstRetainedShape
  refine
    ⟨_, _, _, partition, firstFrame, secondFrame, cursor, framesExact,
      rejectionSteps, ?_⟩
  simpa [firstLiveSourceFrontier] using catchup

end PLeaTTa.PrologPersistentFreeScheduledRejectionCatchupRegression
