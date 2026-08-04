-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologCommittedScheduledOuterCatchupRegression
Purpose: Exercise the general committed-answer classifier on a reachable
  post-cut execution and reject a fabricated first-live outcome.
Trusted boundary: none
-/
import PLeaTTa.Proofs.PrologCommittedScheduledOuterCatchupBridge
import PLeaTTa.Proofs.PrologMaterializedOperandRegression

namespace PLeaTTa.PrologCommittedScheduledOuterCatchupRegression

open PeTTaSpec.PrologCore
open PrologBodyFailureExhaustedResourceTransitionBridge
open PrologCommittedScheduledOuterCatchupBridge
open PrologCommittedScheduledOuterCatchupBridge.RootClosedCommittedAnswerReady
open PrologCommittedScheduledOuterCatchupBridge.RepresentativePersistentFreeCommittedScheduledPayloadState
open PrologMaterializedOperandRegression.VariableCutCommit
open PrologPersistentFreeCommittedScheduledPayloadBridge
open PrologProductResourceContextBridge
open PrologRetainedPayloadSnapshotBridge

/-- The reachable variable-cut/materialized-unification program is accepted
by the general outer-resource classifier and forced into its terminal arm.

The source state is obtained from the full executable prefix regression; it
is not a hand-built compatible carrier.  The first-live arm is contradicted
by the live carrier's literal empty resource list and the partition's exact
nonempty decomposition. -/
theorem reachable_root_cut_uses_general_terminal_classifier
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    exists
      after : RepresentativePersistentFreeCommittedScheduledPayloadState,
      exists ready : RootClosedCommittedAnswerReady after,
        exists partition :
          TerminalOuterResourceCatchupPartition after.carrier.index.alpha
            after.carrier.index.outer after.carrier.index.resources
            after.carrier.index.context [],
          TerminalRelates prog gt ready partition := by
  rcases root_variable_cut_then_body_answer_exact (prog := prog) (gt := gt) with
    ⟨_active, _before, _first, _second, _firstExecutableTail,
      _secondExecutableTail, _firstSourceExtension, _firstExecutableExtension,
      _secondSourceExtension, _secondExecutableExtension, _firstGenerated,
      _firstInstalled, _secondGenerated, _secondInstalled, _firstFacts,
      _secondFacts, after, oldReady, _rest⟩
  have lengths := after.carrier.payloadContext.lengths_eq
  have outerLengthZero : after.carrier.index.outer.length = 0 := by
    calc
      after.carrier.index.outer.length =
          after.carrier.index.resources.length := lengths.2
      _ = 0 := by rw [oldReady.resourcesEmpty]; rfl
  have outerEmpty : after.carrier.index.outer = [] :=
    List.eq_nil_of_length_eq_zero outerLengthZero
  let ready : RootClosedCommittedAnswerReady after :=
    rootClosedAnswerReady after oldReady.callerReferencesEmpty
      (by
        intro segment member
        rw [outerEmpty] at member
        contradiction)
      oldReady.baseAltsEmpty oldReady.rootFrames
  have classified : ClassifiedRelates prog gt ready :=
    ready.classifyAndRelate
  refine ⟨after, ready, ?_⟩
  cases classified with
  | terminal partition relation =>
      exact ⟨partition, relation⟩
  | firstLive partition relation =>
      have resourcesEmpty : after.carrier.index.resources = [] :=
        oldReady.resourcesEmpty
      have impossible := congrArg List.length partition.resourcesEq
      have emptyLength : after.carrier.index.resources.length = 0 :=
        congrArg List.length resourcesEmpty
      have survivingPositive :
          0 < (partition.crossedResources ++
            partition.first :: partition.survivingResources).length := by
        simp
      omega

end PLeaTTa.PrologCommittedScheduledOuterCatchupRegression
