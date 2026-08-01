-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologHeterogeneousPrefixRegression
Purpose: Exercise the Type-valued heterogeneous prefix zipper on two real
  source-administrative steps followed by the reachable non-ground q/1 call.
Trusted boundary: none
-/
import PLeaTTa.Proofs.PrologHeterogeneousPrefixBridge
import PLeaTTa.Proofs.PrologUnboundNestedCallRegression

namespace PLeaTTa.PrologHeterogeneousPrefixRegression

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.Resolver
open PrologHeterogeneousPrefixBridge
open PrologHeterogeneousPrefixBridge.RepresentativeActivePayloadState
open PrologNestedCallReadyBridge
open PrologUnboundNestedCallRegression

/-- The mixed prefix is inhabited by two real source-only administrative steps
followed by the reachable non-ground `q(generated 0)` activation.

The returned state list and dependent split both expose the same literal
middle.  Thus this is not a counts-only witness: the administrative successor
is definitionally the nested-call predecessor.  Its exact source cost is four
while its fine cost is three, so the two schedule folds are observably distinct.
Exact source observations and the one-cell payload push are retained
simultaneously. -/
theorem truth_then_unbound_q_call_exact_literal_middle
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    let request :=
      requestFor "q" [(.variable (.generated 0) : Term)] pSourceExtension
    ∃ before middle after : ProductPhaseState,
      ∃ run : CertifiedPrefix prog gt
          [.administrative 2, .localCall 0 request] before after,
        run.states = [before, middle, after] ∧
          (CertifiedPrefix.split [.administrative 2]
              [.localCall 0 request] run).1 = middle ∧
          StepsN 4 before.sourceState [.opened request] after.sourceState ∧
          DemandDrivenCallStep.StepsN prog gt 3 before.fineState
            after.fineState ∧
          ∃ cell, after.cellIdentities = cell :: middle.cellIdentities := by
  dsimp only
  obtain
    ⟨middleState, head, ready, qPredicate, qPayload, _qReferenceRest,
      _qArguments, _qResult, _qExecutableRest, middleCurrent, _middleDatabase,
      _middleWorld, openedSingleton, _middleNextFresh, _middleCounter,
      _rootSourceSteps, _rootFineSteps⟩ :=
    qMaterializedReadyAfterP (prog := prog) (gt := gt)
  obtain
    ⟨count, skippedBranches, skippedClauses, finish, branch, clause,
      branchTail, clauseTail, altTail, copied, installed, afterState, facts⟩ :=
    ready.pushDetailed (prog := prog) (gt := gt)
  have finishNonempty : finish.remaining ≠ [] := by
    rw [facts.frontier.finishRemaining]
    simp
  have pathExact :=
    RejectedPullsN.eq_zero_of_singleton_of_finish_nonempty
      openedSingleton facts.pulls finishNonempty
  have countZero : count = 0 := pathExact.1
  subst count
  let request :=
    requestFor "q" [(.variable (.generated 0) : Term)] pSourceExtension
  let beforeState := beforeTruth (beforeTruth middleState)
  have administrative :
      CertifiedTransition prog gt (.administrative 2)
        (.active beforeState) (.active middleState) := by
    have raw :=
      CertifiedTransition.administrative (prog := prog) (gt := gt)
        beforeState (beforeTruthTwiceSteps middleState)
    simpa [beforeState, afterAdministrative_beforeTruth_twice] using raw
  have nested :
      CertifiedTransition prog gt (.localCall 0 request)
        (.active middleState) (.active afterState) := by
    simpa [request, qPredicate, qPayload, middleCurrent] using
      (CertifiedTransition.localCall (prog := prog) (gt := gt) facts)
  let run :
      CertifiedPrefix prog gt [.administrative 2, .localCall 0 request]
        (.active beforeState) (.active afterState) :=
    .cons administrative (.cons nested (.nil (.active afterState)))
  refine
    ⟨.active beforeState, .active middleState, .active afterState, run, ?_, ?_,
      ?_, ?_, ?_⟩
  · rfl
  · rfl
  · simpa [run, request, TransitionSchedule.sourceCost,
      TransitionSchedule.sourceEvents, TransitionKind.sourceCost,
      TransitionKind.sourceEvents] using run.sourceSteps
  · simpa [run, TransitionSchedule.fineCost, TransitionKind.fineCost] using
      run.fineSteps
  · simpa [TransitionKind.PayloadEvolution, ProductPhaseState.cellIdentities]
      using nested.payloadEvolution

end PLeaTTa.PrologHeterogeneousPrefixRegression
