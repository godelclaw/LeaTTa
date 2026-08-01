-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologHeterogeneousPrefixRegression
Purpose: Exercise the Type-valued heterogeneous prefix zipper on two real
  source-administrative steps followed by the reachable non-ground q/1 call.
Trusted boundary: none
-/
import PLeaTTa.Proofs.PrologHeterogeneousPrefixBridge
import PLeaTTa.Proofs.PrologNestedCallReadyRegression
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

/-- Two source-only administrative steps, one certified primitive equality,
and the reachable ground `q(7)` activation compose through three literal
dependent middle states.

The equality is a real source and fine step, yet its empty ordered MGU returns
to the exact representative-indexed predecessor state.  The following local
call therefore consumes that same representative rather than a freshly chosen
variant.  Exact costs (five source steps versus four fine steps), the sole
opened-call observation, representative preservation across equality, and the
one-cell local-call push are all exposed simultaneously. -/
theorem truth_then_ground_reflexive_unify_then_q_call_exact_literal_states
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    let request :=
      requestFor "q"
        [PLeaTTa.PrologNestedCallReadyRegression.resultTerm] []
    ∃ before preUnify middle after : ProductPhaseState,
      ∃ run : CertifiedPrefix prog gt
          [.administrative 2, .unify, .localCall 0 request] before after,
        run.states = [before, preUnify, middle, after] ∧
          (CertifiedPrefix.split [.administrative 2, .unify]
              [.localCall 0 request] run).1 = middle ∧
          StepsN 5 before.sourceState [.opened request] after.sourceState ∧
          DemandDrivenCallStep.StepsN prog gt 4 before.fineState
            after.fineState ∧
          preUnify.representative = middle.representative ∧
          preUnify.cellIdentities = middle.cellIdentities ∧
          ∃ cell, after.cellIdentities = cell :: middle.cellIdentities := by
  dsimp only
  obtain
    ⟨middleCarrier, head, rawReady, qPredicate, qPayload, _qReferenceRest,
      _qArguments, _qResult, _qExecutableRest, middleAlpha, _middleSupport,
      middleCurrent, middleRuntime, _middleQterm, _middleDatabase,
      _middleNextFresh, _middleWorld, _rootSourceSteps, _rootFineSteps,
      representativeWitness, only, openedSingleton⟩ :=
    PLeaTTa.PrologNestedCallReadyRegression.qReadyAfterP
      (prog := prog) (gt := gt)
  obtain ⟨middleState, carrierExact, materialized⟩ :=
    representativeWitness
  subst middleCarrier
  have ready : MaterializedNestedCallReady middleState head :=
    { toNestedCallOperationalReady := rawReady.toNestedCallOperationalReady
      materialized := materialized }
  have reading :
      PrologStateBridge.AlphaTermAgrees middleState.carrier.index.alpha
        PLeaTTa.PrologNestedCallReadyRegression.resultTerm
        PLeaTTa.PrologNestedCallReadyRegression.resultAtom := by
    rw [middleAlpha]
    exact PrologStateBridge.AlphaTermAgrees.integer 7
  have trimmed :
      PLeaTTa.trimFor
          (RepresentativeActivePayloadState.unifyExecutableTail middleState
            middleState.carrier.index.bodyExecutables)
          middleState.carrier.index.qterm middleState.carrier.index.runtime =
        middleState.carrier.index.runtime := by
    rw [middleRuntime]
    simp [PLeaTTa.trimFor, PLeaTTa.trimSubst, PLeaTTa.filterLiveSubst]
  let preUnifyState :=
    beforeReflexiveUnify middleState
      PLeaTTa.PrologNestedCallReadyRegression.resultTerm
      PLeaTTa.PrologNestedCallReadyRegression.resultAtom reading
  have unifyFacts :=
    PLeaTTa.PrologHeterogeneousPrefixBridge.RepresentativeActivePayloadState.reflexiveUnifyFacts
      (prog := prog) (gt := gt) middleState
      PLeaTTa.PrologNestedCallReadyRegression.resultTerm
      PLeaTTa.PrologNestedCallReadyRegression.resultAtom reading trimmed
  obtain
    ⟨count, skippedBranches, skippedClauses, finish, branch, clause,
      branchTail, clauseTail, altTail, copied, installed, afterState,
      callFacts⟩ :=
    ready.pushDetailed (prog := prog) (gt := gt)
  have finishNonempty : finish.remaining ≠ [] := by
    rw [callFacts.frontier.finishRemaining]
    simp
  have pulls :
      PrologPrefilterScanBridge.RejectedPullsN count
        (openedFor middleState.carrier.index.session "q"
          [PLeaTTa.PrologNestedCallReadyRegression.resultTerm]
          middleState.carrier.index.current).cursor finish := by
    simpa [qPredicate, qPayload] using callFacts.pulls
  have pathExact :=
    PrologNestedCallReadyBridge.RejectedPullsN.eq_zero_of_singleton_of_finish_nonempty
      openedSingleton pulls finishNonempty
  have countZero : count = 0 := pathExact.1
  subst count
  let request :=
    requestFor "q"
      [PLeaTTa.PrologNestedCallReadyRegression.resultTerm] []
  let beforeState := beforeTruth (beforeTruth preUnifyState)
  have administrative :
      CertifiedTransition prog gt (.administrative 2)
        (.active beforeState) (.active preUnifyState) := by
    have raw :=
      CertifiedTransition.administrative (prog := prog) (gt := gt)
        beforeState (beforeTruthTwiceSteps preUnifyState)
    simpa [beforeState, afterAdministrative_beforeTruth_twice] using raw
  have unified :
      CertifiedTransition prog gt .unify
        (.active preUnifyState) (.active middleState) :=
    .unify unifyFacts
  have nested :
      CertifiedTransition prog gt (.localCall 0 request)
        (.active middleState) (.active afterState) := by
    simpa [request, qPredicate, qPayload, middleCurrent] using
      (CertifiedTransition.localCall (prog := prog) (gt := gt) callFacts)
  let run :
      CertifiedPrefix prog gt
        [.administrative 2, .unify, .localCall 0 request]
        (.active beforeState) (.active afterState) :=
    .cons administrative
      (.cons unified (.cons nested (.nil (.active afterState))))
  refine
    ⟨.active beforeState, .active preUnifyState, .active middleState,
      .active afterState, run, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · simpa [run, request, TransitionSchedule.sourceCost,
      TransitionSchedule.sourceEvents, TransitionKind.sourceCost,
      TransitionKind.sourceEvents] using run.sourceSteps
  · simpa [run, TransitionSchedule.fineCost, TransitionKind.fineCost] using
      run.fineSteps
  · simp [preUnifyState, beforeReflexiveUnify,
      ProductPhaseState.representative]
  · simpa [ProductPhaseState.cellIdentities] using
      unifyFacts.payloadCellsExact.symm
  · simpa [TransitionKind.PayloadEvolution,
      ProductPhaseState.cellIdentities] using nested.payloadEvolution

end PLeaTTa.PrologHeterogeneousPrefixRegression
