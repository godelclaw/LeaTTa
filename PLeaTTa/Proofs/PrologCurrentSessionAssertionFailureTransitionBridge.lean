-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologCurrentSessionAssertionFailureTransitionBridge
Purpose: Compose one persistent assertion with retained primitive-unification
  failure in the exact current-session payload/resource context.
Trusted boundary: none
Main exports:
  false_true_no_unifyResolution,
  SpinedActiveProductPayloadResourceRelatesAt.afterAssertionThenRetainedFailure
-/
import PLeaTTa.Proofs.PrologCurrentSessionAssertionTransitionBridge
import PLeaTTa.Proofs.PrologCurrentSessionFailurePayloadTransitionBridge
import PLeaTTa.Proofs.PrologCurrentSessionUnifyTransitionBridge

namespace PLeaTTa.PrologCurrentSessionAssertionFailureTransitionBridge

open Metta (Atom Subst GroundingTable)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.DatabaseActions
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologActivationMacro
open PrologActivatedProductStepBridge
open PrologBodyFailureResourceTransitionBridge
open PrologControlSegmentSpineBridge
open PrologCurrentSessionAssertionTransitionBridge
open PrologCurrentSessionFailurePayloadTransitionBridge
open PrologCurrentSessionPayloadBridge
open PrologCurrentSessionPayloadTransitionBridge
open PrologCurrentSessionUnifyTransitionBridge
open PrologDatabaseActionStepBridge
open PrologGoalAlpha
open PrologOrdinaryStepBridge
open PrologPrefilterScanBridge
open PrologProductResourceContextBridge
open PrologProductResourceTransitionBridge
open PrologRepresentativeProductActivationBridge
open PrologRetainedPayloadSnapshotBridge
open PrologSourceProductContextBridge
open PrologStateBridge
open PLeaTTa.PrologBooleanAliasSafety

/-!
Pinned PeTTa gives every source assertion a fresh generated result variable.
The source-faithful failure path therefore has three legs: perform the
non-backtrackable assertion, bind its generated result to `true`, then fail a
later rigid `false = true` goal and backtrack into the retained clause bank.

This exact shape distinguishes current-session backtracking from restoring
the historical opener session without assuming a compiler-unreachable
pre-bound assertion result.
-/

/-- A carried substitution cannot make the two rigid Boolean source atoms
unifiable.  The proof is source-semantic: it inverts the ordered canonical MGU
derivation rather than consulting the executable unifier. -/
theorem false_true_no_unifyResolution (bindings : Substitution) :
    ¬ ∃ result,
      UnifyResolution bindings (.atom "false") (.atom "true") result := by
  rintro ⟨_result, _extension, computed, _resultShape⟩
  rcases computed with ⟨canonicalBinding, ordered, _bindingShape⟩
  have rigid :
      OrderedTreeMgu
        [(.node (.atom "false") [], .node (.atom "true") [])]
        canonicalBinding := by
    simpa [Substitution.applyTerm, denoteEquations, Term.denote] using ordered
  cases rigid with
  | cons _ _ _ _ _ head _ =>
      have unifies := head.isMostGeneral.1
        ((.node (.atom "false") []), (.node (.atom "true") [])) (by simp)
      simp at unifies

namespace SpinedActiveProductPayloadResourceRelatesAt

/-- A source-reachable assertion followed by a rigid failure preserves the
advanced persistent state while DFS moves to the next retained clause.

Pinned compilation supplies a fresh result variable to the assertion.  The
first unification below therefore records the assertion's ordinary
`result = true` continuation; only the following source goal `false = true`
fails.  Both source and executable component steps remain explicit, and the
composed executions pin the unique assertion effect before all silent
unification/backtracking work. -/
theorem afterAssertionThenRetainedFailure
    {prog : PLeaTTa.Prog} {gt : GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {session : Session}
    {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {selected : ClauseBranch}
    {selectedTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {operation : AssertionOperation}
    {payload : Term} {resultIndex : Nat}
    {resultBindings : Substitution}
    {bodyRest : List PeTTaSpec.PrologCore.Goal}
    {bodyExecutables : List PLeaTTa.Goal}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {current : Substitution} {runtime : Subst} {qterm : Atom}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {source : Search} {state : OpenConf}
    {payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish selected
        selectedTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context}
    {referenceClause : LocalClause}
    {executableOperation : String}
    {executablePayload executableResult : Atom}
    {bodyExecutableTail : List PLeaTTa.Goal}
    {functor : String} {executableClause : PLeaTTa.Clause}
    (agreement :
      SpinedActiveProductPayloadResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened session pending finish selected
        selectedTail altTail bodyBarrier callerBarrier
        (.call operation.predicate
            [payload, .variable (.generated resultIndex)] ::
          .unify (.atom "false") (.atom "true") :: bodyRest)
        bodyExecutables callerReferences callerExecutables outer current
        runtime qterm active resources callerScope outerScope context baseAlts
        source state payloadContext)
    (bodyExecutableShape :
      bodyExecutables =
        PLeaTTa.Goal.wact executableOperation [executablePayload]
            executableResult ::
          bodyExecutableTail)
    (sourceDecoded :
      decodePredicateClause (current.applyTerm payload) =
        some referenceClause)
    (executableDecoded :
      PLeaTTa.predicateClause? gt (subst runtime executablePayload) =
        some (functor, executableClause))
    (clause :
      LocalClauseAgrees referenceClause (functor, executableClause))
    (noDescendants :
      state.persistent.world.specializationDescendants functor = [])
    (freshAfter :
      freshFrontier session.resolver.nextFresh
        (state.persistent.counter + 1))
    (resultSupported :
      AlphaTreeSupported alpha support
        (Term.denote (.variable (.generated resultIndex))))
    (supportIncluded :
      ∀ pair, pair ∈ support → pair ∈ alpha)
    (currentSafe : Substitution.BooleanAliasSafe current)
    (resultResolution :
      UnifyResolution current (.variable (.generated resultIndex))
        (.atom "true") resultBindings)
    (safeAfterAssertion :
      let executableTail :=
        bodyExecutableTail ++
          (callerExecutables ++ flattenExecutables outer)
      ReadyUnifyContinuationSafe support
        (assertionSuccessor operation state executableResult executableTail
          runtime functor executableClause))
    (nonempty : active.alts ≠ []) :
    let sourceAfterAssertion :=
      session.withDatabase
        (operation.update session.resolver.database referenceClause)
    let assertionExecutableTail :=
      bodyExecutableTail ++
        (callerExecutables ++ flattenExecutables outer)
    let executableAfterAssertion :=
      assertionSuccessor operation state executableResult
        assertionExecutableTail runtime functor executableClause
    let sourceAfterAssertionSearch :=
      ActiveProductContext.plug context
        (activeSourceProduct callerScope opened finish selected selectedTail
          current
          (.unify (.variable (.generated resultIndex)) (.atom "true") ::
            .unify (.atom "false") (.atom "true") :: bodyRest)
          callerReferences)
    ∃ (spelling :
          NormalizedAlphaGoalsAgree.ExecutableUnifySpelling)
        (executableLeft executableRight : Atom)
        (afterResultBodyExecutables : List PLeaTTa.Goal)
        (installed : Subst)
        (count : Nat)
        (skippedBranches : List ClauseBranch)
        (skippedClauses candidates : List PLeaTTa.Clause)
        (next : PreparedCursor)
        (nextBranch : ClauseBranch) (nextClause : PLeaTTa.Clause)
        (nextBranchTail : List ClauseBranch)
        (nextClauseTail : List PLeaTTa.Clause)
        (nextAltTail : List PLeaTTa.Alt)
        (nextCopied : PLeaTTa.Clause)
        (pulls :
          RejectedPullsN count (finish.advance selected selectedTail) next)
        (offset :
          PulledHeadOffsetAgrees alpha next nextBranch nextClause
            nextBranchTail nextCopied active nextAltTail),
      let executableAfterResultTail :=
        afterResultBodyExecutables ++
          (callerExecutables ++ flattenExecutables outer)
      let executableAfterResult :=
        unifySuccessor executableAfterAssertion executableAfterResultTail
          installed
      let sourceAfterResult :=
        ActiveProductContext.plug context
          (activeSourceProduct callerScope opened finish selected selectedTail
            resultBindings
            (.unify (.atom "false") (.atom "true") :: bodyRest)
            callerReferences)
      let finalSource :=
        ActiveProductContext.plug context
          (sourceProductFrontier callerScope opened next callerReferences)
      executableOperation = operation.predicate ∧
        RawStep session source
          [.effect
            (operation.effect session.resolver.database referenceClause)]
          .none sourceAfterAssertion
          (.running sourceAfterAssertionSearch) ∧
        DemandDrivenCallStep.Step prog gt (.ready state)
          (.ready executableAfterAssertion) ∧
        SourceDatabaseEffectErasure
          [.effect
            (operation.effect session.resolver.database referenceClause)]
          session sourceAfterAssertion state.persistent
          executableAfterAssertion.persistent ∧
        AlphaTermAgrees alpha
          (.variable (.generated resultIndex)) executableLeft ∧
        AlphaTermAgrees alpha (.atom "true") executableRight ∧
        executableAfterAssertion.control.cur =
          some
            (spelling.goal executableLeft executableRight ::
              executableAfterResultTail,
              runtime) ∧
        RawStep sourceAfterAssertion sourceAfterAssertionSearch []
          .none sourceAfterAssertion (.running sourceAfterResult) ∧
        DemandDrivenCallStep.Step prog gt (.ready executableAfterAssertion)
          (.ready executableAfterResult) ∧
        selectedTail =
          skippedBranches ++ (nextBranch :: nextBranchTail) ∧
        candidates =
          skippedClauses ++ (nextClause :: nextClauseTail) ∧
        skippedBranches.length = count ∧
        skippedClauses.length = count ∧
        (∀ skipped ∈ skippedClauses,
          resolutionClauseRetained active.argsv
            (PLeaTTa.subst active.binding active.res) skipped = false) ∧
        PeTTaSpec.PrologCore.GoalSemantics.StepsN (count + 1)
          (.running sourceAfterAssertion sourceAfterResult)
          []
          (.running sourceAfterAssertion finalSource) ∧
        DemandDrivenCallStep.Step prog gt (.ready executableAfterResult)
          (.ready (unifyFailureSuccessor executableAfterResult)) ∧
        PeTTaSpec.PrologCore.GoalSemantics.StepsN (count + 3)
          (.running session source)
          [.effect
            (operation.effect session.resolver.database referenceClause)]
          (.running sourceAfterAssertion finalSource) ∧
        DemandDrivenCallStep.StepsN prog gt 3 (.ready state)
          (.ready (unifyFailureSuccessor executableAfterResult)) ∧
        sourceAfterAssertion.resolver.database.generation =
          session.resolver.database.generation + 1 ∧
        (unifyFailureSuccessor
            executableAfterResult).persistent.counter =
          state.persistent.counter + 1 ∧
        SpinedPostFailureFrontierPayloadResourceRelatesAt freshFrontier alpha
          support opened sourceAfterAssertion pending bodyBarrier callerBarrier
          callerReferences callerExecutables outer qterm next nextBranch
          nextClause nextBranchTail nextCopied active nextAltTail resources
          callerScope outerScope context baseAlts finalSource
          (unifyFailureSuccessor executableAfterResult)
          (ActiveProductPayloadContext.afterRejectedPullsAndPulledHead
            payloadContext pulls offset) := by
  dsimp only
  rcases
      PLeaTTa.PrologCurrentSessionAssertionTransitionBridge.SpinedActiveProductPayloadResourceRelatesAt.afterAssertion
        (prog := prog) (gt := gt) agreement bodyExecutableShape sourceDecoded
          executableDecoded clause noDescendants freshAfter with
    ⟨operationExact, assertionSourceStep, assertionExecutableStep,
      effectErasure, afterAssertion⟩

  have trueSupported :
      AlphaTreeSupported alpha support (Term.denote (.atom "true")) := by
    simp [AlphaTreeSupported, Term.denote,
      PrologMguOpenAgreement.TreeVariablesSatisfy,
      PrologMguOpenAgreement.TreesVariablesSatisfy]
  rcases
      PLeaTTa.PrologCurrentSessionUnifyTransitionBridge.SpinedActiveProductPayloadResourceRelatesAt.afterUnifySuccess
        (prog := prog) (gt := gt) afterAssertion resultSupported trueSupported
          supportIncluded safeAfterAssertion resultResolution with
    ⟨spelling, executableLeft, executableRight,
      afterResultBodyExecutables, sourceExtension, installed,
      resultLeftAgreement, resultRightAgreement, afterAssertionHead,
      resultSourceStep, resultExecutableStep, afterResult⟩

  have resultBindingsSafe :
      Substitution.BooleanAliasSafe resultBindings :=
    PLeaTTa.PrologBooleanAliasSafety.UnifyResolution.preserves_booleanAliasSafe
      resultResolution currentSafe
      (by
        simp [TermBooleanAliasSafe, Term.denote,
          PrologCanonicalRuntimeReading.NoRuntimeBooleanAliases])
      (by
        simp [TermBooleanAliasSafe, Term.denote,
          PrologCanonicalRuntimeReading.NoRuntimeBooleanAliases,
          PrologCanonicalRuntimeReading.NoRuntimeBooleanAliasesList])
  have falseSupported :
      AlphaTreeSupported alpha support (Term.denote (.atom "false")) := by
    simp [AlphaTreeSupported, Term.denote,
      PrologMguOpenAgreement.TreeVariablesSatisfy,
      PrologMguOpenAgreement.TreesVariablesSatisfy]
  rcases
      PLeaTTa.PrologCurrentSessionFailurePayloadTransitionBridge.SpinedActiveProductPayloadResourceRelatesAt.afterUnifyFailureRetained
        (prog := prog) (gt := gt) afterResult falseSupported trueSupported
          resultBindingsSafe
        (by
          simp [TermBooleanAliasSafe, Term.denote,
            PrologCanonicalRuntimeReading.NoRuntimeBooleanAliases,
            PrologCanonicalRuntimeReading.NoRuntimeBooleanAliasesList])
        (by
          simp [TermBooleanAliasSafe, Term.denote,
            PrologCanonicalRuntimeReading.NoRuntimeBooleanAliases,
            PrologCanonicalRuntimeReading.NoRuntimeBooleanAliasesList])
        (false_true_no_unifyResolution resultBindings) nonempty with
    ⟨count, skippedBranches, skippedClauses, candidates, next, nextBranch,
      nextClause, nextBranchTail, nextClauseTail, nextAltTail, nextCopied,
      pulls, offset, selectedTailEq, candidatesEq, branchCount, clauseCount,
      skippedRejected, failureSourceSteps, failureExecutableStep,
      postFailure⟩

  let sourceAfterAssertion :=
    session.withDatabase
      (operation.update session.resolver.database referenceClause)
  let assertionExecutableTail :=
    bodyExecutableTail ++
      (callerExecutables ++ flattenExecutables outer)
  let executableAfterAssertion :=
    assertionSuccessor operation state executableResult
      assertionExecutableTail runtime functor executableClause
  let executableAfterResultTail :=
    afterResultBodyExecutables ++
      (callerExecutables ++ flattenExecutables outer)
  let executableAfterResult :=
    unifySuccessor executableAfterAssertion executableAfterResultTail installed
  let sourceAfterAssertionSearch :=
    ActiveProductContext.plug context
      (activeSourceProduct callerScope opened finish selected selectedTail
        current
        (.unify (.variable (.generated resultIndex)) (.atom "true") ::
          .unify (.atom "false") (.atom "true") :: bodyRest)
        callerReferences)
  let sourceAfterResult :=
    ActiveProductContext.plug context
      (activeSourceProduct callerScope opened finish selected selectedTail
        resultBindings
        (.unify (.atom "false") (.atom "true") :: bodyRest)
        callerReferences)
  let finalSource :=
    ActiveProductContext.plug context
      (sourceProductFrontier callerScope opened next callerReferences)

  have assertionTransition :
      Transition (.running session source)
        [.effect
          (operation.effect session.resolver.database referenceClause)]
        (.running sourceAfterAssertion sourceAfterAssertionSearch) :=
    .ordinary source
      [.effect
        (operation.effect session.resolver.database referenceClause)]
      session sourceAfterAssertion (.running sourceAfterAssertionSearch)
      assertionSourceStep
  have resultTransition :
      Transition
        (.running sourceAfterAssertion sourceAfterAssertionSearch)
        []
        (.running sourceAfterAssertion sourceAfterResult) :=
    .ordinary sourceAfterAssertionSearch [] sourceAfterAssertion
      sourceAfterAssertion (.running sourceAfterResult) resultSourceStep
  have combinedSource :
      PeTTaSpec.PrologCore.GoalSemantics.StepsN (count + 3)
        (.running session source)
        [.effect
          (operation.effect session.resolver.database referenceClause)]
        (.running sourceAfterAssertion finalSource) := by
    simpa [Nat.add_assoc] using
      PeTTaSpec.PrologCore.GoalSemantics.StepsN.succ (count + 2)
        (.running session source)
        (.running sourceAfterAssertion sourceAfterAssertionSearch)
        (.running sourceAfterAssertion finalSource)
        [.effect
          (operation.effect session.resolver.database referenceClause)]
        []
        assertionTransition
        (PeTTaSpec.PrologCore.GoalSemantics.StepsN.succ (count + 1)
          (.running sourceAfterAssertion sourceAfterAssertionSearch)
          (.running sourceAfterAssertion sourceAfterResult)
          (.running sourceAfterAssertion finalSource)
          [] [] resultTransition failureSourceSteps)
  have combinedExecutable :
      DemandDrivenCallStep.StepsN prog gt 3 (.ready state)
        (.ready (unifyFailureSuccessor executableAfterResult)) := by
    simpa using
      DemandDrivenCallStep.StepsN.succ 2 (.ready state)
        (.ready executableAfterAssertion)
        (.ready (unifyFailureSuccessor executableAfterResult))
        assertionExecutableStep
        (DemandDrivenCallStep.StepsN.succ 1
          (.ready executableAfterAssertion) (.ready executableAfterResult)
          (.ready (unifyFailureSuccessor executableAfterResult))
          resultExecutableStep
          (DemandDrivenCallStep.StepsN.succ 0
            (.ready executableAfterResult)
            (.ready (unifyFailureSuccessor executableAfterResult))
            (.ready (unifyFailureSuccessor executableAfterResult))
            failureExecutableStep
            (DemandDrivenCallStep.StepsN.zero
              (.ready (unifyFailureSuccessor executableAfterResult)))))

  refine
    ⟨spelling, executableLeft, executableRight, afterResultBodyExecutables,
      installed, count, skippedBranches, skippedClauses,
      candidates, next, nextBranch, nextClause, nextBranchTail,
      nextClauseTail, nextAltTail, nextCopied, pulls, offset, ?_⟩
  exact
    ⟨operationExact, assertionSourceStep, assertionExecutableStep,
      effectErasure, resultLeftAgreement, resultRightAgreement,
      afterAssertionHead, resultSourceStep, resultExecutableStep,
      selectedTailEq, candidatesEq, branchCount, clauseCount,
      skippedRejected, failureSourceSteps, failureExecutableStep,
      combinedSource, combinedExecutable,
      operation.update_generation session.resolver.database referenceClause,
      by simp, postFailure⟩

end SpinedActiveProductPayloadResourceRelatesAt

end PLeaTTa.PrologCurrentSessionAssertionFailureTransitionBridge
