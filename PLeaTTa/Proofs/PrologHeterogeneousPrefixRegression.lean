-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologHeterogeneousPrefixRegression
Purpose: Exercise the Type-valued heterogeneous prefix zipper on two real
  source-administrative steps followed by the reachable non-ground q/1 call.
Trusted boundary: none
-/
import PLeaTTa.Proofs.PrologHeterogeneousPrefixBridge
import PLeaTTa.Proofs.PrologMguVariantRenaming
import PLeaTTa.Proofs.PrologNestedCallReadyRegression
import PLeaTTa.Proofs.PrologUnboundNestedCallRegression

namespace PLeaTTa.PrologHeterogeneousPrefixRegression

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open PrologAlphaFreshFrontierBridge
open PrologHeterogeneousPrefixBridge
open PrologHeterogeneousPrefixBridge.RepresentativeActivePayloadState
open PrologMguBridge
open PrologNestedCallChainBridge
open PrologNestedCallReadyBridge
open PrologOrdinaryStepBridge
open PrologPrefilterCallBridge
open PrologStateBridge
open PrologUnboundNestedCallRegression

/-! ## Concrete non-reflexive primitive equality -/

/-- The exact source binding after the reached root query variable is unified
with `7`.  The new ordered MGU lives at the list head and the earlier
`queryIdentity ↦ generated 0` activation binding remains as its suffix. -/
def querySevenResult : Substitution :=
  TreeSubstitution.reify
      [((.generated 0 : LogicVar), Term.denote (.integer 7))] ++
    pSourceExtension

private theorem querySeven_resolves :
    UnifyResolution pSourceExtension queryTerm (.integer 7)
      querySevenResult := by
  let extension : TreeSubstitution :=
    [((.generated 0 : LogicVar), Term.denote (.integer 7))]
  have computed :
      ComputesDenotationalMgu
        [(.variable (.generated 0), .integer 7)]
        (TreeSubstitution.reify extension) := by
    exact computes_singleton_left_variable (.generated 0)
      (.integer 7) (by
        intro equality
        cases equality) (by rfl)
  refine ⟨TreeSubstitution.reify extension, ?_, ?_⟩
  · simpa [pSourceExtension, queryTerm, queryIdentity, extension,
      TreeSubstitution.reify, Tree.reify, Substitution.applyTerm,
      Term.instantiateOne] using computed
  · rfl

/-- The actual `q/1` occurrence prepared after `Z = 7` keeps the raw
`generated 0 = generated 1` head equation while carrying the new binding.
Normalization, not call preparation, materializes the left side to `7`. -/
def qSevenPreparedBranch : ClauseBranch :=
  { sourceId :=
      ((Database.empty.assertz pReferenceClause).allocate qReferenceClause).id
    callGeneration := referenceDatabase.generation
    freshSubstitution :=
      [(clauseIdentity, .variable (.generated 1))]
    headEquations :=
      [(.variable (.generated 0), .variable (.generated 1))]
    body := []
    bindings := querySevenResult
    firstFresh := 1
    nextFresh := 2 }

def qSevenSourceResult : Substitution :=
  TreeSubstitution.reify
      [((.generated 1 : LogicVar), Term.denote (.integer 7))] ++
    querySevenResult

@[simp] theorem querySevenResult_apply_queryTerm :
    querySevenResult.applyTerm queryTerm = .integer 7 := by
  rfl

@[simp] theorem querySevenResult_apply_generatedZero :
    querySevenResult.applyTerm (.variable (.generated 0)) = .integer 7 := by
  rfl

theorem qSevenPreparedBranch_normalized :
    qSevenPreparedBranch.normalizedHeadEquations =
      [(.integer 7, .variable (.generated 1))] := by
  rfl

private theorem qSevenPreparedBranch_resolves :
    HeadResolution qSevenPreparedBranch qSevenSourceResult := by
  let extension : TreeSubstitution :=
    [((.generated 1 : LogicVar), Term.denote (.integer 7))]
  have computed :
      ComputesDenotationalMgu
        [(.integer 7, .variable (.generated 1))]
        (TreeSubstitution.reify extension) := by
    exact computes_singleton_right_variable (.integer 7) (.generated 1)
      (by
        intro identity equality
        cases equality)
      (by rfl)
  refine ⟨TreeSubstitution.reify extension, ?_, ?_⟩
  · rw [qSevenPreparedBranch_normalized]
    exact computed
  · rfl

/-- The mixed prefix is inhabited by two real source-only administrative steps
followed by the reachable non-ground `q(generated 0)` activation.

The returned state list and dependent split both expose the same literal
middle.  Thus this is not a counts-only witness: the administrative successor
is definitionally the nested-call predecessor.  Its exact source cost is four
while its fine cost is three, so the two schedule folds are observably distinct.
Exact source observations and the one-cell payload push are retained
simultaneously.  Both literal edges also inhabit the premise-only readiness
relation and the unindexed coupled-step relation, so the global producer is
exercised by two different transition kinds rather than existing as unused
scaffolding. -/
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
          ∃ beforeReady : ActiveStepReady before,
            ∃ middleReady : ActiveStepReady middle,
              beforeReady.Produces prog gt middle ∧
                middleReady.Produces prog gt after ∧
                StepsN 4 before.sourceState [.opened request]
                  after.sourceState ∧
                DemandDrivenCallStep.StepsN prog gt 3 before.fineState
                  after.fineState ∧
                ∃ cell,
                  after.cellIdentities = cell :: middle.cellIdentities := by
  dsimp only
  obtain
    ⟨middleState, head, ready, qPredicate, qPayload, _qReferenceRest,
      _qArguments, _qResult, _qExecutableRest, _qExecutableTail, middleCurrent,
      _middleSupport,
      _middleQueryReading, _middleQuerySupported, _middleQterm,
      _middleOpenQterm,
      _middleCallerReferences, _middleCallerExecutables, _middleOuter,
      _middleBaseAlts, _middleFrames,
      _middleDatabase, _middleWorld, openedSingleton, _middleNextFresh, _middleCounter,
      _rootSourceSteps, _rootFineSteps, _runtimeQueryExact,
      _runtimeResultFixed⟩ :=
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
  have administrativePositive : 0 < 2 := by omega
  let administrativeReady : ActiveStepReady (.active beforeState) :=
    .administrative beforeState administrativePositive
      (beforeTruthTwiceSteps middleState)
  let nestedReady : ActiveStepReady (.active middleState) :=
    .localCall middleState head ready
  have administrativeProduction :
      administrativeReady.Produces prog gt
        (.active middleState) :=
    by
      have raw :=
        ActiveStepReady.Produces.administrative
          (prog := prog) (gt := gt) beforeState administrativePositive
          (beforeTruthTwiceSteps middleState)
      simpa [administrativeReady, beforeState,
        afterAdministrative_beforeTruth_twice] using raw
  have nestedProduction :
      nestedReady.Produces prog gt (.active afterState) := by
    simpa [nestedReady] using
      (ActiveStepReady.Produces.localCall
        (prog := prog) (gt := gt) middleState head ready facts)
  let run :
      CertifiedPrefix prog gt [.administrative 2, .localCall 0 request]
        (.active beforeState) (.active afterState) :=
    .cons administrative (.cons nested (.nil (.active afterState)))
  refine
    ⟨.active beforeState, .active middleState, .active afterState, run, ?_, ?_,
      administrativeReady, nestedReady, administrativeProduction,
      nestedProduction,
      ?_, ?_, ?_⟩
  · rfl
  · rfl
  · simpa [run, request, TransitionSchedule.sourceCost,
      TransitionSchedule.sourceEvents, TransitionKind.sourceCost,
      TransitionKind.sourceEvents, ProductPhaseState.sourceState] using
      run.sourceSteps
  · simpa [run, TransitionSchedule.fineCost, TransitionKind.fineCost,
      ProductPhaseState.fineState] using run.fineSteps
  · simpa [TransitionKind.PayloadEvolution, ProductPhaseState.cellIdentities]
      using nested.payloadEvolution

/-- Two source-only administrative steps followed by the reached query
variable's non-reflexive equality with `7` form one exact heterogeneous
prefix.

Unlike the reflexive witness below, both independently ordered MGU residuals
are nonempty.  The executable residual is proved nonempty without exposing
the fresh runtime name: mutual residual variants preserve variable shape,
and the selected alpha valuation then forces the executable bind-left
singleton.  Consequently the representative changes literally while the
payload-cell identities remain unchanged. -/
theorem truth_then_query_unify_seven_exact_nonempty_residual
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
      ∃ before preUnify after : ProductPhaseState,
      ∃ sourceExtension executableExtension : TreeSubstitution,
        ∃ generated : Metta.Subst,
          ∃ run : CertifiedPrefix prog gt
              [.administrative 2, .unify] before after,
            run.states = [before, preUnify, after] ∧
              StepsN 3 before.sourceState [] after.sourceState ∧
              DemandDrivenCallStep.StepsN prog gt 1 before.fineState
                after.fineState ∧
              sourceExtension ≠ [] ∧
              executableExtension ≠ [] ∧
              generated ≠ [] ∧
              preUnify.representative ≠ after.representative ∧
              preUnify.cellIdentities = after.cellIdentities ∧
              querySevenResult.applyTerm queryTerm = .integer 7 := by
  obtain
    ⟨middleState, _head, _ready, _qPredicate, _qPayload, _qReferenceRest,
      _qArguments, _qResult, _qExecutableRest, _qExecutableTail, middleCurrent,
      middleSupport, queryReading, querySupported, middleQterm, middleOpenQterm,
      _middleCallerReferences, _middleCallerExecutables, _middleOuter,
      _middleBaseAlts, _middleFrames,
      _middleDatabase,
      _middleWorld, _openedSingleton, _middleNextFresh, _middleCounter,
      _rootSourceSteps, _rootFineSteps, _runtimeQueryExact,
      _runtimeResultFixed⟩ :=
    qMaterializedReadyAfterP (prog := prog) (gt := gt)
  have integerReading :
      AlphaTermAgrees middleState.carrier.index.alpha (.integer 7)
        (.gnd (.int 7)) :=
    AlphaTermAgrees.integer 7
  let preUnifyState :=
    beforeUnify middleState queryTerm (.integer 7) queryAtom
      (.gnd (.int 7)) queryReading integerReading
  have preCurrent :
      preUnifyState.carrier.index.current = pSourceExtension := by
    simpa [preUnifyState, beforeUnify, ActivePayloadState.ofAgreement] using
      middleCurrent
  have preSupport :
      preUnifyState.carrier.index.support = rootAlpha := by
    simpa [preUnifyState, beforeUnify, ActivePayloadState.ofAgreement] using
      middleSupport
  have preQterm : preUnifyState.carrier.index.qterm = queryAtom := by
    simpa [preUnifyState, beforeUnify, ActivePayloadState.ofAgreement] using
      middleQterm
  have leftSupported :
      AlphaTreeSupported preUnifyState.carrier.index.alpha
        preUnifyState.carrier.index.support (Term.denote queryTerm) := by
    simpa [preUnifyState, beforeUnify, ActivePayloadState.ofAgreement] using
      querySupported
  have rightSupported :
      AlphaTreeSupported preUnifyState.carrier.index.alpha
        preUnifyState.carrier.index.support (Term.denote (.integer 7)) := by
    simp [AlphaTreeSupported, Term.denote,
      PrologMguOpenAgreement.TreeVariablesSatisfy,
      PrologMguOpenAgreement.TreesVariablesSatisfy]
  have continuationLive :
      ReadyUnifyContinuationLive preUnifyState.carrier.index.support
        preUnifyState.carrier.index.openConf := by
    intro executableHead rest runtime _current identity name linked
    rw [preSupport] at linked
    have pairExact : (identity, name) = (queryIdentity, "z") := by
      simpa [rootAlpha] using List.mem_singleton.mp linked
    have nameExact : name = "z" := congrArg Prod.snd pairExact
    have preOpenQterm :
        preUnifyState.carrier.index.openConf.control.qterm = queryAtom := by
      simpa [preUnifyState, beforeUnify, unifyPredecessorOpenConf,
        ActivePayloadState.ofAgreement] using middleOpenQterm
    rw [preOpenQterm, nameExact]
    exact PLeaTTa.isTrimRoot_qterm_mem rest queryAtom "z" (by
      simp [queryAtom, Metta.Atom.vars])
  obtain
    ⟨bodyExecutableTail, sourceExtension, executableExtension, generated,
      _installed, afterState, facts⟩ :=
    PLeaTTa.PrologHeterogeneousPrefixBridge.RepresentativeActivePayloadState.exists_afterUnifySuccessLive
      preUnifyState
      (prog := prog) (gt := gt) (bodyRest := middleState.carrier.index.bodyReferences)
      rfl leftSupported rightSupported continuationLive (by
        simpa [preCurrent] using querySeven_resolves)
  obtain
    ⟨spelling, executableLeft, executableRight, leftAgreement,
      rightAgreement, executableHead, selected⟩ :=
    facts.selectedExecution
  have bodyData :
      TaskDataAgrees preUnifyState.carrier.index.alpha
        preUnifyState.carrier.index.support
        preUnifyState.carrier.index.canonical
        preUnifyState.carrier.index.referenceBase
        preUnifyState.carrier.index.current
        preUnifyState.carrier.index.runtime :=
    preUnifyState.carrier.agreement.core.control.ready.2.2.2.headPayload.data
  have canonicalQueryExact :
      TreeSubstitution.apply
          (preUnifyState.carrier.index.canonical ++
            Substitution.denote preUnifyState.carrier.index.referenceBase)
          (Term.denote queryTerm) =
        .variable (.generated 0) := by
    rw [← bodyData.denoteCurrent, ← Substitution.denote_applyTerm, preCurrent]
    rfl
  obtain ⟨representativeIdentity, representativeQueryExact⟩ :=
    PLeaTTa.PrologMguVariantRenaming.TreeSubstitutionVariants.apply_variable_exists_of_first
      preUnifyState.cumulative.variants (Term.denote queryTerm)
        canonicalQueryExact
  have runtimeLeftAgreement :
      PLeaTTa.PrologPrefilterBridge.CanonicalRuntimeAgrees
        preUnifyState.carrier.index.alpha
        (TreeSubstitution.apply
          (preUnifyState.representative ++
            Substitution.denote preUnifyState.carrier.index.referenceBase)
          (Term.denote queryTerm))
        (PLeaTTa.subst preUnifyState.carrier.index.runtime executableLeft) :=
    canonicalRuntimeAgrees_apply_on
      (PLeaTTa.PrologPrefilterBridge.AlphaTermAgrees.canonicalRuntimeAgrees
        leftAgreement)
      selected.topExact.oldValuation leftSupported
  rw [representativeQueryExact] at runtimeLeftAgreement
  generalize runtimeLeftExact :
      PLeaTTa.subst preUnifyState.carrier.index.runtime executableLeft =
        runtimeLeft at runtimeLeftAgreement
  cases runtimeLeftAgreement with
  | @«variable» _ runtimeName runtimeLink =>
      have runtimeRightExact :
          PLeaTTa.subst preUnifyState.carrier.index.runtime executableRight =
            .gnd (.int 7) := by
        cases rightAgreement
        simp
      have exactRuntimeBind :=
        PLeaTTa.PrologMguDirectSimulation.CanonicalRuntimeAgrees.unifyTopExact_bindLeft
          bodyData.alphaShared runtimeLink
          (PLeaTTa.PrologPrefilterBridge.CanonicalRuntimeAgrees.integer
            (alpha := preUnifyState.carrier.index.alpha) 7) (by rfl)
      have generatedExact :
          generated = [(runtimeName, .gnd (.int 7))] := by
        have actual := selected.topExact.generatedExact
        rw [runtimeLeftExact, runtimeRightExact, exactRuntimeBind.1] at actual
        exact (Option.some.inj actual).symm
      have sourceNonempty : sourceExtension ≠ [] := by
        intro sourceNil
        have shape := selected.topExact.sourceConcreteResultShape
        rw [sourceNil, preCurrent] at shape
        simp [querySevenResult, pSourceExtension, TreeSubstitution.reify,
          Tree.reify] at shape
      have executableNonempty : executableExtension ≠ [] := by
        intro executableNil
        have value := selected.topExact.generatedValuation runtimeLink
        rw [executableNil, generatedExact] at value
        have runtimeSingleton :
            PLeaTTa.subst [(runtimeName, .gnd (.int 7))]
                (.var runtimeName) =
              .gnd (.int 7) := by
          exact
            PLeaTTa.subst_var_of_lookup_closed
              [(runtimeName, .gnd (.int 7))] runtimeName (.gnd (.int 7))
              (by simp [Metta.Subst.lookup]) (by simp [Metta.Atom.vars])
        have impossible :
            PLeaTTa.PrologPrefilterBridge.CanonicalRuntimeAgrees
              preUnifyState.carrier.index.alpha
              (.variable representativeIdentity) (.gnd (.int 7)) := by
          simpa only [TreeSubstitution.apply, runtimeSingleton] using value
        cases impossible
      have generatedNonempty : generated ≠ [] := by
        rw [generatedExact]
        simp
      have representativeChanged :
          afterState.representative ≠ preUnifyState.representative :=
        facts.representative_ne_of_executableExtension_ne_nil
          executableNonempty
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
            (.active preUnifyState) (.active afterState) :=
        .unify facts
      let run :
          CertifiedPrefix prog gt [.administrative 2, .unify]
            (.active beforeState) (.active afterState) :=
        .cons administrative (.cons unified (.nil (.active afterState)))
      refine
        ⟨.active beforeState, .active preUnifyState, .active afterState,
          sourceExtension, executableExtension, generated, run,
          ?_, ?_, ?_, sourceNonempty, executableNonempty,
          generatedNonempty, ?_, ?_, ?_⟩
      · rfl
      · simpa [run, TransitionSchedule.sourceCost,
          TransitionSchedule.sourceEvents, TransitionKind.sourceCost,
          TransitionKind.sourceEvents] using run.sourceSteps
      · simpa [run, TransitionSchedule.fineCost,
          TransitionKind.fineCost] using run.fineSteps
      · intro unchanged
        exact representativeChanged unchanged.symm
      · simpa [ProductPhaseState.cellIdentities] using
          facts.payloadCellsExact.symm
      · rfl

/-- The non-reflexive equality successor remains ready for the literal
`q(7)` activation.

This theorem exercises the general support-free materialization transport;
groundness is used only afterwards to expose the exact runtime value.  The
recomputed source branch keeps raw `generated 0 = generated 1` syntax,
normalizes it under the new binding to `7 = generated 1`, and selects the
ordered right-variable MGU.  Primitive unification allocates neither source
fresh names nor executable names, so alpha, session, and counter remain
literal identities across the edge. -/
theorem query_unify_seven_reaches_materialized_ground_q
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ preUnify after : RepresentativeActivePayloadState,
      ∃ bodyRest : List PeTTaSpec.PrologCore.Goal,
        ∃ bodyExecutableTail : List PLeaTTa.Goal,
          ∃ sourceExtension executableExtension : TreeSubstitution,
            ∃ generated installed : Metta.Subst,
              RepresentativeUnifySuccessorFacts prog gt preUnify after
                  queryTerm (.integer 7) querySevenResult bodyRest
                  bodyExecutableTail sourceExtension executableExtension
                  generated installed ∧
                executableExtension ≠ [] ∧
                ∃ head : NestedCallHead after.carrier,
                  MaterializedNestedCallReady after head ∧
                    head.predicate = "q" ∧
                    head.referencePayload =
                      [(.variable (.generated 0) : Term)] ∧
                    head.referenceRest = [] ∧
                    head.arguments = [] ∧
                    head.executableRest = [] ∧
                    (openedFor after.carrier.index.session head.predicate
                        head.referencePayload after.carrier.index.current).cursor.remaining =
                      [qSevenPreparedBranch] ∧
                    preUnify.carrier.index.current = pSourceExtension ∧
                    after.carrier.index.current = querySevenResult ∧
                    PLeaTTa.subst after.carrier.index.runtime head.result =
                      .gnd (.int 7) ∧
                    after.carrier.index.alpha = preUnify.carrier.index.alpha ∧
                    after.carrier.index.session =
                      preUnify.carrier.index.session ∧
                    after.carrier.index.openConf.persistent.counter =
                      preUnify.carrier.index.openConf.persistent.counter := by
  obtain
    ⟨middleState, middleHead, middleReady, qPredicate, qPayload,
      qReferenceRest, qArguments, _qResult, qExecutableRest, qExecutableTail,
      middleCurrent, middleSupport, queryReading, querySupported, middleQterm,
      middleOpenQterm, _middleCallerReferences, _middleCallerExecutables,
      _middleOuter, _middleBaseAlts, _middleFrames, middleDatabase, middleWorld,
      _middleOpenedSingleton,
      middleNextFresh, _middleCounter, _rootSourceSteps, _rootFineSteps,
      _runtimeQueryExact, _runtimeResultFixed⟩ :=
    qMaterializedReadyAfterP (prog := prog) (gt := gt)
  have integerReading :
      AlphaTermAgrees middleState.carrier.index.alpha (.integer 7)
        (.gnd (.int 7)) :=
    AlphaTermAgrees.integer 7
  let preUnifyState :=
    beforeUnify middleState queryTerm (.integer 7) queryAtom
      (.gnd (.int 7)) queryReading integerReading
  have preCurrent :
      preUnifyState.carrier.index.current = pSourceExtension := by
    simpa [preUnifyState, beforeUnify, ActivePayloadState.ofAgreement] using
      middleCurrent
  have preSupport :
      preUnifyState.carrier.index.support = rootAlpha := by
    simpa [preUnifyState, beforeUnify, ActivePayloadState.ofAgreement] using
      middleSupport
  have leftSupported :
      AlphaTreeSupported preUnifyState.carrier.index.alpha
        preUnifyState.carrier.index.support (Term.denote queryTerm) := by
    simpa [preUnifyState, beforeUnify, ActivePayloadState.ofAgreement] using
      querySupported
  have rightSupported :
      AlphaTreeSupported preUnifyState.carrier.index.alpha
        preUnifyState.carrier.index.support (Term.denote (.integer 7)) := by
    simp [AlphaTreeSupported, Term.denote,
      PrologMguOpenAgreement.TreeVariablesSatisfy,
      PrologMguOpenAgreement.TreesVariablesSatisfy]
  have continuationLive :
      ReadyUnifyContinuationLive preUnifyState.carrier.index.support
        preUnifyState.carrier.index.openConf := by
    intro executableHead rest runtime _current identity name linked
    rw [preSupport] at linked
    have pairExact : (identity, name) = (queryIdentity, "z") := by
      simpa [rootAlpha] using List.mem_singleton.mp linked
    have nameExact : name = "z" := congrArg Prod.snd pairExact
    have preOpenQterm :
        preUnifyState.carrier.index.openConf.control.qterm = queryAtom := by
      simpa [preUnifyState, beforeUnify, unifyPredecessorOpenConf,
        ActivePayloadState.ofAgreement] using middleOpenQterm
    rw [preOpenQterm, nameExact]
    exact PLeaTTa.isTrimRoot_qterm_mem rest queryAtom "z" (by
      simp [queryAtom, Metta.Atom.vars])
  obtain
    ⟨bodyExecutableTail, sourceExtension, executableExtension, generated,
      installed, afterState, facts⟩ :=
    RepresentativeActivePayloadState.exists_afterUnifySuccessLive
      preUnifyState (prog := prog) (gt := gt)
      (bodyRest := middleState.carrier.index.bodyReferences) rfl
      leftSupported rightSupported continuationLive (by
        simpa [preCurrent] using querySeven_resolves)
  obtain
    ⟨spelling, executableLeft, executableRight, _leftAgreement,
      _rightAgreement, selectedHead, selected⟩ :=
    facts.selectedExecution
  have predecessorHead :
      preUnifyState.carrier.index.openConf.control.cur =
        some
          (.eq queryAtom (.gnd (.int 7)) ::
              RepresentativeActivePayloadState.unifyExecutableTail
                preUnifyState middleState.carrier.index.bodyExecutables,
            preUnifyState.carrier.index.runtime) := by
    rfl
  have tailsEqual :
      RepresentativeActivePayloadState.unifyExecutableTail preUnifyState
          middleState.carrier.index.bodyExecutables =
        RepresentativeActivePayloadState.unifyExecutableTail preUnifyState
          bodyExecutableTail := by
    rw [predecessorHead] at selectedHead
    injection selectedHead with pairEqual
    exact (List.cons.inj (Prod.mk.inj pairEqual).1).2
  have bodyExecutableTailExact :
      bodyExecutableTail = middleState.carrier.index.bodyExecutables := by
    unfold RepresentativeActivePayloadState.unifyExecutableTail at tailsEqual
    exact (List.append_cancel_right tailsEqual).symm
  have bodyExecutableHead :
      bodyExecutableTail =
        .call "q" [] middleHead.result :: [] := by
    rw [bodyExecutableTailExact, middleHead.executableHead, qPredicate,
      qArguments, qExecutableRest]
  have bodyCallMember :
      PLeaTTa.Goal.call "q" [] middleHead.result ∈ bodyExecutableTail := by
    rw [bodyExecutableHead]
    simp
  have preMaterialized :
      PrologRecursiveCallPayloadBridge.MaterializedCallAgreesWith
        preUnifyState.carrier.index.alpha preUnifyState.carrier.index.current
        [(.variable (.generated 0) : Term)] []
        (PLeaTTa.subst preUnifyState.carrier.index.runtime middleHead.result)
        preUnifyState.representative
        preUnifyState.carrier.index.referenceBase := by
    simpa [preUnifyState, beforeUnify, ActivePayloadState.ofAgreement,
      qPayload, qArguments] using middleReady.materialized
  have sourcePayloadUnresolved :
      TreeSubstitution.apply
          (Substitution.denote preUnifyState.carrier.index.current)
          (Term.denote (.variable (.generated 0))) =
        .variable (.generated 0) := by
    rw [preCurrent]
    rfl
  obtain ⟨representativePayloadIdentity, representativePayloadExact⟩ :=
    PLeaTTa.PrologMguVariantRenaming.TreeSubstitutionVariants.apply_variable_exists_of_first
      preMaterialized.variants
      (Term.denote (.variable (.generated 0))) sourcePayloadUnresolved
  have postMaterialized :
      PrologRecursiveCallPayloadBridge.MaterializedCallAgreesWith
        afterState.carrier.index.alpha afterState.carrier.index.current
        [(.variable (.generated 0) : Term)] []
        (PLeaTTa.subst afterState.carrier.index.runtime middleHead.result)
        afterState.representative afterState.carrier.index.referenceBase :=
    facts.materializedCallAgreesWith preMaterialized bodyCallMember
  let afterHead : NestedCallHead afterState.carrier :=
    { predicate := "q"
      referencePayload := [(.variable (.generated 0) : Term)]
      referenceRest := []
      arguments := []
      result := middleHead.result
      executableRest := []
      referenceHead := by
        rw [facts.afterIndexExact]
        change
          middleState.carrier.index.bodyReferences =
            .call "q" [(.variable (.generated 0) : Term)] :: []
        simpa [qPredicate, qPayload, qReferenceRest] using
          middleHead.referenceHead
      executableHead := by
        rw [facts.afterIndexExact]
        exact bodyExecutableHead }
  have afterCurrent :
      afterState.carrier.index.current = querySevenResult := by
    rw [facts.afterIndexExact]
    rfl
  have afterAlpha :
      afterState.carrier.index.alpha = preUnifyState.carrier.index.alpha := by
    rw [facts.afterIndexExact]
    rfl
  have afterSupport :
      afterState.carrier.index.support = rootAlpha := by
    rw [facts.afterIndexExact]
    exact preSupport
  have afterSession :
      afterState.carrier.index.session = preUnifyState.carrier.index.session := by
    rw [facts.afterIndexExact]
    rfl
  have afterDatabase :
      afterState.carrier.index.session.resolver.database = referenceDatabase := by
    rw [afterSession]
    simpa [preUnifyState, beforeUnify, ActivePayloadState.ofAgreement] using
      middleDatabase
  have afterNextFresh :
      afterState.carrier.index.session.resolver.nextFresh = 1 := by
    rw [afterSession]
    simpa [preUnifyState, beforeUnify, ActivePayloadState.ofAgreement] using
      middleNextFresh
  have afterWorld :
      afterState.carrier.index.openConf.persistent.world = executableWorld := by
    rw [facts.afterIndexExact]
    simpa [RepresentativeActivePayloadState.unifyIndex,
      RepresentativeActivePayloadState.unifyOpenConf, preUnifyState,
      beforeUnify, unifyPredecessorOpenConf,
      ActivePayloadState.ofAgreement] using middleWorld
  have afterQterm : afterState.carrier.index.qterm = queryAtom := by
    rw [facts.afterIndexExact]
    change preUnifyState.carrier.index.qterm = queryAtom
    simpa [preUnifyState, beforeUnify, ActivePayloadState.ofAgreement] using
      middleQterm
  have afterCounter :
      afterState.carrier.index.openConf.persistent.counter =
        preUnifyState.carrier.index.openConf.persistent.counter := by
    rw [facts.afterIndexExact]
    rfl
  have openedSingleton :
      (openedFor afterState.carrier.index.session "q"
        [(.variable (.generated 0) : Term)]
        afterState.carrier.index.current).cursor.remaining =
          [qSevenPreparedBranch] := by
    change
      (prepareCall afterState.carrier.index.session.resolver
        (requestFor "q" [(.variable (.generated 0) : Term)]
          afterState.carrier.index.current)).1.remaining =
        [qSevenPreparedBranch]
    simp only [prepareCall, requestFor]
    rw [afterDatabase, afterNextFresh, afterCurrent]
    change
      (reserveVisible referenceDatabase.generation
        [(.variable (.generated 0) : Term)] querySevenResult 1
        (referenceDatabase.visibleClausesAt referenceDatabase.generation
          "q" 1)).1 = [qSevenPreparedBranch]
    rw [qVisibleClauses]
    rfl
  have sourceGround :
      TreeSubstitution.apply
          (Substitution.denote afterState.carrier.index.current)
          (Term.denote (.variable (.generated 0))) =
        Term.denote (.integer 7) := by
    rw [← Substitution.denote_applyTerm, afterCurrent]
    rfl
  have sourceGrounded :
      PrologMguVariant.TreeGround
        (TreeSubstitution.apply
          (Substitution.denote afterState.carrier.index.current)
          (Term.denote (.variable (.generated 0)))) := by
    rw [sourceGround]
    change True
    trivial
  have representativeGround :
      TreeSubstitution.apply
          (afterState.representative ++
            Substitution.denote afterState.carrier.index.referenceBase)
          (Term.denote (.variable (.generated 0))) =
        Term.denote (.integer 7) := by
    have same := postMaterialized.variants.apply_eq_of_first_ground
      (Term.denote (.variable (.generated 0))) sourceGrounded
    exact same.symm.trans sourceGround
  have afterReferenceBase :
      afterState.carrier.index.referenceBase =
        preUnifyState.carrier.index.referenceBase := by
    rw [facts.afterIndexExact]
    rfl
  have representativeGroundAtBase :
      TreeSubstitution.apply
          (afterState.representative ++
            Substitution.denote preUnifyState.carrier.index.referenceBase)
          (Term.denote (.variable (.generated 0))) =
        Term.denote (.integer 7) := by
    simpa [afterReferenceBase] using representativeGround
  have representativeValueChanged :
      TreeSubstitution.apply
          (afterState.representative ++
            Substitution.denote preUnifyState.carrier.index.referenceBase)
          (Term.denote (.variable (.generated 0))) ≠
        TreeSubstitution.apply
          (preUnifyState.representative ++
            Substitution.denote preUnifyState.carrier.index.referenceBase)
          (Term.denote (.variable (.generated 0))) := by
    rw [representativeGroundAtBase, representativePayloadExact]
    intro impossible
    cases impossible
  have executableNonempty : executableExtension ≠ [] :=
    facts.executableExtension_ne_nil_of_apply_ne representativeValueChanged
  have runtimeResultExact :
      PLeaTTa.subst afterState.carrier.index.runtime middleHead.result =
        .gnd (.int 7) := by
    have arguments := postMaterialized.arguments
    change List.Forall₂
      (fun term atom =>
        PrologPrefilterBridge.CanonicalRuntimeAgrees
          afterState.carrier.index.alpha
          (TreeSubstitution.apply
            (afterState.representative ++
              Substitution.denote afterState.carrier.index.referenceBase)
            (Term.denote term)) atom)
      [(.variable (.generated 0) : Term)]
      [PLeaTTa.subst afterState.carrier.index.runtime middleHead.result]
      at arguments
    cases arguments with
    | cons head tail =>
        rw [representativeGround] at head
        exact
          _root_.PLeaTTa.PrologPrefilterBridge.CanonicalRuntimeAgrees.integer_atom
            head
  have preBelow :
      ConfBelowResolutionCounter preUnifyState.carrier.index.openConf.toConf := by
    have middleBelow := middleReady.toNestedCallOperationalReady.below
    have middleCur :
        middleState.carrier.index.openConf.toConf.cur =
          some
            (middleState.carrier.index.bodyExecutables ++
                (middleState.carrier.index.callerExecutables ++
                  PrologControlSegmentSpineBridge.flattenExecutables
                    middleState.carrier.index.outer),
              middleState.carrier.index.runtime) := by
      exact middleState.carrier.agreement.core.control.ready.2.1
    have queryBelow :
        resolutionSeedHighWaterNames queryAtom.vars ≤
          middleState.carrier.index.openConf.toConf.counter := by
      have raw := middleBelow.qterm
      change
        resolutionSeedHighWaterNames
            middleState.carrier.index.openConf.control.qterm.vars ≤
          middleState.carrier.index.openConf.persistent.counter at raw
      rw [middleOpenQterm] at raw
      exact raw
    have integerBelow :
        resolutionSeedHighWaterNames (Metta.Atom.gnd (.int 7)).vars ≤
          middleState.carrier.index.openConf.toConf.counter := by
      simp [Metta.Atom.vars, resolutionSeedHighWaterNames]
    have inserted := ConfBelowResolutionCounter.prependEq middleBelow
      (middleState.carrier.index.bodyExecutables ++
        (middleState.carrier.index.callerExecutables ++
          PrologControlSegmentSpineBridge.flattenExecutables
            middleState.carrier.index.outer))
      middleState.carrier.index.runtime middleCur queryAtom (.gnd (.int 7))
      queryBelow integerBelow
    change
      ConfBelowResolutionCounter
        (unifyPredecessorOpenConf middleState queryAtom (.gnd (.int 7))).toConf
    change
      ConfBelowResolutionCounter
        { middleState.carrier.index.openConf.toConf with
          cur := some
            (.eq queryAtom (.gnd (.int 7)) ::
                (middleState.carrier.index.bodyExecutables ++
                  (middleState.carrier.index.callerExecutables ++
                    PrologControlSegmentSpineBridge.flattenExecutables
                      middleState.carrier.index.outer)),
              middleState.carrier.index.runtime) }
    exact inserted
  have sealedStep :
      PLeaTTa.Step prog gt preUnifyState.carrier.index.openConf.toConf
        (RepresentativeActivePayloadState.unifyOpenConf preUnifyState
          bodyExecutableTail installed).toConf := by
    exact executable_unify_sealed_step preUnifyState.carrier.index.openConf
      spelling executableLeft executableRight
      (RepresentativeActivePayloadState.unifyExecutableTail preUnifyState
        bodyExecutableTail)
      preUnifyState.carrier.index.runtime installed selectedHead
      selected.installedExact
  have afterBelow :
      ConfBelowResolutionCounter afterState.carrier.index.openConf.toConf := by
    have preserved := sealedStep.preserves_belowResolutionCounter preBelow
    rw [facts.afterIndexExact]
    exact preserved
  have exactFresh :
      afterState.carrier.index.freshFrontier =
        AlphaFreshFrontier afterState.carrier.index.alpha := by
    rw [facts.afterIndexExact]
    change
      preUnifyState.carrier.index.freshFrontier =
        AlphaFreshFrontier preUnifyState.carrier.index.alpha
    simpa [preUnifyState, beforeUnify, ActivePayloadState.ofAgreement] using
      middleReady.toNestedCallOperationalReady.exactFresh
  have operational : NestedCallOperationalReady afterState.carrier afterHead := by
    refine
      { exactFresh := exactFresh
        indexReady := ?_
        below := afterBelow
        candidateSupported := ?_
        sourceNonempty := ?_
        scanNonempty := ?_
        selected := ?_
        notThrow := ?_
        notDatabase := ?_ }
    · rw [afterWorld]
      rfl
    · change
        SupportedCandidateBank "q"
          (afterState.carrier.index.session.resolver.database.visibleClausesAt
            afterState.carrier.index.session.resolver.database.generation
            "q" 1)
          (afterState.carrier.index.openConf.persistent.world.resolutionCandidates
            "q" 0)
      simpa [afterDatabase, afterWorld] using qCandidateBank
    · change
        afterState.carrier.index.session.resolver.database.visibleClausesAt
          afterState.carrier.index.session.resolver.database.generation
          "q" 1 ≠ []
      rw [afterDatabase, qVisibleClauses]
      simp
    · unfold NestedCallHead.scan
      have executableTailNil : afterHead.executableTail = [] := by
        unfold NestedCallHead.executableTail at qExecutableTail ⊢
        simp only [afterHead, List.nil_append]
        rw [facts.afterIndexExact]
        change
          PrologControlSegmentSpineBridge.flattenExecutables
              ({ barrier := middleState.carrier.index.callerBarrier
                 references := middleState.carrier.index.callerReferences
                 executables := middleState.carrier.index.callerExecutables } ::
                middleState.carrier.index.outer) = []
        simpa [qExecutableRest] using qExecutableTail
      rw [executableTailNil]
      simp only [afterHead, List.length_nil, List.map_nil]
      change
        (resolveAlts
          (afterState.carrier.index.openConf.persistent.world.resolutionCandidates
            "q" 0)
          [] [] middleHead.result [] afterState.carrier.index.runtime
          afterState.carrier.index.openConf.toConf.qterm
          (barrierDepth afterState.carrier.index.openConf.toConf + 1)
          afterState.carrier.index.openConf.toConf.counter).1 ≠ []
      rw [afterWorld, qResolutionCandidates]
      have resultMatch :
          PLeaTTa.prologMatchCompat
              (PLeaTTa.subst afterState.carrier.index.runtime middleHead.result)
              (.var "x") = true := by
        rw [runtimeResultExact]
        rfl
      simp [resolveAlts, qExecutableClause, resultMatch,
        PLeaTTa.prologMatchCompatList]
    · intro count finish branch clause branchTail clauseTail altTail copied
        pulls frontier
      have finishNonempty : finish.remaining ≠ [] := by
        rw [frontier.finishRemaining]
        simp
      have pathExact :=
        RejectedPullsN.eq_zero_of_singleton_of_finish_nonempty
          openedSingleton pulls finishNonempty
      have branchExact : branch = qSevenPreparedBranch := by
        have remaining := frontier.finishRemaining
        rw [pathExact.2, openedSingleton] at remaining
        exact (List.cons.inj remaining).1.symm
      refine ⟨qSevenSourceResult, ?_, ?_⟩
      · simpa [branchExact] using qSevenPreparedBranch_resolves
      · rw [afterSupport, afterQterm]
        intro identity name member
        simp only [rootAlpha, List.mem_singleton] at member
        have identityExact : identity = queryIdentity := congrArg Prod.fst member
        have nameExact : name = "z" := congrArg Prod.snd member
        subst identity
        subst name
        exact PLeaTTa.isTrimRoot_qterm_mem _ queryAtom "z"
          (by simp [queryAtom, Metta.Atom.vars])
    · simp [afterHead, BuiltinThrowCall]
    · rfl
  have ready : MaterializedNestedCallReady afterState afterHead :=
    { toNestedCallOperationalReady := operational
      materialized := by
        simpa [afterHead] using postMaterialized }
  refine
    ⟨preUnifyState, afterState, middleState.carrier.index.bodyReferences,
      bodyExecutableTail, sourceExtension, executableExtension, generated,
      installed, facts, executableNonempty, afterHead, ready, rfl, rfl, rfl,
      rfl, rfl, ?_, preCurrent, afterCurrent, ?_, afterAlpha, afterSession,
      afterCounter⟩
  · simpa [afterHead] using openedSingleton
  · simpa [afterHead] using runtimeResultExact

/-- The non-reflexive `Z = 7` edge and the resulting materialized `q(7)`
activation form one exact heterogeneous prefix.

The predecessor, unification successor, and local-call successor are literal
dependent states from one producer chain.  Thus the source substitution
really changes from `pSourceExtension` to `querySevenResult`, the following
singleton clause activation deterministically reaches `qSevenSourceResult`,
the primitive equality preserves payload-cell identity, and the local call
pushes exactly one new payload cell. -/
theorem truth_then_query_unify_seven_then_q_call_exact_literal_states
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    let request :=
      requestFor "q" [(.variable (.generated 0) : Term)] querySevenResult
    ∃ before preUnify middle after : RepresentativeActivePayloadState,
      ∃ run : CertifiedPrefix prog gt
          [.administrative 2, .unify, .localCall 0 request]
          (.active before) (.active after),
        run.states =
            [.active before, .active preUnify, .active middle, .active after] ∧
          (CertifiedPrefix.split [.administrative 2, .unify]
              [.localCall 0 request] run).1 = .active middle ∧
          StepsN 5 before.carrier.sourceState [.opened request]
            after.carrier.sourceState ∧
          DemandDrivenCallStep.StepsN prog gt 4 before.carrier.fineState
            after.carrier.fineState ∧
          preUnify.carrier.index.current = pSourceExtension ∧
          middle.carrier.index.current = querySevenResult ∧
          after.carrier.index.current = qSevenSourceResult ∧
          preUnify.carrier.index.current ≠ middle.carrier.index.current ∧
          (∃ extension : TreeSubstitution,
            middle.representative = extension ++ preUnify.representative) ∧
          middle.representative ≠ preUnify.representative ∧
          preUnify.carrier.cellIdentities = middle.carrier.cellIdentities ∧
          ∃ cell, after.carrier.cellIdentities =
            cell :: middle.carrier.cellIdentities := by
  dsimp only
  obtain
    ⟨preUnifyState, middleState, _bodyRest, _bodyExecutableTail,
      _sourceExtension, executableExtension, _generated, _installed,
      unifyFacts, executableNonempty, head, ready, qPredicate, qPayload,
      _qReferenceRest,
      _qArguments, _qExecutableRest, openedSingleton, preCurrent,
      middleCurrent, _runtimeResult, _alphaExact, _sessionExact,
      _counterExact⟩ :=
    query_unify_seven_reaches_materialized_ground_q
      (prog := prog) (gt := gt)
  obtain
    ⟨count, skippedBranches, skippedClauses, finish, branch, clause,
      branchTail, clauseTail, altTail, copied, installed, afterState,
      callFacts, segmentPackage⟩ :=
    unifyFacts.thenMaterializedLocalCallDetailed ready
  have finishNonempty : finish.remaining ≠ [] := by
    rw [callFacts.frontier.finishRemaining]
    simp
  have pathExact :=
    RejectedPullsN.eq_zero_of_singleton_of_finish_nonempty
      openedSingleton callFacts.pulls finishNonempty
  have countZero : count = 0 := pathExact.1
  have branchExact : branch = qSevenPreparedBranch := by
    have remaining := callFacts.frontier.finishRemaining
    rw [pathExact.2, openedSingleton] at remaining
    exact (List.cons.inj remaining).1.symm
  have afterCurrent :
      afterState.carrier.index.current = qSevenSourceResult := by
    have exactResolution : HeadResolution branch qSevenSourceResult := by
      simpa [branchExact] using qSevenPreparedBranch_resolves
    exact HeadResolution.deterministic callFacts.resolution exactResolution
  have currentChanged :
      preUnifyState.carrier.index.current ≠
        middleState.carrier.index.current := by
    rw [preCurrent, middleCurrent]
    intro same
    have lengths := congrArg List.length same
    simp [pSourceExtension, querySevenResult, TreeSubstitution.reify] at lengths
  subst count
  let request :=
    requestFor "q" [(.variable (.generated 0) : Term)] querySevenResult
  have requestExact :
      requestFor head.predicate head.referencePayload
          middleState.carrier.index.current = request := by
    simp [request, qPredicate, qPayload, middleCurrent]
  rw [requestExact] at segmentPackage
  have segmentPackageExact :
      ∃ segmentExact :
          CertifiedPrefix prog gt [.unify, .localCall 0 request]
            (.active preUnifyState) (.active afterState),
        segmentExact.states =
            [.active preUnifyState, .active middleState, .active afterState] ∧
          (CertifiedPrefix.split [.unify] [.localCall 0 request]
            segmentExact).1 = .active middleState := by
    exact segmentPackage
  obtain
    ⟨segmentExact, segmentStatesExact, segmentMiddleExact⟩ :=
    segmentPackageExact
  let beforeState := beforeTruth (beforeTruth preUnifyState)
  have administrative :
      CertifiedTransition prog gt (.administrative 2)
        (.active beforeState) (.active preUnifyState) := by
    have raw :=
      CertifiedTransition.administrative (prog := prog) (gt := gt)
        beforeState (beforeTruthTwiceSteps preUnifyState)
    simpa [beforeState, afterAdministrative_beforeTruth_twice] using raw
  let run :
      CertifiedPrefix prog gt
        [.administrative 2, .unify, .localCall 0 request]
        (.active beforeState) (.active afterState) :=
    .cons administrative segmentExact
  refine
    ⟨beforeState, preUnifyState, middleState, afterState, run, ?_, ?_, ?_,
      ?_, preCurrent, middleCurrent, afterCurrent, currentChanged, ?_, ?_, ?_,
      ?_⟩
  · simpa [run, CertifiedPrefix.states] using
      congrArg (List.cons (.active beforeState)) segmentStatesExact
  · simpa [run, CertifiedPrefix.split] using segmentMiddleExact
  · simpa [run, request, TransitionSchedule.sourceCost,
      TransitionSchedule.sourceEvents, TransitionKind.sourceCost,
      TransitionKind.sourceEvents, ProductPhaseState.sourceState] using
      run.sourceSteps
  · simpa [run, TransitionSchedule.fineCost, TransitionKind.fineCost,
      ProductPhaseState.fineState] using run.fineSteps
  · exact ⟨executableExtension, unifyFacts.representativeExact⟩
  · exact
      unifyFacts.representative_ne_of_executableExtension_ne_nil
        executableNonempty
  · simpa using unifyFacts.payloadCellsExact.symm
  · simpa [ProductPhaseState.cellIdentities] using
      callFacts.certificate.payloadCells

/-- The arbitrary-prefix induction is inhabited by the real non-reflexive
three-edge path.  It retains the four literal states and the unification
edge's exact cell-identity preservation while folding every global invariant.

The final one-cell equation is deliberately only a normalization of the
derived schedule-level payload relation: the preceding literal-middle
equations, not that endpoint corollary alone, carry cell identity. -/
theorem truth_then_query_unify_seven_recursive_prefix_invariants
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    let request :=
      requestFor "q" [(.variable (.generated 0) : Term)] querySevenResult
    ∃ before preUnify middle after : ProductPhaseState,
      ∃ run : CertifiedPrefix prog gt
          [.administrative 2, .unify, .localCall 0 request] before after,
        run.states = [before, preUnify, middle, after] ∧
          preUnify.cellIdentities = middle.cellIdentities ∧
          SessionHighWatersExtend before.session after.session ∧
          before.openConf.persistent.counter ≤
            after.openConf.persistent.counter ∧
          AlphaExtendsAbove before.alpha after.alpha
            before.session.resolver.nextFresh
            before.openConf.persistent.counter ∧
          (∃ extension : TreeSubstitution,
            after.representative = extension ++ before.representative) ∧
          TransitionSchedule.PayloadEvolution
            [.administrative 2, .unify, .localCall 0 request]
            before.cellIdentities after.cellIdentities ∧
          ∃ cell, after.cellIdentities = cell :: before.cellIdentities := by
  dsimp only
  obtain
    ⟨beforeState, preUnifyState, middleState, afterState, run, states,
      _middle, _source, _fine, _preCurrent, _middleCurrent, _afterCurrent,
      _currentChanged, _middleRepresentativeExtension,
      _middleRepresentativeChanged, unifyCells, _callCells⟩ :=
    truth_then_query_unify_seven_then_q_call_exact_literal_states
      (prog := prog) (gt := gt)
  have payload := run.payloadEvolution
  have endpointPush :
      ∃ cell,
        (ProductPhaseState.active afterState).cellIdentities =
          cell :: (ProductPhaseState.active beforeState).cellIdentities := by
    simpa [TransitionSchedule.PayloadEvolution,
      TransitionKind.PayloadEvolution] using payload
  exact
    ⟨.active beforeState, .active preUnifyState, .active middleState,
      .active afterState, run, states,
      by simpa [ProductPhaseState.cellIdentities] using unifyCells,
      run.sessionHighWaters, run.executableCounter_mono, run.alphaExtension,
      run.representativeExtension, payload, endpointPush⟩

/-- Two source-only administrative steps, one certified primitive equality,
and the reachable ground `q(7)` activation compose through three literal
dependent middle states.

The equality is a real source and fine step, yet its empty ordered MGU returns
to the exact representative-indexed predecessor state.  The following local
call therefore consumes that same representative rather than a freshly chosen
variant.  Exact costs (five source steps versus four fine steps), the sole
opened-call observation, representative preservation across equality, and the
one-cell local-call push are all exposed simultaneously.  The same concrete
prefix also consumes schedule-level root-closure preservation, so that
abstraction is exercised by a reached endpoint rather than only audited in
isolation. -/
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
          (∃ cell, after.cellIdentities = cell :: middle.cellIdentities) ∧
          after.RootClosed := by
  dsimp only
  obtain
    ⟨middleCarrier, head, rawReady, qPredicate, qPayload, _qReferenceRest,
      _qArguments, _qResult, _qExecutableRest, middleAlpha, _middleSupport,
      middleCurrent, middleRuntime, _middleQterm, _middleCallerReferences,
      _middleOuter, _middleResources, _middleActiveAlts, middleBaseAlts,
      _middleDatabase, _middleNextFresh, _middleWorld,
      _rootSourceSteps, _rootFineSteps, representativeWitness, only,
      openedSingleton⟩ :=
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
      .active afterState, run, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · simpa [run, request, TransitionSchedule.sourceCost,
      TransitionSchedule.sourceEvents, TransitionKind.sourceCost,
      TransitionKind.sourceEvents] using run.sourceSteps
  · simpa [run, TransitionSchedule.fineCost, TransitionKind.fineCost] using
      run.fineSteps
  · simp [preUnifyState, beforeReflexiveUnify, beforeUnify,
      ProductPhaseState.representative]
  · simpa [ProductPhaseState.cellIdentities] using
      unifyFacts.payloadCellsExact.symm
  · simpa [TransitionKind.PayloadEvolution,
      ProductPhaseState.cellIdentities] using nested.payloadEvolution
  · apply run.preserves_rootClosed
    simpa [ProductPhaseState.RootClosed, ProductPhaseState.baseAlts,
      beforeState, beforeTruth, preUnifyState, beforeReflexiveUnify,
      beforeUnify, ActivePayloadState.ofAgreement] using middleBaseAlts

end PLeaTTa.PrologHeterogeneousPrefixRegression
