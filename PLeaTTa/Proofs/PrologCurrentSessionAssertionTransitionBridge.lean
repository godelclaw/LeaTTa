-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologCurrentSessionAssertionTransitionBridge
Purpose: Lift one owned local database assertion through the complete active
  product/resource/payload context.
Trusted boundary: none
Main exports:
  SpinedActiveProductPayloadResourceRelatesAt.afterAssertion,
  RepresentativeAssertionReady,
  RepresentativeActivePayloadState.afterAssertion
-/
import PLeaTTa.Proofs.PrologCurrentSessionPayloadTransitionBridge
import PLeaTTa.Proofs.PrologDatabaseActionStepBridge
import PLeaTTa.Proofs.PrologNestedCallReadyBridge

namespace PLeaTTa.PrologCurrentSessionAssertionTransitionBridge

open Metta (Atom Subst GroundingTable)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.DatabaseActions
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologActivatedProductStepBridge
open PrologControlSegmentSpineBridge
open PrologCurrentSessionPayloadBridge
open PrologCurrentSessionPayloadTransitionBridge
open PrologDatabaseActionStepBridge
open PrologGoalAlpha
open PrologNestedCallChainBridge
open PrologNestedCallReadyBridge
open PrologOrdinaryStepBridge
open PrologProductResourceContextBridge
open PrologProductResourceTransitionBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
open PrologSourceProductContextBridge
open PrologStateBridge

/-!
The leaf database-action theorem intentionally sees one uniformly tagged
source continuation.  A live recursive activation does not have that shape:
the executable flattens the active body, its caller tail, and every older
tail, while the independent semantics retains their distinct cut scopes.

The theorem below performs the missing contextual lift.  It uses the
compiler-produced executable head as factual input, then derives its
operation and payload correspondence from the alpha relation.  The effect
step changes only the persistent database/world and executable counter;
every retained cursor, alternative, barrier, frame, and payload cell remains
owned at the same structural position.
-/

/-- One source/executable assertion transition through an arbitrary active
predicate stack.

The executable head shape is producer evidence, not inferred from source
syntax: the generic alpha relation also represents ordinary defined calls.
`normalizedWactHead` proves that once the actual head is a world action, its
operation and operands cannot be swapped or supplied independently.

The abstract post-frontier premise remains explicit because the executable
world action advances its global counter while the source database mutation
does not allocate a logical variable. -/
theorem SpinedActiveProductPayloadResourceRelatesAt.afterAssertion
    {prog : PLeaTTa.Prog} {gt : GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {session : Session}
    {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {operation : AssertionOperation}
    {payload result : Term}
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
      ActiveProductPayloadContext alpha support qterm opened finish branch
        branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context}
    {referenceClause : LocalClause}
    {executableOperation : String}
    {executablePayload executableResult : Atom}
    {bodyExecutableTail : List PLeaTTa.Goal}
    {functor : String} {executableClause : PLeaTTa.Clause}
    (agreement :
      SpinedActiveProductPayloadResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened session pending finish branch branchTail
        altTail bodyBarrier callerBarrier
        (.call operation.predicate [payload, result] :: bodyRest)
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
        (state.persistent.counter + 1)) :
    let sourceAfter :=
      session.withDatabase
        (operation.update session.resolver.database referenceClause)
    let executableTail :=
      bodyExecutableTail ++
        (callerExecutables ++ flattenExecutables outer)
    let executableAfter :=
      assertionSuccessor operation state executableResult executableTail
        runtime functor executableClause
    let nextSource :=
      ActiveProductContext.plug context
        (activeSourceProduct callerScope opened finish branch branchTail
          current (.unify result (.atom "true") :: bodyRest)
          callerReferences)
    executableOperation = operation.predicate ∧
      RawStep session source
        [.effect
          (operation.effect session.resolver.database referenceClause)]
        .none sourceAfter (.running nextSource) ∧
      DemandDrivenCallStep.Step prog gt (.ready state)
        (.ready executableAfter) ∧
      SourceDatabaseEffectErasure
        [.effect
          (operation.effect session.resolver.database referenceClause)]
        session sourceAfter state.persistent executableAfter.persistent ∧
      SpinedActiveProductPayloadResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened sourceAfter pending finish branch
        branchTail altTail bodyBarrier callerBarrier
        (.unify result (.atom "true") :: bodyRest)
        (PLeaTTa.Goal.eq executableResult trueA :: bodyExecutableTail)
        callerReferences callerExecutables outer current runtime qterm active
        resources callerScope outerScope context baseAlts nextSource
        executableAfter payloadContext := by
  dsimp only
  rcases agreement.core.control.ready with
    ⟨persistent, currentControl, queryTerm, spinePayload⟩
  have bodyPayload :
      TaskPayloadAgrees alpha support bodyBarrier canonical referenceBase
        current runtime
        (.call operation.predicate [payload, result] :: bodyRest)
        bodyExecutables :=
    spinePayload.headPayload
  rcases
      operation.normalizedWactHead bodyPayload.control bodyExecutableShape with
    ⟨operationExact, payloadAgreement, resultAgreement, bodyTailControl⟩
  subst executableOperation

  have executableHead :
      state.control.cur =
        some
          (PLeaTTa.Goal.wact operation.predicate [executablePayload]
              executableResult ::
            (bodyExecutableTail ++
              (callerExecutables ++ flattenExecutables outer)),
            runtime) := by
    simpa [flattenExecutables, ControlSegment.executableGoals,
      bodyExecutableShape, List.append_assoc] using currentControl

  have sourceLeaf :=
    assertionSourceStep (operation := operation) (scope := opened.scope)
      (session := session) (current := current) (payload := payload)
      (result := result) (references := bodyRest)
      (referenceClause := referenceClause) sourceDecoded
  have activeSourceStep :
      RawStep session
        (activeSourceProduct callerScope opened finish branch branchTail
          current
          (.call operation.predicate [payload, result] :: bodyRest)
          callerReferences)
        [.effect
          (operation.effect session.resolver.database referenceClause)]
        .none
        (session.withDatabase
          (operation.update session.resolver.database referenceClause))
        (.running
          (activeSourceProduct callerScope opened finish branch branchTail
            current (.unify result (.atom "true") :: bodyRest)
            callerReferences)) := by
    simpa using
      ActiveProductFrame.liftProgress
        (ActiveProductFrame.ofActiveProduct callerScope opened finish branch
          branchTail callerReferences)
        sourceLeaf (by simp [Trace.AnswerFree])
  have sourceStep :
      RawStep session source
        [.effect
          (operation.effect session.resolver.database referenceClause)]
        .none
        (session.withDatabase
          (operation.update session.resolver.database referenceClause))
        (.running
          (ActiveProductContext.plug context
            (activeSourceProduct callerScope opened finish branch branchTail
              current (.unify result (.atom "true") :: bodyRest)
              callerReferences))) := by
    rw [agreement.core.sourceShape]
    exact
      ActiveProductContext.liftProgress context activeSourceStep
        (by simp [Trace.AnswerFree])

  have executableStep :
      DemandDrivenCallStep.Step prog gt (.ready state)
        (.ready
          (assertionSuccessor operation state executableResult
            (bodyExecutableTail ++
              (callerExecutables ++ flattenExecutables outer))
            runtime functor executableClause)) :=
    assertionExecutableStep executableHead executableDecoded

  have persistentAfter :
      SessionRelatesPersistent freshFrontier
        (session.withDatabase
          (operation.update session.resolver.database referenceClause))
        (assertionSuccessor operation state executableResult
          (bodyExecutableTail ++
            (callerExecutables ++ flattenExecutables outer))
          runtime functor executableClause).persistent :=
    assertionPersistentAfter persistent clause noDescendants freshAfter

  have chronology :
      SessionHighWatersExtend session
        (session.withDatabase
          (operation.update session.resolver.database referenceClause)) :=
    SessionHighWatersExtend.withDatabase _ _ (by
      rw [operation.update_generation]
      exact Nat.le_succ _)

  have nextBodyControl :
      NormalizedAlphaGoalsAgree alpha bodyBarrier
        (.unify result (.atom "true") :: bodyRest)
        (PLeaTTa.Goal.eq executableResult trueA :: bodyExecutableTail) :=
    .cons (.unify resultAgreement .trueAtom) bodyTailControl
  have nextSpinePayload :
      TaskSpinePayloadAgrees alpha support canonical referenceBase current
        runtime
        ({ barrier := bodyBarrier
           references := .unify result (.atom "true") :: bodyRest
           executables :=
             PLeaTTa.Goal.eq executableResult trueA :: bodyExecutableTail } ::
         { barrier := callerBarrier
           references := callerReferences
           executables := callerExecutables } ::
         outer) :=
    ⟨spinePayload.data,
      .cons nextBodyControl spinePayload.control.tail⟩

  let executableAfter :=
    assertionSuccessor operation state executableResult
      (bodyExecutableTail ++
        (callerExecutables ++ flattenExecutables outer))
      runtime functor executableClause
  have nextReady :
      SpinedReadyTaskRelates freshFrontier alpha support canonical
        referenceBase
        (session.withDatabase
          (operation.update session.resolver.database referenceClause))
        current runtime qterm
        ({ barrier := bodyBarrier
           references := .unify result (.atom "true") :: bodyRest
           executables :=
             PLeaTTa.Goal.eq executableResult trueA :: bodyExecutableTail } ::
         { barrier := callerBarrier
           references := callerReferences
           executables := callerExecutables } ::
         outer)
        executableAfter := by
    refine ⟨persistentAfter, ?_, ?_, nextSpinePayload⟩
    · simp [executableAfter, flattenExecutables,
        ControlSegment.executableGoals]
    · change state.control.qterm = qterm
      exact queryTerm

  have nextControl :
      SpinedActiveProductRelatesAt freshFrontier alpha support canonical
        referenceBase opened
        (session.withDatabase
          (operation.update session.resolver.database referenceClause))
        pending finish branch branchTail altTail bodyBarrier callerBarrier
        (.unify result (.atom "true") :: bodyRest)
        (PLeaTTa.Goal.eq executableResult trueA :: bodyExecutableTail)
        callerReferences callerExecutables outer current runtime qterm
        executableAfter := by
    refine
      ⟨nextReady, agreement.core.control.sessionAdvanced.trans chronology,
        ?_, agreement.core.control.retainedAltsZero, ?_,
        agreement.core.control.bodyBarrierTag, ?_⟩
    · simpa [executableAfter] using agreement.core.control.retainedAlts
    · simpa [executableAfter] using agreement.core.control.retainedBarriers
    · simpa [executableAfter] using agreement.core.control.frames

  have nextResourceStack :
      ActiveProductResourceStackAgrees alpha qterm bodyBarrier callerBarrier
        pending (finish.advance branch branchTail)
        (callerExecutables ++ flattenExecutables outer) altTail active outer
        resources callerScope outerScope context baseAlts executableAfter := by
    rcases agreement.core.resourceStack with
      ⟨activeRest, activeQuery, activeBarrier, activeAlts,
        activeFinalCounter, activeOwnership, outerAlignment,
        suspendedOuterAlts, actualAlts⟩
    exact
      ⟨activeRest, activeQuery, activeBarrier, activeAlts,
        activeFinalCounter, activeOwnership, outerAlignment,
        suspendedOuterAlts, by simpa [executableAfter] using actualAlts⟩

  have nextCore :
      SpinedActiveProductResourceRelatesAt freshFrontier alpha support canonical
        referenceBase opened
        (session.withDatabase
          (operation.update session.resolver.database referenceClause))
        pending finish branch branchTail altTail bodyBarrier callerBarrier
        (.unify result (.atom "true") :: bodyRest)
        (PLeaTTa.Goal.eq executableResult trueA :: bodyExecutableTail)
        callerReferences callerExecutables outer current runtime qterm active
        resources callerScope outerScope context baseAlts
        (ActiveProductContext.plug context
          (activeSourceProduct callerScope opened finish branch branchTail
            current (.unify result (.atom "true") :: bodyRest)
            callerReferences))
        executableAfter :=
    ⟨nextControl, nextResourceStack, rfl⟩

  have nextEndpoints :
      endpointsBelow payloadContext
        (session.withDatabase
          (operation.update session.resolver.database
            referenceClause)).resolver.nextFresh
        executableAfter.persistent.counter := by
    apply endpointsBelow_mono payloadContext agreement.endpointsCurrent
    · simp [Session.withDatabase]
    · simp [executableAfter]

  have nextControlOrigins :
      LocalControlOriginSpineRelates baseAlts executableAfter.frames
        executableAfter.control.barriers payloadContext := by
    simpa [executableAfter] using agreement.controlOrigins

  have nextActivationOrigins :
      LocalActivationOriginSpineRelates
        (session.withDatabase
          (operation.update session.resolver.database referenceClause))
        payloadContext :=
    agreement.activationOrigins.advance payloadContext chronology

  have effectErasure :
      SourceDatabaseEffectErasure
        [.effect
          (operation.effect session.resolver.database referenceClause)]
        session
        (session.withDatabase
          (operation.update session.resolver.database referenceClause))
        state.persistent executableAfter.persistent :=
    .intro (operation.effect session.resolver.database referenceClause) rfl
      (operation.mutation session.resolver.database referenceClause)
      persistent.database persistentAfter.database

  exact
    ⟨rfl, sourceStep, executableStep, effectErasure,
      ⟨nextCore, nextEndpoints, agreement.activationOrdered,
        nextActivationOrigins, nextControlOrigins⟩⟩

/-! ## Closed representative producer -/

/-- All source/executable evidence which identifies one successful owned
assertion at the literal head of an active representative carrier.

The executable operation is not a separately supplied string: its head is
required to use `operation.predicate`.  Consequently a downstream transition
label can be computed from this package and cannot relabel an `asserta` step
as `assertz`, change its clause, or attach an unrelated effect observation. -/
structure RepresentativeAssertionReady
    (gt : GroundingTable) (before : RepresentativeActivePayloadState) where
  operation : AssertionOperation
  payload : Term
  result : Term
  bodyRest : List PeTTaSpec.PrologCore.Goal
  executablePayload : Atom
  executableResult : Atom
  bodyExecutableTail : List PLeaTTa.Goal
  referenceClause : LocalClause
  functor : String
  executableClause : PLeaTTa.Clause
  referenceHead :
    before.carrier.index.bodyReferences =
      PeTTaSpec.PrologCore.Goal.call operation.predicate [payload, result] ::
        bodyRest
  executableHead :
    before.carrier.index.bodyExecutables =
      PLeaTTa.Goal.wact operation.predicate [executablePayload]
          executableResult ::
        bodyExecutableTail
  sourceDecoded :
    decodePredicateClause
        (before.carrier.index.current.applyTerm payload) =
      some referenceClause
  executableDecoded :
    PLeaTTa.predicateClause? gt
        (subst before.carrier.index.runtime executablePayload) =
      some (functor, executableClause)
  clause : LocalClauseAgrees referenceClause (functor, executableClause)
  noDescendants :
    before.carrier.index.openConf.persistent.world.specializationDescendants
        functor =
      []
  freshAfter :
    before.carrier.index.freshFrontier
      before.carrier.index.session.resolver.nextFresh
      (before.carrier.index.openConf.persistent.counter + 1)

namespace RepresentativeAssertionReady

/-- The unique typed source observation fixed by this producer package. -/
def effect {gt : GroundingTable} {before : RepresentativeActivePayloadState}
    (ready : RepresentativeAssertionReady gt before) : LocalDatabaseEffect :=
  ready.operation.effect before.carrier.index.session.resolver.database
    ready.referenceClause

/-- Source session after the non-backtrackable database mutation. -/
def sourceAfter
    {gt : GroundingTable} {before : RepresentativeActivePayloadState}
    (ready : RepresentativeAssertionReady gt before) : Session :=
  before.carrier.index.session.withDatabase
    (ready.operation.update
      before.carrier.index.session.resolver.database ready.referenceClause)

/-- Flattened executable continuation after consuming the world action. -/
def executableTail
    {gt : GroundingTable} {before : RepresentativeActivePayloadState}
    (ready : RepresentativeAssertionReady gt before) : List PLeaTTa.Goal :=
  ready.bodyExecutableTail ++
    (before.carrier.index.callerExecutables ++
      flattenExecutables before.carrier.index.outer)

/-- Fine executable state after the matching owned world action. -/
def executableAfter
    {gt : GroundingTable} {before : RepresentativeActivePayloadState}
    (ready : RepresentativeAssertionReady gt before) : OpenConf :=
  assertionSuccessor ready.operation before.carrier.index.openConf
    ready.executableResult ready.executableTail before.carrier.index.runtime
    ready.functor ready.executableClause

/-- Independent source focus after replacing the assertion by its `true`
result equality. -/
def sourceSearchAfter
    {gt : GroundingTable} {before : RepresentativeActivePayloadState}
    (ready : RepresentativeAssertionReady gt before) : Search :=
  ActiveProductContext.plug before.carrier.index.context
    (activeSourceProduct before.carrier.index.callerScope
      before.carrier.index.opened before.carrier.index.finish
      before.carrier.index.branch before.carrier.index.branchTail
      before.carrier.index.current
      (.unify ready.result (.atom "true") :: ready.bodyRest)
      before.carrier.index.callerReferences)

/-- Recover the exact contextual relation at the assertion head once.  The
producer's two head equalities are the only rewriting needed; downstream
projections reuse this certificate instead of rebuilding the same dependent
spine proof independently. -/
theorem activeAgreement
    {gt : GroundingTable} {before : RepresentativeActivePayloadState}
    (ready : RepresentativeAssertionReady gt before) :
    SpinedActiveProductPayloadResourceRelatesAt
      before.carrier.index.freshFrontier before.carrier.index.alpha
      before.carrier.index.support before.carrier.index.canonical
      before.carrier.index.referenceBase before.carrier.index.opened
      before.carrier.index.session before.carrier.index.pending
      before.carrier.index.finish before.carrier.index.branch
      before.carrier.index.branchTail before.carrier.index.altTail
      before.carrier.index.bodyBarrier before.carrier.index.callerBarrier
      (.call ready.operation.predicate [ready.payload, ready.result] ::
        ready.bodyRest)
      (PLeaTTa.Goal.wact ready.operation.predicate
          [ready.executablePayload] ready.executableResult ::
        ready.bodyExecutableTail)
      before.carrier.index.callerReferences
      before.carrier.index.callerExecutables before.carrier.index.outer
      before.carrier.index.current before.carrier.index.runtime
      before.carrier.index.qterm before.carrier.index.active
      before.carrier.index.resources before.carrier.index.callerScope
      before.carrier.index.outerScope before.carrier.index.context
      before.carrier.index.baseAlts before.carrier.index.source
      before.carrier.index.openConf before.carrier.payloadContext := by
  simpa only [ActivePayloadIndex.Relates, ready.referenceHead,
    ready.executableHead] using before.carrier.agreement

/-- Apply the contextual assertion theorem exactly once.  Its dependent
conjunction is retained so the deterministic successor and all exact
projections consume the same proof object. -/
def produced
    (prog : PLeaTTa.Prog) {gt : GroundingTable}
    {before : RepresentativeActivePayloadState}
    (ready : RepresentativeAssertionReady gt before) :=
  SpinedActiveProductPayloadResourceRelatesAt.afterAssertion
    (prog := prog) (gt := gt) ready.activeAgreement rfl ready.sourceDecoded
    ready.executableDecoded ready.clause ready.noDescendants ready.freshAfter

end RepresentativeAssertionReady

namespace RepresentativeActivePayloadState

/-- Deterministic representative successor of one successful local
assertion.  Every data field is fixed by `before` and `ready`; the existing
contextual producer supplies only the proof that those literal endpoints are
related.  The cumulative logical representative is preserved, while the
persistent database/world and executable counter advance. -/
def afterAssertion
    (prog : PLeaTTa.Prog) (gt : GroundingTable)
    (before : RepresentativeActivePayloadState)
    (ready : RepresentativeAssertionReady gt before) :
    RepresentativeActivePayloadState :=
  let produced := ready.produced prog
  let nextAgreement := produced.2.2.2.2
  let nextCarrier := ActivePayloadState.ofAgreement nextAgreement
  { carrier := nextCarrier
    representative := before.representative
    cumulative := by
      simpa [nextCarrier, ActivePayloadState.ofAgreement] using
        before.cumulative }

@[simp] theorem afterAssertion_sourceState
    (prog : PLeaTTa.Prog) (gt : GroundingTable)
    (before : RepresentativeActivePayloadState)
    (ready : RepresentativeAssertionReady gt before) :
    (afterAssertion prog gt before ready).carrier.sourceState =
      .running ready.sourceAfter ready.sourceSearchAfter := rfl

@[simp] theorem afterAssertion_source
    (prog : PLeaTTa.Prog) (gt : GroundingTable)
    (before : RepresentativeActivePayloadState)
    (ready : RepresentativeAssertionReady gt before) :
    (afterAssertion prog gt before ready).carrier.index.source =
      ready.sourceSearchAfter := rfl

@[simp] theorem afterAssertion_fineState
    (prog : PLeaTTa.Prog) (gt : GroundingTable)
    (before : RepresentativeActivePayloadState)
    (ready : RepresentativeAssertionReady gt before) :
    (afterAssertion prog gt before ready).carrier.fineState =
      .ready ready.executableAfter := rfl

@[simp] theorem afterAssertion_session
    (prog : PLeaTTa.Prog) (gt : GroundingTable)
    (before : RepresentativeActivePayloadState)
    (ready : RepresentativeAssertionReady gt before) :
    (afterAssertion prog gt before ready).carrier.index.session =
      ready.sourceAfter := rfl

@[simp] theorem afterAssertion_openConf
    (prog : PLeaTTa.Prog) (gt : GroundingTable)
    (before : RepresentativeActivePayloadState)
    (ready : RepresentativeAssertionReady gt before) :
    (afterAssertion prog gt before ready).carrier.index.openConf =
      ready.executableAfter := rfl

@[simp] theorem afterAssertion_alpha
    (prog : PLeaTTa.Prog) (gt : GroundingTable)
    (before : RepresentativeActivePayloadState)
    (ready : RepresentativeAssertionReady gt before) :
    (afterAssertion prog gt before ready).carrier.index.alpha =
      before.carrier.index.alpha := rfl

@[simp] theorem afterAssertion_representative
    (prog : PLeaTTa.Prog) (gt : GroundingTable)
    (before : RepresentativeActivePayloadState)
    (ready : RepresentativeAssertionReady gt before) :
    (afterAssertion prog gt before ready).representative =
      before.representative := rfl

@[simp] theorem afterAssertion_cellIdentities
    (prog : PLeaTTa.Prog) (gt : GroundingTable)
    (before : RepresentativeActivePayloadState)
    (ready : RepresentativeAssertionReady gt before) :
    (afterAssertion prog gt before ready).carrier.cellIdentities =
      before.carrier.cellIdentities := rfl

@[simp] theorem afterAssertion_baseAlts
    (prog : PLeaTTa.Prog) (gt : GroundingTable)
    (before : RepresentativeActivePayloadState)
    (ready : RepresentativeAssertionReady gt before) :
    (afterAssertion prog gt before ready).carrier.index.baseAlts =
      before.carrier.index.baseAlts := rfl

/-- The deterministic package retains the exact source step supplied by the
contextual assertion producer. -/
theorem afterAssertion_sourceStep
    (prog : PLeaTTa.Prog) (gt : GroundingTable)
    (before : RepresentativeActivePayloadState)
    (ready : RepresentativeAssertionReady gt before) :
    RawStep before.carrier.index.session before.carrier.index.source
      [.effect ready.effect] .none ready.sourceAfter
      (.running ready.sourceSearchAfter) := by
  have produced := ready.produced prog
  simpa [RepresentativeAssertionReady.effect,
    RepresentativeAssertionReady.sourceAfter,
    RepresentativeAssertionReady.sourceSearchAfter] using produced.2.1

/-- The deterministic package retains the exact fine step supplied by the
same contextual assertion producer. -/
theorem afterAssertion_fineStep
    (prog : PLeaTTa.Prog) (gt : GroundingTable)
    (before : RepresentativeActivePayloadState)
    (ready : RepresentativeAssertionReady gt before) :
    DemandDrivenCallStep.Step prog gt before.carrier.fineState
      (afterAssertion prog gt before ready).carrier.fineState := by
  have produced := ready.produced prog
  rw [afterAssertion_fineState]
  simpa [RepresentativeAssertionReady.executableAfter,
    RepresentativeAssertionReady.executableTail,
    ActivePayloadState.fineState] using produced.2.2.1

/-- The effect-erasure certificate is producer-derived and fixes both the
typed source mutation and the two persistent endpoints. -/
theorem afterAssertion_effectErasure
    (prog : PLeaTTa.Prog) (gt : GroundingTable)
    (before : RepresentativeActivePayloadState)
    (ready : RepresentativeAssertionReady gt before) :
    SourceDatabaseEffectErasure [.effect ready.effect]
      before.carrier.index.session
      (afterAssertion prog gt before ready).carrier.index.session
      before.carrier.index.openConf.persistent
      (afterAssertion prog gt before ready).carrier.index.openConf.persistent := by
  have produced := ready.produced prog
  simpa [afterAssertion, RepresentativeAssertionReady.effect,
    RepresentativeAssertionReady.sourceAfter,
    RepresentativeAssertionReady.executableAfter,
    RepresentativeAssertionReady.executableTail,
    ActivePayloadState.ofAgreement] using produced.2.2.2.1

end RepresentativeActivePayloadState

end PLeaTTa.PrologCurrentSessionAssertionTransitionBridge
