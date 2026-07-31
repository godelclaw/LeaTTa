-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologCurrentSessionAssertionTransitionBridge
Purpose: Lift one owned local database assertion through the complete active
  product/resource/payload context.
Trusted boundary: none
Main exports:
  SpinedActiveProductPayloadResourceRelatesAt.afterAssertion
-/
import PLeaTTa.Proofs.PrologCurrentSessionPayloadTransitionBridge
import PLeaTTa.Proofs.PrologDatabaseActionStepBridge

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
    SessionHighWatersExtend.withDatabase _ _

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
      ⟨nextCore, nextEndpoints, agreement.activationOrdered⟩⟩

end PLeaTTa.PrologCurrentSessionAssertionTransitionBridge
