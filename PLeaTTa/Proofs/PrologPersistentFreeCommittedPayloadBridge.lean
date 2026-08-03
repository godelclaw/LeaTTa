-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologPersistentFreeCommittedPayloadBridge
Purpose: State and consume post-cut product correspondence without retaining
  historical activation packets.
Trusted boundary: none
Main exports:
  PersistentFreeCommittedProductPayloadResourceRelatesAt,
  PersistentFreeCommittedPayloadState,
  RepresentativePersistentFreeCommittedPayloadState
-/
import PLeaTTa.Proofs.PrologPersistentFreeActivePayloadBridge
import PLeaTTa.Proofs.PrologCurrentSessionAdministrativeTransitionBridge
import PLeaTTa.Proofs.PrologCurrentSessionPayloadTransitionBridge

namespace PLeaTTa.PrologPersistentFreeCommittedPayloadBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologActivatedProductStepBridge
open PrologAlphaFreshFrontierBridge
open PrologControlSegmentSpineBridge
open PrologCurrentSessionAdministrativeTransitionBridge
open PrologCurrentSessionPayloadBridge
open PrologCurrentSessionPayloadTransitionBridge
open PrologMguComposition
open PrologOrdinaryStepBridge
open PrologPersistentFreeActivePayloadBridge
open PrologProductResourceContextBridge
open PrologProductResourceTransitionBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
open PrologSourceProductContextBridge
open PrologStateBridge

/-!
`OpenedCall` and `PendingCall` are activation packets.  A clause-local cut has
already consumed the selected occurrence and its retained cursor, so neither
packet is part of the committed state.  Keeping them would make a stale
persistent session and an already-pruned alternative bank available to later
continuations.

The committed relation below retains only live data: the current source and
fine states, the predicate's typed cut scope, the current task spine, and the
exact surviving outer payload zipper.  The latter owns all older activation
and control origins recursively.
-/

/-- Packet-free correspondence after a clause-local cut consumed the active
predicate occurrence and its executable marker. -/
structure PersistentFreeCommittedProductPayloadResourceRelatesAt
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (predicateScope : CutScopeId) (session : Session)
    (bodyBarrier callerBarrier : Nat)
    (bodyReferences : List PeTTaSpec.PrologCore.Goal)
    (bodyExecutables : List PLeaTTa.Goal)
    (callerReferences : List PeTTaSpec.PrologCore.Goal)
    (callerExecutables : List PLeaTTa.Goal)
    (outer : List ControlSegment)
    (current : Substitution) (runtime : Subst) (qterm : Atom)
    (resources : List RetainedAlternativeSegment)
    (callerScope outerScope : CutScopeId)
    (context : ActiveProductContext)
    (baseAlts : List PLeaTTa.Alt)
    (source : Search) (state : OpenConf)
    (payloadContext :
      CommittedProductPayloadContext alpha support qterm callerBarrier outer
        resources callerScope outerScope context) : Prop where
  ready :
    SpinedReadyTaskRelates freshFrontier alpha support canonical
      referenceBase session current runtime qterm
      ({ barrier := bodyBarrier
         references := bodyReferences
         executables := bodyExecutables } ::
       { barrier := callerBarrier
         references := callerReferences
         executables := callerExecutables } ::
       outer)
      state
  actualAlts :
    state.control.alts = flattenOwnedAlts resources baseAlts
  cacheCoherent : PLeaTTa.BarrierCacheCoherent state.toConf
  sourceShape :
    source =
      ActiveProductContext.plug context
        (cutSourceProductAt callerScope predicateScope current bodyReferences
          callerReferences)
  endpointsCurrent :
    endpointsBelow payloadContext session.resolver.nextFresh
      state.persistent.counter
  activationOrdered : ActivationOrdered payloadContext
  activationOrigins :
    LocalActivationOriginSpineRelates session payloadContext
  controlOrigins :
    LocalControlOriginSpineRelates baseAlts state.frames
      state.control.barriers payloadContext

namespace PersistentFreeCommittedProductPayloadResourceRelatesAt

/-- Legacy committed relations erase to the live packet-free relation.  No
field of either historical packet is projected except the predicate's typed
scope, which is a live delimiter in the source control. -/
def ofLegacy
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {session : Session}
    {pending : DemandDrivenCallStep.PendingCall}
    {bodyBarrier callerBarrier : Nat}
    {bodyReferences : List PeTTaSpec.PrologCore.Goal}
    {bodyExecutables : List PLeaTTa.Goal}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {current : Substitution} {runtime : Subst} {qterm : Atom}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext} {baseAlts : List PLeaTTa.Alt}
    {source : Search} {state : OpenConf}
    {payloadContext :
      CommittedProductPayloadContext alpha support qterm callerBarrier outer
        resources callerScope outerScope context}
    (agreement :
      SpinedCommittedProductPayloadResourceRelatesAt freshFrontier alpha
        support canonical referenceBase opened session pending bodyBarrier
        callerBarrier bodyReferences bodyExecutables callerReferences
        callerExecutables outer current runtime qterm resources callerScope
        outerScope context baseAlts source state payloadContext) :
    PersistentFreeCommittedProductPayloadResourceRelatesAt freshFrontier
      alpha support canonical referenceBase opened.scope session bodyBarrier
      callerBarrier bodyReferences bodyExecutables callerReferences
      callerExecutables outer current runtime qterm resources callerScope
      outerScope context baseAlts source state payloadContext :=
  { ready := agreement.core.control.ready
    actualAlts := agreement.core.resourceStack.actualAlts
    cacheCoherent := agreement.core.control.cacheCoherent
    sourceShape := by
      simpa [cutSourceProduct, cutSourceProductAt] using
        agreement.core.sourceShape
    endpointsCurrent := agreement.endpointsCurrent
    activationOrdered := agreement.activationOrdered
    activationOrigins := agreement.activationOrigins
    controlOrigins := agreement.controlOrigins }

end PersistentFreeCommittedProductPayloadResourceRelatesAt

/-- The active payload head ties the live executable cut tag to the exact
retained resource occurrence. -/
theorem persistentFreeActive_headResourceBarrier
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {predicateScope : CutScopeId} {session : Session}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {bodyReferences : List PeTTaSpec.PrologCore.Goal}
    {bodyExecutables : List PLeaTTa.Goal}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {current : Substitution} {runtime : Subst} {qterm : Atom}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext} {baseAlts : List PLeaTTa.Alt}
    {source : Search} {state : OpenConf}
    {payloadContext :
      ActiveProductPayloadContextAt alpha support qterm predicateScope finish
        branch branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context}
    (_agreement :
      PersistentFreeActiveProductPayloadResourceRelatesAt freshFrontier alpha
        support canonical referenceBase predicateScope session finish branch
        branchTail altTail bodyBarrier callerBarrier bodyReferences
        bodyExecutables callerReferences callerExecutables outer current
        runtime qterm active resources callerScope outerScope context baseAlts
        source state payloadContext) :
    active.barrier = bodyBarrier := by
  cases payloadContext with
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees =>
      exact resourceBarrier

/-- The live occurrence-indexed control origin determines the exact result
of the predicate-local cut without reconstructing a `PendingCall`.  Both the
alternative bank and optional cache return to the recorded outer control. -/
theorem persistentFreeActive_cutControlExact
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {predicateScope : CutScopeId} {session : Session}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {bodyReferences : List PeTTaSpec.PrologCore.Goal}
    {bodyExecutables : List PLeaTTa.Goal}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {current : Substitution} {runtime : Subst} {qterm : Atom}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext} {baseAlts : List PLeaTTa.Alt}
    {source : Search} {state : OpenConf}
    {payloadContext :
      ActiveProductPayloadContextAt alpha support qterm predicateScope finish
        branch branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context}
    (agreement :
      PersistentFreeActiveProductPayloadResourceRelatesAt freshFrontier alpha
        support canonical referenceBase predicateScope session finish branch
        branchTail altTail bodyBarrier callerBarrier bodyReferences
        bodyExecutables callerReferences callerExecutables outer current
        runtime qterm active resources callerScope outerScope context baseAlts
        source state payloadContext)
    (coherent : PLeaTTa.BarrierCacheCoherent state.toConf) :
    let outerAlts := flattenOwnedAlts resources baseAlts
    let outerBarriers :=
      (headCell payloadContext).snapshot.controlOrigin.outerBarriers
    bodyBarrier = PLeaTTa.barrierCount outerAlts + 1 ∧
      (PLeaTTa.cutToTracked bodyBarrier state.toConf.barriers
        state.toConf.alts).1 = outerAlts ∧
      (PLeaTTa.cutToTracked bodyBarrier state.toConf.barriers
        state.toConf.alts).2 = outerBarriers := by
  dsimp only
  let cell := headCell payloadContext
  have outerAltsExact :
      cell.snapshot.controlOrigin.outerAlts =
        flattenOwnedAlts resources baseAlts :=
    LocalControlOriginSpineRelates.headOuterAlts_eq payloadContext
      agreement.controlOrigins
  have liveBarriersExact :
      state.control.barriers =
        PLeaTTa.pushBarrierCache
          cell.snapshot.controlOrigin.outerBarriers :=
    LocalControlOriginSpineRelates.installedBarriers_eq_push_headOuter
      payloadContext agreement.controlOrigins
  have activeBarrier : active.barrier = bodyBarrier :=
    persistentFreeActive_headResourceBarrier agreement
  have activeMarkerFree : PLeaTTa.barrierCount active.alts = 0 :=
    RetainedAlternativeSegment.HasIndexedOwnershipAt.barrierCount_zero
      cell.ownership
  have coherentControl :
      match state.control.barriers with
      | none => True
      | some depth => depth = PLeaTTa.barrierCount state.control.alts := by
    cases cached : state.control.barriers with
    | none => trivial
    | some depth =>
        have coherentRaw := coherent
        unfold PLeaTTa.BarrierCacheCoherent at coherentRaw
        simpa [OpenConf.toConf, Control.toConf, cached] using coherentRaw
  have outerCoherent :
      match cell.snapshot.controlOrigin.outerBarriers with
      | none => True
      | some depth =>
          depth = PLeaTTa.barrierCount (flattenOwnedAlts resources baseAlts) := by
    cases cached : cell.snapshot.controlOrigin.outerBarriers with
    | none => trivial
    | some depth =>
        have live : state.control.barriers = some (depth + 1) := by
          rw [liveBarriersExact, cached]
          rfl
        have currentCoherent := coherent
        change
          match state.control.barriers with
          | none => True
          | some currentDepth =>
              currentDepth = PLeaTTa.barrierCount state.control.alts
          at currentCoherent
        rw [live, agreement.actualAlts, flattenOwnedAlts_cons,
          PLeaTTa.barrierCount_append, activeMarkerFree,
          PLeaTTa.barrierCount_cons_barrier] at currentCoherent
        omega
  have barrierExact :
      bodyBarrier =
        PLeaTTa.barrierCount (flattenOwnedAlts resources baseAlts) + 1 := by
    calc
      bodyBarrier = active.barrier := activeBarrier.symm
      _ = cell.snapshot.controlOrigin.bodyBarrier :=
        cell.snapshot.controlOriginBarrier.symm
      _ = cell.snapshot.controlOrigin.outerBarriers.getD
            (PLeaTTa.barrierCount cell.snapshot.controlOrigin.outerAlts) + 1 :=
        cell.snapshot.controlOrigin.bodyBarrierTag
      _ = PLeaTTa.barrierCount (flattenOwnedAlts resources baseAlts) + 1 := by
        rw [outerAltsExact]
        cases cached : cell.snapshot.controlOrigin.outerBarriers with
        | none => rfl
        | some depth =>
          simp only [Option.getD_some]
          have depthExact :
              depth =
                PLeaTTa.barrierCount
                  (flattenOwnedAlts resources baseAlts) := by
            simpa [cached] using outerCoherent
          rw [depthExact]
  have trackedAltsControl :
      (PLeaTTa.cutToTracked bodyBarrier state.control.barriers
        state.control.alts).1 = flattenOwnedAlts resources baseAlts
      := by
    rw [PLeaTTa.cutToTracked_fst_of_coherent _ _ _ coherentControl,
      agreement.actualAlts, flattenOwnedAlts_cons, barrierExact]
    exact
      PLeaTTa.PrologCoreAdequacy.cutTo_own_barrier active.alts
        (flattenOwnedAlts resources baseAlts)
  have trackedBarriersControl :
      (PLeaTTa.cutToTracked bodyBarrier state.control.barriers
        state.control.alts).2 =
          cell.snapshot.controlOrigin.outerBarriers := by
    cases cached : cell.snapshot.controlOrigin.outerBarriers with
    | none =>
        have live : state.control.barriers = none := by
          rw [liveBarriersExact, cached]
          rfl
        simp [live, PLeaTTa.cutToTracked]
    | some depth =>
        have live : state.control.barriers = some (depth + 1) := by
          rw [liveBarriersExact, cached]
          rfl
        have resultCoherent :=
          PLeaTTa.cutToTracked_coherent bodyBarrier state.control.barriers
            state.control.alts coherentControl
        generalize resultEq :
            (PLeaTTa.cutToTracked bodyBarrier state.control.barriers
              state.control.alts).2 = resultCache
          at resultCoherent ⊢
        cases resultCache with
        | none =>
            rw [live] at resultEq
            simp [PLeaTTa.cutToTracked] at resultEq
        | some resultDepth =>
            rw [trackedAltsControl] at resultCoherent
            have depthExact :
                depth =
                  PLeaTTa.barrierCount
                    (flattenOwnedAlts resources baseAlts) := by
              simpa [cached] using outerCoherent
            have resultDepthEq : resultDepth = depth := by
              exact resultCoherent.trans depthExact.symm
            simp [resultDepthEq]
  exact ⟨barrierExact, trackedAltsControl, trackedBarriersControl⟩

/-- A packet-free active occurrence performs one exact clause-local cut and
produces a packet-free committed state.  The proof consumes only live state,
the typed predicate scope, and the occurrence-indexed payload head; it never
constructs an `OpenedCall` or `PendingCall`. -/
theorem persistentFreeActive_afterCut
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {predicateScope : CutScopeId} {session : Session}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {bodyRest : List PeTTaSpec.PrologCore.Goal}
    {bodyExecutableTail : List PLeaTTa.Goal}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {current : Substitution} {runtime : Subst} {qterm : Atom}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext} {baseAlts : List PLeaTTa.Alt}
    {source : Search} {state : OpenConf}
    {payloadContext :
      ActiveProductPayloadContextAt alpha support qterm predicateScope finish
        branch branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context}
    (agreement :
      PersistentFreeActiveProductPayloadResourceRelatesAt freshFrontier alpha
        support canonical referenceBase predicateScope session finish branch
        branchTail altTail bodyBarrier callerBarrier (.cut :: bodyRest)
        (.cutAt bodyBarrier :: bodyExecutableTail) callerReferences
        callerExecutables outer current runtime qterm active resources
        callerScope outerScope context baseAlts source state payloadContext)
    (coherent : PLeaTTa.BarrierCacheCoherent state.toConf) :
    let nextState :=
      cutSuccessor state bodyBarrier
        (bodyExecutableTail ++
          (callerExecutables ++ flattenExecutables outer))
        runtime
    state.control.cur =
        some
          (.cutAt bodyBarrier ::
            (bodyExecutableTail ++
              (callerExecutables ++ flattenExecutables outer)),
            runtime) ∧
      RawStep session source
        [.pruned
          (retainedCursorTokenAt predicateScope finish branch branchTail)]
        .none session
        (.running
          (ActiveProductContext.plug context
            (cutSourceProductAt callerScope predicateScope current bodyRest
              callerReferences))) ∧
      DemandDrivenCallStep.Step prog gt (.ready state) (.ready nextState) ∧
      PersistentFreeCommittedProductPayloadResourceRelatesAt freshFrontier
        alpha support canonical referenceBase predicateScope session
        bodyBarrier callerBarrier bodyRest bodyExecutableTail callerReferences
        callerExecutables outer current runtime qterm resources callerScope
        outerScope context baseAlts
        (ActiveProductContext.plug context
          (cutSourceProductAt callerScope predicateScope current bodyRest
            callerReferences))
        nextState (ActiveProductPayloadContextAt.outerPayload payloadContext) ∧
      ActiveProductPayloadContext.cellCount payloadContext =
        ActiveProductPayloadContext.cellCount
          (ActiveProductPayloadContextAt.outerPayload payloadContext) + 1 ∧
      PLeaTTa.barrierCount state.control.alts =
        PLeaTTa.barrierCount nextState.control.alts + 1 := by
  rcases agreement.ready with
    ⟨persistent, currentControl, queryTerm, payload⟩
  have bodyPayload :
      TaskPayloadAgrees alpha support bodyBarrier canonical referenceBase
        current runtime (.cut :: bodyRest)
        (.cutAt bodyBarrier :: bodyExecutableTail) :=
    payload.headPayload
  have bodyTailControl :
      NormalizedAlphaGoalsAgree alpha bodyBarrier bodyRest
        bodyExecutableTail := by
    rcases bodyPayload.control.cutHead with
      ⟨witnessTail, executableShape, witnessControl⟩
    have witnessTailEq : witnessTail = bodyExecutableTail := by
      simpa using (congrArg List.tail executableShape).symm
    subst witnessTail
    exact witnessControl
  have executableHead :
      state.control.cur =
        some
          (.cutAt bodyBarrier ::
            (bodyExecutableTail ++
              (callerExecutables ++ flattenExecutables outer)),
            runtime) := by
    simpa [flattenExecutables, ControlSegment.executableGoals,
      List.append_assoc] using currentControl
  let nextState :=
    cutSuccessor state bodyBarrier
      (bodyExecutableTail ++
        (callerExecutables ++ flattenExecutables outer))
      runtime
  have executableStep :
      DemandDrivenCallStep.Step prog gt (.ready state) (.ready nextState) :=
    executable_cut_step state bodyBarrier
      (bodyExecutableTail ++
        (callerExecutables ++ flattenExecutables outer))
      runtime executableHead
  have nextPayload :
      TaskSpinePayloadAgrees alpha support canonical referenceBase current
        runtime
        ({ barrier := bodyBarrier
           references := bodyRest
           executables := bodyExecutableTail } ::
         { barrier := callerBarrier
           references := callerReferences
           executables := callerExecutables } ::
         outer) :=
    ⟨payload.data, .cons bodyTailControl payload.control.tail⟩
  have nextReady :
      SpinedReadyTaskRelates freshFrontier alpha support canonical
        referenceBase session current runtime qterm
        ({ barrier := bodyBarrier
           references := bodyRest
           executables := bodyExecutableTail } ::
         { barrier := callerBarrier
           references := callerReferences
           executables := callerExecutables } ::
         outer)
        nextState := by
    refine ⟨?_, ?_, ?_, nextPayload⟩
    · simpa [nextState] using persistent
    · simp [nextState, flattenExecutables, ControlSegment.executableGoals]
    · change state.control.qterm = qterm
      exact queryTerm
  have controlExact := persistentFreeActive_cutControlExact agreement coherent
  have nextActualAlts :
      nextState.control.alts = flattenOwnedAlts resources baseAlts := by
    change
      (PLeaTTa.cutToTracked bodyBarrier state.control.barriers
        state.control.alts).1 = flattenOwnedAlts resources baseAlts
    exact controlExact.2.1
  have nextBarriers :
      nextState.control.barriers =
        (headCell payloadContext).snapshot.controlOrigin.outerBarriers := by
    change
      (PLeaTTa.cutToTracked bodyBarrier state.control.barriers
        state.control.alts).2 =
          (headCell payloadContext).snapshot.controlOrigin.outerBarriers
    exact controlExact.2.2
  have nextCoherent : PLeaTTa.BarrierCacheCoherent nextState.toConf := by
    have cutCoherent :=
      PLeaTTa.BarrierCacheCoherent.cut state.toConf bodyBarrier coherent
    unfold PLeaTTa.BarrierCacheCoherent at cutCoherent ⊢
    simpa [nextState, cutSuccessor] using cutCoherent
  have sourceStep :
      RawStep session source
        [.pruned
          (retainedCursorTokenAt predicateScope finish branch branchTail)]
        .none session
        (.running
          (ActiveProductContext.plug context
            (cutSourceProductAt callerScope predicateScope current bodyRest
              callerReferences))) := by
    rw [agreement.sourceShape]
    exact
      ActiveProductContext.liftProgress context activeSourceProductAt_cut
        (by simp [Trace.AnswerFree])
  have outerEndpoints :
      endpointsBelow (ActiveProductPayloadContextAt.outerPayload payloadContext)
        session.resolver.nextFresh nextState.persistent.counter := by
    simpa [nextState] using
      (show
        endpointsBelow
          (ActiveProductPayloadContextAt.outerPayload payloadContext)
          session.resolver.nextFresh state.persistent.counter by
        cases payloadContext
        exact agreement.endpointsCurrent.2.2)
  have outerOrdered :
      ActivationOrdered
        (ActiveProductPayloadContextAt.outerPayload payloadContext) := by
    cases payloadContext
    exact ActivationOrdered.tail _ agreement.activationOrdered
  have outerActivationOrigins :
      LocalActivationOriginSpineRelates session
        (ActiveProductPayloadContextAt.outerPayload payloadContext) := by
    cases payloadContext
    exact LocalActivationOriginSpineRelates.tail _ agreement.activationOrigins
  have poppedOrigins :=
    LocalControlOriginSpineRelates.pop payloadContext agreement.controlOrigins
  have outerControlOrigins :
      LocalControlOriginSpineRelates baseAlts nextState.frames
        nextState.control.barriers
        (ActiveProductPayloadContextAt.outerPayload payloadContext) := by
    have outerPayloadEq :
        ActiveProductPayloadContextAt.outerPayload payloadContext =
          SourceControlResourcePayloadContextAgrees.tail payloadContext := by
      cases payloadContext
      rfl
    rw [outerPayloadEq]
    have nextFrames : nextState.frames = state.frames := by
      simp [nextState, cutSuccessor]
    rw [nextFrames, nextBarriers]
    exact poppedOrigins
  have nextAgreement :
      PersistentFreeCommittedProductPayloadResourceRelatesAt freshFrontier
        alpha support canonical referenceBase predicateScope session
        bodyBarrier callerBarrier bodyRest bodyExecutableTail callerReferences
        callerExecutables outer current runtime qterm resources callerScope
        outerScope context baseAlts
        (ActiveProductContext.plug context
          (cutSourceProductAt callerScope predicateScope current bodyRest
            callerReferences))
        nextState (ActiveProductPayloadContextAt.outerPayload payloadContext) :=
    { ready := nextReady
      actualAlts := nextActualAlts
      cacheCoherent := nextCoherent
      sourceShape := rfl
      endpointsCurrent := outerEndpoints
      activationOrdered := outerOrdered
      activationOrigins := outerActivationOrigins
      controlOrigins := outerControlOrigins }
  have activeMarkerFree : PLeaTTa.barrierCount active.alts = 0 :=
    RetainedAlternativeSegment.HasIndexedOwnershipAt.barrierCount_zero
      (headCell payloadContext).ownership
  have countDrop :
      PLeaTTa.barrierCount state.control.alts =
        PLeaTTa.barrierCount nextState.control.alts + 1 := by
    rw [agreement.actualAlts, flattenOwnedAlts_cons,
      PLeaTTa.barrierCount_append, activeMarkerFree,
      PLeaTTa.barrierCount_cons_barrier, nextActualAlts]
    simp
  exact
    ⟨executableHead, sourceStep, executableStep, nextAgreement,
      (by cases payloadContext; rfl),
      countDrop⟩

/-- All live indices of one packet-free committed product state. -/
structure PersistentFreeCommittedPayloadIndex where
  freshFrontier : FreshFrontierRelation
  alpha : List (LogicVar × String)
  support : List (LogicVar × String)
  canonical : TreeSubstitution
  referenceBase : Substitution
  predicateScope : CutScopeId
  session : Session
  bodyBarrier : Nat
  callerBarrier : Nat
  bodyReferences : List PeTTaSpec.PrologCore.Goal
  bodyExecutables : List PLeaTTa.Goal
  callerReferences : List PeTTaSpec.PrologCore.Goal
  callerExecutables : List PLeaTTa.Goal
  outer : List ControlSegment
  current : Substitution
  runtime : Subst
  qterm : Atom
  resources : List RetainedAlternativeSegment
  callerScope : CutScopeId
  outerScope : CutScopeId
  context : ActiveProductContext
  baseAlts : List PLeaTTa.Alt
  source : Search
  openConf : OpenConf

namespace PersistentFreeCommittedPayloadIndex

abbrev PayloadContext (index : PersistentFreeCommittedPayloadIndex) :=
  CommittedProductPayloadContext index.alpha index.support index.qterm
    index.callerBarrier index.outer index.resources index.callerScope
    index.outerScope index.context

abbrev Relates (index : PersistentFreeCommittedPayloadIndex)
    (payloadContext : index.PayloadContext) :=
  PersistentFreeCommittedProductPayloadResourceRelatesAt index.freshFrontier
    index.alpha index.support index.canonical index.referenceBase
    index.predicateScope index.session index.bodyBarrier index.callerBarrier
    index.bodyReferences index.bodyExecutables index.callerReferences
    index.callerExecutables index.outer index.current index.runtime index.qterm
    index.resources index.callerScope index.outerScope index.context
    index.baseAlts index.source index.openConf payloadContext

end PersistentFreeCommittedPayloadIndex

/-- Proof-relevant committed state with its exact surviving payload tail. -/
structure PersistentFreeCommittedPayloadState where
  index : PersistentFreeCommittedPayloadIndex
  payloadContext : index.PayloadContext
  agreement : index.Relates payloadContext

namespace PersistentFreeCommittedPayloadState

/-- Package an existing packet-free relation without weakening an index. -/
def ofAgreement
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {predicateScope : CutScopeId} {session : Session}
    {bodyBarrier callerBarrier : Nat}
    {bodyReferences : List PeTTaSpec.PrologCore.Goal}
    {bodyExecutables : List PLeaTTa.Goal}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {current : Substitution} {runtime : Subst} {qterm : Atom}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext} {baseAlts : List PLeaTTa.Alt}
    {source : Search} {openConf : OpenConf}
    {payloadContext :
      CommittedProductPayloadContext alpha support qterm callerBarrier outer
        resources callerScope outerScope context}
    (agreement :
      PersistentFreeCommittedProductPayloadResourceRelatesAt freshFrontier
        alpha support canonical referenceBase predicateScope session
        bodyBarrier callerBarrier bodyReferences bodyExecutables
        callerReferences callerExecutables outer current runtime qterm
        resources callerScope outerScope context baseAlts source openConf
        payloadContext) : PersistentFreeCommittedPayloadState :=
  { index :=
      { freshFrontier := freshFrontier
        alpha := alpha
        support := support
        canonical := canonical
        referenceBase := referenceBase
        predicateScope := predicateScope
        session := session
        bodyBarrier := bodyBarrier
        callerBarrier := callerBarrier
        bodyReferences := bodyReferences
        bodyExecutables := bodyExecutables
        callerReferences := callerReferences
        callerExecutables := callerExecutables
        outer := outer
        current := current
        runtime := runtime
        qterm := qterm
        resources := resources
        callerScope := callerScope
        outerScope := outerScope
        context := context
        baseAlts := baseAlts
        source := source
        openConf := openConf }
    payloadContext := payloadContext
    agreement := agreement }

def sourceState (state : PersistentFreeCommittedPayloadState) : State :=
  .running state.index.session state.index.source

def fineState (state : PersistentFreeCommittedPayloadState) :
    DemandDrivenCallStep.FineConf :=
  .ready state.index.openConf

def cellIdentities (state : PersistentFreeCommittedPayloadState) :
    List PrologNestedCallChainBridge.PayloadCellIdentity :=
  PrologNestedCallChainBridge.SourceControlResourcePayloadContextAgrees.cellIdentities
    state.payloadContext

def cellCount (state : PersistentFreeCommittedPayloadState) : Nat :=
  PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount
    state.payloadContext

theorem cellIdentities_length (state : PersistentFreeCommittedPayloadState) :
    state.cellIdentities.length = state.cellCount :=
  PrologNestedCallChainBridge.SourceControlResourcePayloadContextAgrees.cellIdentities_length_eq_cellCount
    state.payloadContext

end PersistentFreeCommittedPayloadState

/-- A packet-free committed state with its literal cumulative residual. -/
structure RepresentativePersistentFreeCommittedPayloadState where
  carrier : PersistentFreeCommittedPayloadState
  representative : TreeSubstitution
  cumulative :
    AlphaCumulativeResidualVariantAgreesOnWith carrier.index.alpha
      carrier.index.support carrier.index.canonical carrier.index.referenceBase
      carrier.index.runtime representative

namespace RepresentativePersistentFreeActivePayloadState

/-- Re-index the live packet-free active relation at an exposed cut head.
Keeping this projection named ensures the cut producer and every exact
successor projection consume the same occurrence-indexed evidence. -/
def cutAgreement
    (state : RepresentativePersistentFreeActivePayloadState)
    (bodyRest : List PeTTaSpec.PrologCore.Goal)
    (bodyExecutableTail : List PLeaTTa.Goal)
    (referenceHead :
      state.carrier.index.bodyReferences = .cut :: bodyRest)
    (executableHead :
      state.carrier.index.bodyExecutables =
        .cutAt state.carrier.index.bodyBarrier :: bodyExecutableTail) :
    PersistentFreeActiveProductPayloadResourceRelatesAt
      state.carrier.index.freshFrontier state.carrier.index.alpha
      state.carrier.index.support state.carrier.index.canonical
      state.carrier.index.referenceBase state.carrier.index.predicateScope
      state.carrier.index.session state.carrier.index.finish
      state.carrier.index.branch state.carrier.index.branchTail
      state.carrier.index.altTail state.carrier.index.bodyBarrier
      state.carrier.index.callerBarrier (.cut :: bodyRest)
      (.cutAt state.carrier.index.bodyBarrier :: bodyExecutableTail)
      state.carrier.index.callerReferences
      state.carrier.index.callerExecutables state.carrier.index.outer
      state.carrier.index.current state.carrier.index.runtime
      state.carrier.index.qterm state.carrier.index.active
      state.carrier.index.resources state.carrier.index.callerScope
      state.carrier.index.outerScope state.carrier.index.context
      state.carrier.index.baseAlts state.carrier.index.source
      state.carrier.index.openConf state.carrier.payloadContext := by
  simpa only [PersistentFreeActivePayloadIndex.Relates, referenceHead,
    executableHead] using state.carrier.agreement

/-- Packet-free source focus after the current clause commits. -/
def committedSource
    (state : RepresentativePersistentFreeActivePayloadState)
    (bodyRest : List PeTTaSpec.PrologCore.Goal) : Search :=
  ActiveProductContext.plug state.carrier.index.context
    (cutSourceProductAt state.carrier.index.callerScope
      state.carrier.index.predicateScope state.carrier.index.current bodyRest
      state.carrier.index.callerReferences)

/-- Packet-free fine state after the same tagged cut. -/
def committedOpenConf
    (state : RepresentativePersistentFreeActivePayloadState)
    (bodyExecutableTail : List PLeaTTa.Goal) : OpenConf :=
  cutSuccessor state.carrier.index.openConf state.carrier.index.bodyBarrier
    (bodyExecutableTail ++
      (state.carrier.index.callerExecutables ++
        flattenExecutables state.carrier.index.outer))
    state.carrier.index.runtime

/-- Native packet-free cut producer.  The target carrier contains neither
activation packet, and the proof itself consumes the live origin zipper
rather than manufacturing compatibility records. -/
def afterCut
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativePersistentFreeActivePayloadState)
    (bodyRest : List PeTTaSpec.PrologCore.Goal)
    (bodyExecutableTail : List PLeaTTa.Goal)
    (referenceHead :
      state.carrier.index.bodyReferences = .cut :: bodyRest)
    (executableHead :
      state.carrier.index.bodyExecutables =
        .cutAt state.carrier.index.bodyBarrier :: bodyExecutableTail)
    (coherent :
      PLeaTTa.BarrierCacheCoherent state.carrier.index.openConf.toConf) :
    RepresentativePersistentFreeCommittedPayloadState :=
  let activeAgreement :=
    cutAgreement state bodyRest bodyExecutableTail referenceHead executableHead
  let nextAgreement :
      PersistentFreeCommittedProductPayloadResourceRelatesAt
        state.carrier.index.freshFrontier state.carrier.index.alpha
        state.carrier.index.support state.carrier.index.canonical
        state.carrier.index.referenceBase state.carrier.index.predicateScope
        state.carrier.index.session state.carrier.index.bodyBarrier
        state.carrier.index.callerBarrier bodyRest bodyExecutableTail
        state.carrier.index.callerReferences
        state.carrier.index.callerExecutables state.carrier.index.outer
        state.carrier.index.current state.carrier.index.runtime
        state.carrier.index.qterm state.carrier.index.resources
        state.carrier.index.callerScope state.carrier.index.outerScope
        state.carrier.index.context state.carrier.index.baseAlts
        (committedSource state bodyRest)
        (committedOpenConf state bodyExecutableTail)
        (ActiveProductPayloadContextAt.outerPayload
          state.carrier.payloadContext) := by
    simpa [committedSource, committedOpenConf] using
      (persistentFreeActive_afterCut (prog := prog) (gt := gt)
        activeAgreement coherent).2.2.2.1
  let nextCarrier :=
    PersistentFreeCommittedPayloadState.ofAgreement nextAgreement
  { carrier := nextCarrier
    representative := state.representative
    cumulative := by
      simpa [nextCarrier, PersistentFreeCommittedPayloadState.ofAgreement]
        using state.cumulative }

@[simp] theorem afterCut_sourceState
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativePersistentFreeActivePayloadState)
    (bodyRest : List PeTTaSpec.PrologCore.Goal)
    (bodyExecutableTail : List PLeaTTa.Goal)
    (referenceHead :
      state.carrier.index.bodyReferences = .cut :: bodyRest)
    (executableHead :
      state.carrier.index.bodyExecutables =
        .cutAt state.carrier.index.bodyBarrier :: bodyExecutableTail)
    (coherent :
      PLeaTTa.BarrierCacheCoherent state.carrier.index.openConf.toConf) :
    (afterCut prog gt state bodyRest bodyExecutableTail referenceHead
      executableHead coherent).carrier.sourceState =
      .running state.carrier.index.session (committedSource state bodyRest) :=
  rfl

@[simp] theorem afterCut_fineState
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativePersistentFreeActivePayloadState)
    (bodyRest : List PeTTaSpec.PrologCore.Goal)
    (bodyExecutableTail : List PLeaTTa.Goal)
    (referenceHead :
      state.carrier.index.bodyReferences = .cut :: bodyRest)
    (executableHead :
      state.carrier.index.bodyExecutables =
        .cutAt state.carrier.index.bodyBarrier :: bodyExecutableTail)
    (coherent :
      PLeaTTa.BarrierCacheCoherent state.carrier.index.openConf.toConf) :
    (afterCut prog gt state bodyRest bodyExecutableTail referenceHead
      executableHead coherent).carrier.fineState =
      .ready (committedOpenConf state bodyExecutableTail) := rfl

/-- A packet-free cut consumes exactly the active payload head.  This is a
literal zipper-tail equation, not merely a cell-count decrease. -/
@[simp] theorem afterCut_cellIdentities
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativePersistentFreeActivePayloadState)
    (bodyRest : List PeTTaSpec.PrologCore.Goal)
    (bodyExecutableTail : List PLeaTTa.Goal)
    (referenceHead :
      state.carrier.index.bodyReferences = .cut :: bodyRest)
    (executableHead :
      state.carrier.index.bodyExecutables =
        .cutAt state.carrier.index.bodyBarrier :: bodyExecutableTail)
    (coherent :
      PLeaTTa.BarrierCacheCoherent state.carrier.index.openConf.toConf) :
    (afterCut prog gt state bodyRest bodyExecutableTail referenceHead
      executableHead coherent).carrier.cellIdentities =
        state.carrier.cellIdentities.tail := by
  change
    PrologNestedCallChainBridge.SourceControlResourcePayloadContextAgrees.cellIdentities
        (ActiveProductPayloadContextAt.outerPayload
          state.carrier.payloadContext) =
      (PrologNestedCallChainBridge.SourceControlResourcePayloadContextAgrees.cellIdentities
        state.carrier.payloadContext).tail
  cases state.carrier.payloadContext
  rfl

/-- The committed resource zipper is exactly the one-cell tail of the active
zipper.  Stating the equation through `drop 1` makes the cut occurrence and
surviving suffix explicit and rejects a forged compatible outer resource
list. -/
@[simp] theorem afterCut_resources_exact
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativePersistentFreeActivePayloadState)
    (bodyRest : List PeTTaSpec.PrologCore.Goal)
    (bodyExecutableTail : List PLeaTTa.Goal)
    (referenceHead :
      state.carrier.index.bodyReferences = .cut :: bodyRest)
    (executableHead :
      state.carrier.index.bodyExecutables =
        .cutAt state.carrier.index.bodyBarrier :: bodyExecutableTail)
    (coherent :
      PLeaTTa.BarrierCacheCoherent state.carrier.index.openConf.toConf) :
    (afterCut prog gt state bodyRest bodyExecutableTail referenceHead
      executableHead coherent).carrier.index.resources =
        (state.carrier.index.active :: state.carrier.index.resources).drop 1 :=
  by simp [afterCut, PersistentFreeCommittedPayloadState.ofAgreement]

/-- The fine cut leaves exactly the alternative bank owned by the surviving
resource suffix plus the literal base bank.  No uncounted catch/soft-cut
marker can disappear unnoticed behind a barrier-count equation. -/
@[simp] theorem afterCut_alts_exact
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativePersistentFreeActivePayloadState)
    (bodyRest : List PeTTaSpec.PrologCore.Goal)
    (bodyExecutableTail : List PLeaTTa.Goal)
    (referenceHead :
      state.carrier.index.bodyReferences = .cut :: bodyRest)
    (executableHead :
      state.carrier.index.bodyExecutables =
        .cutAt state.carrier.index.bodyBarrier :: bodyExecutableTail)
    (coherent :
      PLeaTTa.BarrierCacheCoherent state.carrier.index.openConf.toConf) :
    (afterCut prog gt state bodyRest bodyExecutableTail referenceHead
      executableHead coherent).carrier.index.openConf.control.alts =
        flattenOwnedAlts state.carrier.index.resources
          state.carrier.index.baseAlts :=
  (afterCut prog gt state bodyRest bodyExecutableTail referenceHead
    executableHead coherent).carrier.agreement.actualAlts

/-- The fine cut restores the exact cache recorded by the consumed
occurrence's outer control origin.  This is stronger than cache coherence and
would reject dropping an uncounted catch/soft-cut delimiter. -/
@[simp] theorem afterCut_barriers_exact
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativePersistentFreeActivePayloadState)
    (bodyRest : List PeTTaSpec.PrologCore.Goal)
    (bodyExecutableTail : List PLeaTTa.Goal)
    (referenceHead :
      state.carrier.index.bodyReferences = .cut :: bodyRest)
    (executableHead :
      state.carrier.index.bodyExecutables =
        .cutAt state.carrier.index.bodyBarrier :: bodyExecutableTail)
    (coherent :
      PLeaTTa.BarrierCacheCoherent state.carrier.index.openConf.toConf) :
    (afterCut prog gt state bodyRest bodyExecutableTail referenceHead
      executableHead coherent).carrier.index.openConf.control.barriers =
        (headCell state.carrier.payloadContext).snapshot.controlOrigin.outerBarriers := by
  have exact :=
    persistentFreeActive_cutControlExact
      (cutAgreement state bodyRest bodyExecutableTail referenceHead
        executableHead) coherent
  change
    (PLeaTTa.cutToTracked state.carrier.index.bodyBarrier
      state.carrier.index.openConf.toConf.barriers
      state.carrier.index.openConf.toConf.alts).2 =
        (headCell state.carrier.payloadContext).snapshot.controlOrigin.outerBarriers
  exact exact.2.2

end RepresentativePersistentFreeActivePayloadState

/-! ## Native committed administration -/

/-- Exactly counted compiler-erased administration through the packet-free
post-cut wrapper.  The fine machine stays literal while each source task step
remains present in the public step count. -/
theorem administrativeSteps_cutProductContextSourceStepsAt
    {count : Nat}
    {beforeBody afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps : AdministrativeStepsN count beforeBody afterBody)
    (context : ActiveProductContext)
    (callerScope predicateScope : CutScopeId)
    (current : Substitution)
    (callerReferences : List PeTTaSpec.PrologCore.Goal)
    (session : Session) :
    StepsN count
      (.running session
        (ActiveProductContext.plug context
          (cutSourceProductAt callerScope predicateScope current beforeBody
            callerReferences)))
      []
      (.running session
        (ActiveProductContext.plug context
          (cutSourceProductAt callerScope predicateScope current afterBody
            callerReferences))) := by
  induction steps with
  | zero goals =>
      exact .zero _
  | succ count before middle after head tail inductionHypothesis =>
      have child :
          RawStep session (.task predicateScope before current) [] .none
            session (.running (.task predicateScope middle current)) :=
        head.rawStep predicateScope current session
      have boundary :
          RawStep session
            (.cutBoundary predicateScope
              (.task predicateScope before current))
            [] .none session
            (.running
              (.cutBoundary predicateScope
                (.task predicateScope middle current))) :=
        .cutBoundaryProgress predicateScope _ _ [] session session child
      have product :
          RawStep session
            (cutSourceProductAt callerScope predicateScope current before
              callerReferences)
            [] .none session
            (.running
              (cutSourceProductAt callerScope predicateScope current middle
                callerReferences)) := by
        simpa [cutSourceProductAt] using
          (RawStep.productProgress callerScope _ _ callerReferences [] .none
            session session boundary (by simp [Trace.AnswerFree]))
      have lifted :
          RawStep session
            (ActiveProductContext.plug context
              (cutSourceProductAt callerScope predicateScope current before
                callerReferences))
            [] .none session
            (.running
              (ActiveProductContext.plug context
                (cutSourceProductAt callerScope predicateScope current middle
                  callerReferences))) :=
        ActiveProductContext.liftProgress context product
          (by simp [Trace.AnswerFree])
      have first :
          Transition
            (.running session
              (ActiveProductContext.plug context
                (cutSourceProductAt callerScope predicateScope current before
                  callerReferences)))
            []
            (.running session
              (ActiveProductContext.plug context
                (cutSourceProductAt callerScope predicateScope current middle
                  callerReferences))) :=
        .ordinary _ [] session session
          (.running
            (ActiveProductContext.plug context
              (cutSourceProductAt callerScope predicateScope current middle
                callerReferences)))
          lifted
      simpa using
        StepsN.succ count
          (.running session
            (ActiveProductContext.plug context
              (cutSourceProductAt callerScope predicateScope current before
                callerReferences)))
          (.running session
            (ActiveProductContext.plug context
              (cutSourceProductAt callerScope predicateScope current middle
                callerReferences)))
          (.running session
            (ActiveProductContext.plug context
              (cutSourceProductAt callerScope predicateScope current after
                callerReferences)))
          [] [] first inductionHypothesis

namespace RepresentativePersistentFreeCommittedPayloadState

/-- Source focus after a compiler-erased committed-body prefix. -/
def administrativeSource
    (state : RepresentativePersistentFreeCommittedPayloadState)
    (afterBody : List PeTTaSpec.PrologCore.Goal) : Search :=
  ActiveProductContext.plug state.carrier.index.context
    (cutSourceProductAt state.carrier.index.callerScope
      state.carrier.index.predicateScope state.carrier.index.current afterBody
      state.carrier.index.callerReferences)

/-- Consume compiler-erased source administration directly from a committed
state.  No activation packet is reconstructed and no persistent state can be
restored from a backtrackable frame. -/
def afterAdministrative
    (state : RepresentativePersistentFreeCommittedPayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) : RepresentativePersistentFreeCommittedPayloadState :=
  let oldAgreement := state.carrier.agreement
  let oldReady := oldAgreement.ready
  let oldSpinePayload := oldReady.2.2.2
  let nextBodyPayload :=
    taskPayload_afterAdministrativeSteps oldSpinePayload.headPayload steps
  let nextSpinePayload :
      TaskSpinePayloadAgrees state.carrier.index.alpha
        state.carrier.index.support state.carrier.index.canonical
        state.carrier.index.referenceBase state.carrier.index.current
        state.carrier.index.runtime
        ({ barrier := state.carrier.index.bodyBarrier
           references := afterBody
           executables := state.carrier.index.bodyExecutables } ::
         { barrier := state.carrier.index.callerBarrier
           references := state.carrier.index.callerReferences
           executables := state.carrier.index.callerExecutables } ::
         state.carrier.index.outer) :=
    ⟨nextBodyPayload.data,
      .cons nextBodyPayload.control oldSpinePayload.control.tail⟩
  let nextReady :
      SpinedReadyTaskRelates state.carrier.index.freshFrontier
        state.carrier.index.alpha state.carrier.index.support
        state.carrier.index.canonical state.carrier.index.referenceBase
        state.carrier.index.session state.carrier.index.current
        state.carrier.index.runtime state.carrier.index.qterm
        ({ barrier := state.carrier.index.bodyBarrier
           references := afterBody
           executables := state.carrier.index.bodyExecutables } ::
         { barrier := state.carrier.index.callerBarrier
           references := state.carrier.index.callerReferences
           executables := state.carrier.index.callerExecutables } ::
         state.carrier.index.outer)
        state.carrier.index.openConf :=
    ⟨oldReady.1, oldReady.2.1, oldReady.2.2.1, nextSpinePayload⟩
  let nextIndex : PersistentFreeCommittedPayloadIndex :=
    { state.carrier.index with
      bodyReferences := afterBody
      source := administrativeSource state afterBody }
  let nextAgreement : nextIndex.Relates state.carrier.payloadContext :=
    { ready := nextReady
      actualAlts := oldAgreement.actualAlts
      cacheCoherent := oldAgreement.cacheCoherent
      sourceShape := rfl
      endpointsCurrent := oldAgreement.endpointsCurrent
      activationOrdered := oldAgreement.activationOrdered
      activationOrigins := oldAgreement.activationOrigins
      controlOrigins := oldAgreement.controlOrigins }
  let nextCarrier : PersistentFreeCommittedPayloadState :=
    { index := nextIndex
      payloadContext := state.carrier.payloadContext
      agreement := nextAgreement }
  { carrier := nextCarrier
    representative := state.representative
    cumulative := by
      simpa [nextCarrier, nextIndex] using state.cumulative }

@[simp] theorem afterAdministrative_sourceState
    (state : RepresentativePersistentFreeCommittedPayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    (afterAdministrative state steps).carrier.sourceState =
      .running state.carrier.index.session
        (administrativeSource state afterBody) := rfl

@[simp] theorem afterAdministrative_fineState
    (state : RepresentativePersistentFreeCommittedPayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    (afterAdministrative state steps).carrier.fineState =
      state.carrier.fineState := rfl

@[simp] theorem afterAdministrative_session
    (state : RepresentativePersistentFreeCommittedPayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    (afterAdministrative state steps).carrier.index.session =
      state.carrier.index.session := rfl

@[simp] theorem afterAdministrative_openConf
    (state : RepresentativePersistentFreeCommittedPayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    (afterAdministrative state steps).carrier.index.openConf =
      state.carrier.index.openConf := rfl

@[simp] theorem afterAdministrative_alpha
    (state : RepresentativePersistentFreeCommittedPayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    (afterAdministrative state steps).carrier.index.alpha =
      state.carrier.index.alpha := rfl

@[simp] theorem afterAdministrative_representative
    (state : RepresentativePersistentFreeCommittedPayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    (afterAdministrative state steps).representative = state.representative :=
  rfl

@[simp] theorem afterAdministrative_cellIdentities
    (state : RepresentativePersistentFreeCommittedPayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    (afterAdministrative state steps).carrier.cellIdentities =
      state.carrier.cellIdentities := rfl

theorem afterAdministrative_sourceSteps
    (state : RepresentativePersistentFreeCommittedPayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    StepsN count state.carrier.sourceState []
      (afterAdministrative state steps).carrier.sourceState := by
  change
    StepsN count
      (.running state.carrier.index.session state.carrier.index.source) []
      (.running state.carrier.index.session
        (administrativeSource state afterBody))
  rw [state.carrier.agreement.sourceShape]
  exact
    administrativeSteps_cutProductContextSourceStepsAt steps
      state.carrier.index.context state.carrier.index.callerScope
      state.carrier.index.predicateScope state.carrier.index.current
      state.carrier.index.callerReferences state.carrier.index.session

end RepresentativePersistentFreeCommittedPayloadState

end PLeaTTa.PrologPersistentFreeCommittedPayloadBridge
