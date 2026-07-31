-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologCurrentSessionPostFailureActivationBridge
Purpose: Reactivate the exact eagerly pulled retained head after primitive
  failure, preserving current persistent state and the complete payload bank.
Trusted boundary: none
Main exports:
  SpinedPostFailureFrontierPayloadResourceRelatesAt.activateSelectedHead
-/
import PLeaTTa.Proofs.PrologCurrentSessionFailurePayloadTransitionBridge

namespace PLeaTTa.PrologCurrentSessionPostFailureActivationBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PLeaTTa.PrologAlphaFreshFrontierBridge
open PrologActivationMacro
open PrologBodyFailureResourceTransitionBridge
open PrologCallPayloadBridge
open PrologControlSegmentSpineBridge
open PrologCurrentSessionFailurePayloadTransitionBridge
open PrologCurrentSessionPayloadBridge
open PrologMguBridge
open PrologOrdinaryStepBridge
open PrologProductResourceContextBridge
open PrologProductResourceTransitionBridge
open PrologRecursiveCallPayloadBridge
open PrologRepresentativeProductActivationBridge
open PrologRetainedCursorOwnershipBridge
open PrologRetainedPayloadActivationBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
open PrologSourceProductContextBridge
open PrologStateBridge

/-!
The post-failure source is stopped at an unadvanced retained cursor while the
executable has already installed that cursor's first retained clause.  The
payload snapshot consequently lives on the consumed resource and advanced
cursor.  Its proof-only chronology token restores the strictly stronger
pre-pull bounds needed by clause-head activation; current world, database,
frames, alternatives, and allocator state always come from the actual input
state.
-/

namespace SpinedPostFailureFrontierPayloadResourceRelatesAt

/-- One exact retained-head activation closes the executable-ahead
post-failure offset.

The independent source selects the same frozen clause occurrence in one silent
step.  The fine executable performs the already-installed full-head equality
in one step.  Every older payload cell is alpha-extended only because its
literal source/executable endpoints predate the selected head's two allocation
seeds.  [SPEC metta.pl:251-256; ISO:unification] -/
theorem activateSelectedHead
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {alpha support : List (LogicVar × String)}
    {opened : OpenedCall} {session : Session}
    {pending : DemandDrivenCallStep.PendingCall}
    {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {qterm : Atom}
    {cursor : PreparedCursor}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    {branchTail : List ClauseBranch}
    {copied : PLeaTTa.Clause}
    {resource : RetainedAlternativeSegment}
    {remainingAlts : List PLeaTTa.Alt}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {source : Search} {state : OpenConf}
    {payloadContext :
      PostFailurePayloadOffsetContext alpha support qterm opened cursor branch
        branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer resource remainingAlts resources callerScope
        outerScope context}
    {independentResult : Substitution}
    (agreement :
      SpinedPostFailureFrontierPayloadResourceRelatesAt
        (AlphaFreshFrontier alpha) alpha support opened session pending
        bodyBarrier callerBarrier callerReferences callerExecutables outer
        qterm cursor branch clause branchTail copied resource remainingAlts
        resources callerScope outerScope context baseAlts source state
        payloadContext)
    (currentShared : SharedRuntimeAlpha alpha)
    (below : ConfBelowResolutionCounter state.toConf)
    (live :
      AlphaRuntimeNamesLive support
        (copied.body ++ resource.rest) resource.qterm)
    (resolved : HeadResolution branch independentResult) :
    let consumed :=
      PostFailurePayloadOffsetContext.headSnapshot payloadContext
    let restored :=
      SelectedHeadActivationChronology.restoreSnapshot consumed
        agreement.activationChronology agreement.core.resourceStack.offset
    ∃ (nextAlpha : List (LogicVar × String))
        (sourceCanonical : TreeSubstitution)
        (installed : Subst),
      ∃ extension :
          AlphaExtendsAbove alpha nextAlpha branch.firstFresh resource.counter,
        ∃ nextPayloadContext :
            ActiveProductPayloadContext nextAlpha support qterm opened cursor
              branch branchTail bodyBarrier callerBarrier callerReferences
              callerExecutables outer (afterPulledHead resource remainingAlts)
              resources callerScope outerScope context,
        SharedRuntimeAlpha nextAlpha ∧
          (∀ pair, pair ∈ alpha → pair ∈ nextAlpha) ∧
        SourceControlResourcePayloadContextAgrees.tail nextPayloadContext =
          SourceControlResourcePayloadContextAgrees.extendAbove extension
            (SourceControlResourcePayloadContextAgrees.tail payloadContext)
            agreement.outerActivationEndpoints ∧
        RawStep session source [] .none session
          (.running
            (ActiveProductContext.plug context
              (activatedSourceProduct callerScope opened cursor branch
                branchTail independentResult callerReferences))) ∧
        PLeaTTa.Step prog gt state.toConf
          (unifySuccessor state (copied.body ++ resource.rest)
            installed).toConf ∧
        DemandDrivenCallStep.Step prog gt (.ready state)
          (.ready
            (unifySuccessor state (copied.body ++ resource.rest)
              installed)) ∧
        SpinedActiveProductPayloadResourceRelatesAt
          (AlphaFreshFrontier nextAlpha) nextAlpha support
          (sourceCanonical ++ restored.canonical) restored.referenceBase
          opened session pending cursor branch branchTail remainingAlts
          bodyBarrier callerBarrier branch.body copied.body callerReferences
          callerExecutables outer independentResult
          (PLeaTTa.trimFor (copied.body ++ resource.rest)
            state.control.qterm installed)
          qterm (afterPulledHead resource remainingAlts) resources callerScope
          outerScope context baseAlts
          (ActiveProductContext.plug context
            (activatedSourceProduct callerScope opened cursor branch
              branchTail independentResult callerReferences))
          (unifySuccessor state (copied.body ++ resource.rest) installed)
          nextPayloadContext := by
  let consumed :=
    PostFailurePayloadOffsetContext.headSnapshot payloadContext
  let restored :=
    SelectedHeadActivationChronology.restoreSnapshot consumed
      agreement.activationChronology agreement.core.resourceStack.offset
  have currentQuery :
      state.control.qterm = resource.qterm :=
    agreement.core.control.queryTerm.trans
      agreement.core.control.resourceQuery.symm
  have endpointComponents :=
    SourceControlResourcePayloadContextAgrees.endpointsBelow_head
      payloadContext agreement.endpointsCurrent
  have cursorDominated :
      cursor.reservedUntil ≤ session.resolver.nextFresh := by
    simpa [PreparedCursor.advance] using endpointComponents.1
  have resourceDominated :
      resource.finalCounter ≤ state.persistent.counter := by
    simpa [afterPulledHead] using endpointComponents.2.1
  obtain
      ⟨_representative, nextAlpha, sourceCanonical, _flattened, installed,
        nextShared, alphaIncluded, extension, freshFrontier,
        independentShape, sourceOrdered, sourceLeaf, sealedStep, fineStep,
        cumulative, bodyPayload, nextSnapshotNonempty, successorBelow,
        persistentExact, framesExact, altsExact⟩ :=
    RetainedCallPayloadSnapshot.activateSelectedHead
      (prog := prog) (gt := gt) restored agreement.core.resourceStack.offset
      agreement.core.control.current currentQuery currentShared
      agreement.core.control.persistent cursorDominated resourceDominated
      below live resolved
  have sourceBoundary :
      RawStep session
        (.cutBoundary opened.scope (.clauses opened.scope cursor))
        [] .none session
        (.running
          (.cutBoundary opened.scope
            (.choice opened.scope
              (.task opened.scope branch.body independentResult)
              (.clauses opened.scope
                (cursor.advance branch branchTail))))) :=
    .cutBoundaryProgress opened.scope _ _ [] session session sourceLeaf
  have sourceProductStep :
      RawStep session
        (sourceProductFrontier callerScope opened cursor callerReferences)
        [] .none session
        (.running
          (activatedSourceProduct callerScope opened cursor branch branchTail
            independentResult callerReferences)) := by
    exact
      .productProgress callerScope _ _ callerReferences [] .none session
        session sourceBoundary (by simp [Trace.AnswerFree])
  have sourceStep :
      RawStep session source [] .none session
        (.running
          (ActiveProductContext.plug context
            (activatedSourceProduct callerScope opened cursor branch branchTail
              independentResult callerReferences))) := by
    rw [agreement.core.sourceShape]
    exact
      ActiveProductContext.liftProgress context sourceProductStep
        (by simp [Trace.AnswerFree])

  let outerBefore :=
    SourceControlResourcePayloadContextAgrees.tail payloadContext
  let outerNext :=
    SourceControlResourcePayloadContextAgrees.extendAbove extension outerBefore
      agreement.outerActivationEndpoints
  have outerNextAtSeed :
      endpointsBelow outerNext branch.firstFresh resource.counter := by
    simpa [outerNext, outerBefore] using
      SourceControlResourcePayloadContextAgrees.extendAbove_endpointsBelow
        extension outerBefore agreement.outerActivationEndpoints
  have branchMember : branch ∈ cursor.remaining := by
    rw [agreement.core.resourceStack.offset.cursorRemaining]
    simp
  have branchFirstBelowSession :
      branch.firstFresh ≤ session.resolver.nextFresh := by
    calc
      branch.firstFresh ≤ branch.nextFresh :=
        agreement.core.resourceStack.offset.cursorWellFormed.1
          |>.member_first_le_next branchMember
      _ ≤ cursor.reservedUntil :=
        agreement.core.resourceStack.offset.cursorWellFormed.1
          |>.member_next_le_final branchMember
      _ ≤ session.resolver.nextFresh := cursorDominated
  have seedReserved :
      resource.counter + 1 ≤ resource.finalCounter := by
    rcases agreement.core.resourceStack.offset.tailOwnership with
      ⟨_candidates, _wellFormed, _query, _substitutedArgs, _supported,
        _arities, scan⟩
    have scanExact := scan.counter_exact
    simpa only [afterPulledHead_counter, afterPulledHead_finalCounter] using
      (show
        (afterPulledHead resource remainingAlts).counter ≤
          (afterPulledHead resource remainingAlts).finalCounter by
        omega)
  have resourceSeedBelowState :
      resource.counter ≤ state.persistent.counter :=
    Nat.le_trans (Nat.le_trans (Nat.le_succ _) seedReserved)
      resourceDominated
  have outerNextCurrent :
      endpointsBelow outerNext session.resolver.nextFresh
        state.persistent.counter :=
    endpointsBelow_mono outerNext outerNextAtSeed branchFirstBelowSession
      resourceSeedBelowState
  have outerNextAtActivation :
      endpointsBelow outerNext
        (cursor.advance branch branchTail).reservationStart
        (afterPulledHead resource remainingAlts).counter :=
    endpointsBelow_mono outerNext outerNextAtSeed
      (by
        simpa [PreparedCursor.advance] using
          agreement.core.resourceStack.offset.cursorWellFormed.1
            |>.member_first_le_next branchMember)
      (by simp [afterPulledHead])

  rcases nextSnapshotNonempty with ⟨nextSnapshot⟩
  have callerAgrees :
      ({ barrier := callerBarrier
         references := callerReferences
         executables := callerExecutables } :
        ControlSegment).Agrees nextAlpha :=
    (agreement.core.control.callerSpine.head).mono alphaIncluded
  have activeOwnership :
      (afterPulledHead resource remainingAlts).Owns nextAlpha
        (cursor.advance branch branchTail) :=
    agreement.core.resourceStack.offset.tailOwnership.mono alphaIncluded
  let nextPayloadContext :
      ActiveProductPayloadContext nextAlpha support qterm opened cursor branch
        branchTail bodyBarrier callerBarrier callerReferences callerExecutables
        outer (afterPulledHead resource remainingAlts) resources callerScope
        outerScope context :=
    .cons bodyBarrier opened.scope callerScope outerScope
      { barrier := callerBarrier
        references := callerReferences
        executables := callerExecutables }
      outer (afterPulledHead resource remainingAlts) resources
      (cursor.advance branch branchTail) context callerAgrees
      (by simpa [afterPulledHead] using agreement.core.control.resourceRest)
      (by simpa [afterPulledHead] using agreement.core.control.resourceQuery)
      (by simpa [afterPulledHead] using agreement.core.control.resourceBarrier)
      activeOwnership nextSnapshot outerNext
  have nextEndpointsCurrent :
      endpointsBelow nextPayloadContext session.resolver.nextFresh
        (unifySuccessor state (copied.body ++ resource.rest)
          installed).persistent.counter := by
    simp only [nextPayloadContext, endpointsBelow]
    rw [unifySuccessor_persistent]
    exact
      ⟨by simpa [PreparedCursor.advance] using endpointComponents.1,
        by simpa [afterPulledHead] using endpointComponents.2.1,
        outerNextCurrent⟩
  have nextOuterActivationEndpoints :
      endpointsBelow
        (SourceControlResourcePayloadContextAgrees.tail nextPayloadContext)
        (cursor.advance branch branchTail).reservationStart
        (afterPulledHead resource remainingAlts).counter := by
    simpa [nextPayloadContext,
      SourceControlResourcePayloadContextAgrees.tail] using
      outerNextAtActivation
  have nextOuterPayloadExact :
      SourceControlResourcePayloadContextAgrees.tail nextPayloadContext =
        SourceControlResourcePayloadContextAgrees.extendAbove extension
          (SourceControlResourcePayloadContextAgrees.tail payloadContext)
          agreement.outerActivationEndpoints := by
    rfl
  have outerNextOrdered : ActivationOrdered outerNext := by
    exact
      ActivationOrdered.extendAbove extension
        (SourceControlResourcePayloadContextAgrees.tail payloadContext)
        agreement.outerActivationEndpoints
        (ActivationOrdered.tail payloadContext
          agreement.activationOrdered)
  have nextActivationOrdered :
      ActivationOrdered nextPayloadContext := by
    exact ⟨outerNextAtActivation, outerNextOrdered⟩

  have bodyPayloadAtCurrentQuery :
      TaskPayloadAgrees nextAlpha support bodyBarrier
        (sourceCanonical ++ restored.canonical) restored.referenceBase
        independentResult
        (PLeaTTa.trimFor (copied.body ++ resource.rest)
          state.control.qterm installed)
        branch.body copied.body := by
    simpa [currentQuery, agreement.core.control.resourceBarrier] using
      bodyPayload
  have spinePayload :
      TaskSpinePayloadAgrees nextAlpha support
        (sourceCanonical ++ restored.canonical) restored.referenceBase
        independentResult
        (PLeaTTa.trimFor (copied.body ++ resource.rest)
          state.control.qterm installed)
        ({ barrier := bodyBarrier
           references := branch.body
           executables := copied.body } ::
         { barrier := callerBarrier
           references := callerReferences
           executables := callerExecutables } ::
         outer) :=
    TaskSpinePayloadAgrees.activateLocalCall restored.payload
      bodyPayloadAtCurrentQuery
      (fun pair member =>
        alphaIncluded pair (restored.alphaIncluded pair member))
  have targetPersistent :
      SessionRelatesPersistent (AlphaFreshFrontier nextAlpha) session
        (unifySuccessor state (copied.body ++ resource.rest)
          installed).persistent := by
    constructor
    · simpa using agreement.core.control.persistent.database
    · simpa using freshFrontier
  have targetCurrent :
      (unifySuccessor state (copied.body ++ resource.rest)
        installed).control.cur =
          some
            (flattenExecutables
              ({ barrier := bodyBarrier
                 references := branch.body
                 executables := copied.body } ::
               { barrier := callerBarrier
                 references := callerReferences
                 executables := callerExecutables } ::
               outer),
             PLeaTTa.trimFor (copied.body ++ resource.rest)
               state.control.qterm installed) := by
    rw [unifySuccessor_current]
    simp only [flattenExecutables_cons]
    rw [agreement.core.control.resourceRest]
  have targetQuery :
      (unifySuccessor state (copied.body ++ resource.rest)
        installed).control.qterm = qterm := by
    simpa using agreement.core.control.queryTerm
  have targetControl :
      SpinedActiveProductRelatesAt (AlphaFreshFrontier nextAlpha) nextAlpha
        support (sourceCanonical ++ restored.canonical)
        restored.referenceBase opened session pending cursor branch branchTail
        remainingAlts bodyBarrier callerBarrier branch.body copied.body
        callerReferences callerExecutables outer independentResult
        (PLeaTTa.trimFor (copied.body ++ resource.rest)
          state.control.qterm installed)
        qterm
        (unifySuccessor state (copied.body ++ resource.rest) installed) := by
    refine
      { ready := ⟨targetPersistent, targetCurrent, targetQuery, spinePayload⟩
        sessionAdvanced := agreement.core.control.sessionAdvanced
        retainedAlts := ?_
        retainedAltsZero :=
          agreement.core.resourceStack.offset.tailOwnership.barrierCount_zero
        retainedBarriers := ?_
        bodyBarrierTag := agreement.core.control.bodyBarrierTag
        frames := ?_ }
    · simpa using agreement.core.control.retainedAlts
    · simpa using agreement.core.control.retainedBarriers
    · simpa using agreement.core.control.frames
  have targetResourceStack :
      ActiveProductResourceStackAgrees nextAlpha qterm bodyBarrier callerBarrier
        pending (cursor.advance branch branchTail)
        (callerExecutables ++ flattenExecutables outer) remainingAlts
        (afterPulledHead resource remainingAlts) outer resources callerScope
        outerScope context baseAlts
        (unifySuccessor state (copied.body ++ resource.rest) installed) := by
    refine
      { activeRest := ?_
        activeQuery := ?_
        activeBarrier := ?_
        activeAlts := rfl
        activeFinalCounter := ?_
        activeOwnership := activeOwnership
        outerAlignment := outerNext.alignment
        suspendedOuterAlts :=
          agreement.core.resourceStack.suspendedOuterAlts
        actualAlts := ?_ }
    · simpa [afterPulledHead] using agreement.core.control.resourceRest
    · simpa [afterPulledHead] using agreement.core.control.resourceQuery
    · simpa [afterPulledHead] using agreement.core.control.resourceBarrier
    · simpa [afterPulledHead] using agreement.resourceFinalCounter
    · simpa using agreement.core.resourceStack.actualAlts
  have targetCore :
      SpinedActiveProductResourceRelatesAt
        (AlphaFreshFrontier nextAlpha) nextAlpha support
        (sourceCanonical ++ restored.canonical) restored.referenceBase opened
        session pending cursor branch branchTail remainingAlts bodyBarrier
        callerBarrier branch.body copied.body callerReferences
        callerExecutables outer independentResult
        (PLeaTTa.trimFor (copied.body ++ resource.rest)
          state.control.qterm installed)
        qterm (afterPulledHead resource remainingAlts) resources callerScope
        outerScope context baseAlts
        (ActiveProductContext.plug context
          (activatedSourceProduct callerScope opened cursor branch branchTail
            independentResult callerReferences))
        (unifySuccessor state (copied.body ++ resource.rest) installed) :=
    ⟨targetControl, targetResourceStack, rfl⟩
  have targetPayload :
      SpinedActiveProductPayloadResourceRelatesAt
        (AlphaFreshFrontier nextAlpha) nextAlpha support
        (sourceCanonical ++ restored.canonical) restored.referenceBase opened
        session pending cursor branch branchTail remainingAlts bodyBarrier
        callerBarrier branch.body copied.body callerReferences
        callerExecutables outer independentResult
        (PLeaTTa.trimFor (copied.body ++ resource.rest)
          state.control.qterm installed)
        qterm (afterPulledHead resource remainingAlts) resources callerScope
        outerScope context baseAlts
        (ActiveProductContext.plug context
          (activatedSourceProduct callerScope opened cursor branch branchTail
            independentResult callerReferences))
        (unifySuccessor state (copied.body ++ resource.rest) installed)
        nextPayloadContext :=
    ⟨targetCore, nextEndpointsCurrent, nextActivationOrdered⟩
  exact
    ⟨nextAlpha, sourceCanonical, installed, extension, nextPayloadContext,
      nextShared, alphaIncluded, nextOuterPayloadExact, sourceStep, sealedStep,
      fineStep, targetPayload⟩

end SpinedPostFailureFrontierPayloadResourceRelatesAt

end PLeaTTa.PrologCurrentSessionPostFailureActivationBridge
