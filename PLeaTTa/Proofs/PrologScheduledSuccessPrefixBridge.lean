-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologScheduledSuccessPrefixBridge
Purpose: Add successful scheduled-head activation to the exact global
  transition zipper and compose its literal persistent-free midpoint.
Trusted boundary: none
Main exports:
  RepresentativePersistentFreeActivePayloadState.afterAdministrative,
  GlobalTransitionKind,
  GlobalCertifiedTransition,
  GlobalCertifiedPrefix,
  GlobalCertifiedPrefix.scheduledSuccessThenAdministrative
-/
import PLeaTTa.Proofs.PrologScheduledPayloadSuccessCarrierBridge
import PLeaTTa.Proofs.PrologFailureRebasePrefixBridge

namespace PLeaTTa.PrologScheduledSuccessPrefixBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologActivatedProductStepBridge
open PrologAlphaFreshFrontierBridge
open PrologBodyFailureResourceTransitionBridge
open PrologCurrentSessionAdministrativeTransitionBridge
open PrologCurrentSessionPayloadBridge
open PrologControlSegmentSpineBridge
open PrologFailureRebasePrefixBridge
open PrologHeterogeneousPrefixBridge
open PrologMguComposition
open PrologOrdinaryStepBridge
open PrologPersistentFreeActivePayloadBridge
open PrologProductResourceContextBridge
open PrologProductResourceTransitionBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
open PrologRootClosedAnswerBridge
open PrologScheduledPayloadLandingBridge
open PrologScheduledPayloadPostHeadBridge
open PrologScheduledPayloadRejectionBridge
open PrologScheduledPayloadSuccessBridge
open PrologScheduledPayloadSuccessCarrierBridge
open PrologSourceProductContextBridge
open PrologStateBridge

/-! ## Persistent-free source administration -/

/-- Exactly counted compiler-erased administration through an active product
whose predicate identity is the typed cut scope itself.  No `OpenedCall` is
needed or fabricated. -/
theorem administrativeSteps_activeProductContextSourceStepsAt
    {count : Nat}
    {beforeBody afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps : AdministrativeStepsN count beforeBody afterBody)
    (context : ActiveProductContext)
    (callerScope predicateScope : CutScopeId)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (current : Substitution)
    (callerReferences : List PeTTaSpec.PrologCore.Goal)
    (session : Session) :
    StepsN count
      (.running session
        (ActiveProductContext.plug context
          (activeSourceProductAt callerScope predicateScope finish branch
            branchTail current beforeBody callerReferences)))
      []
      (.running session
        (ActiveProductContext.plug context
          (activeSourceProductAt callerScope predicateScope finish branch
            branchTail current afterBody callerReferences))) := by
  induction steps with
  | zero goals =>
      exact .zero _
  | succ count before middle after head tail inductionHypothesis =>
      have child :
          RawStep session (.task predicateScope before current) [] .none
            session (.running (.task predicateScope middle current)) :=
        head.rawStep predicateScope current session
      let frame : ActiveProductFrame :=
        { callerScope := callerScope
          predicateScope := predicateScope
          retained :=
            .clauses predicateScope (finish.advance branch branchTail)
          callerRest := callerReferences }
      have active :
          RawStep session
            (activeSourceProductAt callerScope predicateScope finish branch
              branchTail current before callerReferences)
            [] .none session
            (.running
              (activeSourceProductAt callerScope predicateScope finish branch
                branchTail current middle callerReferences)) := by
        simpa [frame, ActiveProductFrame.wrap, activeSourceProductAt] using
          ActiveProductFrame.liftProgress frame child
            (by simp [Trace.AnswerFree])
      have lifted :
          RawStep session
            (ActiveProductContext.plug context
              (activeSourceProductAt callerScope predicateScope finish branch
                branchTail current before callerReferences))
            [] .none session
            (.running
              (ActiveProductContext.plug context
                (activeSourceProductAt callerScope predicateScope finish branch
                  branchTail current middle callerReferences))) :=
        ActiveProductContext.liftProgress context active
          (by simp [Trace.AnswerFree])
      have first :
          Transition
            (.running session
              (ActiveProductContext.plug context
                (activeSourceProductAt callerScope predicateScope finish branch
                  branchTail current before callerReferences)))
            []
            (.running session
              (ActiveProductContext.plug context
                (activeSourceProductAt callerScope predicateScope finish branch
                  branchTail current middle callerReferences))) :=
        .ordinary _ [] session session
          (.running
            (ActiveProductContext.plug context
              (activeSourceProductAt callerScope predicateScope finish branch
                branchTail current middle callerReferences)))
          lifted
      simpa using
        StepsN.succ count
          (.running session
            (ActiveProductContext.plug context
              (activeSourceProductAt callerScope predicateScope finish branch
                branchTail current before callerReferences)))
          (.running session
            (ActiveProductContext.plug context
              (activeSourceProductAt callerScope predicateScope finish branch
                branchTail current middle callerReferences)))
          (.running session
            (ActiveProductContext.plug context
              (activeSourceProductAt callerScope predicateScope finish branch
                branchTail current after callerReferences)))
          [] [] first inductionHypothesis

namespace RepresentativePersistentFreeActivePayloadState

/-- Source focus after a compiler-erased prefix, stated directly over the
persistent-free predicate scope. -/
def administrativeSource
    (state : RepresentativePersistentFreeActivePayloadState)
    (afterBody : List PeTTaSpec.PrologCore.Goal) : Search :=
  ActiveProductContext.plug state.carrier.index.context
    (activeSourceProductAt state.carrier.index.callerScope
      state.carrier.index.predicateScope state.carrier.index.finish
      state.carrier.index.branch state.carrier.index.branchTail
      state.carrier.index.current afterBody
      state.carrier.index.callerReferences)

/-- Compute an administrative successor for an arbitrary persistent-free
active carrier.  This is the first ordinary producer which consumes a
scheduled-success endpoint directly; it never reconstructs legacy
`OpenedCall` or `PendingCall` packets. -/
def afterAdministrative
    (state : RepresentativePersistentFreeActivePayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) : RepresentativePersistentFreeActivePayloadState :=
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
  let nextIndex : PersistentFreeActivePayloadIndex :=
    { state.carrier.index with
      bodyReferences := afterBody
      source := administrativeSource state afterBody }
  let nextAgreement : nextIndex.Relates state.carrier.payloadContext :=
    { ready := nextReady
      activeAlts := oldAgreement.activeAlts
      actualAlts := oldAgreement.actualAlts
      sourceShape := rfl
      endpointsCurrent := oldAgreement.endpointsCurrent
      activationOrdered := oldAgreement.activationOrdered
      activationOrigins := oldAgreement.activationOrigins
      controlOrigins := oldAgreement.controlOrigins }
  let nextCarrier : PersistentFreeActivePayloadState :=
    { index := nextIndex
      payloadContext := state.carrier.payloadContext
      agreement := nextAgreement }
  { carrier := nextCarrier
    representative := state.representative
    cumulative := by
      simpa [nextCarrier, nextIndex] using state.cumulative }

@[simp] theorem afterAdministrative_sourceState
    (state : RepresentativePersistentFreeActivePayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    (afterAdministrative state steps).carrier.sourceState =
      .running state.carrier.index.session
        (administrativeSource state afterBody) := rfl

@[simp] theorem afterAdministrative_fineState
    (state : RepresentativePersistentFreeActivePayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    (afterAdministrative state steps).carrier.fineState =
      state.carrier.fineState := rfl

@[simp] theorem afterAdministrative_session
    (state : RepresentativePersistentFreeActivePayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    (afterAdministrative state steps).carrier.index.session =
      state.carrier.index.session := rfl

@[simp] theorem afterAdministrative_openConf
    (state : RepresentativePersistentFreeActivePayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    (afterAdministrative state steps).carrier.index.openConf =
      state.carrier.index.openConf := rfl

@[simp] theorem afterAdministrative_alpha
    (state : RepresentativePersistentFreeActivePayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    (afterAdministrative state steps).carrier.index.alpha =
      state.carrier.index.alpha := rfl

@[simp] theorem afterAdministrative_representative
    (state : RepresentativePersistentFreeActivePayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    (afterAdministrative state steps).representative =
      state.representative := rfl

@[simp] theorem afterAdministrative_cellIdentities
    (state : RepresentativePersistentFreeActivePayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    (afterAdministrative state steps).carrier.cellIdentities =
      state.carrier.cellIdentities := rfl

theorem afterAdministrative_sourceSteps
    (state : RepresentativePersistentFreeActivePayloadState)
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
    administrativeSteps_activeProductContextSourceStepsAt steps
      state.carrier.index.context state.carrier.index.callerScope
      state.carrier.index.predicateScope state.carrier.index.finish
      state.carrier.index.branch state.carrier.index.branchTail
      state.carrier.index.current state.carrier.index.callerReferences
      state.carrier.index.session

end RepresentativePersistentFreeActivePayloadState

/-! ## Exact scheduled-success transition -/

/-- Public data carried by a successful scheduled transition label.  The
allocation floors and exact target representative remain observable to
prefix invariants after the proof-relevant producer is hidden. -/
structure ScheduledSuccessLabel where
  sourceCost : Nat
  answer : Substitution
  referenceFloor : Nat
  executableFloor : Nat
  targetRepresentative : TreeSubstitution

namespace ScheduledSuccessLabel

def of
    {before : RepresentativeScheduledPayloadState}
    (ready : RootClosedAnswerReady before)
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session)
    (partition : RootPayloadPartition before)
    (flattened : TreeSubstitution) : ScheduledSuccessLabel :=
  { sourceCost :=
      before.carrier.index.outer.length + 1 +
        postAnswerSuccessfulHeadCount ready transition partition
    answer := before.carrier.index.current
    referenceFloor := transition.branch.firstFresh
    executableFloor := selection.selected.resource.counter
    targetRepresentative :=
      flattened ++ transition.selectedSnapshotAtFinish.residualRepresentative }

end ScheduledSuccessLabel

/-- Additive global transition vocabulary.  Existing resolver transitions are
embedded unchanged; the two new constructors are the successful scheduled
edge and the first legacy-free ordinary producer consuming its endpoint. -/
inductive GlobalTransitionKind where
  | resolver (kind : ResolverTransitionKind)
  | activeAdministrative (count : Nat)
  | scheduledSuccess (label : ScheduledSuccessLabel)

namespace GlobalTransitionKind

def sourceCost : GlobalTransitionKind → Nat
  | .resolver kind => kind.sourceCost
  | .activeAdministrative count => count
  | .scheduledSuccess label => label.sourceCost

def sourceEvents : GlobalTransitionKind → List Observation
  | .resolver kind => kind.sourceEvents
  | .activeAdministrative _ => []
  | .scheduledSuccess label => [.answer label.answer]

def fineCost : GlobalTransitionKind → Nat
  | .resolver kind => kind.fineCost
  | .activeAdministrative _ => 0
  | .scheduledSuccess _ => 2

/-- Kind-indexed alpha chronology.  Scheduled success allocates above the
selected retained occurrence's frozen floors while proving those floors are
dominated by the current persistent high-waters. -/
def AlphaEvolution (kind : GlobalTransitionKind)
    (before after : ResolverPhaseState) : Prop :=
  match kind with
  | .resolver resolverKind => resolverKind.AlphaEvolution before after
  | .activeAdministrative _ => after.alpha = before.alpha
  | .scheduledSuccess label =>
      AlphaExtendsAbove before.alpha after.alpha
          label.referenceFloor label.executableFloor ∧
        label.referenceFloor ≤ before.session.resolver.nextFresh ∧
        label.executableFloor ≤ before.openConf.persistent.counter

/-- Scheduled success fixes its literal reconstructed representative instead
of pretending it necessarily extends the scheduled phase's current one. -/
def RepresentativeEvolution (kind : GlobalTransitionKind)
    (before after : ResolverPhaseState) : Prop :=
  match kind with
  | .resolver resolverKind =>
      resolverKind.RepresentativeEvolution before after
  | .activeAdministrative _ => after.representative = before.representative
  | .scheduledSuccess label =>
      after.representative = label.targetRepresentative

end GlobalTransitionKind

/-- Every constructor owns one independent producer package.  There is no
generic constructor accepting separately supplied source and fine traces. -/
inductive GlobalCertifiedTransition
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable) :
    GlobalTransitionKind → ResolverPhaseState → ResolverPhaseState → Type where
  | resolver
      {kind : ResolverTransitionKind} {before after : ResolverPhaseState}
      (step : ResolverCertifiedTransition prog gt kind before after) :
      GlobalCertifiedTransition prog gt (.resolver kind) before after
  | activeAdministrative
      (before : RepresentativePersistentFreeActivePayloadState)
      {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
      (positive : 0 < count)
      (steps :
        AdministrativeStepsN count before.carrier.index.bodyReferences
          afterBody) :
      GlobalCertifiedTransition prog gt (.activeAdministrative count)
        (.ordinary (.active before))
        (.ordinary
          (.active
            (RepresentativePersistentFreeActivePayloadState.afterAdministrative
              before steps)))
  | scheduledSuccess
      {before : RepresentativeScheduledPayloadState}
      {ready : RootClosedAnswerReady before}
      {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
      {scope : CutScopeId}
      {transition :
        ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
          before.carrier.index.session}
      {partition : RootPayloadPartition before}
      {independentResult : Substitution}
      {nextAlpha : List (LogicVar × String)}
      {sourceCanonical flattened : TreeSubstitution}
      {installed : Subst}
      (relation :
        ScheduledSuccessfulHeadRelates prog gt before ready selection scope
          transition partition independentResult nextAlpha sourceCanonical
          flattened installed)
      (successor :
        ScheduledSelectedHeadTransition.ScheduledSuccessfulHeadSuccessor
          prog gt before ready selection scope transition partition
          independentResult nextAlpha sourceCanonical flattened installed
          relation) :
      GlobalCertifiedTransition prog gt
        (.scheduledSuccess
          (ScheduledSuccessLabel.of ready transition partition flattened))
        (.ordinary (.scheduled before))
        (.ordinary (.active successor.after))

namespace GlobalCertifiedTransition

/-- A closed administrative label always preserves the active phase.  The
target is indexed by the actual persistent-free carrier supplied to the
constructor, so no endpoint-compatible committed state can be substituted. -/
theorem activeAdministrative_target_active
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {count : Nat}
    {before : RepresentativePersistentFreeActivePayloadState}
    {after : ResolverPhaseState}
    (step :
      GlobalCertifiedTransition prog gt (.activeAdministrative count)
        (.ordinary (.active before)) after) :
    ∃ target : RepresentativePersistentFreeActivePayloadState,
      after = .ordinary (.active target) := by
  cases step with
  | activeAdministrative before positive steps =>
      exact
        ⟨RepresentativePersistentFreeActivePayloadState.afterAdministrative
          before steps, rfl⟩

/-- The administrative label cannot launder its successor through the
committed phase.  This is a constructor-discrimination fact, independent of
the source and fine endpoint projections. -/
theorem activeAdministrative_not_committed
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (before : RepresentativePersistentFreeActivePayloadState)
    (count : Nat) (target : RepresentativeCommittedPayloadState) :
    IsEmpty
      (GlobalCertifiedTransition prog gt (.activeAdministrative count)
        (.ordinary (.active before)) (.ordinary (.committed target))) := by
  constructor
  intro step
  obtain ⟨after, impossible⟩ := step.activeAdministrative_target_active
  cases impossible

theorem sourceSteps
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kind : GlobalTransitionKind} {before after : ResolverPhaseState}
    (step : GlobalCertifiedTransition prog gt kind before after) :
    StepsN kind.sourceCost before.sourceState kind.sourceEvents
      after.sourceState := by
  cases step with
  | resolver step =>
      simpa [GlobalTransitionKind.sourceCost,
        GlobalTransitionKind.sourceEvents] using step.sourceSteps
  | activeAdministrative before positive steps =>
      simpa [GlobalTransitionKind.sourceCost,
        GlobalTransitionKind.sourceEvents, ResolverPhaseState.sourceState,
        ProductPhaseState.sourceState] using
        PLeaTTa.PrologScheduledSuccessPrefixBridge.RepresentativePersistentFreeActivePayloadState.afterAdministrative_sourceSteps
          before steps
  | scheduledSuccess relation successor =>
      simpa [GlobalTransitionKind.sourceCost,
        GlobalTransitionKind.sourceEvents, ScheduledSuccessLabel.of,
        ResolverPhaseState.sourceState, ProductPhaseState.sourceState] using
        relation.fullSourceRun

/-- The answer pull and selected-head equality are two present fine steps.
Neither is erased into the scheduled-success macro edge. -/
theorem fineSteps
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kind : GlobalTransitionKind} {before after : ResolverPhaseState}
    (step : GlobalCertifiedTransition prog gt kind before after) :
    DemandDrivenCallStep.StepsN prog gt kind.fineCost before.fineState
      after.fineState := by
  cases step with
  | resolver step =>
      simpa [GlobalTransitionKind.fineCost] using step.fineSteps
  | activeAdministrative before positive steps =>
      exact .zero _
  | @scheduledSuccess before ready selection scope transition partition
      independentResult nextAlpha sourceCanonical flattened installed
      relation successor =>
      have notLocal :
          ¬ DemandDrivenCallStep.LocalResolveHead
            before.carrier.index.openConf := by
        intro localHead
        rcases localHead with
          ⟨predicate, args, result, rest, binding, head, _nonempty, _arity⟩
        rw [ready.fineHead] at head
        cases head
      have answerOpen :
          DemandDrivenStep.Step prog gt before.carrier.index.openConf
            (selectedFineState before) := by
        simpa [selectedFineState] using
          DemandDrivenStep.answer_is_one_step prog gt
            before.carrier.index.openConf before.carrier.index.runtime
            ready.fineHead
      have answerFine :
          DemandDrivenCallStep.Step prog gt
            (.ready before.carrier.index.openConf)
            (.ready (selectedFineState before)) :=
        .ordinary _ _ notLocal answerOpen
      have resolvedFine :
          DemandDrivenCallStep.StepsN prog gt 1
            (.ready (selectedFineState before))
            (.ready (successfulFineState transition installed)) := by
        simpa using
          DemandDrivenCallStep.StepsN.succ 0
            (.ready (selectedFineState before))
            (.ready (successfulFineState transition installed))
            (.ready (successfulFineState transition installed))
            relation.fineStep (.zero _)
      have paired :
          DemandDrivenCallStep.StepsN prog gt 2
            (.ready before.carrier.index.openConf)
            (.ready (successfulFineState transition installed)) := by
        simpa using
          DemandDrivenCallStep.StepsN.succ 1
            (.ready before.carrier.index.openConf)
            (.ready (selectedFineState before))
            (.ready (successfulFineState transition installed))
            answerFine resolvedFine
      simpa [GlobalTransitionKind.fineCost,
        ResolverPhaseState.fineState, ProductPhaseState.fineState,
        ScheduledPayloadState.fineState] using paired

theorem sessionHighWaters
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kind : GlobalTransitionKind} {before after : ResolverPhaseState}
    (step : GlobalCertifiedTransition prog gt kind before after) :
    SessionHighWatersExtend before.session after.session := by
  cases step with
  | resolver step => exact step.sessionHighWaters
  | activeAdministrative before positive steps =>
      exact SessionHighWatersExtend.refl _
  | scheduledSuccess relation successor =>
      exact SessionHighWatersExtend.refl _

theorem executableCounter_mono
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kind : GlobalTransitionKind} {before after : ResolverPhaseState}
    (step : GlobalCertifiedTransition prog gt kind before after) :
    before.openConf.persistent.counter ≤ after.openConf.persistent.counter := by
  cases step with
  | resolver step => exact step.executableCounter_mono
  | activeAdministrative before positive steps => exact Nat.le_refl _
  | @scheduledSuccess before ready selection scope transition partition
      independentResult nextAlpha sourceCanonical flattened installed
      relation successor =>
      change before.carrier.index.openConf.persistent.counter ≤
        (successfulFineState transition installed).persistent.counter
      rw [relation.finePersistent]
      simp [selectedFineState, privateAnswerTarget_persistent]

theorem alphaIncluded
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kind : GlobalTransitionKind} {before after : ResolverPhaseState}
    (step : GlobalCertifiedTransition prog gt kind before after) :
    ∀ pair, pair ∈ before.alpha → pair ∈ after.alpha := by
  cases step with
  | resolver step => exact step.alphaIncluded
  | activeAdministrative before positive steps =>
      intro pair present
      exact present
  | scheduledSuccess relation successor =>
      exact relation.alphaIncluded

theorem alphaEvolution
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kind : GlobalTransitionKind} {before after : ResolverPhaseState}
    (step : GlobalCertifiedTransition prog gt kind before after) :
    kind.AlphaEvolution before after := by
  cases step with
  | resolver step =>
      simpa [GlobalTransitionKind.AlphaEvolution] using step.alphaEvolution
  | activeAdministrative before positive steps => rfl
  | @scheduledSuccess before ready selection scope transition partition
      independentResult nextAlpha sourceCanonical flattened installed
      relation successor =>
      have endpointBounds :=
        transition.selectedEndpointBounds
          before.carrier.agreement.endpointsCurrent
      have branchMember : transition.branch ∈ transition.finish.remaining := by
        rw [transition.offset.cursorRemaining]
        simp
      have referenceFloor :
          transition.branch.firstFresh ≤
            before.carrier.index.session.resolver.nextFresh :=
        Nat.le_trans
          (transition.offset.cursorWellFormed.1.member_first_le_next
            branchMember)
          (Nat.le_trans
            (transition.offset.cursorWellFormed.1.member_next_le_final
              branchMember)
            endpointBounds.1)
      have selectedCounterLeFinal :
          selection.selected.resource.counter ≤
            selection.selected.resource.finalCounter := by
        rcases transition.offset.tailOwnership with
          ⟨_callStart, _position, tailOwnership⟩
        rcases tailOwnership.scan with
          ⟨_candidates, _wellFormed, _query, _substitutedArgs, _supported,
            _arities, scan⟩
        have scanExact := scan.counter_exact
        have selectedSeedReserved :
            selection.selected.resource.counter + 1 ≤
              selection.selected.resource.finalCounter := by
          simpa only [afterPulledHead_counter,
            afterPulledHead_finalCounter] using
            (show
              (afterPulledHead selection.selected.resource
                    selection.localTail).counter ≤
                (afterPulledHead selection.selected.resource
                    selection.localTail).finalCounter by
              omega)
        omega
      have executableFloor :
          selection.selected.resource.counter ≤
            before.carrier.index.openConf.persistent.counter :=
        Nat.le_trans selectedCounterLeFinal endpointBounds.2
      exact ⟨relation.extensionAbove, referenceFloor, executableFloor⟩

theorem representativeEvolution
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kind : GlobalTransitionKind} {before after : ResolverPhaseState}
    (step : GlobalCertifiedTransition prog gt kind before after) :
    kind.RepresentativeEvolution before after := by
  cases step with
  | resolver step =>
      simpa [GlobalTransitionKind.RepresentativeEvolution] using
        step.representativeEvolution
  | activeAdministrative before positive steps => rfl
  | scheduledSuccess relation successor => rfl

/-- The closed label cannot turn a successful scheduled transition into a
different phase. -/
theorem scheduledSuccess_target_active
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {label : ScheduledSuccessLabel}
    {before : RepresentativeScheduledPayloadState}
    {after : ResolverPhaseState}
    (step :
      GlobalCertifiedTransition prog gt (.scheduledSuccess label)
        (.ordinary (.scheduled before)) after) :
    ∃ target : RepresentativePersistentFreeActivePayloadState,
      after = .ordinary (.active target) := by
  cases step with
  | scheduledSuccess relation successor => exact ⟨successor.after, rfl⟩

/-- The successful label's source cost is fixed by its producer and is
strictly positive; a caller cannot relabel the edge as a zero-step stutter. -/
theorem scheduledSuccess_sourceCost_positive
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {label : ScheduledSuccessLabel}
    {before : RepresentativeScheduledPayloadState}
    {after : ResolverPhaseState}
    (step :
      GlobalCertifiedTransition prog gt (.scheduledSuccess label)
        (.ordinary (.scheduled before)) after) :
    0 < label.sourceCost := by
  cases step with
  | scheduledSuccess relation successor =>
      simp [ScheduledSuccessLabel.of]

/-- The answer observation stored in the label is definitionally the
scheduled state's current source substitution. -/
theorem scheduledSuccess_answer_exact
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {label : ScheduledSuccessLabel}
    {before : RepresentativeScheduledPayloadState}
    {after : ResolverPhaseState}
    (step :
      GlobalCertifiedTransition prog gt (.scheduledSuccess label)
        (.ordinary (.scheduled before)) after) :
    label.answer = before.carrier.index.current := by
  cases step with
  | scheduledSuccess relation successor => rfl

/-- This first successful carrier is honestly root-closed.  General
unowned executable suffixes remain outside the transition until their
resource relation is represented explicitly. -/
theorem scheduledSuccess_target_rootClosed
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {label : ScheduledSuccessLabel}
    {before : RepresentativeScheduledPayloadState}
    {after : ResolverPhaseState}
    (step :
      GlobalCertifiedTransition prog gt (.scheduledSuccess label)
        (.ordinary (.scheduled before)) after) :
    match after with
    | .ordinary state => state.RootClosed
    | .postFailure _ => False := by
  cases step with
  | scheduledSuccess relation successor => rfl

/-- The constructive Prop-level producer establishes inhabitation of the
Type-valued successor and transition together.  The transition itself stores
the explicit successor; `Nonempty` is not a phase field. -/
theorem scheduledSuccess_nonempty
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    {transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session}
    {partition : RootPayloadPartition before}
    {independentResult : Substitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattened : TreeSubstitution}
    {installed : Subst}
    (relation :
      ScheduledSuccessfulHeadRelates prog gt before ready selection scope
        transition partition independentResult nextAlpha sourceCanonical
        flattened installed) :
    Nonempty
      (Σ successor :
          ScheduledSelectedHeadTransition.ScheduledSuccessfulHeadSuccessor
            prog gt before ready selection scope transition partition
            independentResult nextAlpha sourceCanonical flattened installed
            relation,
        GlobalCertifiedTransition prog gt
          (.scheduledSuccess
            (ScheduledSuccessLabel.of ready transition partition flattened))
          (.ordinary (.scheduled before))
          (.ordinary (.active successor.after))) := by
  rcases
      ScheduledSelectedHeadTransition.ScheduledSuccessfulHeadSuccessor.nonempty
        relation with
    ⟨successor⟩
  exact ⟨⟨successor, .scheduledSuccess relation successor⟩⟩

end GlobalCertifiedTransition

/-! ## Exact global prefixes -/

namespace GlobalTransitionSchedule

def sourceCost : List GlobalTransitionKind → Nat
  | [] => 0
  | kind :: kinds => kind.sourceCost + sourceCost kinds

def sourceEvents : List GlobalTransitionKind → List Observation
  | [] => []
  | kind :: kinds => kind.sourceEvents ++ sourceEvents kinds

def fineCost : List GlobalTransitionKind → Nat
  | [] => 0
  | kind :: kinds => kind.fineCost + fineCost kinds

@[simp] theorem sourceCost_append
    (left right : List GlobalTransitionKind) :
    sourceCost (left ++ right) = sourceCost left + sourceCost right := by
  induction left with
  | nil => simp [sourceCost]
  | cons kind kinds ih =>
      simp only [List.cons_append, sourceCost, ih, Nat.add_assoc]

@[simp] theorem sourceEvents_append
    (left right : List GlobalTransitionKind) :
    sourceEvents (left ++ right) =
      sourceEvents left ++ sourceEvents right := by
  induction left with
  | nil => rfl
  | cons kind kinds ih =>
      simp only [List.cons_append, sourceEvents, ih, List.append_assoc]

@[simp] theorem fineCost_append
    (left right : List GlobalTransitionKind) :
    fineCost (left ++ right) = fineCost left + fineCost right := by
  induction left with
  | nil => simp [fineCost]
  | cons kind kinds ih =>
      simp only [List.cons_append, fineCost, ih, Nat.add_assoc]

@[simp] theorem sourceCost_resolver_map
    (kinds : List ResolverTransitionKind) :
    sourceCost (kinds.map GlobalTransitionKind.resolver) =
      ResolverTransitionSchedule.sourceCost kinds := by
  induction kinds with
  | nil => rfl
  | cons kind kinds ih =>
      simp [sourceCost, GlobalTransitionKind.sourceCost,
        ResolverTransitionSchedule.sourceCost, ih]

@[simp] theorem sourceEvents_resolver_map
    (kinds : List ResolverTransitionKind) :
    sourceEvents (kinds.map GlobalTransitionKind.resolver) =
      ResolverTransitionSchedule.sourceEvents kinds := by
  induction kinds with
  | nil => rfl
  | cons kind kinds ih =>
      simp [sourceEvents, GlobalTransitionKind.sourceEvents,
        ResolverTransitionSchedule.sourceEvents, ih]

@[simp] theorem fineCost_resolver_map
    (kinds : List ResolverTransitionKind) :
    fineCost (kinds.map GlobalTransitionKind.resolver) =
      ResolverTransitionSchedule.fineCost kinds := by
  induction kinds with
  | nil => rfl
  | cons kind kinds ih =>
      simp [fineCost, GlobalTransitionKind.fineCost,
        ResolverTransitionSchedule.fineCost, ih]

/-- Chronological alpha evolution retains the literal midpoint of every
scheduled-success and ordinary transition. -/
def AlphaEvolution :
    List GlobalTransitionKind → ResolverPhaseState →
      ResolverPhaseState → Prop
  | [], before, after => after = before
  | kind :: kinds, before, after =>
      ∃ middle,
        kind.AlphaEvolution before middle ∧
          AlphaEvolution kinds middle after

/-- Chronological representative evolution keeps scheduled reconstruction,
rollback, and ordinary extension as distinct kind-indexed laws. -/
def RepresentativeEvolution :
    List GlobalTransitionKind → ResolverPhaseState →
      ResolverPhaseState → Prop
  | [], before, after => after = before
  | kind :: kinds, before, after =>
      ∃ middle,
        kind.RepresentativeEvolution before middle ∧
          RepresentativeEvolution kinds middle after

end GlobalTransitionSchedule

/-- Proof-relevant global finite prefix.  Every adjacent transition shares
one literal dependent `ResolverPhaseState`; endpoint compatibility is not a
constructor. -/
inductive GlobalCertifiedPrefix
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable) :
    List GlobalTransitionKind → ResolverPhaseState →
      ResolverPhaseState → Type where
  | nil (state : ResolverPhaseState) :
      GlobalCertifiedPrefix prog gt [] state state
  | cons
      {kind : GlobalTransitionKind}
      {kinds : List GlobalTransitionKind}
      {before middle after : ResolverPhaseState}
      (head : GlobalCertifiedTransition prog gt kind before middle)
      (tail : GlobalCertifiedPrefix prog gt kinds middle after) :
      GlobalCertifiedPrefix prog gt (kind :: kinds) before after

namespace GlobalCertifiedPrefix

/-- Embed an existing failure-aware resolver prefix without changing any
literal midpoint or schedule datum. -/
def ofResolver
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List ResolverTransitionKind}
    {before after : ResolverPhaseState}
    (run : ResolverCertifiedPrefix prog gt kinds before after) :
    GlobalCertifiedPrefix prog gt
      (kinds.map GlobalTransitionKind.resolver) before after :=
  match run with
  | .nil state => .nil state
  | .cons head tail => .cons (.resolver head) (ofResolver tail)

/-- Concatenate only at one definitionally shared dependent phase. -/
def append
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {leftKinds rightKinds : List GlobalTransitionKind}
    {before middle after : ResolverPhaseState}
    (left : GlobalCertifiedPrefix prog gt leftKinds before middle)
    (right : GlobalCertifiedPrefix prog gt rightKinds middle after) :
    GlobalCertifiedPrefix prog gt (leftKinds ++ rightKinds) before after :=
  match left with
  | .nil _ => right
  | .cons head tail => .cons head (append tail right)

/-- A split returns the actual dependent midpoint as Type data. -/
def split
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (leftKinds rightKinds : List GlobalTransitionKind)
    {before after : ResolverPhaseState}
    (run :
      GlobalCertifiedPrefix prog gt (leftKinds ++ rightKinds) before after) :
    Σ middle : ResolverPhaseState,
      GlobalCertifiedPrefix prog gt leftKinds before middle ×
        GlobalCertifiedPrefix prog gt rightKinds middle after := by
  induction leftKinds generalizing before with
  | nil => exact ⟨before, .nil before, run⟩
  | cons kind kinds ih =>
      cases run with
      | cons head tail =>
          obtain ⟨middle, left, right⟩ := ih tail
          exact ⟨middle, .cons head left, right⟩

theorem sourceSteps
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List GlobalTransitionKind}
    {before after : ResolverPhaseState}
    (run : GlobalCertifiedPrefix prog gt kinds before after) :
    StepsN (GlobalTransitionSchedule.sourceCost kinds) before.sourceState
      (GlobalTransitionSchedule.sourceEvents kinds) after.sourceState := by
  induction run with
  | nil state => exact StepsN.zero state.sourceState
  | cons head tail ih =>
      simpa [GlobalTransitionSchedule.sourceCost,
        GlobalTransitionSchedule.sourceEvents] using
        StepsN.trans head.sourceSteps ih

theorem fineSteps
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List GlobalTransitionKind}
    {before after : ResolverPhaseState}
    (run : GlobalCertifiedPrefix prog gt kinds before after) :
    DemandDrivenCallStep.StepsN prog gt
      (GlobalTransitionSchedule.fineCost kinds) before.fineState
      after.fineState := by
  induction run with
  | nil state => exact DemandDrivenCallStep.StepsN.zero state.fineState
  | cons head tail ih =>
      simpa [GlobalTransitionSchedule.fineCost] using
        DemandDrivenCallStep.StepsN.trans head.fineSteps ih

theorem sessionHighWaters
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List GlobalTransitionKind}
    {before after : ResolverPhaseState}
    (run : GlobalCertifiedPrefix prog gt kinds before after) :
    SessionHighWatersExtend before.session after.session := by
  induction run with
  | nil state => exact SessionHighWatersExtend.refl state.session
  | cons head tail ih =>
      exact SessionHighWatersExtend.trans head.sessionHighWaters ih

theorem executableCounter_mono
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List GlobalTransitionKind}
    {before after : ResolverPhaseState}
    (run : GlobalCertifiedPrefix prog gt kinds before after) :
    before.openConf.persistent.counter ≤ after.openConf.persistent.counter := by
  induction run with
  | nil state => exact Nat.le_refl _
  | cons head tail ih =>
      exact Nat.le_trans head.executableCounter_mono ih

theorem alphaIncluded
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List GlobalTransitionKind}
    {before after : ResolverPhaseState}
    (run : GlobalCertifiedPrefix prog gt kinds before after) :
    ∀ pair, pair ∈ before.alpha → pair ∈ after.alpha := by
  induction run with
  | nil state =>
      intro pair present
      exact present
  | cons head tail ih =>
      intro pair present
      exact ih pair (head.alphaIncluded pair present)

theorem alphaEvolution
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List GlobalTransitionKind}
    {before after : ResolverPhaseState}
    (run : GlobalCertifiedPrefix prog gt kinds before after) :
    GlobalTransitionSchedule.AlphaEvolution kinds before after := by
  induction run with
  | nil state => rfl
  | @cons kind kinds before middle after head tail ih =>
      exact ⟨middle, head.alphaEvolution, ih⟩

theorem representativeEvolution
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List GlobalTransitionKind}
    {before after : ResolverPhaseState}
    (run : GlobalCertifiedPrefix prog gt kinds before after) :
    GlobalTransitionSchedule.RepresentativeEvolution kinds before after := by
  induction run with
  | nil state => rfl
  | @cons kind kinds before middle after head tail ih =>
      exact ⟨middle, head.representativeEvolution, ih⟩

/-- Chronological list of literal global phase states. -/
def states
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List GlobalTransitionKind}
    {before after : ResolverPhaseState} :
    GlobalCertifiedPrefix prog gt kinds before after →
      List ResolverPhaseState
  | .nil state => [state]
  | .cons _ tail => before :: states tail

@[simp] theorem states_length
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List GlobalTransitionKind}
    {before after : ResolverPhaseState}
    (run : GlobalCertifiedPrefix prog gt kinds before after) :
    run.states.length = kinds.length + 1 := by
  induction run with
  | nil state => rfl
  | cons head tail ih =>
      simp only [states, List.length_cons, List.length, ih]

@[simp] theorem states_ofResolver
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List ResolverTransitionKind}
    {before after : ResolverPhaseState}
    (run : ResolverCertifiedPrefix prog gt kinds before after) :
    (ofResolver run).states = run.states := by
  induction run with
  | nil state => rfl
  | @cons kind kinds start middle finish head tail ih =>
      simp only [ofResolver, states, ResolverCertifiedPrefix.states]
      exact congrArg (start :: ·) ih

/-- The exact success edge followed immediately by a legacy-free ordinary
administrative edge.  The second constructor is indexed by `successor.after`
itself, so the success midpoint cannot be rebuilt from historical packets or
replaced by an endpoint-compatible state. -/
def scheduledSuccessThenAdministrative
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    {transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session}
    {partition : RootPayloadPartition before}
    {independentResult : Substitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattened : TreeSubstitution}
    {installed : Subst}
    (relation :
      ScheduledSuccessfulHeadRelates prog gt before ready selection scope
        transition partition independentResult nextAlpha sourceCanonical
        flattened installed)
    (successor :
      ScheduledSelectedHeadTransition.ScheduledSuccessfulHeadSuccessor
        prog gt before ready selection scope transition partition
        independentResult nextAlpha sourceCanonical flattened installed
        relation)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (positive : 0 < count)
    (steps :
      AdministrativeStepsN count
        successor.after.carrier.index.bodyReferences afterBody) :
    GlobalCertifiedPrefix prog gt
      [ .scheduledSuccess
          (ScheduledSuccessLabel.of ready transition partition flattened),
        .activeAdministrative count ]
      (.ordinary (.scheduled before))
      (.ordinary
        (.active
          (RepresentativePersistentFreeActivePayloadState.afterAdministrative
            successor.after steps))) :=
  .cons (.scheduledSuccess relation successor)
    (.cons (.activeAdministrative successor.after positive steps)
      (.nil
        (.ordinary
          (.active
            (RepresentativePersistentFreeActivePayloadState.afterAdministrative
              successor.after steps)))))

@[simp] theorem scheduledSuccessThenAdministrative_states
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    {transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session}
    {partition : RootPayloadPartition before}
    {independentResult : Substitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattened : TreeSubstitution}
    {installed : Subst}
    (relation :
      ScheduledSuccessfulHeadRelates prog gt before ready selection scope
        transition partition independentResult nextAlpha sourceCanonical
        flattened installed)
    (successor :
      ScheduledSelectedHeadTransition.ScheduledSuccessfulHeadSuccessor
        prog gt before ready selection scope transition partition
        independentResult nextAlpha sourceCanonical flattened installed
        relation)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (positive : 0 < count)
    (steps :
      AdministrativeStepsN count
        successor.after.carrier.index.bodyReferences afterBody) :
    (scheduledSuccessThenAdministrative relation successor positive
      steps).states =
      [ .ordinary (.scheduled before),
        .ordinary (.active successor.after),
        .ordinary
          (.active
            (RepresentativePersistentFreeActivePayloadState.afterAdministrative
              successor.after steps)) ] := rfl

/-- Splitting the two-edge run after scheduled success returns the literal
Type-valued active successor as its dependent midpoint. -/
@[simp] theorem scheduledSuccessThenAdministrative_split_middle
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    {transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session}
    {partition : RootPayloadPartition before}
    {independentResult : Substitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattened : TreeSubstitution}
    {installed : Subst}
    (relation :
      ScheduledSuccessfulHeadRelates prog gt before ready selection scope
        transition partition independentResult nextAlpha sourceCanonical
        flattened installed)
    (successor :
      ScheduledSelectedHeadTransition.ScheduledSuccessfulHeadSuccessor
        prog gt before ready selection scope transition partition
        independentResult nextAlpha sourceCanonical flattened installed
        relation)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (positive : 0 < count)
    (steps :
      AdministrativeStepsN count
        successor.after.carrier.index.bodyReferences afterBody) :
    (split
      [.scheduledSuccess
        (ScheduledSuccessLabel.of ready transition partition flattened)]
      [.activeAdministrative count]
      (scheduledSuccessThenAdministrative relation successor positive
        steps)).1 =
      .ordinary (.active successor.after) := rfl

end GlobalCertifiedPrefix

end PLeaTTa.PrologScheduledSuccessPrefixBridge
