-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologHeterogeneousPrefixBridge
Purpose: Expose exact active/scheduled/committed source-to-open-machine states
  as Type-valued data and compose closed, kind-specific transitions through
  an extractable finite-prefix zipper.
Trusted boundary: none
Main exports:
  ProductPhaseState,
  CertifiedTransition,
  CertifiedPrefix
-/
import PLeaTTa.Proofs.PrologNestedCallPrefixInductionBridge
import PLeaTTa.Proofs.PrologCurrentSessionAdministrativeTransitionBridge
import PLeaTTa.Proofs.PrologCurrentSessionPayloadTransitionBridge

namespace PLeaTTa.PrologHeterogeneousPrefixBridge

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
open PrologNestedCallChainBridge
open PrologNestedCallPrefixInductionBridge
open PrologNestedCallReadyBridge
open PrologOrdinaryStepBridge
open PrologProductSchedulingBridge
open PrologProductResourceContextBridge
open PrologProductResourceTransitionBridge
open PrologRepresentativeProductActivationBridge
open PrologRetainedPayloadSnapshotBridge
open PrologSourceProductContextBridge
open PrologStateBridge

/-! ## Type-valued phase states

The existing active relation already has a proof-relevant Type carrier.
Body success and cut leave that active phase, however, and their scheduled
and committed relations previously existed only as long dependent theorem
indices.  The following carriers retain every such index as data.  They do
not quotient states by answer lists, observations, or proof compatibility.
-/

/-- All data indices of one scheduled product state. -/
structure ScheduledPayloadIndex where
  freshFrontier : FreshFrontierRelation
  alpha : List (LogicVar × String)
  support : List (LogicVar × String)
  canonical : TreeSubstitution
  referenceBase : Substitution
  opened : OpenedCall
  session : Session
  pending : DemandDrivenCallStep.PendingCall
  finish : PreparedCursor
  branch : ClauseBranch
  branchTail : List ClauseBranch
  altTail : List PLeaTTa.Alt
  bodyBarrier : Nat
  callerBarrier : Nat
  callerReferences : List PeTTaSpec.PrologCore.Goal
  callerExecutables : List PLeaTTa.Goal
  outer : List ControlSegment
  current : Substitution
  runtime : Subst
  qterm : Atom
  active : RetainedAlternativeSegment
  resources : List RetainedAlternativeSegment
  callerScope : CutScopeId
  outerScope : CutScopeId
  context : ActiveProductContext
  baseAlts : List PLeaTTa.Alt
  source : Search
  openConf : OpenConf

namespace ScheduledPayloadIndex

abbrev PayloadContext (index : ScheduledPayloadIndex) :=
  ScheduledProductPayloadContext index.alpha index.support index.qterm
    index.opened index.finish index.branch index.branchTail index.bodyBarrier
    index.callerBarrier index.callerReferences index.callerExecutables
    index.outer index.active index.resources index.callerScope index.outerScope
    index.context

abbrev Relates (index : ScheduledPayloadIndex)
    (payloadContext : index.PayloadContext) :=
  SpinedScheduledProductPayloadResourceRelatesAt index.freshFrontier
    index.alpha index.support index.canonical index.referenceBase index.opened
    index.session index.pending index.finish index.branch index.branchTail
    index.altTail index.bodyBarrier index.callerBarrier index.callerReferences
    index.callerExecutables index.outer index.current index.runtime index.qterm
    index.active index.resources index.callerScope index.outerScope
    index.context index.baseAlts index.source index.openConf payloadContext

end ScheduledPayloadIndex

/-- One proof-relevant scheduled state with its literal payload zipper. -/
structure ScheduledPayloadState where
  index : ScheduledPayloadIndex
  payloadContext : index.PayloadContext
  agreement : index.Relates payloadContext

namespace ScheduledPayloadState

/-- Package an existing scheduled relation without hiding any Type index. -/
def ofAgreement
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {session : Session}
    {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {current : Substitution} {runtime : Subst} {qterm : Atom}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext} {baseAlts : List PLeaTTa.Alt}
    {source : Search} {openConf : OpenConf}
    {payloadContext :
      ScheduledProductPayloadContext alpha support qterm opened finish branch
        branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context}
    (agreement :
      SpinedScheduledProductPayloadResourceRelatesAt freshFrontier alpha
        support canonical referenceBase opened session pending finish branch
        branchTail altTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer current runtime qterm active resources
        callerScope outerScope context baseAlts source openConf
        payloadContext) : ScheduledPayloadState :=
  { index :=
      { freshFrontier := freshFrontier
        alpha := alpha
        support := support
        canonical := canonical
        referenceBase := referenceBase
        opened := opened
        session := session
        pending := pending
        finish := finish
        branch := branch
        branchTail := branchTail
        altTail := altTail
        bodyBarrier := bodyBarrier
        callerBarrier := callerBarrier
        callerReferences := callerReferences
        callerExecutables := callerExecutables
        outer := outer
        current := current
        runtime := runtime
        qterm := qterm
        active := active
        resources := resources
        callerScope := callerScope
        outerScope := outerScope
        context := context
        baseAlts := baseAlts
        source := source
        openConf := openConf }
    payloadContext := payloadContext
    agreement := agreement }

def sourceState (state : ScheduledPayloadState) : State :=
  .running state.index.session state.index.source

def fineState (state : ScheduledPayloadState) : DemandDrivenCallStep.FineConf :=
  .ready state.index.openConf

def cellIdentities (state : ScheduledPayloadState) :
    List PayloadCellIdentity :=
  SourceControlResourcePayloadContextAgrees.cellIdentities
    state.payloadContext

def cellCount (state : ScheduledPayloadState) : Nat :=
  ActiveProductPayloadContext.cellCount state.payloadContext

theorem cellIdentities_length (state : ScheduledPayloadState) :
    state.cellIdentities.length = state.cellCount :=
  SourceControlResourcePayloadContextAgrees.cellIdentities_length_eq_cellCount
    state.payloadContext

end ScheduledPayloadState

/-- A scheduled state with the concrete cumulative residual representative
made Type-valued for later unification and recursive-call transitions. -/
structure RepresentativeScheduledPayloadState where
  carrier : ScheduledPayloadState
  representative : TreeSubstitution
  cumulative :
    AlphaCumulativeResidualVariantAgreesOnWith carrier.index.alpha
      carrier.index.support carrier.index.canonical carrier.index.referenceBase
      carrier.index.runtime representative

/-- All data indices of one committed product state. -/
structure CommittedPayloadIndex where
  freshFrontier : FreshFrontierRelation
  alpha : List (LogicVar × String)
  support : List (LogicVar × String)
  canonical : TreeSubstitution
  referenceBase : Substitution
  opened : OpenedCall
  session : Session
  pending : DemandDrivenCallStep.PendingCall
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

namespace CommittedPayloadIndex

abbrev PayloadContext (index : CommittedPayloadIndex) :=
  CommittedProductPayloadContext index.alpha index.support index.qterm
    index.callerBarrier index.outer index.resources index.callerScope
    index.outerScope index.context

abbrev Relates (index : CommittedPayloadIndex)
    (payloadContext : index.PayloadContext) :=
  SpinedCommittedProductPayloadResourceRelatesAt index.freshFrontier
    index.alpha index.support index.canonical index.referenceBase index.opened
    index.session index.pending index.bodyBarrier index.callerBarrier
    index.bodyReferences index.bodyExecutables index.callerReferences
    index.callerExecutables index.outer index.current index.runtime index.qterm
    index.resources index.callerScope index.outerScope index.context
    index.baseAlts index.source index.openConf payloadContext

end CommittedPayloadIndex

/-- One proof-relevant committed state with its exact surviving payload tail. -/
structure CommittedPayloadState where
  index : CommittedPayloadIndex
  payloadContext : index.PayloadContext
  agreement : index.Relates payloadContext

namespace CommittedPayloadState

/-- Package an existing committed relation without weakening any index. -/
def ofAgreement
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
    {source : Search} {openConf : OpenConf}
    {payloadContext :
      CommittedProductPayloadContext alpha support qterm callerBarrier outer
        resources callerScope outerScope context}
    (agreement :
      SpinedCommittedProductPayloadResourceRelatesAt freshFrontier alpha
        support canonical referenceBase opened session pending bodyBarrier
        callerBarrier bodyReferences bodyExecutables callerReferences
        callerExecutables outer current runtime qterm resources callerScope
        outerScope context baseAlts source openConf payloadContext) :
    CommittedPayloadState :=
  { index :=
      { freshFrontier := freshFrontier
        alpha := alpha
        support := support
        canonical := canonical
        referenceBase := referenceBase
        opened := opened
        session := session
        pending := pending
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

def sourceState (state : CommittedPayloadState) : State :=
  .running state.index.session state.index.source

def fineState (state : CommittedPayloadState) : DemandDrivenCallStep.FineConf :=
  .ready state.index.openConf

def cellIdentities (state : CommittedPayloadState) :
    List PayloadCellIdentity :=
  SourceControlResourcePayloadContextAgrees.cellIdentities
    state.payloadContext

def cellCount (state : CommittedPayloadState) : Nat :=
  ActiveProductPayloadContext.cellCount state.payloadContext

theorem cellIdentities_length (state : CommittedPayloadState) :
    state.cellIdentities.length = state.cellCount :=
  SourceControlResourcePayloadContextAgrees.cellIdentities_length_eq_cellCount
    state.payloadContext

end CommittedPayloadState

/-- A committed state with its literal cumulative residual representative. -/
structure RepresentativeCommittedPayloadState where
  carrier : CommittedPayloadState
  representative : TreeSubstitution
  cumulative :
    AlphaCumulativeResidualVariantAgreesOnWith carrier.index.alpha
      carrier.index.support carrier.index.canonical carrier.index.referenceBase
      carrier.index.runtime representative

/-- The three ordinary product phases which are genuine state
correspondences.  Post-failure and exhausted certificates are intentionally
not forced into this type: the latter already relates a predecessor and a
successor and will enter the later frontier-transition layer. -/
inductive ProductPhaseState where
  | active (state : RepresentativeActivePayloadState)
  | scheduled (state : RepresentativeScheduledPayloadState)
  | committed (state : RepresentativeCommittedPayloadState)

namespace ProductPhaseState

def sourceState : ProductPhaseState → State
  | .active state => state.carrier.sourceState
  | .scheduled state => state.carrier.sourceState
  | .committed state => state.carrier.sourceState

def fineState : ProductPhaseState → DemandDrivenCallStep.FineConf
  | .active state => state.carrier.fineState
  | .scheduled state => state.carrier.fineState
  | .committed state => state.carrier.fineState

def session : ProductPhaseState → Session
  | .active state => state.carrier.index.session
  | .scheduled state => state.carrier.index.session
  | .committed state => state.carrier.index.session

def openConf : ProductPhaseState → OpenConf
  | .active state => state.carrier.index.openConf
  | .scheduled state => state.carrier.index.openConf
  | .committed state => state.carrier.index.openConf

def alpha : ProductPhaseState → List (LogicVar × String)
  | .active state => state.carrier.index.alpha
  | .scheduled state => state.carrier.index.alpha
  | .committed state => state.carrier.index.alpha

def representative : ProductPhaseState → TreeSubstitution
  | .active state => state.representative
  | .scheduled state => state.representative
  | .committed state => state.representative

def cellIdentities : ProductPhaseState → List PayloadCellIdentity
  | .active state => state.carrier.cellIdentities
  | .scheduled state => state.carrier.cellIdentities
  | .committed state => state.carrier.cellIdentities

def cellCount : ProductPhaseState → Nat
  | .active state => state.carrier.cellCount
  | .scheduled state => state.carrier.cellCount
  | .committed state => state.carrier.cellCount

theorem cellIdentities_length (state : ProductPhaseState) :
    state.cellIdentities.length = state.cellCount := by
  cases state with
  | active state => exact state.carrier.cellIdentities_length
  | scheduled state => exact state.carrier.cellIdentities_length
  | committed state => exact state.carrier.cellIdentities_length

end ProductPhaseState

namespace ActivePayloadState

/-- Runtime identity of the unique active payload cell.  Every field is
already fixed by the dependent active-state index; no proof annotation enters
the identity. -/
def headCell (state : ActivePayloadState) : PayloadCellIdentity :=
  { currentBarrier := state.index.bodyBarrier
    currentScope := state.index.opened.scope
    nextScope := state.index.callerScope
    outerScope := state.index.outerScope
    segment :=
      { barrier := state.index.callerBarrier
        references := state.index.callerReferences
        executables := state.index.callerExecutables }
    resource := state.index.active
    cursor :=
      state.index.finish.advance state.index.branch state.index.branchTail }

/-- The active cell is literally the head of the erased runtime zipper and
`outerPayload` is literally its tail. -/
theorem cellIdentities_eq_headCell_cons_outerPayload
    (state : ActivePayloadState) :
    state.cellIdentities =
      PLeaTTa.PrologHeterogeneousPrefixBridge.ActivePayloadState.headCell state ::
        SourceControlResourcePayloadContextAgrees.cellIdentities
          (ActiveProductPayloadContext.outerPayload state.payloadContext) := by
  change
    SourceControlResourcePayloadContextAgrees.cellIdentities
          state.payloadContext =
      PLeaTTa.PrologHeterogeneousPrefixBridge.ActivePayloadState.headCell state ::
        SourceControlResourcePayloadContextAgrees.cellIdentities
          (ActiveProductPayloadContext.outerPayload state.payloadContext)
  cases state.payloadContext
  rfl

end ActivePayloadState

/-! ## Deterministic phase successors

These functions compute only successor data already fixed by the source and
fine semantics.  Their proof fields reuse the closed phase producers.  No
existential proof is eliminated to choose a Type-valued state.
-/

namespace RepresentativeActivePayloadState

/-- Source focus obtained by prepending one compiler-erased truth node to the
active clause body. -/
def truthPredecessorSource (state : RepresentativeActivePayloadState) : Search :=
  ActiveProductContext.plug state.carrier.index.context
    (activeSourceProduct state.carrier.index.callerScope
      state.carrier.index.opened state.carrier.index.finish
      state.carrier.index.branch state.carrier.index.branchTail
      state.carrier.index.current
      (.truth :: state.carrier.index.bodyReferences)
      state.carrier.index.callerReferences)

/-- Add one source-only truth predecessor while retaining every executable,
persistent, resource, payload, alpha, and representative datum literally. -/
def beforeTruth
    (state : RepresentativeActivePayloadState) :
    RepresentativeActivePayloadState :=
  let oldAgreement := state.carrier.agreement
  let oldControl := oldAgreement.core.control
  let oldReady := oldControl.ready
  let oldPayload := oldReady.2.2.2
  let nextPayload :
      TaskSpinePayloadAgrees state.carrier.index.alpha
        state.carrier.index.support state.carrier.index.canonical
        state.carrier.index.referenceBase state.carrier.index.current
        state.carrier.index.runtime
        ({ barrier := state.carrier.index.bodyBarrier
           references := .truth :: state.carrier.index.bodyReferences
           executables := state.carrier.index.bodyExecutables } ::
         { barrier := state.carrier.index.callerBarrier
           references := state.carrier.index.callerReferences
           executables := state.carrier.index.callerExecutables } ::
         state.carrier.index.outer) :=
    { data := oldPayload.data
      control :=
        .cons (.truth oldPayload.control.head) oldPayload.control.tail }
  let nextReady :
      SpinedReadyTaskRelates state.carrier.index.freshFrontier
        state.carrier.index.alpha state.carrier.index.support
        state.carrier.index.canonical state.carrier.index.referenceBase
        state.carrier.index.session state.carrier.index.current
        state.carrier.index.runtime state.carrier.index.qterm
        ({ barrier := state.carrier.index.bodyBarrier
           references := .truth :: state.carrier.index.bodyReferences
           executables := state.carrier.index.bodyExecutables } ::
         { barrier := state.carrier.index.callerBarrier
           references := state.carrier.index.callerReferences
           executables := state.carrier.index.callerExecutables } ::
         state.carrier.index.outer)
        state.carrier.index.openConf :=
    ⟨oldReady.1, oldReady.2.1, oldReady.2.2.1, nextPayload⟩
  let nextControl :
      SpinedActiveProductRelatesAt state.carrier.index.freshFrontier
        state.carrier.index.alpha state.carrier.index.support
        state.carrier.index.canonical state.carrier.index.referenceBase
        state.carrier.index.opened state.carrier.index.session
        state.carrier.index.pending state.carrier.index.finish
        state.carrier.index.branch state.carrier.index.branchTail
        state.carrier.index.altTail state.carrier.index.bodyBarrier
        state.carrier.index.callerBarrier
        (.truth :: state.carrier.index.bodyReferences)
        state.carrier.index.bodyExecutables
        state.carrier.index.callerReferences
        state.carrier.index.callerExecutables state.carrier.index.outer
        state.carrier.index.current state.carrier.index.runtime
        state.carrier.index.qterm state.carrier.index.openConf :=
    { ready := nextReady
      sessionAdvanced := oldControl.sessionAdvanced
      retainedAlts := oldControl.retainedAlts
      retainedAltsZero := oldControl.retainedAltsZero
      retainedBarriers := oldControl.retainedBarriers
      bodyBarrierTag := oldControl.bodyBarrierTag
      frames := oldControl.frames }
  let nextCore :
      SpinedActiveProductResourceRelatesAt
        state.carrier.index.freshFrontier state.carrier.index.alpha
        state.carrier.index.support state.carrier.index.canonical
        state.carrier.index.referenceBase state.carrier.index.opened
        state.carrier.index.session state.carrier.index.pending
        state.carrier.index.finish state.carrier.index.branch
        state.carrier.index.branchTail state.carrier.index.altTail
        state.carrier.index.bodyBarrier state.carrier.index.callerBarrier
        (.truth :: state.carrier.index.bodyReferences)
        state.carrier.index.bodyExecutables
        state.carrier.index.callerReferences
        state.carrier.index.callerExecutables state.carrier.index.outer
        state.carrier.index.current state.carrier.index.runtime
        state.carrier.index.qterm state.carrier.index.active
        state.carrier.index.resources state.carrier.index.callerScope
        state.carrier.index.outerScope state.carrier.index.context
        state.carrier.index.baseAlts
        (truthPredecessorSource state) state.carrier.index.openConf :=
    { control := nextControl
      resourceStack := oldAgreement.core.resourceStack
      sourceShape := rfl }
  let nextAgreement :
      SpinedActiveProductPayloadResourceRelatesAt
        state.carrier.index.freshFrontier state.carrier.index.alpha
        state.carrier.index.support state.carrier.index.canonical
        state.carrier.index.referenceBase state.carrier.index.opened
        state.carrier.index.session state.carrier.index.pending
        state.carrier.index.finish state.carrier.index.branch
        state.carrier.index.branchTail state.carrier.index.altTail
        state.carrier.index.bodyBarrier state.carrier.index.callerBarrier
        (.truth :: state.carrier.index.bodyReferences)
        state.carrier.index.bodyExecutables
        state.carrier.index.callerReferences
        state.carrier.index.callerExecutables state.carrier.index.outer
        state.carrier.index.current state.carrier.index.runtime
        state.carrier.index.qterm state.carrier.index.active
        state.carrier.index.resources state.carrier.index.callerScope
        state.carrier.index.outerScope state.carrier.index.context
        state.carrier.index.baseAlts (truthPredecessorSource state)
        state.carrier.index.openConf state.carrier.payloadContext :=
    { core := nextCore
      endpointsCurrent := oldAgreement.endpointsCurrent
      activationOrdered := oldAgreement.activationOrdered }
  let nextCarrier := ActivePayloadState.ofAgreement nextAgreement
  { carrier := nextCarrier
    representative := state.representative
    cumulative := by
      simpa [nextCarrier, ActivePayloadState.ofAgreement] using
        state.cumulative }

/-- The prepended truth is exactly one independent administrative step. -/
def beforeTruthSteps (state : RepresentativeActivePayloadState) :
    AdministrativeStepsN 1
      (.truth :: state.carrier.index.bodyReferences)
      state.carrier.index.bodyReferences :=
  .succ 0 _ _ _ (.truth _) (.zero _)

/-- Source focus after a compiler-erased administrative prefix. -/
def administrativeSource (state : RepresentativeActivePayloadState)
    (afterBody : List PeTTaSpec.PrologCore.Goal) : Search :=
  ActiveProductContext.plug state.carrier.index.context
    (activeSourceProduct state.carrier.index.callerScope
      state.carrier.index.opened state.carrier.index.finish
      state.carrier.index.branch state.carrier.index.branchTail
      state.carrier.index.current afterBody
      state.carrier.index.callerReferences)

/-- A source-only administrative prefix changes exactly the active source
body and source focus.  The executable state and cumulative representative
remain literal Type data. -/
def afterAdministrative
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) : RepresentativeActivePayloadState :=
  let nextAgreement :
      SpinedActiveProductPayloadResourceRelatesAt
        state.carrier.index.freshFrontier state.carrier.index.alpha
        state.carrier.index.support state.carrier.index.canonical
        state.carrier.index.referenceBase state.carrier.index.opened
        state.carrier.index.session state.carrier.index.pending
        state.carrier.index.finish state.carrier.index.branch
        state.carrier.index.branchTail state.carrier.index.altTail
        state.carrier.index.bodyBarrier state.carrier.index.callerBarrier
        afterBody state.carrier.index.bodyExecutables
        state.carrier.index.callerReferences
        state.carrier.index.callerExecutables state.carrier.index.outer
        state.carrier.index.current state.carrier.index.runtime
        state.carrier.index.qterm state.carrier.index.active
        state.carrier.index.resources state.carrier.index.callerScope
        state.carrier.index.outerScope state.carrier.index.context
        state.carrier.index.baseAlts (administrativeSource state afterBody)
        state.carrier.index.openConf state.carrier.payloadContext := by
    exact
      (PrologCurrentSessionAdministrativeTransitionBridge.SpinedActiveProductPayloadResourceRelatesAt.afterAdministrativeSteps
        (prog := prog) (gt := gt) state.carrier.agreement steps).2.2.1
  let nextCarrier := ActivePayloadState.ofAgreement nextAgreement
  { carrier := nextCarrier
    representative := state.representative
    cumulative := by
      simpa [nextCarrier, ActivePayloadState.ofAgreement] using
        state.cumulative }

@[simp] theorem afterAdministrative_sourceState
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    (afterAdministrative prog gt state steps).carrier.sourceState =
      .running state.carrier.index.session
        (administrativeSource state afterBody) := rfl

@[simp] theorem afterAdministrative_fineState
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    (afterAdministrative prog gt state steps).carrier.fineState =
      state.carrier.fineState := rfl

/-- Consuming the constructed truth predecessor returns the same literal
proof-relevant active state. -/
theorem afterAdministrative_beforeTruth
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState) :
    afterAdministrative prog gt (beforeTruth state) (beforeTruthSteps state) =
      state := by
  rcases state with
    ⟨⟨index, payloadContext, agreement⟩, representative, cumulative⟩
  rcases index with
    ⟨freshFrontier, alpha, support, canonical, referenceBase, opened, session,
      pending, finish, branch, branchTail, altTail, bodyBarrier, callerBarrier,
      bodyReferences, bodyExecutables, callerReferences, callerExecutables,
      outer, current, runtime, qterm, active, resources, callerScope, outerScope,
      context, baseAlts, source, openConf⟩
  have sourceShape := agreement.core.sourceShape
  dsimp only at sourceShape
  subst source
  rfl

/-- Two prepended truth nodes form an exact two-step administrative prefix.
This is the smallest prefix whose source cost differs from the three-step
fine local-call activation that can follow it. -/
def beforeTruthTwiceSteps (state : RepresentativeActivePayloadState) :
    AdministrativeStepsN 2
      (beforeTruth (beforeTruth state)).carrier.index.bodyReferences
      state.carrier.index.bodyReferences :=
  .succ 1 _ _ _ (.truth _) (beforeTruthSteps state)

/-- Consuming both constructed truth predecessors returns the same literal
proof-relevant active state. -/
theorem afterAdministrative_beforeTruth_twice
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState) :
    afterAdministrative prog gt (beforeTruth (beforeTruth state))
        (beforeTruthTwiceSteps state) = state := by
  rcases state with
    ⟨⟨index, payloadContext, agreement⟩, representative, cumulative⟩
  rcases index with
    ⟨freshFrontier, alpha, support, canonical, referenceBase, opened, session,
      pending, finish, branch, branchTail, altTail, bodyBarrier, callerBarrier,
      bodyReferences, bodyExecutables, callerReferences, callerExecutables,
      outer, current, runtime, qterm, active, resources, callerScope, outerScope,
      context, baseAlts, source, openConf⟩
  have sourceShape := agreement.core.sourceShape
  dsimp only at sourceShape
  subst source
  rfl

/-- Source focus after the selected clause body succeeds. -/
def bodyAnswerSource (state : RepresentativeActivePayloadState) : Search :=
  ActiveProductContext.plug state.carrier.index.context
    (scheduledSourceProduct state.carrier.index.callerScope
      state.carrier.index.opened state.carrier.index.finish
      state.carrier.index.branch state.carrier.index.branchTail
      state.carrier.index.current state.carrier.index.callerReferences)

/-- A completed selected body moves from active to scheduled phase without
moving a payload cell or changing the cumulative representative. -/
def afterBodyAnswer
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    (referenceEmpty : state.carrier.index.bodyReferences = [])
    (executableEmpty : state.carrier.index.bodyExecutables = []) :
    RepresentativeScheduledPayloadState :=
  let activeAgreement :
      SpinedActiveProductPayloadResourceRelatesAt
        state.carrier.index.freshFrontier state.carrier.index.alpha
        state.carrier.index.support state.carrier.index.canonical
        state.carrier.index.referenceBase state.carrier.index.opened
        state.carrier.index.session state.carrier.index.pending
        state.carrier.index.finish state.carrier.index.branch
        state.carrier.index.branchTail state.carrier.index.altTail
        state.carrier.index.bodyBarrier state.carrier.index.callerBarrier
        [] [] state.carrier.index.callerReferences
        state.carrier.index.callerExecutables state.carrier.index.outer
        state.carrier.index.current state.carrier.index.runtime
        state.carrier.index.qterm state.carrier.index.active
        state.carrier.index.resources state.carrier.index.callerScope
        state.carrier.index.outerScope state.carrier.index.context
        state.carrier.index.baseAlts state.carrier.index.source
        state.carrier.index.openConf state.carrier.payloadContext := by
    simpa only [ActivePayloadIndex.Relates, referenceEmpty, executableEmpty]
      using state.carrier.agreement
  let nextAgreement :
      SpinedScheduledProductPayloadResourceRelatesAt
        state.carrier.index.freshFrontier state.carrier.index.alpha
        state.carrier.index.support state.carrier.index.canonical
        state.carrier.index.referenceBase state.carrier.index.opened
        state.carrier.index.session state.carrier.index.pending
        state.carrier.index.finish state.carrier.index.branch
        state.carrier.index.branchTail state.carrier.index.altTail
        state.carrier.index.bodyBarrier state.carrier.index.callerBarrier
        state.carrier.index.callerReferences
        state.carrier.index.callerExecutables state.carrier.index.outer
        state.carrier.index.current state.carrier.index.runtime
        state.carrier.index.qterm state.carrier.index.active
        state.carrier.index.resources state.carrier.index.callerScope
        state.carrier.index.outerScope state.carrier.index.context
        state.carrier.index.baseAlts (bodyAnswerSource state)
        state.carrier.index.openConf state.carrier.payloadContext := by
    exact
      (PrologCurrentSessionPayloadTransitionBridge.SpinedActiveProductPayloadResourceRelatesAt.afterBodyAnswer
        (prog := prog) (gt := gt) activeAgreement).2.2
  let nextCarrier := ScheduledPayloadState.ofAgreement nextAgreement
  { carrier := nextCarrier
    representative := state.representative
    cumulative := by
      simpa [nextCarrier, ScheduledPayloadState.ofAgreement] using
        state.cumulative }

@[simp] theorem afterBodyAnswer_sourceState
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    (referenceEmpty : state.carrier.index.bodyReferences = [])
    (executableEmpty : state.carrier.index.bodyExecutables = []) :
    (afterBodyAnswer prog gt state referenceEmpty executableEmpty).carrier.sourceState =
      .running state.carrier.index.session (bodyAnswerSource state) := rfl

@[simp] theorem afterBodyAnswer_fineState
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    (referenceEmpty : state.carrier.index.bodyReferences = [])
    (executableEmpty : state.carrier.index.bodyExecutables = []) :
    (afterBodyAnswer prog gt state referenceEmpty executableEmpty).carrier.fineState =
      state.carrier.fineState := rfl

/-- Source focus after a clause-local cut consumes the selected product. -/
def cutSource (state : RepresentativeActivePayloadState)
    (bodyRest : List PeTTaSpec.PrologCore.Goal) : Search :=
  ActiveProductContext.plug state.carrier.index.context
    (cutSourceProduct state.carrier.index.callerScope
      state.carrier.index.opened state.carrier.index.current bodyRest
      state.carrier.index.callerReferences)

/-- Fine state after the same clause-local cut. -/
def cutOpenConf (state : RepresentativeActivePayloadState)
    (bodyExecutableTail : List PLeaTTa.Goal) : OpenConf :=
  cutSuccessor state.carrier.index.openConf state.carrier.index.bodyBarrier
    (bodyExecutableTail ++
      (state.carrier.index.callerExecutables ++
        flattenExecutables state.carrier.index.outer))
    state.carrier.index.runtime

/-- A clause-local cut moves to the committed phase and exposes the exact
outer payload tail.  The persistent state and semantic representative are
carried by the producer unchanged. -/
def afterCut
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    (bodyRest : List PeTTaSpec.PrologCore.Goal)
    (bodyExecutableTail : List PLeaTTa.Goal)
    (referenceHead :
      state.carrier.index.bodyReferences = .cut :: bodyRest)
    (executableHead :
      state.carrier.index.bodyExecutables =
        .cutAt state.carrier.index.bodyBarrier :: bodyExecutableTail)
    (coherent : PLeaTTa.BarrierCacheCoherent state.carrier.index.openConf.toConf) :
    RepresentativeCommittedPayloadState :=
  let activeAgreement :
      SpinedActiveProductPayloadResourceRelatesAt
        state.carrier.index.freshFrontier state.carrier.index.alpha
        state.carrier.index.support state.carrier.index.canonical
        state.carrier.index.referenceBase state.carrier.index.opened
        state.carrier.index.session state.carrier.index.pending
        state.carrier.index.finish state.carrier.index.branch
        state.carrier.index.branchTail state.carrier.index.altTail
        state.carrier.index.bodyBarrier state.carrier.index.callerBarrier
        (.cut :: bodyRest)
        (.cutAt state.carrier.index.bodyBarrier :: bodyExecutableTail)
        state.carrier.index.callerReferences
        state.carrier.index.callerExecutables state.carrier.index.outer
        state.carrier.index.current state.carrier.index.runtime
        state.carrier.index.qterm state.carrier.index.active
        state.carrier.index.resources state.carrier.index.callerScope
        state.carrier.index.outerScope state.carrier.index.context
        state.carrier.index.baseAlts state.carrier.index.source
        state.carrier.index.openConf state.carrier.payloadContext := by
    simpa only [ActivePayloadIndex.Relates, referenceHead, executableHead]
      using state.carrier.agreement
  let nextAgreement :
      SpinedCommittedProductPayloadResourceRelatesAt
        state.carrier.index.freshFrontier state.carrier.index.alpha
        state.carrier.index.support state.carrier.index.canonical
        state.carrier.index.referenceBase state.carrier.index.opened
        state.carrier.index.session state.carrier.index.pending
        state.carrier.index.bodyBarrier state.carrier.index.callerBarrier
        bodyRest bodyExecutableTail state.carrier.index.callerReferences
        state.carrier.index.callerExecutables state.carrier.index.outer
        state.carrier.index.current state.carrier.index.runtime
        state.carrier.index.qterm state.carrier.index.resources
        state.carrier.index.callerScope state.carrier.index.outerScope
        state.carrier.index.context state.carrier.index.baseAlts
        (cutSource state bodyRest) (cutOpenConf state bodyExecutableTail)
        (ActiveProductPayloadContext.outerPayload
          state.carrier.payloadContext) := by
    exact
      (PrologCurrentSessionPayloadTransitionBridge.SpinedActiveProductPayloadResourceRelatesAt.afterCut
        (prog := prog) (gt := gt) activeAgreement coherent).2.2.2.1
  let nextCarrier := CommittedPayloadState.ofAgreement nextAgreement
  { carrier := nextCarrier
    representative := state.representative
    cumulative := by
      simpa [nextCarrier, CommittedPayloadState.ofAgreement] using
        state.cumulative }

@[simp] theorem afterCut_sourceState
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    (bodyRest : List PeTTaSpec.PrologCore.Goal)
    (bodyExecutableTail : List PLeaTTa.Goal)
    (referenceHead :
      state.carrier.index.bodyReferences = .cut :: bodyRest)
    (executableHead :
      state.carrier.index.bodyExecutables =
        .cutAt state.carrier.index.bodyBarrier :: bodyExecutableTail)
    (coherent : PLeaTTa.BarrierCacheCoherent state.carrier.index.openConf.toConf) :
    (afterCut prog gt state bodyRest bodyExecutableTail referenceHead
      executableHead coherent).carrier.sourceState =
      .running state.carrier.index.session (cutSource state bodyRest) := rfl

@[simp] theorem afterCut_fineState
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    (bodyRest : List PeTTaSpec.PrologCore.Goal)
    (bodyExecutableTail : List PLeaTTa.Goal)
    (referenceHead :
      state.carrier.index.bodyReferences = .cut :: bodyRest)
    (executableHead :
      state.carrier.index.bodyExecutables =
        .cutAt state.carrier.index.bodyBarrier :: bodyExecutableTail)
    (coherent : PLeaTTa.BarrierCacheCoherent state.carrier.index.openConf.toConf) :
    (afterCut prog gt state bodyRest bodyExecutableTail referenceHead
      executableHead coherent).carrier.fineState =
      .ready (cutOpenConf state bodyExecutableTail) := rfl

end RepresentativeActivePayloadState

/-! ## Closed transition vocabulary -/

/-- Public transition identity.  Costs and observations are functions of
this closed vocabulary; a caller cannot attach an arbitrary execution trace
to a transition label. -/
inductive TransitionKind where
  | administrative (count : Nat)
  | localCall (rejected : Nat) (request : CallRequest)
  | bodyAnswer
  | cut (token : CursorToken)
deriving Repr

namespace TransitionKind

def sourceCost : TransitionKind → Nat
  | .administrative count => count
  | .localCall rejected _ => rejected + 2
  | .bodyAnswer => 1
  | .cut _ => 1

def sourceEvents : TransitionKind → List Observation
  | .administrative _ => []
  | .localCall _ request => [.opened request]
  | .bodyAnswer => []
  | .cut token => [.pruned token]

def fineCost : TransitionKind → Nat
  | .administrative _ => 0
  | .localCall _ _ => 3
  | .bodyAnswer => 0
  | .cut _ => 1

/-- Exact payload-stack effect of one closed transition kind.  This is a
structural equation over ordered cell identities, not an arithmetic count:
administrative and body-answer steps preserve the zipper, a local call pushes
one literal cell, and a cut removes its literal head. -/
def PayloadEvolution (kind : TransitionKind)
    (before after : List PayloadCellIdentity) : Prop :=
  match kind with
  | .administrative _ => after = before
  | .localCall _ _ => ∃ head, after = head :: before
  | .bodyAnswer => after = before
  | .cut _ => ∃ head, before = head :: after

end TransitionKind

/-- A Type-valued transition whose constructors are exactly the independent
producer packages.  There is deliberately no generic constructor accepting
separate source/fine/alpha/representative proofs: such a constructor could
pair different residual orientations which happen to share endpoints. -/
inductive CertifiedTransition (prog : PLeaTTa.Prog)
    (gt : Metta.GroundingTable) :
    TransitionKind → ProductPhaseState → ProductPhaseState → Type where
  | administrative
      (before : RepresentativeActivePayloadState)
      {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
      (steps :
        AdministrativeStepsN count before.carrier.index.bodyReferences
          afterBody) :
      CertifiedTransition prog gt (.administrative count)
        (.active before)
        (.active
          (RepresentativeActivePayloadState.afterAdministrative
            prog gt before steps))
  | localCall
      {before after : RepresentativeActivePayloadState}
      {head : NestedCallHead before.carrier}
      {rejected : Nat} {skippedBranches : List ClauseBranch}
      {skippedClauses : List PLeaTTa.Clause}
      {finish : PreparedCursor} {branch : ClauseBranch}
      {clause : PLeaTTa.Clause} {branchTail : List ClauseBranch}
      {clauseTail : List PLeaTTa.Clause} {altTail : List PLeaTTa.Alt}
      {copied : PLeaTTa.Clause} {installed : Subst}
      (facts :
        RepresentativeNestedCallSuccessorFacts prog gt before head rejected
          skippedBranches skippedClauses finish branch clause branchTail
          clauseTail altTail copied installed after) :
      CertifiedTransition prog gt
        (.localCall rejected
          (requestFor head.predicate head.referencePayload
            before.carrier.index.current))
        (.active before) (.active after)
  | bodyAnswer
      (before : RepresentativeActivePayloadState)
      (referenceEmpty : before.carrier.index.bodyReferences = [])
      (executableEmpty : before.carrier.index.bodyExecutables = []) :
      CertifiedTransition prog gt .bodyAnswer (.active before)
        (.scheduled
          (RepresentativeActivePayloadState.afterBodyAnswer
            prog gt before referenceEmpty executableEmpty))
  | cut
      (before : RepresentativeActivePayloadState)
      (bodyRest : List PeTTaSpec.PrologCore.Goal)
      (bodyExecutableTail : List PLeaTTa.Goal)
      (referenceHead :
        before.carrier.index.bodyReferences = .cut :: bodyRest)
      (executableHead :
        before.carrier.index.bodyExecutables =
          .cutAt before.carrier.index.bodyBarrier :: bodyExecutableTail)
      (coherent :
        PLeaTTa.BarrierCacheCoherent before.carrier.index.openConf.toConf) :
      CertifiedTransition prog gt
        (.cut
          (retainedCursorToken before.carrier.index.opened
            before.carrier.index.finish before.carrier.index.branch
            before.carrier.index.branchTail))
        (.active before)
        (.committed
          (RepresentativeActivePayloadState.afterCut prog gt before bodyRest
            bodyExecutableTail referenceHead executableHead coherent))

namespace CertifiedTransition

/-- One independent raw step is one exact public source step. -/
theorem oneSourceStep
    {session : Session} {before after : Search}
    {events : List Observation}
    (step : RawStep session before events .none session (.running after)) :
    StepsN 1 (.running session before) events (.running session after) := by
  have publicStep :
      Transition (.running session before) events (.running session after) :=
    Transition.ordinary _ _ _ _ _ step
  simpa using
    StepsN.succ 0 (.running session before) (.running session after)
      (.running session after) events [] publicStep (.zero _)

/-- One fine transition remains one exact fine step. -/
theorem oneFineStep
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : DemandDrivenCallStep.FineConf}
    (step : DemandDrivenCallStep.Step prog gt before after) :
    DemandDrivenCallStep.StepsN prog gt 1 before after := by
  simpa using
    DemandDrivenCallStep.StepsN.succ 0 before after after step (.zero _)

/-- Every closed transition exposes its exact independent source execution. -/
theorem sourceSteps
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kind : TransitionKind} {before after : ProductPhaseState}
    (transition : CertifiedTransition prog gt kind before after) :
    StepsN kind.sourceCost before.sourceState kind.sourceEvents
      after.sourceState := by
  cases transition with
  | @administrative before count afterBody steps =>
      change StepsN count before.carrier.sourceState []
        (RepresentativeActivePayloadState.afterAdministrative
          prog gt before steps).carrier.sourceState
      rw [RepresentativeActivePayloadState.afterAdministrative_sourceState]
      simpa [ActivePayloadState.sourceState,
        RepresentativeActivePayloadState.administrativeSource] using
        (PrologCurrentSessionAdministrativeTransitionBridge.SpinedActiveProductPayloadResourceRelatesAt.afterAdministrativeSteps
          (prog := prog) (gt := gt) before.carrier.agreement steps).1
  | localCall facts =>
      simpa [TransitionKind.sourceCost, TransitionKind.sourceEvents,
        ProductPhaseState.sourceState, ActivePayloadState.sourceState] using
        facts.certificate.sourceSteps
  | bodyAnswer before referenceEmpty executableEmpty =>
      have activeAgreement :
          SpinedActiveProductPayloadResourceRelatesAt
            before.carrier.index.freshFrontier before.carrier.index.alpha
            before.carrier.index.support before.carrier.index.canonical
            before.carrier.index.referenceBase before.carrier.index.opened
            before.carrier.index.session before.carrier.index.pending
            before.carrier.index.finish before.carrier.index.branch
            before.carrier.index.branchTail before.carrier.index.altTail
            before.carrier.index.bodyBarrier before.carrier.index.callerBarrier
            [] [] before.carrier.index.callerReferences
            before.carrier.index.callerExecutables before.carrier.index.outer
            before.carrier.index.current before.carrier.index.runtime
            before.carrier.index.qterm before.carrier.index.active
            before.carrier.index.resources before.carrier.index.callerScope
            before.carrier.index.outerScope before.carrier.index.context
            before.carrier.index.baseAlts before.carrier.index.source
            before.carrier.index.openConf before.carrier.payloadContext := by
        simpa only [ActivePayloadIndex.Relates, referenceEmpty,
          executableEmpty] using before.carrier.agreement
      have raw :=
        (PrologCurrentSessionPayloadTransitionBridge.SpinedActiveProductPayloadResourceRelatesAt.afterBodyAnswer
          (prog := prog) (gt := gt) activeAgreement).1
      simpa [TransitionKind.sourceCost, TransitionKind.sourceEvents,
        ProductPhaseState.sourceState, ActivePayloadState.sourceState,
        RepresentativeActivePayloadState.bodyAnswerSource] using
        oneSourceStep raw
  | cut before bodyRest bodyExecutableTail referenceHead executableHead
      coherent =>
      have activeAgreement :
          SpinedActiveProductPayloadResourceRelatesAt
            before.carrier.index.freshFrontier before.carrier.index.alpha
            before.carrier.index.support before.carrier.index.canonical
            before.carrier.index.referenceBase before.carrier.index.opened
            before.carrier.index.session before.carrier.index.pending
            before.carrier.index.finish before.carrier.index.branch
            before.carrier.index.branchTail before.carrier.index.altTail
            before.carrier.index.bodyBarrier before.carrier.index.callerBarrier
            (.cut :: bodyRest)
            (.cutAt before.carrier.index.bodyBarrier :: bodyExecutableTail)
            before.carrier.index.callerReferences
            before.carrier.index.callerExecutables before.carrier.index.outer
            before.carrier.index.current before.carrier.index.runtime
            before.carrier.index.qterm before.carrier.index.active
            before.carrier.index.resources before.carrier.index.callerScope
            before.carrier.index.outerScope before.carrier.index.context
            before.carrier.index.baseAlts before.carrier.index.source
            before.carrier.index.openConf before.carrier.payloadContext := by
        simpa only [ActivePayloadIndex.Relates, referenceHead, executableHead]
          using before.carrier.agreement
      have raw :=
        (PrologCurrentSessionPayloadTransitionBridge.SpinedActiveProductPayloadResourceRelatesAt.afterCut
          (prog := prog) (gt := gt) activeAgreement coherent).2.1
      simpa [TransitionKind.sourceCost, TransitionKind.sourceEvents,
        ProductPhaseState.sourceState, ActivePayloadState.sourceState,
        RepresentativeActivePayloadState.cutSource] using oneSourceStep raw

/-- Every closed transition exposes its exact fine executable execution. -/
theorem fineSteps
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kind : TransitionKind} {before after : ProductPhaseState}
    (transition : CertifiedTransition prog gt kind before after) :
    DemandDrivenCallStep.StepsN prog gt kind.fineCost before.fineState
      after.fineState := by
  cases transition with
  | administrative before steps =>
      change DemandDrivenCallStep.StepsN prog gt 0 before.carrier.fineState
        (RepresentativeActivePayloadState.afterAdministrative
          prog gt before steps).carrier.fineState
      rw [RepresentativeActivePayloadState.afterAdministrative_fineState]
      exact
        (PrologCurrentSessionAdministrativeTransitionBridge.SpinedActiveProductPayloadResourceRelatesAt.afterAdministrativeSteps
          (prog := prog) (gt := gt) before.carrier.agreement steps).2.1
  | localCall facts =>
      simpa [TransitionKind.fineCost, ProductPhaseState.fineState,
        ActivePayloadState.fineState] using
        facts.certificate.fineSteps
  | bodyAnswer before referenceEmpty executableEmpty =>
      change DemandDrivenCallStep.StepsN prog gt 0 before.carrier.fineState
        (RepresentativeActivePayloadState.afterBodyAnswer prog gt before
          referenceEmpty executableEmpty).carrier.fineState
      rw [RepresentativeActivePayloadState.afterBodyAnswer_fineState]
      exact DemandDrivenCallStep.StepsN.zero before.carrier.fineState
  | cut before bodyRest bodyExecutableTail referenceHead executableHead
      coherent =>
      have activeAgreement :
          SpinedActiveProductPayloadResourceRelatesAt
            before.carrier.index.freshFrontier before.carrier.index.alpha
            before.carrier.index.support before.carrier.index.canonical
            before.carrier.index.referenceBase before.carrier.index.opened
            before.carrier.index.session before.carrier.index.pending
            before.carrier.index.finish before.carrier.index.branch
            before.carrier.index.branchTail before.carrier.index.altTail
            before.carrier.index.bodyBarrier before.carrier.index.callerBarrier
            (.cut :: bodyRest)
            (.cutAt before.carrier.index.bodyBarrier :: bodyExecutableTail)
            before.carrier.index.callerReferences
            before.carrier.index.callerExecutables before.carrier.index.outer
            before.carrier.index.current before.carrier.index.runtime
            before.carrier.index.qterm before.carrier.index.active
            before.carrier.index.resources before.carrier.index.callerScope
            before.carrier.index.outerScope before.carrier.index.context
            before.carrier.index.baseAlts before.carrier.index.source
            before.carrier.index.openConf before.carrier.payloadContext := by
        simpa only [ActivePayloadIndex.Relates, referenceHead, executableHead]
          using before.carrier.agreement
      have fine :=
        (PrologCurrentSessionPayloadTransitionBridge.SpinedActiveProductPayloadResourceRelatesAt.afterCut
          (prog := prog) (gt := gt) activeAgreement coherent).2.2.1
      change DemandDrivenCallStep.StepsN prog gt 1 before.carrier.fineState
        (RepresentativeActivePayloadState.afterCut prog gt before bodyRest
          bodyExecutableTail referenceHead executableHead coherent).carrier.fineState
      rw [RepresentativeActivePayloadState.afterCut_fineState]
      simpa [ActivePayloadState.fineState,
        RepresentativeActivePayloadState.cutOpenConf] using oneFineStep fine

/-- Every closed heterogeneous transition advances all four independent
source allocator high-waters. -/
theorem sessionHighWaters
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kind : TransitionKind} {before after : ProductPhaseState}
    (transition : CertifiedTransition prog gt kind before after) :
    SessionHighWatersExtend before.session after.session := by
  cases transition with
  | administrative before steps =>
      exact SessionHighWatersExtend.refl before.carrier.index.session
  | localCall facts =>
      simpa [ProductPhaseState.session] using
        (RepresentativeNestedCallSuccessorFacts.sessionHighWaters facts)
  | bodyAnswer before referenceEmpty executableEmpty =>
      exact SessionHighWatersExtend.refl before.carrier.index.session
  | cut before bodyRest bodyExecutableTail referenceHead executableHead
      coherent =>
      exact SessionHighWatersExtend.refl before.carrier.index.session

/-- Every closed heterogeneous transition advances the independent
executable fresh-name counter. -/
theorem executableCounter_mono
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kind : TransitionKind} {before after : ProductPhaseState}
    (transition : CertifiedTransition prog gt kind before after) :
    before.openConf.persistent.counter ≤ after.openConf.persistent.counter := by
  cases transition with
  | administrative before steps => exact Nat.le_refl _
  | localCall facts =>
      simpa [ProductPhaseState.openConf] using
        (RepresentativeNestedCallSuccessorFacts.executableCounter_mono facts)
  | bodyAnswer before referenceEmpty executableEmpty => exact Nat.le_refl _
  | cut before bodyRest bodyExecutableTail referenceHead executableHead
      coherent =>
      exact Nat.le_refl _

/-- Alpha chronology is expressed above the actual incoming source and
executable high-waters.  A nested call weakens its selected-clause extension
back to those incoming floors; every other closed transition is the exact
empty-suffix extension. -/
theorem alphaExtension
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kind : TransitionKind} {before after : ProductPhaseState}
    (transition : CertifiedTransition prog gt kind before after) :
    AlphaExtendsAbove before.alpha after.alpha
      before.session.resolver.nextFresh before.openConf.persistent.counter := by
  cases transition with
  | administrative before steps =>
      exact AlphaExtendsAbove.refl before.carrier.index.alpha _ _
  | localCall facts =>
      simpa [ProductPhaseState.alpha, ProductPhaseState.session,
        ProductPhaseState.openConf, OpenConf.toConf, Control.toConf] using
        facts.alphaExtension.weaken
          (RepresentativeNestedCallSuccessorFacts.sourceFresh_le_selected facts)
          (Nat.le_refl _)
  | bodyAnswer before referenceEmpty executableEmpty =>
      exact AlphaExtendsAbove.refl before.carrier.index.alpha _ _
  | cut before bodyRest bodyExecutableTail referenceHead executableHead
      coherent =>
      exact AlphaExtendsAbove.refl before.carrier.index.alpha _ _

/-- The cumulative residual representative is extended only by prepending a
new local-call MGU.  Phase-only transitions use the empty extension. -/
theorem representativeExtension
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kind : TransitionKind} {before after : ProductPhaseState}
    (transition : CertifiedTransition prog gt kind before after) :
    ∃ extension : TreeSubstitution,
      after.representative = extension ++ before.representative := by
  cases transition with
  | administrative before steps => exact ⟨[], rfl⟩
  | localCall facts =>
      simpa [ProductPhaseState.representative] using
        facts.representativeExtension
  | bodyAnswer before referenceEmpty executableEmpty => exact ⟨[], rfl⟩
  | cut before bodyRest bodyExecutableTail referenceHead executableHead
      coherent =>
      exact ⟨[], rfl⟩

/-- One transition has exactly the payload-stack effect prescribed by its
closed kind.  In particular, cut exposes the literal dependent zipper tail;
it is not justified through a weaker cell-count inequality. -/
theorem payloadEvolution
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kind : TransitionKind} {before after : ProductPhaseState}
    (transition : CertifiedTransition prog gt kind before after) :
    kind.PayloadEvolution before.cellIdentities after.cellIdentities := by
  cases transition with
  | administrative before steps => rfl
  | localCall facts =>
      simpa [TransitionKind.PayloadEvolution,
        ProductPhaseState.cellIdentities] using facts.certificate.payloadCells
  | bodyAnswer before referenceEmpty executableEmpty => rfl
  | cut before bodyRest bodyExecutableTail referenceHead executableHead
      coherent =>
      refine
        ⟨PLeaTTa.PrologHeterogeneousPrefixBridge.ActivePayloadState.headCell
            before.carrier,
          ?_⟩
      calc
        before.carrier.cellIdentities =
            PLeaTTa.PrologHeterogeneousPrefixBridge.ActivePayloadState.headCell
                before.carrier ::
              SourceControlResourcePayloadContextAgrees.cellIdentities
                (ActiveProductPayloadContext.outerPayload
                  before.carrier.payloadContext) :=
          PLeaTTa.PrologHeterogeneousPrefixBridge.ActivePayloadState.cellIdentities_eq_headCell_cons_outerPayload
            before.carrier
        _ =
            PLeaTTa.PrologHeterogeneousPrefixBridge.ActivePayloadState.headCell
                before.carrier ::
              (RepresentativeActivePayloadState.afterCut prog gt before
                bodyRest bodyExecutableTail referenceHead executableHead
                coherent).carrier.cellIdentities := rfl

end CertifiedTransition

/-! ## Exact heterogeneous prefixes -/

namespace TransitionSchedule

/-- Exact number of independent source transitions in a heterogeneous
schedule. -/
def sourceCost : List TransitionKind → Nat
  | [] => 0
  | kind :: kinds => kind.sourceCost + sourceCost kinds

/-- Exact public source observations in chronological order. -/
def sourceEvents : List TransitionKind → List Observation
  | [] => []
  | kind :: kinds => kind.sourceEvents ++ sourceEvents kinds

/-- Exact number of fine executable transitions in a heterogeneous schedule. -/
def fineCost : List TransitionKind → Nat
  | [] => 0
  | kind :: kinds => kind.fineCost + fineCost kinds

@[simp] theorem sourceCost_append (left right : List TransitionKind) :
    sourceCost (left ++ right) = sourceCost left + sourceCost right := by
  induction left with
  | nil => simp [sourceCost]
  | cons kind kinds ih =>
      simp only [List.cons_append, sourceCost, ih, Nat.add_assoc]

@[simp] theorem sourceEvents_append (left right : List TransitionKind) :
    sourceEvents (left ++ right) =
      sourceEvents left ++ sourceEvents right := by
  induction left with
  | nil => rfl
  | cons kind kinds ih =>
      simp only [List.cons_append, sourceEvents, ih, List.append_assoc]

@[simp] theorem fineCost_append (left right : List TransitionKind) :
    fineCost (left ++ right) = fineCost left + fineCost right := by
  induction left with
  | nil => simp [fineCost]
  | cons kind kinds ih =>
      simp only [List.cons_append, fineCost, ih, Nat.add_assoc]

end TransitionSchedule

/-- A proof-relevant heterogeneous prefix.  The shared `middle` is a literal
Type index of both the head transition and the tail prefix, so two compatible-
looking but independently chosen residual orientations cannot be paired. -/
inductive CertifiedPrefix (prog : PLeaTTa.Prog)
    (gt : Metta.GroundingTable) :
    List TransitionKind → ProductPhaseState → ProductPhaseState → Type where
  | nil (state : ProductPhaseState) : CertifiedPrefix prog gt [] state state
  | cons
      {kind : TransitionKind} {kinds : List TransitionKind}
      {before middle after : ProductPhaseState}
      (head : CertifiedTransition prog gt kind before middle)
      (tail : CertifiedPrefix prog gt kinds middle after) :
      CertifiedPrefix prog gt (kind :: kinds) before after

namespace CertifiedPrefix

/-- Exact independent source execution of a heterogeneous prefix. -/
theorem sourceSteps
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List TransitionKind} {before after : ProductPhaseState}
    (run : CertifiedPrefix prog gt kinds before after) :
    StepsN (TransitionSchedule.sourceCost kinds) before.sourceState
      (TransitionSchedule.sourceEvents kinds) after.sourceState := by
  induction run with
  | nil state => exact StepsN.zero state.sourceState
  | cons head tail ih =>
      simpa [TransitionSchedule.sourceCost, TransitionSchedule.sourceEvents]
        using StepsN.trans head.sourceSteps ih

/-- Exact fine executable execution of the same heterogeneous prefix. -/
theorem fineSteps
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List TransitionKind} {before after : ProductPhaseState}
    (run : CertifiedPrefix prog gt kinds before after) :
    DemandDrivenCallStep.StepsN prog gt
      (TransitionSchedule.fineCost kinds) before.fineState after.fineState := by
  induction run with
  | nil state => exact DemandDrivenCallStep.StepsN.zero state.fineState
  | cons head tail ih =>
      simpa [TransitionSchedule.fineCost] using
        DemandDrivenCallStep.StepsN.trans head.fineSteps ih

/-- Extract every literal phase state in chronological order.  This is data,
not an existential assertion that intermediate states happen to exist. -/
def states
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List TransitionKind} {before after : ProductPhaseState} :
    CertifiedPrefix prog gt kinds before after → List ProductPhaseState
  | .nil state => [state]
  | .cons head tail => before :: states tail

@[simp] theorem states_length
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List TransitionKind} {before after : ProductPhaseState}
    (run : CertifiedPrefix prog gt kinds before after) :
    run.states.length = kinds.length + 1 := by
  induction run with
  | nil state => rfl
  | cons head tail ih =>
      simp only [states, List.length_cons, List.length, ih]

/-- Concatenate two prefixes only when they share the same literal middle
state. -/
def append
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {leftKinds rightKinds : List TransitionKind}
    {before middle after : ProductPhaseState}
    (left : CertifiedPrefix prog gt leftKinds before middle)
    (right : CertifiedPrefix prog gt rightKinds middle after) :
    CertifiedPrefix prog gt (leftKinds ++ rightKinds) before after :=
  match left with
  | .nil _ => right
  | .cons head tail => .cons head (append tail right)

/-- Split at a requested kind-prefix and return the literal shared phase state
as Type data.  No endpoint equality or compatibility proposition substitutes
for this state. -/
def split
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (leftKinds rightKinds : List TransitionKind)
    {before after : ProductPhaseState}
    (run :
      CertifiedPrefix prog gt (leftKinds ++ rightKinds) before after) :
    Σ middle : ProductPhaseState,
      CertifiedPrefix prog gt leftKinds before middle ×
        CertifiedPrefix prog gt rightKinds middle after := by
  induction leftKinds generalizing before with
  | nil =>
      exact ⟨before, .nil before, run⟩
  | cons kind kinds ih =>
      cases run with
      | cons head tail =>
          obtain ⟨middle, left, right⟩ := ih tail
          exact ⟨middle, .cons head left, right⟩

/-- Splitting an appended prefix returns a genuine decomposition through some
literal middle state. -/
theorem exists_split_of_append
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {leftKinds rightKinds : List TransitionKind}
    {before after : ProductPhaseState}
    (run :
      CertifiedPrefix prog gt (leftKinds ++ rightKinds) before after) :
    ∃ middle : ProductPhaseState,
      Nonempty (CertifiedPrefix prog gt leftKinds before middle) ∧
        Nonempty (CertifiedPrefix prog gt rightKinds middle after) := by
  let result := split leftKinds rightKinds run
  exact ⟨result.1, ⟨result.2.1⟩, ⟨result.2.2⟩⟩

end CertifiedPrefix

end PLeaTTa.PrologHeterogeneousPrefixBridge
