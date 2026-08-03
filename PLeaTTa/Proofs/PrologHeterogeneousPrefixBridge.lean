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
import PLeaTTa.Proofs.PrologCurrentSessionUnifyTransitionBridge
import PLeaTTa.Proofs.PrologPersistentFreeActivePayloadBridge
import PLeaTTa.Proofs.PrologPersistentFreeScheduledPayloadBridge

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
open PrologCurrentSessionUnifyTransitionBridge
open PrologMguComposition
open PrologPersistentFreeActivePayloadBridge
open PrologPersistentFreeScheduledPayloadBridge
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

/-- The scheduled task payload selected by the carrier's literal active
control.  Centralizing the conjunction traversal here keeps downstream
observation proofs independent of the internal readiness-product layout. -/
def headPayload (state : ScheduledPayloadState) :=
  state.agreement.core.control.ready.2.2.2.headPayload

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

namespace PersistentFreeScheduledPayloadState

/-- Erase the two historical call-entry packets from a legacy scheduled
carrier while preserving every literal live endpoint and payload identity. -/
def ofLegacy (state : ScheduledPayloadState) :
    PersistentFreeScheduledPayloadState :=
  { index :=
      { freshFrontier := state.index.freshFrontier
        alpha := state.index.alpha
        support := state.index.support
        canonical := state.index.canonical
        referenceBase := state.index.referenceBase
        predicateScope := state.index.opened.scope
        session := state.index.session
        finish := state.index.finish
        branch := state.index.branch
        branchTail := state.index.branchTail
        altTail := state.index.altTail
        bodyBarrier := state.index.bodyBarrier
        callerBarrier := state.index.callerBarrier
        callerReferences := state.index.callerReferences
        callerExecutables := state.index.callerExecutables
        outer := state.index.outer
        current := state.index.current
        runtime := state.index.runtime
        qterm := state.index.qterm
        active := state.index.active
        resources := state.index.resources
        callerScope := state.index.callerScope
        outerScope := state.index.outerScope
        context := state.index.context
        baseAlts := state.index.baseAlts
        source := state.index.source
        openConf := state.index.openConf }
    payloadContext := state.payloadContext
    agreement :=
      PersistentFreeScheduledProductPayloadResourceRelatesAt.ofLegacy
        state.agreement }

@[simp] theorem ofLegacy_sourceState (state : ScheduledPayloadState) :
    (ofLegacy state).sourceState = state.sourceState := rfl

@[simp] theorem ofLegacy_fineState (state : ScheduledPayloadState) :
    (ofLegacy state).fineState = state.fineState := rfl

@[simp] theorem ofLegacy_session (state : ScheduledPayloadState) :
    (ofLegacy state).index.session = state.index.session := rfl

@[simp] theorem ofLegacy_openConf (state : ScheduledPayloadState) :
    (ofLegacy state).index.openConf = state.index.openConf := rfl

@[simp] theorem ofLegacy_alpha (state : ScheduledPayloadState) :
    (ofLegacy state).index.alpha = state.index.alpha := rfl

@[simp] theorem ofLegacy_baseAlts (state : ScheduledPayloadState) :
    (ofLegacy state).index.baseAlts = state.index.baseAlts := rfl

@[simp] theorem ofLegacy_predicateScope (state : ScheduledPayloadState) :
    (ofLegacy state).index.predicateScope = state.index.opened.scope := rfl

@[simp] theorem ofLegacy_cellIdentities (state : ScheduledPayloadState) :
    (ofLegacy state).cellIdentities = state.cellIdentities := rfl

@[simp] theorem ofLegacy_cellCount (state : ScheduledPayloadState) :
    (ofLegacy state).cellCount = state.cellCount := rfl

end PersistentFreeScheduledPayloadState

namespace RepresentativePersistentFreeScheduledPayloadState

/-- Legacy representative carriers embed without changing their source/fine
endpoints, residual orientation, or retained payload spine. -/
def ofLegacy (state : RepresentativeScheduledPayloadState) :
    RepresentativePersistentFreeScheduledPayloadState :=
  { carrier := PersistentFreeScheduledPayloadState.ofLegacy state.carrier
    representative := state.representative
    cumulative := by
      simpa [PersistentFreeScheduledPayloadState.ofLegacy] using
        state.cumulative }

@[simp] theorem ofLegacy_sourceState
    (state : RepresentativeScheduledPayloadState) :
    (ofLegacy state).carrier.sourceState = state.carrier.sourceState := by
  simp [ofLegacy]

@[simp] theorem ofLegacy_fineState
    (state : RepresentativeScheduledPayloadState) :
    (ofLegacy state).carrier.fineState = state.carrier.fineState := by
  simp [ofLegacy]

@[simp] theorem ofLegacy_session
    (state : RepresentativeScheduledPayloadState) :
    (ofLegacy state).carrier.index.session = state.carrier.index.session := rfl

@[simp] theorem ofLegacy_openConf
    (state : RepresentativeScheduledPayloadState) :
    (ofLegacy state).carrier.index.openConf =
      state.carrier.index.openConf := rfl

@[simp] theorem ofLegacy_alpha
    (state : RepresentativeScheduledPayloadState) :
    (ofLegacy state).carrier.index.alpha = state.carrier.index.alpha := rfl

@[simp] theorem ofLegacy_baseAlts
    (state : RepresentativeScheduledPayloadState) :
    (ofLegacy state).carrier.index.baseAlts = state.carrier.index.baseAlts := rfl

@[simp] theorem ofLegacy_cellIdentities
    (state : RepresentativeScheduledPayloadState) :
    (ofLegacy state).carrier.cellIdentities =
      state.carrier.cellIdentities := rfl

@[simp] theorem ofLegacy_cellCount
    (state : RepresentativeScheduledPayloadState) :
    (ofLegacy state).carrier.cellCount = state.carrier.cellCount := rfl

@[simp] theorem ofLegacy_representative
    (state : RepresentativeScheduledPayloadState) :
    (ofLegacy state).representative = state.representative := rfl

end RepresentativePersistentFreeScheduledPayloadState

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
  | active (state : RepresentativePersistentFreeActivePayloadState)
  | scheduled (state : RepresentativePersistentFreeScheduledPayloadState)
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

/-- Literal executable alternative suffix below every locally owned resource
region.  Keeping this projection in the phase vocabulary lets rooted closure
flow through the same proof-relevant transition path as the source and fine
states. -/
def baseAlts : ProductPhaseState → List PLeaTTa.Alt
  | .active state => state.carrier.index.baseAlts
  | .scheduled state => state.carrier.index.baseAlts
  | .committed state => state.carrier.index.baseAlts

/-- A locally rooted phase has no unowned executable alternative below its
complete resource zipper. -/
def RootClosed (state : ProductPhaseState) : Prop :=
  state.baseAlts = []

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
      activationOrdered := oldAgreement.activationOrdered
      activationOrigins := oldAgreement.activationOrigins
      controlOrigins := oldAgreement.controlOrigins }
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

/-- Source-only administration preserves the literal fine open state. -/
@[simp] theorem afterAdministrative_openConf
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    (afterAdministrative prog gt state steps).carrier.index.openConf =
      state.carrier.index.openConf := rfl

/-- Source-only administration preserves the observable query spelling. -/
@[simp] theorem afterAdministrative_qterm
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    (afterAdministrative prog gt state steps).carrier.index.qterm =
      state.carrier.index.qterm := rfl

/-- Source-only administration preserves the cumulative source binding. -/
@[simp] theorem afterAdministrative_current
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    (afterAdministrative prog gt state steps).carrier.index.current =
      state.carrier.index.current := rfl

/-- Source-only administration preserves the executable substitution. -/
@[simp] theorem afterAdministrative_runtime
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    (afterAdministrative prog gt state steps).carrier.index.runtime =
      state.carrier.index.runtime := rfl

/-- Source-only administration preserves the caller continuation literally. -/
@[simp] theorem afterAdministrative_callerReferences
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    (afterAdministrative prog gt state steps).carrier.index.callerReferences =
      state.carrier.index.callerReferences := rfl

/-- Source-only administration preserves every older control segment. -/
@[simp] theorem afterAdministrative_outer
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    (afterAdministrative prog gt state steps).carrier.index.outer =
      state.carrier.index.outer := rfl

/-- Source-only administration neither consumes nor manufactures an older
executable alternative. -/
@[simp] theorem afterAdministrative_baseAlts
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    (afterAdministrative prog gt state steps).carrier.index.baseAlts =
      state.carrier.index.baseAlts := rfl

/-- Source-only administration preserves the selected call's retained
alternative resource. -/
@[simp] theorem afterAdministrative_active
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    (afterAdministrative prog gt state steps).carrier.index.active =
      state.carrier.index.active := rfl

/-- Source-only administration preserves the already-owned outer resources. -/
@[simp] theorem afterAdministrative_resources
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody) :
    (afterAdministrative prog gt state steps).carrier.index.resources =
      state.carrier.index.resources := rfl

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

/-- Body success changes phase but preserves the literal fine open state. -/
@[simp] theorem afterBodyAnswer_openConf
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    (referenceEmpty : state.carrier.index.bodyReferences = [])
    (executableEmpty : state.carrier.index.bodyExecutables = []) :
    (afterBodyAnswer prog gt state referenceEmpty
        executableEmpty).carrier.index.openConf =
      state.carrier.index.openConf := rfl

/-- Body success preserves the observable query spelling. -/
@[simp] theorem afterBodyAnswer_qterm
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    (referenceEmpty : state.carrier.index.bodyReferences = [])
    (executableEmpty : state.carrier.index.bodyExecutables = []) :
    (afterBodyAnswer prog gt state referenceEmpty
        executableEmpty).carrier.index.qterm =
      state.carrier.index.qterm := rfl

/-- Body success preserves the cumulative source binding. -/
@[simp] theorem afterBodyAnswer_current
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    (referenceEmpty : state.carrier.index.bodyReferences = [])
    (executableEmpty : state.carrier.index.bodyExecutables = []) :
    (afterBodyAnswer prog gt state referenceEmpty
        executableEmpty).carrier.index.current =
      state.carrier.index.current := rfl

/-- Body success preserves the executable substitution. -/
@[simp] theorem afterBodyAnswer_runtime
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    (referenceEmpty : state.carrier.index.bodyReferences = [])
    (executableEmpty : state.carrier.index.bodyExecutables = []) :
    (afterBodyAnswer prog gt state referenceEmpty
        executableEmpty).carrier.index.runtime =
      state.carrier.index.runtime := rfl

/-- Completing the selected body preserves the literal caller continuation. -/
@[simp] theorem afterBodyAnswer_callerReferences
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    (referenceEmpty : state.carrier.index.bodyReferences = [])
    (executableEmpty : state.carrier.index.bodyExecutables = []) :
    (afterBodyAnswer prog gt state referenceEmpty executableEmpty).carrier.index.callerReferences =
      state.carrier.index.callerReferences := rfl

/-- Completing the selected body preserves the literal older control spine. -/
@[simp] theorem afterBodyAnswer_outer
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    (referenceEmpty : state.carrier.index.bodyReferences = [])
    (executableEmpty : state.carrier.index.bodyExecutables = []) :
    (afterBodyAnswer prog gt state referenceEmpty executableEmpty).carrier.index.outer =
      state.carrier.index.outer := rfl

/-- Completing the selected body preserves the rooted executable suffix. -/
@[simp] theorem afterBodyAnswer_baseAlts
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    (referenceEmpty : state.carrier.index.bodyReferences = [])
    (executableEmpty : state.carrier.index.bodyExecutables = []) :
    (afterBodyAnswer prog gt state referenceEmpty executableEmpty).carrier.index.baseAlts =
      state.carrier.index.baseAlts := rfl

/-- Completing the selected body preserves its retained sibling resource. -/
@[simp] theorem afterBodyAnswer_active
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    (referenceEmpty : state.carrier.index.bodyReferences = [])
    (executableEmpty : state.carrier.index.bodyExecutables = []) :
    (afterBodyAnswer prog gt state referenceEmpty
      executableEmpty).carrier.index.active =
        state.carrier.index.active := rfl

/-- Completing the selected body preserves every older owned resource. -/
@[simp] theorem afterBodyAnswer_resources
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativeActivePayloadState)
    (referenceEmpty : state.carrier.index.bodyReferences = [])
    (executableEmpty : state.carrier.index.bodyExecutables = []) :
    (afterBodyAnswer prog gt state referenceEmpty
      executableEmpty).carrier.index.resources =
        state.carrier.index.resources := rfl

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

/-! ## Selected primitive-unification successor -/

namespace RepresentativeActivePayloadState

/-- Source predecessor obtained by prepending one primitive equality to the
active clause body. -/
def unifyPredecessorSource
    (state : RepresentativeActivePayloadState) (left right : Term) : Search :=
  ActiveProductContext.plug state.carrier.index.context
    (activeSourceProduct state.carrier.index.callerScope
      state.carrier.index.opened state.carrier.index.finish
      state.carrier.index.branch state.carrier.index.branchTail
      state.carrier.index.current
      (.unify left right :: state.carrier.index.bodyReferences)
      state.carrier.index.callerReferences)

/-- Reflexive source predecessor retained as a compatibility specialization. -/
def reflexiveUnifyPredecessorSource
    (state : RepresentativeActivePayloadState) (term : Term) : Search :=
  unifyPredecessorSource state term term

/-- Fine predecessor with the matching executable equality at the literal
leftmost control position. -/
def unifyPredecessorOpenConf
    (state : RepresentativeActivePayloadState)
    (left right : Atom) : OpenConf :=
  { state.carrier.index.openConf with
    control :=
      { state.carrier.index.openConf.control with
        cur :=
          some
            (.eq left right ::
              (state.carrier.index.bodyExecutables ++
                (state.carrier.index.callerExecutables ++
                  flattenExecutables state.carrier.index.outer)),
              state.carrier.index.runtime) } }

/-- Reflexive fine predecessor retained as a compatibility specialization. -/
def reflexiveUnifyPredecessorOpenConf
    (state : RepresentativeActivePayloadState) (atom : Atom) : OpenConf :=
  unifyPredecessorOpenConf state atom atom

/-- Prepend one source/executable primitive equality to both exact lanes
without changing the selected representative or any
persistent/resource/payload datum. -/
def beforeUnify
    (state : RepresentativeActivePayloadState)
    (left right : Term) (executableLeft executableRight : Atom)
    (leftReading :
      AlphaTermAgrees state.carrier.index.alpha left executableLeft)
    (rightReading :
      AlphaTermAgrees state.carrier.index.alpha right executableRight) :
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
           references := .unify left right :: state.carrier.index.bodyReferences
           executables :=
             .eq executableLeft executableRight ::
               state.carrier.index.bodyExecutables } ::
         { barrier := state.carrier.index.callerBarrier
           references := state.carrier.index.callerReferences
           executables := state.carrier.index.callerExecutables } ::
         state.carrier.index.outer) :=
    { data := oldPayload.data
      control :=
        .cons
          (.cons (.unify leftReading rightReading) oldPayload.control.head)
          oldPayload.control.tail }
  let nextOpen :=
    unifyPredecessorOpenConf state executableLeft executableRight
  let nextReady :
      SpinedReadyTaskRelates state.carrier.index.freshFrontier
        state.carrier.index.alpha state.carrier.index.support
        state.carrier.index.canonical state.carrier.index.referenceBase
        state.carrier.index.session state.carrier.index.current
        state.carrier.index.runtime state.carrier.index.qterm
        ({ barrier := state.carrier.index.bodyBarrier
           references := .unify left right :: state.carrier.index.bodyReferences
           executables :=
             .eq executableLeft executableRight ::
               state.carrier.index.bodyExecutables } ::
         { barrier := state.carrier.index.callerBarrier
           references := state.carrier.index.callerReferences
           executables := state.carrier.index.callerExecutables } ::
         state.carrier.index.outer)
        nextOpen :=
    ⟨by
      simpa [nextOpen, unifyPredecessorOpenConf] using oldReady.1,
      by simp [nextOpen, unifyPredecessorOpenConf,
        flattenExecutables, ControlSegment.executableGoals],
      by
        simpa [nextOpen, unifyPredecessorOpenConf] using
          oldReady.2.2.1,
      nextPayload⟩
  let nextControl :
      SpinedActiveProductRelatesAt state.carrier.index.freshFrontier
        state.carrier.index.alpha state.carrier.index.support
        state.carrier.index.canonical state.carrier.index.referenceBase
        state.carrier.index.opened state.carrier.index.session
        state.carrier.index.pending state.carrier.index.finish
        state.carrier.index.branch state.carrier.index.branchTail
        state.carrier.index.altTail state.carrier.index.bodyBarrier
        state.carrier.index.callerBarrier
        (.unify left right :: state.carrier.index.bodyReferences)
        (.eq executableLeft executableRight ::
          state.carrier.index.bodyExecutables)
        state.carrier.index.callerReferences
        state.carrier.index.callerExecutables state.carrier.index.outer
        state.carrier.index.current state.carrier.index.runtime
        state.carrier.index.qterm nextOpen :=
    { ready := nextReady
      sessionAdvanced := oldControl.sessionAdvanced
      retainedAlts := by
        simpa [nextOpen, unifyPredecessorOpenConf] using
          oldControl.retainedAlts
      retainedAltsZero := oldControl.retainedAltsZero
      retainedBarriers := by
        simpa [nextOpen, unifyPredecessorOpenConf] using
          oldControl.retainedBarriers
      bodyBarrierTag := oldControl.bodyBarrierTag
      frames := by
        simpa [nextOpen, unifyPredecessorOpenConf] using
          oldControl.frames }
  let nextCore :
      SpinedActiveProductResourceRelatesAt
        state.carrier.index.freshFrontier state.carrier.index.alpha
        state.carrier.index.support state.carrier.index.canonical
        state.carrier.index.referenceBase state.carrier.index.opened
        state.carrier.index.session state.carrier.index.pending
        state.carrier.index.finish state.carrier.index.branch
        state.carrier.index.branchTail state.carrier.index.altTail
        state.carrier.index.bodyBarrier state.carrier.index.callerBarrier
        (.unify left right :: state.carrier.index.bodyReferences)
        (.eq executableLeft executableRight ::
          state.carrier.index.bodyExecutables)
        state.carrier.index.callerReferences
        state.carrier.index.callerExecutables state.carrier.index.outer
        state.carrier.index.current state.carrier.index.runtime
        state.carrier.index.qterm state.carrier.index.active
        state.carrier.index.resources state.carrier.index.callerScope
        state.carrier.index.outerScope state.carrier.index.context
        state.carrier.index.baseAlts
        (unifyPredecessorSource state left right) nextOpen :=
    { control := nextControl
      resourceStack := by
        rcases oldAgreement.core.resourceStack with
          ⟨activeRest, activeQuery, activeBarrier, activeAlts,
            activeFinalCounter, activeOwnership, outerAlignment,
            suspendedOuterAlts, actualAlts⟩
        exact
          ⟨activeRest, activeQuery, activeBarrier, activeAlts,
            activeFinalCounter, activeOwnership, outerAlignment,
            suspendedOuterAlts, by
              simpa [nextOpen, unifyPredecessorOpenConf] using
                actualAlts⟩
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
        (.unify left right :: state.carrier.index.bodyReferences)
        (.eq executableLeft executableRight ::
          state.carrier.index.bodyExecutables)
        state.carrier.index.callerReferences
        state.carrier.index.callerExecutables state.carrier.index.outer
        state.carrier.index.current state.carrier.index.runtime
        state.carrier.index.qterm state.carrier.index.active
        state.carrier.index.resources state.carrier.index.callerScope
        state.carrier.index.outerScope state.carrier.index.context
        state.carrier.index.baseAlts
        (unifyPredecessorSource state left right) nextOpen
        state.carrier.payloadContext :=
    { core := nextCore
      endpointsCurrent := by
        simpa [nextOpen, unifyPredecessorOpenConf] using
          oldAgreement.endpointsCurrent
      activationOrdered := oldAgreement.activationOrdered
      activationOrigins := oldAgreement.activationOrigins
      controlOrigins := by
        simpa [nextOpen, unifyPredecessorOpenConf] using
          oldAgreement.controlOrigins }
  let nextCarrier := ActivePayloadState.ofAgreement nextAgreement
  { carrier := nextCarrier
    representative := state.representative
    cumulative := by
      simpa [nextCarrier, ActivePayloadState.ofAgreement] using
        state.cumulative }

/-- Prepend a reflexive equality to both exact lanes without changing the
selected representative or any persistent/resource/payload datum. -/
def beforeReflexiveUnify
    (state : RepresentativeActivePayloadState) (term : Term) (atom : Atom)
    (reading : AlphaTermAgrees state.carrier.index.alpha term atom) :
    RepresentativeActivePayloadState :=
  beforeUnify state term term atom atom reading reading

/-- Exact flattened continuation after consuming the active primitive
equality. -/
def unifyExecutableTail (state : RepresentativeActivePayloadState)
    (bodyExecutableTail : List PLeaTTa.Goal) : List PLeaTTa.Goal :=
  bodyExecutableTail ++
    (state.carrier.index.callerExecutables ++
      flattenExecutables state.carrier.index.outer)

/-- Exact independent source focus after the primitive equality succeeds. -/
def unifySource (state : RepresentativeActivePayloadState)
    (result : Substitution)
    (bodyRest : List PeTTaSpec.PrologCore.Goal) : Search :=
  ActiveProductContext.plug state.carrier.index.context
    (activeSourceProduct state.carrier.index.callerScope
      state.carrier.index.opened state.carrier.index.finish
      state.carrier.index.branch state.carrier.index.branchTail result bodyRest
      state.carrier.index.callerReferences)

/-- Exact fine successor after installing the selected executable MGU. -/
def unifyOpenConf (state : RepresentativeActivePayloadState)
    (bodyExecutableTail : List PLeaTTa.Goal) (installed : Subst) : OpenConf :=
  unifySuccessor state.carrier.index.openConf
    (unifyExecutableTail state bodyExecutableTail) installed

/-- Every data index of the active successor.  Chosen MGU data are explicit
arguments; all persistent, scope, resource, and payload indices are inherited
by record update and therefore cannot be silently reselected. -/
def unifyIndex (state : RepresentativeActivePayloadState)
    (bodyRest : List PeTTaSpec.PrologCore.Goal)
    (bodyExecutableTail : List PLeaTTa.Goal)
    (result : Substitution) (sourceExtension : TreeSubstitution)
    (installed : Subst) : ActivePayloadIndex :=
  { state.carrier.index with
    canonical := sourceExtension ++ state.carrier.index.canonical
    bodyReferences := bodyRest
    bodyExecutables := bodyExecutableTail
    current := result
    runtime :=
      PLeaTTa.trimFor (unifyExecutableTail state bodyExecutableTail)
        state.carrier.index.qterm installed
    source := unifySource state result bodyRest
    openConf := unifyOpenConf state bodyExecutableTail installed }

/-- A reflexive equality over an already-trimmed active payload returns the
literal predecessor target index, not merely an extensionally related state. -/
theorem unifyIndex_beforeReflexiveUnify
    (state : RepresentativeActivePayloadState) (term : Term) (atom : Atom)
    (reading : AlphaTermAgrees state.carrier.index.alpha term atom)
    (trimmed :
      PLeaTTa.trimFor
          (unifyExecutableTail state state.carrier.index.bodyExecutables)
          state.carrier.index.qterm state.carrier.index.runtime =
        state.carrier.index.runtime) :
    unifyIndex (beforeReflexiveUnify state term atom reading)
        state.carrier.index.bodyReferences
        state.carrier.index.bodyExecutables state.carrier.index.current []
        state.carrier.index.runtime =
      state.carrier.index := by
  have sourceShape := state.carrier.agreement.core.sourceShape
  have currentControl :=
    state.carrier.agreement.core.control.ready.2.1
  have queryTerm :=
    state.carrier.agreement.core.control.ready.2.2.1
  rcases state with
    ⟨⟨⟨freshFrontier, alpha, support, canonical, referenceBase, opened,
          session, pending, finish, branch, branchTail, altTail, bodyBarrier,
          callerBarrier, bodyReferences, bodyExecutables, callerReferences,
          callerExecutables, outer, current, runtime, qterm, active, resources,
          callerScope, outerScope, context, baseAlts, source, openConf⟩,
        payloadContext, agreement⟩,
      representative, cumulative⟩
  change
    trimFor (bodyExecutables ++ (callerExecutables ++ flattenExecutables outer))
        qterm runtime = runtime at trimmed
  change
    source =
      context.plug
        (activeSourceProduct callerScope opened finish branch branchTail current
          bodyReferences callerReferences) at sourceShape
  change
    openConf.control.cur =
      some
        (bodyExecutables ++ (callerExecutables ++ flattenExecutables outer),
          runtime) at currentControl
  change openConf.control.qterm = qterm at queryTerm
  simp [unifyIndex, beforeReflexiveUnify, beforeUnify, unifyExecutableTail,
    unifySource, unifyOpenConf, unifyPredecessorSource,
    unifyPredecessorOpenConf, unifySuccessor,
    ActivePayloadState.ofAgreement, sourceShape.symm, trimmed]
  apply OpenConf.eq_of_toConf_eq_of_frames_eq_of_scopes_eq
  · rw [OpenConf.stepOpen_toConf]
    apply PLeaTTa.Conf.ext <;>
      simp [OpenConf.toConf, Control.toConf, currentControl, queryTerm, trimmed]
  · rfl
  · rfl

end RepresentativeActivePayloadState

/-- Closed producer facts for one selected primitive-unification successor.

The exact successor index, selected installation certificate, source step,
fine step, representative equation, and payload identity all belong to one
package.  A caller cannot pair an unrelated source and executable transition
under the public `.unify` label. -/
structure RepresentativeUnifySuccessorFacts
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (before after : RepresentativeActivePayloadState)
    (left right : Term) (result : Substitution)
    (bodyRest : List PeTTaSpec.PrologCore.Goal)
    (bodyExecutableTail : List PLeaTTa.Goal)
    (sourceExtension executableExtension : TreeSubstitution)
    (generated installed : Subst) : Prop where
  referenceHead :
    before.carrier.index.bodyReferences = .unify left right :: bodyRest
  afterIndexExact :
    after.carrier.index =
      RepresentativeActivePayloadState.unifyIndex before bodyRest
        bodyExecutableTail result sourceExtension installed
  selectedExecution :
    ∃ (spelling : NormalizedAlphaGoalsAgree.ExecutableUnifySpelling)
        (executableLeft executableRight : Atom),
      AlphaTermAgrees before.carrier.index.alpha left executableLeft ∧
        AlphaTermAgrees before.carrier.index.alpha right executableRight ∧
        before.carrier.index.openConf.control.cur =
          some
            (spelling.goal executableLeft executableRight ::
              RepresentativeActivePayloadState.unifyExecutableTail before
                bodyExecutableTail,
              before.carrier.index.runtime) ∧
        SelectedUnifySuccessData before.carrier.index.alpha
          before.carrier.index.support before.carrier.index.canonical
          before.representative before.carrier.index.referenceBase
          before.carrier.index.current before.carrier.index.runtime left right
          left right executableLeft executableRight result sourceExtension
          executableExtension generated installed
  sourceStep :
    RawStep before.carrier.index.session before.carrier.index.source [] .none
      before.carrier.index.session (.running after.carrier.index.source)
  fineStep :
    DemandDrivenCallStep.Step prog gt
      (.ready before.carrier.index.openConf)
      (.ready after.carrier.index.openConf)
  /-- Deliberately literal list equality.  The anti-laundering theorems below
  use syntactic prefix length; replacing this with denotational or variant
  equality would remove their force even if their surface statements still
  looked similar. -/
  representativeExact :
    after.representative = executableExtension ++ before.representative
  payloadCellsExact :
    after.carrier.cellIdentities = before.carrier.cellIdentities

namespace RepresentativeUnifySuccessorFacts

/-- A certified primitive-unification successor that returns to the literal
same representative must have installed the empty executable extension.

This is a structural anti-laundering guard: a nonempty residual orientation
cannot be hidden behind endpoint compatibility when the heterogeneous zipper
claims exact representative identity. -/
theorem executableExtension_eq_nil_of_representative_eq
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : RepresentativeActivePayloadState}
    {left right : Term} {result : Substitution}
    {bodyRest : List PeTTaSpec.PrologCore.Goal}
    {bodyExecutableTail : List PLeaTTa.Goal}
    {sourceExtension executableExtension : TreeSubstitution}
    {generated installed : Subst}
    (facts :
      RepresentativeUnifySuccessorFacts prog gt before after left right result
        bodyRest bodyExecutableTail sourceExtension executableExtension
        generated installed)
    (same : after.representative = before.representative) :
    executableExtension = [] := by
  have lengths := congrArg List.length facts.representativeExact
  rw [same] at lengths
  simp only [List.length_append] at lengths
  apply List.eq_nil_of_length_eq_zero
  omega

/-- Equivalently, every nonempty executable residual extension changes the
literal representative.  A wrong orientation therefore cannot inhabit the
exact reflexive middle used by a certified prefix. -/
theorem representative_ne_of_executableExtension_ne_nil
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : RepresentativeActivePayloadState}
    {left right : Term} {result : Substitution}
    {bodyRest : List PeTTaSpec.PrologCore.Goal}
    {bodyExecutableTail : List PLeaTTa.Goal}
    {sourceExtension executableExtension : TreeSubstitution}
    {generated installed : Subst}
    (facts :
      RepresentativeUnifySuccessorFacts prog gt before after left right result
        bodyRest bodyExecutableTail sourceExtension executableExtension
        generated installed)
    (nonempty : executableExtension ≠ []) :
    after.representative ≠ before.representative := by
  intro same
  exact nonempty (facts.executableExtension_eq_nil_of_representative_eq same)

/-- A selected successor that changes the denotation of any tree under one
fixed carried base must have a nonempty executable residual extension.

Unlike a length-only endpoint test, this discriminator can be discharged by
an independently transported materialized value.  It therefore exposes the
semantic work performed by the residual without fixing its concrete fresh
variable spelling. -/
theorem executableExtension_ne_nil_of_apply_ne
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : RepresentativeActivePayloadState}
    {left right : Term} {result : Substitution}
    {bodyRest : List PeTTaSpec.PrologCore.Goal}
    {bodyExecutableTail : List PLeaTTa.Goal}
    {sourceExtension executableExtension : TreeSubstitution}
    {generated installed : Subst}
    (facts :
      RepresentativeUnifySuccessorFacts prog gt before after left right result
        bodyRest bodyExecutableTail sourceExtension executableExtension
        generated installed)
    {base : TreeSubstitution} {tree : Tree}
    (changed :
      TreeSubstitution.apply (after.representative ++ base) tree ≠
        TreeSubstitution.apply (before.representative ++ base) tree) :
    executableExtension ≠ [] := by
  intro empty
  apply changed
  rw [facts.representativeExact, empty]
  rfl

/-- Transport one already-materialized call head through the selected
primitive-unification successor and its executable trimming step.

The exact call must occur in the retained body tail.  This premise is what
licenses trim preservation; the literal successor representative is taken
from `representativeExact`, never reselected through a variants relation. -/
theorem materializedCallAgreesWith
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : RepresentativeActivePayloadState}
    {left right : Term} {result : Substitution}
    {bodyRest : List PeTTaSpec.PrologCore.Goal}
    {bodyExecutableTail : List PLeaTTa.Goal}
    {sourceExtension executableExtension : TreeSubstitution}
    {generated installed : Subst}
    (facts :
      RepresentativeUnifySuccessorFacts prog gt before after left right result
        bodyRest bodyExecutableTail sourceExtension executableExtension
        generated installed)
    {referencePayload : List Term} {executableArguments : List Atom}
    {executableResult : Atom} {predicate : String}
    (materialized :
      PrologRecursiveCallPayloadBridge.MaterializedCallAgreesWith
        before.carrier.index.alpha before.carrier.index.current
        referencePayload
        (executableArguments.map
          (PLeaTTa.subst before.carrier.index.runtime))
        (PLeaTTa.subst before.carrier.index.runtime executableResult)
        before.representative before.carrier.index.referenceBase)
    (callMember :
      PLeaTTa.Goal.call predicate executableArguments executableResult ∈
        bodyExecutableTail) :
    PrologRecursiveCallPayloadBridge.MaterializedCallAgreesWith
      after.carrier.index.alpha after.carrier.index.current referencePayload
      (executableArguments.map
        (PLeaTTa.subst after.carrier.index.runtime))
      (PLeaTTa.subst after.carrier.index.runtime executableResult)
      after.representative after.carrier.index.referenceBase := by
  obtain
    ⟨_spelling, _executableLeft, _executableRight, _leftAgreement,
      _rightAgreement, _executableHead, selected⟩ :=
    facts.selectedExecution
  have untrimmed :=
    PrologRecursiveCallPayloadBridge.MaterializedCallAgreesWith.afterSelectedUnify
      materialized selected
  have trimmed :=
    PrologRecursiveCallPayloadBridge.MaterializedCallAgreesWith.trimFor
      untrimmed
      (RepresentativeActivePayloadState.unifyExecutableTail before
        bodyExecutableTail)
      before.carrier.index.qterm selected.installedTopological predicate
      (by
        exact List.mem_append.mpr (Or.inl callMember))
  rw [facts.afterIndexExact, facts.representativeExact]
  simpa [RepresentativeActivePayloadState.unifyIndex] using trimmed

end RepresentativeUnifySuccessorFacts

namespace RepresentativeActivePayloadState

/-- A reflexive equality prepended to an already-trimmed active payload is an
exact closed `.unify` transition back to that payload.

Both ordered MGU extensions and the executable generated block are literally
empty, so the representative, cumulative valuation, persistent state, and
payload cells are preserved by construction rather than only up to variants. -/
theorem reflexiveUnifyFacts
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (state : RepresentativeActivePayloadState) (term : Term) (atom : Atom)
    (reading : AlphaTermAgrees state.carrier.index.alpha term atom)
    (trimmed :
      PLeaTTa.trimFor
          (RepresentativeActivePayloadState.unifyExecutableTail state
            state.carrier.index.bodyExecutables)
          state.carrier.index.qterm state.carrier.index.runtime =
        state.carrier.index.runtime) :
    RepresentativeUnifySuccessorFacts prog gt
      (beforeReflexiveUnify state term atom reading) state term term
      state.carrier.index.current state.carrier.index.bodyReferences
      state.carrier.index.bodyExecutables [] [] []
      state.carrier.index.runtime := by
  let before := beforeReflexiveUnify state term atom reading
  have bodyPayload :
      TaskPayloadAgrees before.carrier.index.alpha
        before.carrier.index.support before.carrier.index.bodyBarrier
        before.carrier.index.canonical before.carrier.index.referenceBase
        before.carrier.index.current before.carrier.index.runtime
        before.carrier.index.bodyReferences
        before.carrier.index.bodyExecutables :=
    before.carrier.agreement.core.control.ready.2.2.2.headPayload
  have topExact :
      SelectedUnifyTopExact before.carrier.index.alpha
        before.carrier.index.support before.carrier.index.canonical
        before.representative before.carrier.index.referenceBase
        before.carrier.index.current before.carrier.index.runtime term term
        term term atom atom before.carrier.index.current [] [] [] :=
    bodyPayload.data.selectedUnifyTopExact_reflexive before.cumulative term atom
  have selectedSuccess :
      SelectedUnifySuccessData before.carrier.index.alpha
        before.carrier.index.support before.carrier.index.canonical
        before.representative before.carrier.index.referenceBase
        before.carrier.index.current before.carrier.index.runtime term term
        term term atom atom before.carrier.index.current [] [] []
        before.carrier.index.runtime := by
    refine
      { topExact := topExact
        installedExact := ?_
        nextCanonicalWellFormed := ?_
        nextBindingShape := ?_
        nextCumulative := ?_ }
    · simp [PLeaTTa.unifyB, PLeaTTa.unifyTopExact_self]
    · simpa using bodyPayload.data.canonicalWellFormed
    · simpa using bodyPayload.data.bindingShape
    · simpa [before, beforeReflexiveUnify] using before.cumulative
  have resolved :
      UnifyResolution state.carrier.index.current term term
        state.carrier.index.current := by
    refine ⟨[], ?_, by rfl⟩
    refine ⟨[], ?_, rfl⟩
    let tree := Term.denote (state.carrier.index.current.applyTerm term)
    simpa [denoteEquations, tree] using
      (OrderedTreeMgu.cons tree tree [] [] [] (.reflexive tree)
        OrderedTreeMgu.nil)
  have child :
      RawStep state.carrier.index.session
        (.task state.carrier.index.opened.scope
          (.unify term term :: state.carrier.index.bodyReferences)
          state.carrier.index.current)
        [] .none state.carrier.index.session
        (.running
          (.task state.carrier.index.opened.scope
            state.carrier.index.bodyReferences
            state.carrier.index.current)) :=
    .taskUnifySuccess state.carrier.index.opened.scope term term
      state.carrier.index.bodyReferences state.carrier.index.current
      state.carrier.index.current state.carrier.index.session resolved
  have activeSourceStep :
      RawStep state.carrier.index.session
        (activeSourceProduct state.carrier.index.callerScope
          state.carrier.index.opened state.carrier.index.finish
          state.carrier.index.branch state.carrier.index.branchTail
          state.carrier.index.current
          (.unify term term :: state.carrier.index.bodyReferences)
          state.carrier.index.callerReferences)
        [] .none state.carrier.index.session
        (.running
          (activeSourceProduct state.carrier.index.callerScope
            state.carrier.index.opened state.carrier.index.finish
            state.carrier.index.branch state.carrier.index.branchTail
            state.carrier.index.current state.carrier.index.bodyReferences
            state.carrier.index.callerReferences)) := by
    simpa using
      ActiveProductFrame.liftProgress
        (ActiveProductFrame.ofActiveProduct state.carrier.index.callerScope
          state.carrier.index.opened state.carrier.index.finish
          state.carrier.index.branch state.carrier.index.branchTail
          state.carrier.index.callerReferences)
        child (by simp [Trace.AnswerFree])
  have sourceStep :
      RawStep state.carrier.index.session before.carrier.index.source [] .none
        state.carrier.index.session (.running state.carrier.index.source) := by
    change
      RawStep state.carrier.index.session
        (reflexiveUnifyPredecessorSource state term) [] .none
        state.carrier.index.session (.running state.carrier.index.source)
    rw [state.carrier.agreement.core.sourceShape]
    exact
      ActiveProductContext.liftProgress state.carrier.index.context
        activeSourceStep (by simp [Trace.AnswerFree])
  have executableHead :
      before.carrier.index.openConf.control.cur =
        some
          (.eq atom atom ::
            RepresentativeActivePayloadState.unifyExecutableTail before
              state.carrier.index.bodyExecutables,
            before.carrier.index.runtime) := by
    simp [before, beforeReflexiveUnify, beforeUnify,
      unifyPredecessorOpenConf,
      RepresentativeActivePayloadState.unifyExecutableTail,
      ActivePayloadState.ofAgreement]
  have afterIndexExact :=
    unifyIndex_beforeReflexiveUnify state term atom reading trimmed
  have executableAfter :
      RepresentativeActivePayloadState.unifyOpenConf before
          state.carrier.index.bodyExecutables state.carrier.index.runtime =
        state.carrier.index.openConf := by
    exact congrArg ActivePayloadIndex.openConf afterIndexExact
  have fineStep :
      DemandDrivenCallStep.Step prog gt
        (.ready before.carrier.index.openConf)
        (.ready state.carrier.index.openConf) := by
    have step :=
      executable_unify_step (prog := prog) (gt := gt)
        before.carrier.index.openConf
        NormalizedAlphaGoalsAgree.ExecutableUnifySpelling.equality atom atom
        (RepresentativeActivePayloadState.unifyExecutableTail before
          state.carrier.index.bodyExecutables)
        before.carrier.index.runtime state.carrier.index.runtime
        executableHead selectedSuccess.installedExact
    simpa [RepresentativeActivePayloadState.unifyOpenConf] using
      (executableAfter ▸ step)
  refine
    { referenceHead := rfl
      afterIndexExact := afterIndexExact.symm
      selectedExecution :=
        ⟨NormalizedAlphaGoalsAgree.ExecutableUnifySpelling.equality,
          atom, atom, ?_, ?_, executableHead, selectedSuccess⟩
      sourceStep := sourceStep
      fineStep := fineStep
      representativeExact := ?_
      payloadCellsExact := ?_ }
  · simpa [before, beforeReflexiveUnify, beforeUnify,
      ActivePayloadState.ofAgreement] using
      reading
  · simpa [before, beforeReflexiveUnify, beforeUnify,
      ActivePayloadState.ofAgreement] using
      reading
  · simp [beforeReflexiveUnify, beforeUnify,
      ActivePayloadState.ofAgreement]
  · rfl

/-- Produce the literal active successor while retaining the selected old and
new residual orientations.  Existential elimination stays inside `Prop`; the
returned Type carrier itself stores every chosen datum in its indices. -/
theorem exists_afterUnifySuccessLive
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (before : RepresentativeActivePayloadState)
    {left right : Term} {result : Substitution}
    {bodyRest : List PeTTaSpec.PrologCore.Goal}
    (referenceHead :
      before.carrier.index.bodyReferences = .unify left right :: bodyRest)
    (leftSupported :
      AlphaTreeSupported before.carrier.index.alpha
        before.carrier.index.support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported before.carrier.index.alpha
        before.carrier.index.support (Term.denote right))
    (continuationLive :
      ReadyUnifyContinuationLive before.carrier.index.support
        before.carrier.index.openConf)
    (resolved :
      UnifyResolution before.carrier.index.current left right result) :
    ∃ bodyExecutableTail : List PLeaTTa.Goal,
      ∃ sourceExtension executableExtension : TreeSubstitution,
      ∃ generated installed : Subst,
      ∃ after : RepresentativeActivePayloadState,
        RepresentativeUnifySuccessorFacts prog gt before after left right
          result bodyRest bodyExecutableTail sourceExtension
          executableExtension generated installed := by
  have activeAgreement :
      SpinedActiveProductPayloadResourceRelatesAt
        before.carrier.index.freshFrontier before.carrier.index.alpha
        before.carrier.index.support before.carrier.index.canonical
        before.carrier.index.referenceBase before.carrier.index.opened
        before.carrier.index.session before.carrier.index.pending
        before.carrier.index.finish before.carrier.index.branch
        before.carrier.index.branchTail before.carrier.index.altTail
        before.carrier.index.bodyBarrier before.carrier.index.callerBarrier
        (.unify left right :: bodyRest) before.carrier.index.bodyExecutables
        before.carrier.index.callerReferences
        before.carrier.index.callerExecutables before.carrier.index.outer
        before.carrier.index.current before.carrier.index.runtime
        before.carrier.index.qterm before.carrier.index.active
        before.carrier.index.resources before.carrier.index.callerScope
        before.carrier.index.outerScope before.carrier.index.context
        before.carrier.index.baseAlts before.carrier.index.source
        before.carrier.index.openConf before.carrier.payloadContext := by
    simpa only [ActivePayloadIndex.Relates, referenceHead] using
      before.carrier.agreement
  obtain
    ⟨spelling, executableLeft, executableRight, bodyExecutableTail,
      sourceExtension, executableExtension, generated, installed,
      leftAgreement, rightAgreement, executableHead, selectedSuccess,
      sourceStep, fineStep, nextAgreement, nextSelected⟩ :=
    PLeaTTa.PrologCurrentSessionUnifyTransitionBridge.SpinedActiveProductPayloadResourceRelatesAt.afterUnifySuccessWithLive
      activeAgreement before.cumulative leftSupported rightSupported
      continuationLive resolved
  let nextCarrier := ActivePayloadState.ofAgreement nextAgreement
  let after : RepresentativeActivePayloadState :=
    { carrier := nextCarrier
      representative := executableExtension ++ before.representative
      cumulative := by
        simpa [nextCarrier, ActivePayloadState.ofAgreement] using nextSelected }
  refine
    ⟨bodyExecutableTail, sourceExtension, executableExtension, generated,
      installed, after, ?_⟩
  refine
    { referenceHead := referenceHead
      afterIndexExact := ?_
      selectedExecution :=
        ⟨spelling, executableLeft, executableRight, leftAgreement,
          rightAgreement, executableHead, selectedSuccess⟩
      sourceStep := ?_
      fineStep := ?_
      representativeExact := rfl
      payloadCellsExact := rfl }
  · rfl
  · simpa [after, nextCarrier, ActivePayloadState.ofAgreement] using sourceStep
  · simpa [after, nextCarrier, ActivePayloadState.ofAgreement] using fineStep

/-- Compatibility producer for callers carrying the older conservative
runtime-avoidance and support-inclusion premises. -/
theorem exists_afterUnifySuccess
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (before : RepresentativeActivePayloadState)
    {left right : Term} {result : Substitution}
    {bodyRest : List PeTTaSpec.PrologCore.Goal}
    (referenceHead :
      before.carrier.index.bodyReferences = .unify left right :: bodyRest)
    (leftSupported :
      AlphaTreeSupported before.carrier.index.alpha
        before.carrier.index.support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported before.carrier.index.alpha
        before.carrier.index.support (Term.denote right))
    (_supportIncluded :
      ∀ pair, pair ∈ before.carrier.index.support →
        pair ∈ before.carrier.index.alpha)
    (safe :
      ReadyUnifyContinuationSafe before.carrier.index.support
        before.carrier.index.openConf)
    (resolved :
      UnifyResolution before.carrier.index.current left right result) :
    ∃ bodyExecutableTail : List PLeaTTa.Goal,
      ∃ sourceExtension executableExtension : TreeSubstitution,
      ∃ generated installed : Subst,
      ∃ after : RepresentativeActivePayloadState,
        RepresentativeUnifySuccessorFacts prog gt before after left right
          result bodyRest bodyExecutableTail sourceExtension
          executableExtension generated installed :=
  PLeaTTa.PrologHeterogeneousPrefixBridge.RepresentativeActivePayloadState.exists_afterUnifySuccessLive
    before referenceHead leftSupported rightSupported safe.live resolved

end RepresentativeActivePayloadState

/-! ## Closed transition vocabulary -/

/-- Public transition identity.  Costs and observations are functions of
this closed vocabulary; a caller cannot attach an arbitrary execution trace
to a transition label. -/
inductive TransitionKind where
  | administrative (count : Nat)
  | unify
  | localCall (rejected : Nat) (request : CallRequest)
  | bodyAnswer
  | cut (token : CursorToken)
deriving Repr

namespace TransitionKind

def sourceCost : TransitionKind → Nat
  | .administrative count => count
  | .unify => 1
  | .localCall rejected _ => rejected + 2
  | .bodyAnswer => 1
  | .cut _ => 1

def sourceEvents : TransitionKind → List Observation
  | .administrative _ => []
  | .unify => []
  | .localCall _ request => [.opened request]
  | .bodyAnswer => []
  | .cut token => [.pruned token]

def fineCost : TransitionKind → Nat
  | .administrative _ => 0
  | .unify => 1
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
  | .unify => after = before
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
        (.active (RepresentativePersistentFreeActivePayloadState.ofLegacy before))
        (.active
          (RepresentativePersistentFreeActivePayloadState.ofLegacy
            (RepresentativeActivePayloadState.afterAdministrative
              prog gt before steps)))
  | unify
      {before after : RepresentativeActivePayloadState}
      {left right : Term} {result : Substitution}
      {bodyRest : List PeTTaSpec.PrologCore.Goal}
      {bodyExecutableTail : List PLeaTTa.Goal}
      {sourceExtension executableExtension : TreeSubstitution}
      {generated installed : Subst}
      (facts :
        RepresentativeUnifySuccessorFacts prog gt before after left right
          result bodyRest bodyExecutableTail sourceExtension
          executableExtension generated installed) :
      CertifiedTransition prog gt .unify
        (.active (RepresentativePersistentFreeActivePayloadState.ofLegacy before))
        (.active (RepresentativePersistentFreeActivePayloadState.ofLegacy after))
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
        (.active (RepresentativePersistentFreeActivePayloadState.ofLegacy before))
        (.active (RepresentativePersistentFreeActivePayloadState.ofLegacy after))
  | bodyAnswer
      (before : RepresentativeActivePayloadState)
      (referenceEmpty : before.carrier.index.bodyReferences = [])
      (executableEmpty : before.carrier.index.bodyExecutables = []) :
      CertifiedTransition prog gt .bodyAnswer
        (.active (RepresentativePersistentFreeActivePayloadState.ofLegacy before))
        (.scheduled
          (RepresentativePersistentFreeScheduledPayloadState.ofLegacy
            (RepresentativeActivePayloadState.afterBodyAnswer
              prog gt before referenceEmpty executableEmpty)))
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
        (.active (RepresentativePersistentFreeActivePayloadState.ofLegacy before))
        (.committed
          (RepresentativeActivePayloadState.afterCut prog gt before bodyRest
            bodyExecutableTail referenceHead executableHead coherent))

namespace CertifiedTransition

/-- An administrative transition always remains in the active phase.  The
target constructor is recoverable without asking the one-way legacy erasure
to be injective. -/
theorem administrative_target_active
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {count : Nat} {before after : ProductPhaseState}
    (step : CertifiedTransition prog gt (.administrative count) before after) :
    ∃ state : RepresentativePersistentFreeActivePayloadState,
      after = .active state := by
  cases step with
  | administrative before steps =>
      exact
        ⟨RepresentativePersistentFreeActivePayloadState.ofLegacy
            (RepresentativeActivePayloadState.afterAdministrative
              prog gt before steps),
          rfl⟩

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
  | @unify before after left right result bodyRest bodyExecutableTail
      sourceExtension executableExtension generated installed facts =>
      have sessionEq :
          after.carrier.index.session = before.carrier.index.session := by
        have projected :=
          congrArg ActivePayloadIndex.session facts.afterIndexExact
        simpa [RepresentativeActivePayloadState.unifyIndex] using projected
      simpa [TransitionKind.sourceCost, TransitionKind.sourceEvents,
        ProductPhaseState.sourceState, ActivePayloadState.sourceState,
        sessionEq] using
        oneSourceStep facts.sourceStep
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
  | @unify before after left right result bodyRest bodyExecutableTail
      sourceExtension executableExtension generated installed facts =>
      simpa [TransitionKind.fineCost, ProductPhaseState.fineState,
        ActivePayloadState.fineState] using oneFineStep facts.fineStep
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
  | @unify before after left right result bodyRest bodyExecutableTail
      sourceExtension executableExtension generated installed facts =>
      change
        SessionHighWatersExtend before.carrier.index.session
          after.carrier.index.session
      rw [facts.afterIndexExact]
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
  | @unify before after left right result bodyRest bodyExecutableTail
      sourceExtension executableExtension generated installed facts =>
      change
        before.carrier.index.openConf.persistent.counter ≤
          after.carrier.index.openConf.persistent.counter
      rw [facts.afterIndexExact]
      simp [RepresentativeActivePayloadState.unifyIndex,
        RepresentativeActivePayloadState.unifyOpenConf]
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
  | @unify before after left right result bodyRest bodyExecutableTail
      sourceExtension executableExtension generated installed facts =>
      change
        AlphaExtendsAbove before.carrier.index.alpha
          after.carrier.index.alpha
          before.carrier.index.session.resolver.nextFresh
          before.carrier.index.openConf.persistent.counter
      rw [facts.afterIndexExact]
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
  | @unify before after left right result bodyRest bodyExecutableTail
      sourceExtension executableExtension generated installed facts =>
      exact ⟨executableExtension, facts.representativeExact⟩
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
  | @unify before after left right result bodyRest bodyExecutableTail
      sourceExtension executableExtension generated installed facts =>
      simpa [TransitionKind.PayloadEvolution,
        ProductPhaseState.cellIdentities] using facts.payloadCellsExact
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

/-- Every closed transition preserves the literal base alternative suffix.
Recursive-call push uses the producer's explicit preservation field; no
consumer is allowed to infer closure from an unrelated final bank. -/
theorem baseAlts_eq
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kind : TransitionKind} {before after : ProductPhaseState}
    (transition : CertifiedTransition prog gt kind before after) :
    after.baseAlts = before.baseAlts := by
  cases transition with
  | administrative before steps => rfl
  | @unify before after left right result bodyRest bodyExecutableTail
      sourceExtension executableExtension generated installed facts =>
      simpa [ProductPhaseState.baseAlts,
        RepresentativeActivePayloadState.unifyIndex] using
        congrArg ActivePayloadIndex.baseAlts facts.afterIndexExact
  | localCall facts =>
      simpa [ProductPhaseState.baseAlts] using facts.baseAltsPreserved
  | bodyAnswer before referenceEmpty executableEmpty => rfl
  | cut before bodyRest bodyExecutableTail referenceHead executableHead
      coherent => rfl

/-- Root closure is a subject-reduction property of one certified phase
transition. -/
theorem preserves_rootClosed
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kind : TransitionKind} {before after : ProductPhaseState}
    (transition : CertifiedTransition prog gt kind before after)
    (closed : before.RootClosed) : after.RootClosed := by
  unfold ProductPhaseState.RootClosed at closed ⊢
  rw [transition.baseAlts_eq]
  exact closed

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

/-- Exact ordered payload-cell evolution for a heterogeneous schedule.

The intermediate cell spine is existential only at this schedule-only view.
`CertifiedPrefix.payloadEvolution` derives every witness from the literal
Type-valued intermediate state, so callers cannot independently choose a
compatible-looking payload path. -/
def PayloadEvolution :
    List TransitionKind → List PayloadCellIdentity →
      List PayloadCellIdentity → Prop
  | [], before, after => after = before
  | kind :: kinds, before, after =>
      ∃ middle, kind.PayloadEvolution before middle ∧
        PayloadEvolution kinds middle after

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

/-- Every source allocator high-water advances monotonically through an
arbitrary exact heterogeneous prefix. -/
theorem sessionHighWaters
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List TransitionKind} {before after : ProductPhaseState}
    (run : CertifiedPrefix prog gt kinds before after) :
    SessionHighWatersExtend before.session after.session := by
  induction run with
  | nil state => exact SessionHighWatersExtend.refl state.session
  | cons head tail ih =>
      exact SessionHighWatersExtend.trans head.sessionHighWaters ih

/-- The executable allocation counter cannot roll back anywhere in an
arbitrary exact heterogeneous prefix. -/
theorem executableCounter_mono
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List TransitionKind} {before after : ProductPhaseState}
    (run : CertifiedPrefix prog gt kinds before after) :
    before.openConf.persistent.counter ≤ after.openConf.persistent.counter := by
  induction run with
  | nil state => exact Nat.le_refl _
  | cons head tail ih =>
      exact Nat.le_trans head.executableCounter_mono ih

/-- The exact chronological alpha suffix composes through arbitrary mixed
transition kinds.  Each later suffix is weakened only to the literal earlier
state's certified allocator floors before concatenation. -/
theorem alphaExtension
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List TransitionKind} {before after : ProductPhaseState}
    (run : CertifiedPrefix prog gt kinds before after) :
    AlphaExtendsAbove before.alpha after.alpha
      before.session.resolver.nextFresh
      before.openConf.persistent.counter := by
  induction run with
  | nil state =>
      exact AlphaExtendsAbove.refl state.alpha
        state.session.resolver.nextFresh state.openConf.persistent.counter
  | cons head tail ih =>
      exact head.alphaExtension.trans
        (ih.weaken head.sessionHighWaters.fresh
          head.executableCounter_mono)

/-- Every cumulative residual representative is an exact chronological
extension of the prefix origin.  No association-list orientation is selected
between steps; each transition contributes its already-certified suffix. -/
theorem representativeExtension
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List TransitionKind} {before after : ProductPhaseState}
    (run : CertifiedPrefix prog gt kinds before after) :
    ∃ extension : TreeSubstitution,
      after.representative = extension ++ before.representative := by
  induction run with
  | nil state => exact ⟨[], rfl⟩
  | cons head tail ih =>
      obtain ⟨headExtension, headExact⟩ := head.representativeExtension
      obtain ⟨tailExtension, tailExact⟩ := ih
      refine ⟨tailExtension ++ headExtension, ?_⟩
      rw [tailExact, headExact, List.append_assoc]

/-- Exact payload push/preserve/pop behavior composes through the same
literal state-indexed prefix used for source and fine execution. -/
theorem payloadEvolution
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List TransitionKind} {before after : ProductPhaseState}
    (run : CertifiedPrefix prog gt kinds before after) :
    TransitionSchedule.PayloadEvolution kinds before.cellIdentities
      after.cellIdentities := by
  induction run with
  | nil state => rfl
  | @cons kind kinds before middle after head tail ih =>
      exact ⟨middle.cellIdentities, head.payloadEvolution, ih⟩

/-- An arbitrary exact heterogeneous prefix preserves the literal unowned
alternative suffix. -/
theorem baseAlts_eq
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List TransitionKind} {before after : ProductPhaseState}
    (run : CertifiedPrefix prog gt kinds before after) :
    after.baseAlts = before.baseAlts := by
  induction run with
  | nil state => rfl
  | cons head tail ih => exact ih.trans head.baseAlts_eq

/-- Root closure survives every transition in the same proof-relevant prefix
used for exact source/fine execution. -/
theorem preserves_rootClosed
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List TransitionKind} {before after : ProductPhaseState}
    (run : CertifiedPrefix prog gt kinds before after)
    (closed : before.RootClosed) : after.RootClosed := by
  unfold ProductPhaseState.RootClosed at closed ⊢
  rw [run.baseAlts_eq]
  exact closed

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

/-! ## Producer readiness and arbitrary finite progress -/

/-- Producer premises for one covered transition out of an active state.

This is deliberately not phrased as "some transition exists": that would
make progress preservation circular.  Every constructor contains only the
semantic and operational premises consumed by its independent producer.  It
contains no successor, transition, step count, or observation claim; those
are reconstructed by `ActiveStepReady.produces` below.

The relation covers the complete current `CertifiedTransition` vocabulary.
It is still only a *one-step* readiness relation: body completion and cut
leave the active phase, so an invariant used with `ProgressPreservesReady`
must separately establish readiness of the reached scheduled or committed
phase once those outgoing transition kinds are added. -/
inductive ActiveStepReady : ProductPhaseState → Type where
  | administrative (state : RepresentativeActivePayloadState)
      {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
      (positive : 0 < count)
      (steps :
        AdministrativeStepsN count state.carrier.index.bodyReferences
          afterBody) :
      ActiveStepReady
        (.active (RepresentativePersistentFreeActivePayloadState.ofLegacy state))
  | unify (state : RepresentativeActivePayloadState)
      {left right : Term} {result : Substitution}
      {bodyRest : List PeTTaSpec.PrologCore.Goal}
      (referenceHead :
        state.carrier.index.bodyReferences = .unify left right :: bodyRest)
      (leftSupported :
        AlphaTreeSupported state.carrier.index.alpha
          state.carrier.index.support (Term.denote left))
      (rightSupported :
        AlphaTreeSupported state.carrier.index.alpha
          state.carrier.index.support (Term.denote right))
      (continuationLive :
        ReadyUnifyContinuationLive state.carrier.index.support
          state.carrier.index.openConf)
      (resolved :
        UnifyResolution state.carrier.index.current left right result) :
      ActiveStepReady
        (.active (RepresentativePersistentFreeActivePayloadState.ofLegacy state))
  | localCall (state : RepresentativeActivePayloadState)
      (head : NestedCallHead state.carrier)
      (ready : MaterializedNestedCallReady state head) :
      ActiveStepReady
        (.active (RepresentativePersistentFreeActivePayloadState.ofLegacy state))
  | bodyAnswer (state : RepresentativeActivePayloadState)
      (referenceEmpty : state.carrier.index.bodyReferences = [])
      (executableEmpty : state.carrier.index.bodyExecutables = []) :
      ActiveStepReady
        (.active (RepresentativePersistentFreeActivePayloadState.ofLegacy state))
  | cut (state : RepresentativeActivePayloadState)
      (bodyRest : List PeTTaSpec.PrologCore.Goal)
      (bodyExecutableTail : List PLeaTTa.Goal)
      (referenceHead :
        state.carrier.index.bodyReferences = .cut :: bodyRest)
      (executableHead :
        state.carrier.index.bodyExecutables =
          .cutAt state.carrier.index.bodyBarrier :: bodyExecutableTail)
      (coherent :
        PLeaTTa.BarrierCacheCoherent state.carrier.index.openConf.toConf) :
      ActiveStepReady
        (.active (RepresentativePersistentFreeActivePayloadState.ofLegacy state))

/-- The unindexed coupled-step relation obtained by hiding only the closed
transition label.  The source and fine endpoints remain the literal fields of
the same `ProductPhaseState`s, and the Type-valued transition is retained
under `Nonempty`; this is not an endpoint-compatibility quotient.  The
positive combined cost rejects the otherwise-admissible zero-length
administrative constructor, so relation length cannot be inflated by
semantic stutters.  No endpoint-inequality premise is imposed: a labelled
small-step semantics must retain positive-cost self-loops, whose infinite
iteration is genuine divergence rather than termination progress. -/
def CertifiedCoupledStep (prog : PLeaTTa.Prog)
    (gt : Metta.GroundingTable)
    (before after : ProductPhaseState) : Prop :=
  ∃ kind : TransitionKind,
    0 < kind.sourceCost + kind.fineCost ∧
      Nonempty (CertifiedTransition prog gt kind before after)

namespace CertifiedCoupledStep

/-- Every currently covered coupled step performs at least one independent
source transition.  Fine-only administrative suppression is allowed, but a
schedule edge can never be a zero/zero stutter. -/
theorem sourceCost_positive
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : ProductPhaseState}
    (step : CertifiedCoupledStep prog gt before after) :
    ∃ kind : TransitionKind, 0 < kind.sourceCost := by
  obtain ⟨kind, positive, _transition⟩ := step
  refine ⟨kind, ?_⟩
  cases kind <;>
    simp_all [TransitionKind.sourceCost, TransitionKind.fineCost]

/-- A coupled step exposes one exact source run and one exact fine run under
the same hidden closed label. -/
theorem exactExecutions
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : ProductPhaseState}
    (step : CertifiedCoupledStep prog gt before after) :
    ∃ kind : TransitionKind,
      StepsN kind.sourceCost before.sourceState kind.sourceEvents
          after.sourceState ∧
        DemandDrivenCallStep.StepsN prog gt kind.fineCost before.fineState
          after.fineState := by
  obtain ⟨kind, _positive, ⟨transition⟩⟩ := step
  exact ⟨kind, transition.sourceSteps, transition.fineSteps⟩

/-- Hiding the transition label does not hide persistent allocator
chronology. -/
theorem sessionHighWaters
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : ProductPhaseState}
    (step : CertifiedCoupledStep prog gt before after) :
    SessionHighWatersExtend before.session after.session := by
  obtain ⟨_kind, _positive, ⟨transition⟩⟩ := step
  exact transition.sessionHighWaters

/-- Hiding the transition label does not hide executable fresh-counter
chronology. -/
theorem executableCounter_mono
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : ProductPhaseState}
    (step : CertifiedCoupledStep prog gt before after) :
    before.openConf.persistent.counter ≤ after.openConf.persistent.counter := by
  obtain ⟨_kind, _positive, ⟨transition⟩⟩ := step
  exact transition.executableCounter_mono

/-- The hidden-label relation retains the source/executable alpha chronology
above the literal incoming high-waters. -/
theorem alphaExtension
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : ProductPhaseState}
    (step : CertifiedCoupledStep prog gt before after) :
    AlphaExtendsAbove before.alpha after.alpha
      before.session.resolver.nextFresh
      before.openConf.persistent.counter := by
  obtain ⟨_kind, _positive, ⟨transition⟩⟩ := step
  exact transition.alphaExtension

/-- The cumulative representative still changes only by one certified
prefix extension after the transition label is hidden. -/
theorem representativeExtension
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : ProductPhaseState}
    (step : CertifiedCoupledStep prog gt before after) :
    ∃ extension : TreeSubstitution,
      after.representative = extension ++ before.representative := by
  obtain ⟨_kind, _positive, ⟨transition⟩⟩ := step
  exact transition.representativeExtension

/-- Payload ownership remains classified by the same hidden transition kind;
the relation does not replace the ordered stack equation by a count. -/
theorem payloadEvolution
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : ProductPhaseState}
    (step : CertifiedCoupledStep prog gt before after) :
    ∃ kind : TransitionKind,
      kind.PayloadEvolution before.cellIdentities after.cellIdentities := by
  obtain ⟨kind, _positive, ⟨transition⟩⟩ := step
  exact ⟨kind, transition.payloadEvolution⟩

/-- Every covered step preserves the literal rooted alternative suffix. -/
theorem baseAlts_eq
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : ProductPhaseState}
    (step : CertifiedCoupledStep prog gt before after) :
    after.baseAlts = before.baseAlts := by
  obtain ⟨_kind, _positive, ⟨transition⟩⟩ := step
  exact transition.baseAlts_eq

/-- Root closure is preserved by the hidden-label coupled relation. -/
theorem preserves_rootClosed
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : ProductPhaseState}
    (step : CertifiedCoupledStep prog gt before after)
    (closed : before.RootClosed) : after.RootClosed := by
  obtain ⟨_kind, _positive, ⟨transition⟩⟩ := step
  exact transition.preserves_rootClosed closed

end CertifiedCoupledStep

namespace ActiveStepReady

/-- The exact successor generated by one proof-relevant readiness packet.

The readiness packet lives in `Type`, not `Prop`: constructor identity and
its data indices therefore cannot be erased by proof irrelevance.  Each
production constructor retains the corresponding independent producer facts,
so an administrative readiness cannot be paired with a cut successor merely
because both happen to leave the same active state. -/
inductive Produces (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable) :
    {before : ProductPhaseState} →
      ActiveStepReady before → ProductPhaseState → Prop where
  | administrative
      (state : RepresentativeActivePayloadState)
      {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
      (positive : 0 < count)
      (steps :
        AdministrativeStepsN count state.carrier.index.bodyReferences
          afterBody) :
      Produces prog gt
        (ActiveStepReady.administrative state positive steps)
        (.active
          (RepresentativePersistentFreeActivePayloadState.ofLegacy
            (RepresentativeActivePayloadState.afterAdministrative
              prog gt state steps)))
  | unify
      (state : RepresentativeActivePayloadState)
      {left right : Term} {result : Substitution}
      {bodyRest : List PeTTaSpec.PrologCore.Goal}
      (referenceHead :
        state.carrier.index.bodyReferences = .unify left right :: bodyRest)
      (leftSupported :
        AlphaTreeSupported state.carrier.index.alpha
          state.carrier.index.support (Term.denote left))
      (rightSupported :
        AlphaTreeSupported state.carrier.index.alpha
          state.carrier.index.support (Term.denote right))
      (continuationLive :
        ReadyUnifyContinuationLive state.carrier.index.support
          state.carrier.index.openConf)
      (resolved :
        UnifyResolution state.carrier.index.current left right result)
      {bodyExecutableTail : List PLeaTTa.Goal}
      {sourceExtension executableExtension : TreeSubstitution}
      {generated installed : Subst}
      {after : RepresentativeActivePayloadState}
      (facts :
        RepresentativeUnifySuccessorFacts prog gt state after left right
          result bodyRest bodyExecutableTail sourceExtension
          executableExtension generated installed) :
      Produces prog gt
        (ActiveStepReady.unify state referenceHead leftSupported
          rightSupported continuationLive resolved)
        (.active (RepresentativePersistentFreeActivePayloadState.ofLegacy after))
  | localCall
      (state : RepresentativeActivePayloadState)
      (head : NestedCallHead state.carrier)
      (ready : MaterializedNestedCallReady state head)
      {rejected : Nat} {skippedBranches : List ClauseBranch}
      {skippedClauses : List PLeaTTa.Clause}
      {finish : PreparedCursor} {branch : ClauseBranch}
      {clause : PLeaTTa.Clause} {branchTail : List ClauseBranch}
      {clauseTail : List PLeaTTa.Clause} {altTail : List PLeaTTa.Alt}
      {copied : PLeaTTa.Clause} {installed : Subst}
      {after : RepresentativeActivePayloadState}
      (facts :
        RepresentativeNestedCallSuccessorFacts prog gt state head rejected
          skippedBranches skippedClauses finish branch clause branchTail
          clauseTail altTail copied installed after) :
      Produces prog gt (ActiveStepReady.localCall state head ready)
        (.active (RepresentativePersistentFreeActivePayloadState.ofLegacy after))
  | bodyAnswer
      (state : RepresentativeActivePayloadState)
      (referenceEmpty : state.carrier.index.bodyReferences = [])
      (executableEmpty : state.carrier.index.bodyExecutables = []) :
      Produces prog gt
        (ActiveStepReady.bodyAnswer state referenceEmpty executableEmpty)
        (.scheduled
          (RepresentativePersistentFreeScheduledPayloadState.ofLegacy
            (RepresentativeActivePayloadState.afterBodyAnswer
              prog gt state referenceEmpty executableEmpty)))
  | cut
      (state : RepresentativeActivePayloadState)
      (bodyRest : List PeTTaSpec.PrologCore.Goal)
      (bodyExecutableTail : List PLeaTTa.Goal)
      (referenceHead :
        state.carrier.index.bodyReferences = .cut :: bodyRest)
      (executableHead :
        state.carrier.index.bodyExecutables =
          .cutAt state.carrier.index.bodyBarrier :: bodyExecutableTail)
      (coherent :
        PLeaTTa.BarrierCacheCoherent state.carrier.index.openConf.toConf) :
      Produces prog gt
        (ActiveStepReady.cut state bodyRest bodyExecutableTail referenceHead
          executableHead coherent)
        (.committed
          (RepresentativeActivePayloadState.afterCut prog gt state bodyRest
            bodyExecutableTail referenceHead executableHead coherent))

namespace Produces

/-- Readiness fixes the outer constructor of its generated target without
recovering any erased legacy packet. -/
theorem target_shape
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : ProductPhaseState}
    {ready : ActiveStepReady before}
    (production : Produces prog gt ready after) :
    match ready with
    | .administrative _ _ _ => ∃ state, after = .active state
    | .unify _ _ _ _ _ _ => ∃ state, after = .active state
    | .localCall _ _ _ => ∃ state, after = .active state
    | .bodyAnswer _ _ _ => ∃ state, after = .scheduled state
    | .cut _ _ _ _ _ _ => ∃ state, after = .committed state := by
  cases production with
  | administrative state positive steps => exact ⟨_, rfl⟩
  | unify state referenceHead leftSupported rightSupported continuationLive
      resolved facts =>
      exact ⟨_, rfl⟩
  | localCall state head ready facts => exact ⟨_, rfl⟩
  | bodyAnswer state referenceEmpty executableEmpty => exact ⟨_, rfl⟩
  | cut state bodyRest bodyExecutableTail referenceHead executableHead
      coherent =>
      exact ⟨_, rfl⟩

/-- Forgetting the readiness packet preserves the one real, non-stuttering
coupled transition it generated. -/
theorem certifiedCoupledStep
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : ProductPhaseState}
    {ready : ActiveStepReady before}
    (production : Produces prog gt ready after) :
    CertifiedCoupledStep prog gt before after := by
  cases production with
  | administrative state positive steps =>
      exact
        ⟨.administrative _, positive,
          ⟨.administrative state steps⟩⟩
  | unify state referenceHead leftSupported rightSupported continuationLive
      resolved facts =>
      exact
        ⟨.unify,
          by simp [TransitionKind.sourceCost, TransitionKind.fineCost],
          ⟨.unify facts⟩⟩
  | localCall state head callReady facts =>
      exact
        ⟨.localCall _
            (requestFor head.predicate head.referencePayload
              state.carrier.index.current),
          by simp [TransitionKind.sourceCost, TransitionKind.fineCost],
          ⟨.localCall facts⟩⟩
  | bodyAnswer state referenceEmpty executableEmpty =>
      exact
        ⟨.bodyAnswer,
          by simp [TransitionKind.sourceCost, TransitionKind.fineCost],
          ⟨.bodyAnswer state referenceEmpty executableEmpty⟩⟩
  | cut state bodyRest bodyExecutableTail referenceHead executableHead
      coherent =>
      exact
        ⟨.cut
            (retainedCursorToken state.carrier.index.opened
              state.carrier.index.finish state.carrier.index.branch
              state.carrier.index.branchTail),
          by simp [TransitionKind.sourceCost, TransitionKind.fineCost],
          ⟨.cut state bodyRest bodyExecutableTail referenceHead executableHead
            coherent⟩⟩

/-- The closed transition label prevents an administrative step from being
laundered through a committed successor, even when the same source state also
admits a cut transition.  This formulation deliberately avoids relying on
injectivity of the one-way legacy-to-persistent-free carrier erasure. -/
theorem administrative_not_committed
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (state : RepresentativeActivePayloadState)
    (count : Nat)
    (target : RepresentativeCommittedPayloadState) :
    IsEmpty (CertifiedTransition prog gt (.administrative count)
        (.active (RepresentativePersistentFreeActivePayloadState.ofLegacy state))
        (.committed target)) := by
  constructor
  intro transition
  obtain ⟨after, impossible⟩ := transition.administrative_target_active
  cases impossible

/-- A realizable administrative readiness produces an active target.  This
is the producer-side companion to `administrative_not_committed`; it uses the
readiness packet, while the latter is purely a closed-label shape theorem. -/
theorem administrative_produces_target_active
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (state : RepresentativeActivePayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (positive : 0 < count)
    (steps :
      AdministrativeStepsN count state.carrier.index.bodyReferences
        afterBody)
    (after : ProductPhaseState)
    (production :
      Produces prog gt (.administrative state positive steps) after) :
    ∃ target, after = .active target := by
  simpa using production.target_shape

end Produces

/-- Every readiness packet constructs a real transition in the closed
vocabulary.  The proof invokes the independent unification and local-call
producers; it does not attach a caller-supplied successor to the packet. -/
theorem produces
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : ProductPhaseState}
    (ready : ActiveStepReady before) :
    ∃ after : ProductPhaseState,
      Produces prog gt ready after := by
  cases ready with
  | administrative state positive steps =>
      exact
        ⟨.active
            (RepresentativePersistentFreeActivePayloadState.ofLegacy
              (RepresentativeActivePayloadState.afterAdministrative
                prog gt state steps)),
          .administrative state positive steps⟩
  | @unify state left right result bodyRest referenceHead leftSupported
      rightSupported continuationLive resolved =>
      obtain
        ⟨bodyExecutableTail, sourceExtension, executableExtension, generated,
          installed, after, facts⟩ :=
        RepresentativeActivePayloadState.exists_afterUnifySuccessLive
          (prog := prog) (gt := gt) state referenceHead leftSupported
          rightSupported continuationLive resolved
      exact
        ⟨.active (RepresentativePersistentFreeActivePayloadState.ofLegacy after),
          .unify state referenceHead leftSupported rightSupported
            continuationLive resolved facts⟩
  | localCall state head callReady =>
      obtain
        ⟨rejected, skippedBranches, skippedClauses, finish, branch, clause,
          branchTail, clauseTail, altTail, copied, installed, after, facts⟩ :=
        callReady.pushDetailed (prog := prog) (gt := gt)
      exact
        ⟨.active (RepresentativePersistentFreeActivePayloadState.ofLegacy after),
          .localCall state head callReady facts⟩
  | bodyAnswer state referenceEmpty executableEmpty =>
      exact
        ⟨.scheduled
            (RepresentativePersistentFreeScheduledPayloadState.ofLegacy
              (RepresentativeActivePayloadState.afterBodyAnswer
                prog gt state referenceEmpty executableEmpty)),
          .bodyAnswer state referenceEmpty executableEmpty⟩
  | cut state bodyRest bodyExecutableTail referenceHead executableHead
      coherent =>
      exact
        ⟨.committed
            (RepresentativeActivePayloadState.afterCut prog gt state bodyRest
              bodyExecutableTail referenceHead executableHead coherent),
          .cut state bodyRest bodyExecutableTail referenceHead executableHead
            coherent⟩

/-- Readiness produces one shared closed label carrying both exact executions
and every chronology/ownership invariant needed by prefix composition.

Keeping `kind` outside all conjunctions is load-bearing: source execution,
fine execution, and payload evolution cannot be justified by three different
compatible-looking transition labels. -/
theorem produces_exact_coupled_transition
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : ProductPhaseState}
    (ready : ActiveStepReady before) :
    ∃ after : ProductPhaseState, ∃ kind : TransitionKind,
      0 < kind.sourceCost + kind.fineCost ∧
        StepsN kind.sourceCost before.sourceState kind.sourceEvents
          after.sourceState ∧
        DemandDrivenCallStep.StepsN prog gt kind.fineCost before.fineState
          after.fineState ∧
        SessionHighWatersExtend before.session after.session ∧
        before.openConf.persistent.counter ≤
          after.openConf.persistent.counter ∧
        AlphaExtendsAbove before.alpha after.alpha
          before.session.resolver.nextFresh
          before.openConf.persistent.counter ∧
        (∃ extension : TreeSubstitution,
          after.representative = extension ++ before.representative) ∧
        kind.PayloadEvolution before.cellIdentities after.cellIdentities := by
  obtain ⟨after, production⟩ := ready.produces (prog := prog) (gt := gt)
  have coupled := production.certifiedCoupledStep
  obtain ⟨kind, positive, ⟨transition⟩⟩ := coupled
  exact
    ⟨after, kind, positive, transition.sourceSteps, transition.fineSteps,
      transition.sessionHighWaters, transition.executableCounter_mono,
      transition.alphaExtension, transition.representativeExtension,
      transition.payloadEvolution⟩

end ActiveStepReady

/-- One readiness-indexed, non-stuttering coupled progress-and-preservation
obligation.

The proof-relevant readiness packet and `Produces` relation select the same
constructor and successor.  Thus an invariant cannot be transported along a
cut transition while presenting unrelated administrative readiness for the
same source state. -/
def ProgressPreservesReady (prog : PLeaTTa.Prog)
    (gt : Metta.GroundingTable)
    (invariant : ProductPhaseState → Prop) : Prop :=
  ∀ {state : ProductPhaseState}, invariant state →
    ∃ ready : ActiveStepReady state, ∃ next : ProductPhaseState,
      ready.Produces prog gt next ∧ invariant next

namespace ActiveStepReady

/-- Repeated coupled progress inhabits an exact `CertifiedPrefix` of every
requested finite length.

This theorem intentionally returns a proposition containing the Type-valued
run.  No `Classical.choice` extracts a successor or scan result into a
computable definition; every intermediate remains the literal dependent
index shared by adjacent constructors. -/
theorem exists_prefix_of_ready
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {invariant : ProductPhaseState → Prop}
    (progress : ProgressPreservesReady prog gt invariant)
    {before : ProductPhaseState} (ready : invariant before) :
    ∀ count : Nat,
      ∃ kinds : List TransitionKind, ∃ after : ProductPhaseState,
        kinds.length = count ∧
          ∃ _run : CertifiedPrefix prog gt kinds before after,
            invariant after ∧ Nonempty (ActiveStepReady after) := by
  intro count
  induction count generalizing before with
  | zero =>
      obtain ⟨currentReady, _next, _production, _nextInvariant⟩ :=
        progress ready
      exact ⟨[], before, rfl, .nil before, ready, ⟨currentReady⟩⟩
  | succ count inductionHypothesis =>
      obtain ⟨_currentReady, middle, production, middleReady⟩ :=
        progress ready
      have coupled := production.certifiedCoupledStep
      obtain ⟨kind, _positive, ⟨step⟩⟩ := coupled
      obtain ⟨kinds, after, lengthExact, tail, afterInvariant,
          afterReady⟩ :=
        inductionHypothesis middleReady
      exact
        ⟨kind :: kinds, after, by simp [lengthExact],
          .cons step tail, afterInvariant, afterReady⟩

end ActiveStepReady

namespace RepresentativeUnifySuccessorFacts

/-- Compose one selected primitive-unification successor with the immediately
following materialized local call while retaining the complete call-successor
packet.

The unification successor `middle` is the literal Type index shared by both
transition constructors.  Thus the returned two-edge zipper cannot pair a
materialization derived from one residual orientation with a call activated
from another compatible-looking state.  The detailed call facts remain
available to construct the next recursive head. -/
theorem thenMaterializedLocalCallDetailed
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before middle : RepresentativeActivePayloadState}
    {left right : Term} {result : Substitution}
    {bodyRest : List PeTTaSpec.PrologCore.Goal}
    {bodyExecutableTail : List PLeaTTa.Goal}
    {sourceExtension executableExtension : TreeSubstitution}
    {generated installedUnify : Subst}
    (unifyFacts :
      RepresentativeUnifySuccessorFacts prog gt before middle left right result
        bodyRest bodyExecutableTail sourceExtension executableExtension
        generated installedUnify)
    {head : NestedCallHead middle.carrier}
    (ready : MaterializedNestedCallReady middle head) :
    ∃ rejected : Nat, ∃ skippedBranches : List ClauseBranch,
      ∃ skippedClauses : List PLeaTTa.Clause,
      ∃ finish : PreparedCursor, ∃ branch : ClauseBranch,
      ∃ clause : PLeaTTa.Clause, ∃ branchTail : List ClauseBranch,
      ∃ clauseTail : List PLeaTTa.Clause, ∃ altTail : List PLeaTTa.Alt,
      ∃ copied : PLeaTTa.Clause, ∃ installedCall : Subst,
      ∃ after : RepresentativeActivePayloadState,
        RepresentativeNestedCallSuccessorFacts prog gt middle head rejected
            skippedBranches skippedClauses finish branch clause branchTail
            clauseTail altTail copied installedCall after ∧
          ∃ run : CertifiedPrefix prog gt
              [.unify,
                .localCall rejected
                  (requestFor head.predicate head.referencePayload
                    middle.carrier.index.current)]
              (.active (RepresentativePersistentFreeActivePayloadState.ofLegacy before))
              (.active (RepresentativePersistentFreeActivePayloadState.ofLegacy after)),
            run.states =
              [.active (RepresentativePersistentFreeActivePayloadState.ofLegacy before),
                .active (RepresentativePersistentFreeActivePayloadState.ofLegacy middle),
                .active (RepresentativePersistentFreeActivePayloadState.ofLegacy after)] ∧
              (CertifiedPrefix.split [.unify]
                [.localCall rejected
                  (requestFor head.predicate head.referencePayload
                    middle.carrier.index.current)] run).1 =
                .active (RepresentativePersistentFreeActivePayloadState.ofLegacy middle) := by
  obtain
    ⟨rejected, skippedBranches, skippedClauses, finish, branch, clause,
      branchTail, clauseTail, altTail, copied, installedCall, after,
      callFacts⟩ :=
    ready.pushDetailed (prog := prog) (gt := gt)
  let callTransition :
      CertifiedTransition prog gt
        (.localCall rejected
          (requestFor head.predicate head.referencePayload
            middle.carrier.index.current))
        (.active (RepresentativePersistentFreeActivePayloadState.ofLegacy middle))
        (.active (RepresentativePersistentFreeActivePayloadState.ofLegacy after)) :=
    .localCall callFacts
  let run :
      CertifiedPrefix prog gt
        [.unify,
          .localCall rejected
            (requestFor head.predicate head.referencePayload
              middle.carrier.index.current)]
        (.active (RepresentativePersistentFreeActivePayloadState.ofLegacy before))
        (.active (RepresentativePersistentFreeActivePayloadState.ofLegacy after)) :=
    .cons (.unify unifyFacts)
      (.cons callTransition
        (.nil (.active
          (RepresentativePersistentFreeActivePayloadState.ofLegacy after))))
  exact
    ⟨rejected, skippedBranches, skippedClauses, finish, branch, clause,
      branchTail, clauseTail, altTail, copied, installedCall, after, callFacts,
      run, rfl, rfl⟩

end RepresentativeUnifySuccessorFacts

end PLeaTTa.PrologHeterogeneousPrefixBridge
