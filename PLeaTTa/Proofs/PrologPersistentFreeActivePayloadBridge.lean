-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologPersistentFreeActivePayloadBridge
Purpose: State active retained-call correspondence without retaining or
  fabricating a historical persistent machine state.
Trusted boundary: none
Main exports:
  PersistentFreeActiveProductPayloadResourceRelatesAt,
  PersistentFreeActivePayloadState,
  RepresentativePersistentFreeActivePayloadState
-/
import PLeaTTa.Proofs.PrologNestedCallReadyBridge

namespace PLeaTTa.PrologPersistentFreeActivePayloadBridge

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
open PrologCurrentSessionPayloadBridge
open PrologMguComposition
open PrologProductResourceContextBridge
open PrologProductResourceTransitionBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
open PrologSourceProductContextBridge
open PrologStateBridge

/-!
`OpenedCall` and `PendingCall` are creation packets, not persistent resources.
Both contain a historical persistent state.  Retaining either packet after a
nested call, assertion, or allocator advance makes an unsound restoration
available; pairing an older cursor with the current state instead fabricates
an activation which never occurred.

The relation below consumes only the data which remains meaningful:

* the current `Session` and current `OpenConf`;
* the predicate's typed cut scope;
* the occurrence-indexed payload zipper, whose head snapshot already owns the
  compact activation and control origins; and
* the literal current source/executable resource shapes.

Historical origins are therefore derived from the dependent payload head,
never duplicated as freely chosen carrier fields.  The current domination
facts remain recursive over that same payload value.
-/

/-- Active retained-call correspondence with no historical persistent packet.

Most resource equations are already constructor fields of `payloadContext`:
the active resource's continuation, query, barrier, cursor ownership, and the
complete outer alignment.  The two explicit alternative equations below are
the remaining live-machine facts. -/
structure PersistentFreeActiveProductPayloadResourceRelatesAt
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (predicateScope : CutScopeId) (session : Session)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (altTail : List PLeaTTa.Alt)
    (bodyBarrier callerBarrier : Nat)
    (bodyReferences : List PeTTaSpec.PrologCore.Goal)
    (bodyExecutables : List PLeaTTa.Goal)
    (callerReferences : List PeTTaSpec.PrologCore.Goal)
    (callerExecutables : List PLeaTTa.Goal)
    (outer : List ControlSegment)
    (current : Substitution) (runtime : Subst) (qterm : Atom)
    (active : RetainedAlternativeSegment)
    (resources : List RetainedAlternativeSegment)
    (callerScope outerScope : CutScopeId)
    (context : ActiveProductContext)
    (baseAlts : List PLeaTTa.Alt)
    (source : Search) (state : OpenConf)
    (payloadContext :
      ActiveProductPayloadContextAt alpha support qterm predicateScope finish
        branch branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context) : Prop where
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
  activeAlts : active.alts = altTail
  actualAlts :
    state.control.alts = flattenOwnedAlts (active :: resources) baseAlts
  sourceShape :
    source =
      ActiveProductContext.plug context
        (activeSourceProductAt callerScope predicateScope finish branch
          branchTail current bodyReferences callerReferences)
  endpointsCurrent :
    endpointsBelow payloadContext session.resolver.nextFresh
      state.persistent.counter
  activationOrdered : ActivationOrdered payloadContext
  activationOrigins :
    LocalActivationOriginSpineRelates session payloadContext
  controlOrigins :
    LocalControlOriginSpineRelates baseAlts state.frames
      state.control.barriers payloadContext

namespace PersistentFreeActiveProductPayloadResourceRelatesAt

/-- The exact head occurrence's historical activation is dominated by the
current session; no historical session can be recovered from this fact. -/
theorem activationExtends
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
        source state payloadContext) :
    (headCell payloadContext).snapshot.activationOrigin.Extends session :=
  LocalActivationOriginSpineRelates.headExtends payloadContext
    agreement.activationOrigins

/-- The historical activation's cut high-water is tied to the literal typed
scope of this exact active occurrence. -/
theorem activationCutScope
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
        source state payloadContext) :
    (headCell payloadContext).snapshot.activationOrigin.nextCutScope =
      predicateScope + 1 :=
  LocalActivationOriginSpineRelates.headCutScope payloadContext
    agreement.activationOrigins

/-- Legacy current-session active relations embed without weakening any live
state or payload fact.  The discarded packet fields are not projected into
the target relation. -/
def ofLegacy
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {session : Session}
    {pending : DemandDrivenCallStep.PendingCall}
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
      ActiveProductPayloadContext alpha support qterm opened finish branch
        branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context}
    (agreement :
      SpinedActiveProductPayloadResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened session pending finish branch branchTail
        altTail bodyBarrier callerBarrier bodyReferences bodyExecutables
        callerReferences callerExecutables outer current runtime qterm active
        resources callerScope outerScope context baseAlts source state
        payloadContext) :
    PersistentFreeActiveProductPayloadResourceRelatesAt freshFrontier alpha
      support canonical referenceBase opened.scope session finish branch
      branchTail altTail bodyBarrier callerBarrier bodyReferences
      bodyExecutables callerReferences callerExecutables outer current runtime
      qterm active resources callerScope outerScope context baseAlts source
      state payloadContext :=
  { ready := agreement.core.control.ready
    activeAlts := agreement.core.resourceStack.activeAlts
    actualAlts := agreement.core.resourceStack.actualAlts
    sourceShape := by
      simpa [activeSourceProduct] using agreement.core.sourceShape
    endpointsCurrent := agreement.endpointsCurrent
    activationOrdered := agreement.activationOrdered
    activationOrigins := agreement.activationOrigins
    controlOrigins := agreement.controlOrigins }

end PersistentFreeActiveProductPayloadResourceRelatesAt

/-! ## Type-valued persistent-free carrier -/

/-- All data indices of one active occurrence, retaining only current
persistent state and the typed predicate scope. -/
structure PersistentFreeActivePayloadIndex where
  freshFrontier : FreshFrontierRelation
  alpha : List (LogicVar × String)
  support : List (LogicVar × String)
  canonical : TreeSubstitution
  referenceBase : Substitution
  predicateScope : CutScopeId
  session : Session
  finish : PreparedCursor
  branch : ClauseBranch
  branchTail : List ClauseBranch
  altTail : List PLeaTTa.Alt
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
  active : RetainedAlternativeSegment
  resources : List RetainedAlternativeSegment
  callerScope : CutScopeId
  outerScope : CutScopeId
  context : ActiveProductContext
  baseAlts : List PLeaTTa.Alt
  source : Search
  openConf : OpenConf

namespace PersistentFreeActivePayloadIndex

abbrev PayloadContext (index : PersistentFreeActivePayloadIndex) :=
  ActiveProductPayloadContextAt index.alpha index.support index.qterm
    index.predicateScope index.finish index.branch index.branchTail
    index.bodyBarrier index.callerBarrier index.callerReferences
    index.callerExecutables index.outer index.active index.resources
    index.callerScope index.outerScope index.context

abbrev Relates (index : PersistentFreeActivePayloadIndex)
    (payloadContext : index.PayloadContext) :=
  PersistentFreeActiveProductPayloadResourceRelatesAt index.freshFrontier
    index.alpha index.support index.canonical index.referenceBase
    index.predicateScope index.session index.finish index.branch
    index.branchTail index.altTail index.bodyBarrier index.callerBarrier
    index.bodyReferences index.bodyExecutables index.callerReferences
    index.callerExecutables index.outer index.current index.runtime index.qterm
    index.active index.resources index.callerScope index.outerScope
    index.context index.baseAlts index.source index.openConf payloadContext

end PersistentFreeActivePayloadIndex

/-- One exact source/fine/payload state from which no stale persistent packet
can be projected. -/
structure PersistentFreeActivePayloadState where
  index : PersistentFreeActivePayloadIndex
  payloadContext : index.PayloadContext
  agreement : index.Relates payloadContext

namespace PersistentFreeActivePayloadState

def sourceState (state : PersistentFreeActivePayloadState) : State :=
  .running state.index.session state.index.source

def fineState (state : PersistentFreeActivePayloadState) :
    DemandDrivenCallStep.FineConf :=
  .ready state.index.openConf

/-- Erase a legacy carrier while preserving both literal machine endpoints. -/
def ofLegacy (state : PrologNestedCallChainBridge.ActivePayloadState) :
    PersistentFreeActivePayloadState :=
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
        bodyReferences := state.index.bodyReferences
        bodyExecutables := state.index.bodyExecutables
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
      PersistentFreeActiveProductPayloadResourceRelatesAt.ofLegacy
        state.agreement }

@[simp] theorem ofLegacy_sourceState
    (state : PrologNestedCallChainBridge.ActivePayloadState) :
    (ofLegacy state).sourceState = state.sourceState := by
  simp [ofLegacy, sourceState,
    PrologNestedCallChainBridge.ActivePayloadState.sourceState]

@[simp] theorem ofLegacy_fineState
    (state : PrologNestedCallChainBridge.ActivePayloadState) :
    (ofLegacy state).fineState = state.fineState := by
  simp [ofLegacy, fineState,
    PrologNestedCallChainBridge.ActivePayloadState.fineState]

end PersistentFreeActivePayloadState

/-- Persistent-free active state with its exact cumulative residual
representative. -/
structure RepresentativePersistentFreeActivePayloadState where
  carrier : PersistentFreeActivePayloadState
  representative : TreeSubstitution
  cumulative :
    AlphaCumulativeResidualVariantAgreesOnWith carrier.index.alpha
      carrier.index.support carrier.index.canonical carrier.index.referenceBase
      carrier.index.runtime representative

namespace RepresentativePersistentFreeActivePayloadState

/-- Legacy representative carriers embed without changing their source or
fine endpoints. -/
def ofLegacy
    (state : PrologNestedCallReadyBridge.RepresentativeActivePayloadState) :
    RepresentativePersistentFreeActivePayloadState :=
  { carrier := PersistentFreeActivePayloadState.ofLegacy state.carrier
    representative := state.representative
    cumulative := by
      simpa [PersistentFreeActivePayloadState.ofLegacy] using state.cumulative }

end RepresentativePersistentFreeActivePayloadState

end PLeaTTa.PrologPersistentFreeActivePayloadBridge
