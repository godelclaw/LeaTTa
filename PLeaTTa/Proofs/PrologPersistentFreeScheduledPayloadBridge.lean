-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologPersistentFreeScheduledPayloadBridge
Purpose: State post-body-success correspondence without retaining or
  fabricating historical call-entry packets.
Trusted boundary: none
Main exports:
  PersistentFreeScheduledProductPayloadResourceRelatesAt,
  PersistentFreeScheduledPayloadState,
  RepresentativePersistentFreeScheduledPayloadState
-/
import PLeaTTa.Proofs.PrologCurrentSessionPayloadTransitionBridge
import PLeaTTa.Proofs.PrologNestedCallChainBridge

namespace PLeaTTa.PrologPersistentFreeScheduledPayloadBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologAlphaFreshFrontierBridge
open PrologControlSegmentSpineBridge
open PrologCurrentSessionPayloadBridge
open PrologCurrentSessionPayloadTransitionBridge
open PrologMguComposition
open PrologProductResourceContextBridge
open PrologProductResourceTransitionBridge
open PrologProductSchedulingBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
open PrologSourceProductContextBridge
open PrologStateBridge

/-!
`OpenedCall` and `PendingCall` are creation packets, not live scheduled-state
resources.  Retaining either after a clause body succeeds leaves a stale
persistent state available to later consumers.  The relation below keeps only
the current `Session` and `OpenConf`, the typed predicate scope, the exact
retained-resource zipper, and its compact activation/control origins.

The completed body segment is deliberately absent.  A scheduled state starts
at the caller continuation; the retained predicate cursor survives only in the
right branch of `scheduledSourceProductAt` and in the payload head.
-/

/-- Post-body-success correspondence with no historical persistent packet.

The current alternative equation owns every live retained resource exactly
once.  Immutable occurrence origins recover the outer alternatives, cache,
frames, and typed allocator chronology without restoring an old world or
counter. -/
structure PersistentFreeScheduledProductPayloadResourceRelatesAt
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (predicateScope : CutScopeId) (session : Session)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (altTail : List PLeaTTa.Alt)
    (bodyBarrier callerBarrier : Nat)
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
      ScheduledProductPayloadContextAt alpha support qterm predicateScope
        finish branch branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context) : Prop where
  /-- Only the caller segment and older segments remain executable. -/
  ready :
    SpinedReadyTaskRelates freshFrontier alpha support canonical
      referenceBase session current runtime qterm
      ({ barrier := callerBarrier
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
        (scheduledSourceProductAt callerScope predicateScope finish branch
          branchTail current callerReferences)
  endpointsCurrent :
    endpointsBelow payloadContext session.resolver.nextFresh
      state.persistent.counter
  activationOrdered : ActivationOrdered payloadContext
  activationOrigins :
    LocalActivationOriginSpineRelates session payloadContext
  controlOrigins :
    LocalControlOriginSpineRelates baseAlts state.frames
      state.control.barriers payloadContext

namespace PersistentFreeScheduledProductPayloadResourceRelatesAt

/-- A retained local bank contains branches only.  This is the load-bearing
replacement for the legacy relation's explicit `retainedAltsZero` field: it is
derived from the same occurrence-indexed ownership cell as the scheduled
cursor, rather than from a historical pending packet. -/
theorem retainedAltsZero
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {predicateScope : CutScopeId} {session : Session}
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
    {source : Search} {state : OpenConf}
    {payloadContext :
      ScheduledProductPayloadContextAt alpha support qterm predicateScope
        finish branch branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context}
    (agreement :
      PersistentFreeScheduledProductPayloadResourceRelatesAt freshFrontier
        alpha support canonical referenceBase predicateScope session finish
        branch branchTail altTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer current runtime qterm active resources
        callerScope outerScope context baseAlts source state payloadContext) :
    PLeaTTa.barrierCount altTail = 0 := by
  rw [← agreement.activeAlts]
  exact
    RetainedAlternativeSegment.HasIndexedOwnershipAt.barrierCount_zero
      (headCell payloadContext).ownership

/-- The exact head occurrence's historical activation is dominated by the
current session; no historical session can be reconstructed from this fact. -/
theorem activationExtends
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {predicateScope : CutScopeId} {session : Session}
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
    {source : Search} {state : OpenConf}
    {payloadContext :
      ScheduledProductPayloadContextAt alpha support qterm predicateScope
        finish branch branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context}
    (agreement :
      PersistentFreeScheduledProductPayloadResourceRelatesAt freshFrontier
        alpha support canonical referenceBase predicateScope session finish
        branch branchTail altTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer current runtime qterm active resources
        callerScope outerScope context baseAlts source state payloadContext) :
    (headCell payloadContext).snapshot.activationOrigin.Extends session :=
  LocalActivationOriginSpineRelates.headExtends payloadContext
    agreement.activationOrigins

/-- The historical activation's cut frontier is tied to the literal typed
predicate scope of this exact scheduled occurrence. -/
theorem activationCutScope
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {predicateScope : CutScopeId} {session : Session}
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
    {source : Search} {state : OpenConf}
    {payloadContext :
      ScheduledProductPayloadContextAt alpha support qterm predicateScope
        finish branch branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context}
    (agreement :
      PersistentFreeScheduledProductPayloadResourceRelatesAt freshFrontier
        alpha support canonical referenceBase predicateScope session finish
        branch branchTail altTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer current runtime qterm active resources
        callerScope outerScope context baseAlts source state payloadContext) :
    (headCell payloadContext).snapshot.activationOrigin.nextCutScope =
      predicateScope + 1 :=
  LocalActivationOriginSpineRelates.headCutScope payloadContext
    agreement.activationOrigins

/-- Legacy current-session scheduled relations embed without weakening any
live state or payload fact.  Discarded packet fields are not projected into
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
      ScheduledProductPayloadContext alpha support qterm opened finish branch
        branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context}
    (agreement :
      SpinedScheduledProductPayloadResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened session pending finish branch branchTail
        altTail bodyBarrier callerBarrier callerReferences callerExecutables
        outer current runtime qterm active resources callerScope outerScope
        context baseAlts source state payloadContext) :
    PersistentFreeScheduledProductPayloadResourceRelatesAt freshFrontier alpha
      support canonical referenceBase opened.scope session finish branch
      branchTail altTail bodyBarrier callerBarrier callerReferences
      callerExecutables outer current runtime qterm active resources
      callerScope outerScope context baseAlts source state payloadContext :=
  { ready := agreement.core.control.ready
    activeAlts := agreement.core.resourceStack.activeAlts
    actualAlts := agreement.core.resourceStack.actualAlts
    sourceShape := by
      simpa [scheduledSourceProduct] using agreement.core.sourceShape
    endpointsCurrent := agreement.endpointsCurrent
    activationOrdered := agreement.activationOrdered
    activationOrigins := agreement.activationOrigins
    controlOrigins := agreement.controlOrigins }

end PersistentFreeScheduledProductPayloadResourceRelatesAt

/-! ## Type-valued persistent-free carrier -/

/-- All data indices of one scheduled occurrence, retaining only current
persistent state and the typed predicate scope. -/
structure PersistentFreeScheduledPayloadIndex where
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

namespace PersistentFreeScheduledPayloadIndex

abbrev PayloadContext (index : PersistentFreeScheduledPayloadIndex) :=
  ScheduledProductPayloadContextAt index.alpha index.support index.qterm
    index.predicateScope index.finish index.branch index.branchTail
    index.bodyBarrier index.callerBarrier index.callerReferences
    index.callerExecutables index.outer index.active index.resources
    index.callerScope index.outerScope index.context

abbrev Relates (index : PersistentFreeScheduledPayloadIndex)
    (payloadContext : index.PayloadContext) :=
  PersistentFreeScheduledProductPayloadResourceRelatesAt index.freshFrontier
    index.alpha index.support index.canonical index.referenceBase
    index.predicateScope index.session index.finish index.branch
    index.branchTail index.altTail index.bodyBarrier index.callerBarrier
    index.callerReferences index.callerExecutables index.outer index.current
    index.runtime index.qterm index.active index.resources index.callerScope
    index.outerScope index.context index.baseAlts index.source index.openConf
    payloadContext

end PersistentFreeScheduledPayloadIndex

/-- One exact source/fine/payload scheduled state from which no stale
persistent packet can be projected. -/
structure PersistentFreeScheduledPayloadState where
  index : PersistentFreeScheduledPayloadIndex
  payloadContext : index.PayloadContext
  agreement : index.Relates payloadContext

namespace PersistentFreeScheduledPayloadState

def sourceState (state : PersistentFreeScheduledPayloadState) : State :=
  .running state.index.session state.index.source

def fineState (state : PersistentFreeScheduledPayloadState) :
    DemandDrivenCallStep.FineConf :=
  .ready state.index.openConf

def cellIdentities (state : PersistentFreeScheduledPayloadState) :
    List PrologNestedCallChainBridge.PayloadCellIdentity :=
  PrologNestedCallChainBridge.SourceControlResourcePayloadContextAgrees.cellIdentities
    state.payloadContext

def cellCount (state : PersistentFreeScheduledPayloadState) : Nat :=
  ActiveProductPayloadContext.cellCount state.payloadContext

/-- The scheduled task payload selected by the literal current caller control.
No completed body segment is present in this projection. -/
def headPayload (state : PersistentFreeScheduledPayloadState) :=
  state.agreement.ready.2.2.2.headPayload

theorem cellIdentities_length (state : PersistentFreeScheduledPayloadState) :
    state.cellIdentities.length = state.cellCount :=
  PrologNestedCallChainBridge.SourceControlResourcePayloadContextAgrees.cellIdentities_length_eq_cellCount
    state.payloadContext

end PersistentFreeScheduledPayloadState

/-- Persistent-free scheduled state with its exact cumulative residual
representative. -/
structure RepresentativePersistentFreeScheduledPayloadState where
  carrier : PersistentFreeScheduledPayloadState
  representative : TreeSubstitution
  cumulative :
    AlphaCumulativeResidualVariantAgreesOnWith carrier.index.alpha
      carrier.index.support carrier.index.canonical carrier.index.referenceBase
      carrier.index.runtime representative

end PLeaTTa.PrologPersistentFreeScheduledPayloadBridge
