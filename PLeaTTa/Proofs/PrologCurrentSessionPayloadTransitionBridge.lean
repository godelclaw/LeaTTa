-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologCurrentSessionPayloadTransitionBridge
Purpose: Preserve exact current-session payload ownership through local
  product body success and clause-local cut.
Trusted boundary: none
Main exports:
  SpinedScheduledProductPayloadResourceRelatesAt,
  SpinedCommittedProductPayloadResourceRelatesAt,
  SpinedActiveProductPayloadResourceRelatesAt.afterBodyAnswer,
  SpinedActiveProductPayloadResourceRelatesAt.afterCut
-/
import PLeaTTa.Proofs.PrologCurrentSessionPayloadBridge

namespace PLeaTTa.PrologCurrentSessionPayloadTransitionBridge

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
open PrologOrdinaryStepBridge
open PrologProductResourceContextBridge
open PrologProductResourceTransitionBridge
open PrologProductSchedulingBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
open PrologSourceProductContextBridge
open PrologStateBridge

/-- The payload zipper retained after a clause body succeeds.  The source
focus changes to the private scheduling choice, but no retained cursor,
resource descriptor, or immutable payload cell moves. -/
abbrev ScheduledProductPayloadContext
    (alpha support : List (LogicVar × String)) (qterm : Atom)
    (opened : OpenedCall) (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (bodyBarrier callerBarrier : Nat)
    (callerReferences : List PeTTaSpec.PrologCore.Goal)
    (callerExecutables : List PLeaTTa.Goal)
    (outer : List ControlSegment)
    (active : RetainedAlternativeSegment)
    (resources : List RetainedAlternativeSegment)
    (callerScope outerScope : CutScopeId)
    (context : ActiveProductContext) :=
  ActiveProductPayloadContext alpha support qterm opened finish branch
    branchTail bodyBarrier callerBarrier callerReferences callerExecutables
    outer active resources callerScope outerScope context

/-- The exact payload tail remaining after the selected clause-local cut
consumes its active retained alternative. -/
abbrev CommittedProductPayloadContext
    (alpha support : List (LogicVar × String)) (qterm : Atom)
    (callerBarrier : Nat) (outer : List ControlSegment)
    (resources : List RetainedAlternativeSegment)
    (callerScope outerScope : CutScopeId)
    (context : ActiveProductContext) :=
  SourceControlResourcePayloadContextAgrees alpha support qterm callerBarrier
    outer resources callerScope context outerScope

namespace ActiveProductPayloadContext

/- `ActiveProductPayloadContext` is an abbreviation whose head symbol unfolds
to `SourceControlResourcePayloadContextAgrees`.  Use the explicitly qualified
functions in this namespace: dot notation on a value resolves through the
unfolded inductive namespace rather than through this abbreviation namespace. -/

/-- Remove the unique active payload cell and expose the literal outer tail.

The impossible empty case is excluded by the dependent indices: an active
product always has one caller segment, one retained resource, and one source
context frame. -/
def outerPayload
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {opened : OpenedCall} {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    (payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish branch
        branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context) :
    CommittedProductPayloadContext alpha support qterm callerBarrier outer
      resources callerScope outerScope context :=
  match payloadContext with
  | .cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outerAgrees =>
      outerAgrees

/-- The active-product-specific pop is exactly the generic linear zipper
tail.  Naming the equality avoids dependent abbreviation unfolding at every
chronology-preservation site. -/
theorem outerPayload_eq_tail
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {opened : OpenedCall} {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    (payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish branch
        branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context) :
    outerPayload payloadContext =
      SourceControlResourcePayloadContextAgrees.tail payloadContext := by
  cases payloadContext
  rfl

/-- Domination of the complete active zipper entails domination of its exact
outer tail. -/
theorem endpointsBelow_outerPayload
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {opened : OpenedCall} {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {referenceFloor executableFloor : Nat}
    (payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish branch
        branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context)
    (below :
      endpointsBelow payloadContext referenceFloor executableFloor) :
    endpointsBelow (outerPayload payloadContext) referenceFloor
      executableFloor := by
  cases payloadContext with
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees =>
      exact below.2.2

/-- Count the linear payload cells in one exact dependent zipper. -/
def cellCount
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext} :
    SourceControlResourcePayloadContextAgrees alpha support qterm currentBarrier
        segments resources inner context outer →
      Nat
  | .nil _ _ => 0
  | .cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outerAgrees =>
      cellCount outerAgrees + 1

/-- Removing the active payload cell decreases the exact zipper by one. -/
theorem cellCount_outerPayload
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {opened : OpenedCall} {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    (payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish branch
        branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context) :
    cellCount payloadContext =
      cellCount (outerPayload payloadContext) + 1 := by
  cases payloadContext
  rfl

/-- The committed tail has strictly fewer cells than the active zipper.
Consequently a purported cut result retaining the active cell cannot satisfy
the public payload-count guarantee. -/
theorem cellCount_outerPayload_lt
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {opened : OpenedCall} {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    (payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish branch
        branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context) :
    cellCount (outerPayload payloadContext) < cellCount payloadContext := by
  rw [cellCount_outerPayload payloadContext]
  omega

end ActiveProductPayloadContext

/-- Current-session scheduled state with the same exact payload zipper as the
active state from which it arose. -/
structure SpinedScheduledProductPayloadResourceRelatesAt
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (opened : OpenedCall) (session : Session)
    (pending : DemandDrivenCallStep.PendingCall)
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
      ScheduledProductPayloadContext alpha support qterm opened finish branch
        branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context) : Prop where
  core :
    SpinedScheduledProductResourceRelatesAt freshFrontier alpha support
      canonical referenceBase opened session pending finish branch branchTail
      altTail bodyBarrier callerBarrier callerReferences callerExecutables outer
      current runtime qterm active resources callerScope outerScope context
      baseAlts source state
  endpointsCurrent :
    endpointsBelow payloadContext session.resolver.nextFresh
      state.persistent.counter
  activationOrdered : ActivationOrdered payloadContext

/-- Current-session committed state whose payload zipper is exactly the outer
tail left after the active resource has been consumed. -/
structure SpinedCommittedProductPayloadResourceRelatesAt
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (opened : OpenedCall) (session : Session)
    (pending : DemandDrivenCallStep.PendingCall)
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
  core :
    SpinedCommittedProductResourceRelatesAt freshFrontier alpha support
      canonical referenceBase opened session pending bodyBarrier callerBarrier
      bodyReferences bodyExecutables callerReferences callerExecutables outer
      current runtime qterm resources callerScope outerScope context baseAlts
      source state
  endpointsCurrent :
    endpointsBelow payloadContext session.resolver.nextFresh
      state.persistent.counter
  activationOrdered : ActivationOrdered payloadContext

namespace SpinedScheduledProductPayloadResourceRelatesAt

/-- Erase immutable payload evidence without changing any scheduled-state
index. -/
def weak
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
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
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
    SpinedScheduledProductResourceRelatesAt freshFrontier alpha support canonical
      referenceBase opened session pending finish branch branchTail altTail
      bodyBarrier callerBarrier callerReferences callerExecutables outer current
      runtime qterm active resources callerScope outerScope context baseAlts
      source state :=
  agreement.core

/-- Transport a scheduled payload state to a later source session.  The
executable state and exact payload zipper remain literal; only the supplied
persistent-state witness and source high-water chronology advance. -/
def reindex
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {session nextSession : Session}
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
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
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
        context baseAlts source state payloadContext)
    (persistent :
      SessionRelatesPersistent freshFrontier nextSession state.persistent)
    (advanced : SessionHighWatersExtend session nextSession) :
    SpinedScheduledProductPayloadResourceRelatesAt freshFrontier alpha support
      canonical referenceBase opened nextSession pending finish branch
      branchTail altTail bodyBarrier callerBarrier callerReferences
      callerExecutables outer current runtime qterm active resources callerScope
      outerScope context baseAlts source state payloadContext := by
  rcases agreement.core.control.ready with
    ⟨_oldPersistent, currentControl, queryTerm, payload⟩
  have nextControl :
      SpinedScheduledProductRelatesAt freshFrontier alpha support canonical
        referenceBase opened nextSession pending finish branch branchTail
        altTail bodyBarrier callerBarrier callerReferences callerExecutables
        outer current runtime qterm state :=
    ⟨⟨persistent, currentControl, queryTerm, payload⟩,
      agreement.core.control.sessionAdvanced.trans advanced,
      agreement.core.control.retainedAlts,
      agreement.core.control.retainedAltsZero,
      agreement.core.control.retainedBarriers,
      agreement.core.control.bodyBarrierTag,
      agreement.core.control.frames⟩
  have nextCore :
      SpinedScheduledProductResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened nextSession pending finish branch
        branchTail altTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer current runtime qterm active resources
        callerScope outerScope context baseAlts source state :=
    ⟨nextControl, agreement.core.resourceStack, agreement.core.sourceShape⟩
  exact
    ⟨nextCore,
      endpointsBelow_mono payloadContext agreement.endpointsCurrent
        advanced.fresh (Nat.le_refl _),
      agreement.activationOrdered⟩

/-- A scheduled successor cannot be indexed by a fresh allocator below its
opener. -/
theorem rejectsFreshRegression
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
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {source : Search} {state : OpenConf}
    {payloadContext :
      ScheduledProductPayloadContext alpha support qterm opened finish branch
        branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context}
    (regressed :
      session.resolver.nextFresh < opened.session.resolver.nextFresh) :
    ¬ SpinedScheduledProductPayloadResourceRelatesAt freshFrontier alpha support
      canonical referenceBase opened session pending finish branch branchTail
      altTail bodyBarrier callerBarrier callerReferences callerExecutables outer
      current runtime qterm active resources callerScope outerScope context
      baseAlts source state payloadContext := by
  intro agreement
  exact
    (Nat.not_lt_of_ge agreement.core.control.sessionAdvanced.fresh) regressed

end SpinedScheduledProductPayloadResourceRelatesAt

namespace SpinedCommittedProductPayloadResourceRelatesAt

/-- Erase immutable payload evidence without changing any committed-state
index. -/
def weak
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
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {source : Search} {state : OpenConf}
    {payloadContext :
      CommittedProductPayloadContext alpha support qterm callerBarrier outer
        resources callerScope outerScope context}
    (agreement :
      SpinedCommittedProductPayloadResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened session pending bodyBarrier callerBarrier
        bodyReferences bodyExecutables callerReferences callerExecutables outer
        current runtime qterm resources callerScope outerScope context baseAlts
        source state payloadContext) :
    SpinedCommittedProductResourceRelatesAt freshFrontier alpha support canonical
      referenceBase opened session pending bodyBarrier callerBarrier
      bodyReferences bodyExecutables callerReferences callerExecutables outer
      current runtime qterm resources callerScope outerScope context baseAlts
      source state :=
  agreement.core

/-- Transport a committed payload state to a later source session while the
exact surviving payload tail and executable state remain literal. -/
def reindex
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {session nextSession : Session}
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
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {source : Search} {state : OpenConf}
    {payloadContext :
      CommittedProductPayloadContext alpha support qterm callerBarrier outer
        resources callerScope outerScope context}
    (agreement :
      SpinedCommittedProductPayloadResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened session pending bodyBarrier callerBarrier
        bodyReferences bodyExecutables callerReferences callerExecutables outer
        current runtime qterm resources callerScope outerScope context baseAlts
        source state payloadContext)
    (persistent :
      SessionRelatesPersistent freshFrontier nextSession state.persistent)
    (advanced : SessionHighWatersExtend session nextSession) :
    SpinedCommittedProductPayloadResourceRelatesAt freshFrontier alpha support
      canonical referenceBase opened nextSession pending bodyBarrier
      callerBarrier bodyReferences bodyExecutables callerReferences
      callerExecutables outer current runtime qterm resources callerScope
      outerScope context baseAlts source state payloadContext := by
  rcases agreement.core.control.ready with
    ⟨_oldPersistent, currentControl, queryTerm, payload⟩
  have nextControl :
      SpinedCommittedProductRelatesAt freshFrontier alpha support canonical
        referenceBase opened nextSession pending bodyBarrier callerBarrier
        bodyReferences bodyExecutables callerReferences callerExecutables outer
        current runtime qterm state :=
    ⟨⟨persistent, currentControl, queryTerm, payload⟩,
      agreement.core.control.sessionAdvanced.trans advanced,
      agreement.core.control.outerAlts,
      agreement.core.control.cacheCoherent,
      agreement.core.control.frames⟩
  have nextCore :
      SpinedCommittedProductResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened nextSession pending bodyBarrier
        callerBarrier bodyReferences bodyExecutables callerReferences
        callerExecutables outer current runtime qterm resources callerScope
        outerScope context baseAlts source state :=
    ⟨nextControl, agreement.core.resourceStack, agreement.core.sourceShape⟩
  exact
    ⟨nextCore,
      endpointsBelow_mono payloadContext agreement.endpointsCurrent
        advanced.fresh (Nat.le_refl _),
      agreement.activationOrdered⟩

/-- A committed successor cannot be indexed by a fresh allocator below its
opener. -/
theorem rejectsFreshRegression
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
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {source : Search} {state : OpenConf}
    {payloadContext :
      CommittedProductPayloadContext alpha support qterm callerBarrier outer
        resources callerScope outerScope context}
    (regressed :
      session.resolver.nextFresh < opened.session.resolver.nextFresh) :
    ¬ SpinedCommittedProductPayloadResourceRelatesAt freshFrontier alpha support
      canonical referenceBase opened session pending bodyBarrier callerBarrier
      bodyReferences bodyExecutables callerReferences callerExecutables outer
      current runtime qterm resources callerScope outerScope context baseAlts
      source state payloadContext := by
  intro agreement
  exact
    (Nat.not_lt_of_ge agreement.core.control.sessionAdvanced.fresh) regressed

end SpinedCommittedProductPayloadResourceRelatesAt

namespace SpinedActiveProductPayloadResourceRelatesAt

/-- Successful completion of the selected body preserves every payload cell
at the same current source session and executable persistent counter. -/
theorem afterBodyAnswer
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
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
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {source : Search} {state : OpenConf}
    {payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish branch
        branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context}
    (agreement :
      SpinedActiveProductPayloadResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened session pending finish branch branchTail
        altTail bodyBarrier callerBarrier [] [] callerReferences
        callerExecutables outer current runtime qterm active resources
        callerScope outerScope context baseAlts source state payloadContext) :
    RawStep session source [] .none session
        (.running
          (ActiveProductContext.plug context
            (scheduledSourceProduct callerScope opened finish branch branchTail
              current callerReferences))) ∧
      DemandDrivenCallStep.StepsN prog gt 0
        (.ready state) (.ready state) ∧
      SpinedScheduledProductPayloadResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened session pending finish branch branchTail
        altTail bodyBarrier callerBarrier callerReferences callerExecutables
        outer current runtime qterm active resources callerScope outerScope
        context baseAlts
        (ActiveProductContext.plug context
          (scheduledSourceProduct callerScope opened finish branch branchTail
            current callerReferences))
        state payloadContext := by
  rcases
      PrologProductResourceTransitionBridge.SpinedActiveProductResourceRelates.afterBodyAnswer
        agreement.core with
    ⟨sourceStep, executableSteps, scheduled⟩
  exact
    ⟨sourceStep, executableSteps,
      ⟨scheduled, agreement.endpointsCurrent,
        agreement.activationOrdered⟩⟩

/-- Clause-local cut consumes the exact head payload cell while preserving the
literal outer payload tail at the same persistent high-waters. -/
theorem afterCut
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {session : Session}
    {pending : DemandDrivenCallStep.PendingCall}
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
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {source : Search} {state : OpenConf}
    {payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish branch
        branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context}
    (agreement :
      SpinedActiveProductPayloadResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened session pending finish branch branchTail
        altTail bodyBarrier callerBarrier (.cut :: bodyRest)
        (.cutAt bodyBarrier :: bodyExecutableTail)
        callerReferences callerExecutables outer current runtime qterm active
        resources callerScope outerScope context baseAlts source state
        payloadContext)
    (coherent : PLeaTTa.BarrierCacheCoherent state.toConf) :
    state.control.cur =
        some
          (.cutAt bodyBarrier ::
            (bodyExecutableTail ++
              (callerExecutables ++ flattenExecutables outer)),
            runtime) ∧
      RawStep session source
        [.pruned (retainedCursorToken opened finish branch branchTail)]
        .none session
        (.running
          (ActiveProductContext.plug context
            (cutSourceProduct callerScope opened current bodyRest
              callerReferences))) ∧
      DemandDrivenCallStep.Step prog gt (.ready state)
        (.ready
          (cutSuccessor state bodyBarrier
            (bodyExecutableTail ++
              (callerExecutables ++ flattenExecutables outer))
            runtime)) ∧
      SpinedCommittedProductPayloadResourceRelatesAt freshFrontier alpha
        support canonical referenceBase opened session pending bodyBarrier
        callerBarrier bodyRest bodyExecutableTail callerReferences
        callerExecutables outer current runtime qterm resources callerScope
        outerScope context baseAlts
        (ActiveProductContext.plug context
          (cutSourceProduct callerScope opened current bodyRest
            callerReferences))
        (cutSuccessor state bodyBarrier
          (bodyExecutableTail ++
            (callerExecutables ++ flattenExecutables outer))
          runtime)
        (ActiveProductPayloadContext.outerPayload payloadContext) ∧
      ActiveProductPayloadContext.cellCount payloadContext =
        ActiveProductPayloadContext.cellCount
          (ActiveProductPayloadContext.outerPayload payloadContext) + 1 ∧
      PLeaTTa.barrierCount state.control.alts =
        PLeaTTa.barrierCount
          (cutSuccessor state bodyBarrier
            (bodyExecutableTail ++
              (callerExecutables ++ flattenExecutables outer))
            runtime).control.alts + 1 := by
  rcases
      PrologProductResourceTransitionBridge.SpinedActiveProductResourceRelates.afterCut
        agreement.core coherent with
    ⟨executableHead, sourceStep, executableStep, committed, countDrop⟩
  have outerEndpoints :
      endpointsBelow
        (ActiveProductPayloadContext.outerPayload payloadContext)
        session.resolver.nextFresh
        (cutSuccessor state bodyBarrier
          (bodyExecutableTail ++
            (callerExecutables ++ flattenExecutables outer))
          runtime).persistent.counter := by
    simpa using
      ActiveProductPayloadContext.endpointsBelow_outerPayload payloadContext
        agreement.endpointsCurrent
  have outerOrdered :
      ActivationOrdered
        (ActiveProductPayloadContext.outerPayload payloadContext) := by
    rw [ActiveProductPayloadContext.outerPayload_eq_tail payloadContext]
    exact ActivationOrdered.tail payloadContext agreement.activationOrdered
  exact
    ⟨executableHead, sourceStep, executableStep,
      ⟨committed, outerEndpoints, outerOrdered⟩,
      ActiveProductPayloadContext.cellCount_outerPayload payloadContext,
      countDrop⟩

end SpinedActiveProductPayloadResourceRelatesAt

end PLeaTTa.PrologCurrentSessionPayloadTransitionBridge
