-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologProductResourceTransitionBridge
Purpose: Preserve exact retained-cursor/executable-alternative ownership
  through real arbitrary-depth local-product transitions.
Trusted boundary: none
Main exports:
  SpinedActiveProductRelates,
  ActiveProductResourceStackAgrees,
  SpinedRepresentativeProductActivation.spinedActiveProductRelates,
  SpinedRepresentativeProductActivation.activeResourceStackAgrees,
  SpinedActiveProductRelates.afterCutThroughResourceStack
-/
import PLeaTTa.Proofs.PrologProductResourceContextBridge
import PLeaTTa.Proofs.PrologProductSchedulingBridge

namespace PLeaTTa.PrologProductResourceTransitionBridge

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
open PrologOrdinaryStepBridge
open PrologProductResourceContextBridge
open PrologProductSchedulingBridge
open PrologRepresentativeProductActivationBridge
open PrologRepresentativeStepActivationBridge
open PrologSourceProductContextBridge
open PrologStateBridge

/-- Pulling an alternative changes only active control and the alternative
bank; the query term is inherited literally. -/
theorem pull_qterm {Binding : Type} (conf : PLeaTTa.Conf Binding) :
    (PLeaTTa.pull conf).qterm = conf.qterm := by
  unfold PLeaTTa.pull
  generalize resultEq :
    PLeaTTa.pullAuxTracked conf.barriers conf.alts = result
  cases result with
  | mk branch cache =>
      cases branch with
      | none => rfl
      | some pulled =>
          rcases pulled with ⟨target, rest⟩
          cases target <;> rfl

/-!
`SegmentedActiveProductRelates` is intentionally insufficient here.  It gives
the selected body one barrier and the entire caller tail one other barrier,
whereas an arbitrary recursive spine retains a distinct barrier at every
older predicate region.  Reusing it at depth would silently retag those older
regions.

The relations below therefore preserve `TaskSpinePayloadAgrees` directly.
Logical control and executable resource ownership remain separate:

* `SpinedActiveProductRelates` certifies every flattened goal segment at its
  own barrier and carries the executable call marker/cache/frame facts.
* `ActiveProductResourceStackAgrees` ties the exact advanced source cursor to
  its exact executable alternative suffix, then aligns every older source
  frame and executable resource in inner-to-outer order.

The cut theorem consumes both certificates.  It reuses the already-proved
source cut and executable `cutToTracked` transition rather than re-specifying
either operation.
-/

/-! ## Spine-native task relations -/

/-- A ready executable task related to an arbitrary list of independently
tagged source control regions. -/
def SpinedReadyTaskRelates
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (session : Session) (current : Substitution)
    (runtime : Subst) (qterm : Atom)
    (segments : List ControlSegment) (state : OpenConf) : Prop :=
  SessionRelatesPersistent freshFrontier session state.persistent ∧
    state.control.cur =
      some (flattenExecutables segments, runtime) ∧
    state.control.qterm = qterm ∧
    TaskSpinePayloadAgrees alpha support canonical referenceBase current
      runtime segments

/-- Relation while one selected clause body is active above an arbitrary
caller-control spine.

The first two regions are named explicitly because the current body and its
immediate caller tail participate in scheduling.  `outer` retains every older
barrier pointwise. -/
structure SpinedActiveProductRelatesAt
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (opened : OpenedCall) (session : Session)
    (pending : DemandDrivenCallStep.PendingCall)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (altTail : List PLeaTTa.Alt)
    (bodyBarrier callerBarrier : Nat)
    (bodyReferences : List PeTTaSpec.PrologCore.Goal)
    (bodyExecutables : List PLeaTTa.Goal)
    (callerReferences : List PeTTaSpec.PrologCore.Goal)
    (callerExecutables : List PLeaTTa.Goal)
    (outer : List ControlSegment)
    (current : Substitution) (runtime : Subst) (qterm : Atom)
    (state : OpenConf) : Prop where
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
  sessionAdvanced :
    SessionHighWatersExtend opened.session session
  retainedAlts :
    state.control.alts =
      altTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts
  retainedAltsZero : PLeaTTa.barrierCount altTail = 0
  retainedBarriers :
    state.control.barriers =
      PLeaTTa.pushBarrierCache pending.outer.barriers
  bodyBarrierTag :
    bodyBarrier =
      pending.outer.barriers.getD
        (PLeaTTa.barrierCount pending.outer.alts) + 1
  frames : state.frames = pending.frames

/-- Backward-compatible exact specialization at the activation session.
This is definitionally the `At` relation, not a weaker wrapper. -/
abbrev SpinedActiveProductRelates
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (opened : OpenedCall) (pending : DemandDrivenCallStep.PendingCall)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (altTail : List PLeaTTa.Alt)
    (bodyBarrier callerBarrier : Nat)
    (bodyReferences : List PeTTaSpec.PrologCore.Goal)
    (bodyExecutables : List PLeaTTa.Goal)
    (callerReferences : List PeTTaSpec.PrologCore.Goal)
    (callerExecutables : List PLeaTTa.Goal)
    (outer : List ControlSegment)
    (current : Substitution) (runtime : Subst) (qterm : Atom)
    (state : OpenConf) : Prop :=
  SpinedActiveProductRelatesAt freshFrontier alpha support canonical
    referenceBase opened opened.session pending finish branch branchTail
    altTail bodyBarrier callerBarrier bodyReferences bodyExecutables
    callerReferences callerExecutables outer current runtime qterm state

/-- Control-independent active predicate resources projected from the
spine-native logical relation. -/
def SpinedActiveProductRelatesAt.resources
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
    {state : OpenConf}
    (agreement :
      SpinedActiveProductRelatesAt freshFrontier alpha support canonical
        referenceBase opened session pending finish branch branchTail altTail
        bodyBarrier callerBarrier bodyReferences bodyExecutables
        callerReferences callerExecutables outer current runtime qterm state) :
    RetainedProductResources bodyBarrier pending altTail state :=
  ⟨agreement.retainedAlts, agreement.retainedAltsZero,
    agreement.retainedBarriers, agreement.bodyBarrierTag⟩

/-- Compatibility projection for the exact opener-session specialization. -/
def SpinedActiveProductRelates.resources
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {bodyReferences : List PeTTaSpec.PrologCore.Goal}
    {bodyExecutables : List PLeaTTa.Goal}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {current : Substitution} {runtime : Subst} {qterm : Atom}
    {state : OpenConf}
    (agreement :
      SpinedActiveProductRelates freshFrontier alpha support canonical
        referenceBase opened pending finish branch branchTail altTail
        bodyBarrier callerBarrier bodyReferences bodyExecutables
        callerReferences callerExecutables outer current runtime qterm state) :
    RetainedProductResources bodyBarrier pending altTail state :=
  SpinedActiveProductRelatesAt.resources agreement

/-- Spine-native state relation after a clause-local cut removed the active
predicate's later-clause alternatives and marker. -/
structure SpinedCommittedProductRelatesAt
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
    (state : OpenConf) : Prop where
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
  sessionAdvanced :
    SessionHighWatersExtend opened.session session
  outerAlts : state.control.alts = pending.outer.alts
  cacheCoherent : PLeaTTa.BarrierCacheCoherent state.toConf
  frames : state.frames = pending.frames

/-- Exact opener-session specialization of the committed relation. -/
abbrev SpinedCommittedProductRelates
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (opened : OpenedCall) (pending : DemandDrivenCallStep.PendingCall)
    (bodyBarrier callerBarrier : Nat)
    (bodyReferences : List PeTTaSpec.PrologCore.Goal)
    (bodyExecutables : List PLeaTTa.Goal)
    (callerReferences : List PeTTaSpec.PrologCore.Goal)
    (callerExecutables : List PLeaTTa.Goal)
    (outer : List ControlSegment)
    (current : Substitution) (runtime : Subst) (qterm : Atom)
    (state : OpenConf) : Prop :=
  SpinedCommittedProductRelatesAt freshFrontier alpha support canonical
    referenceBase opened opened.session pending bodyBarrier callerBarrier
    bodyReferences bodyExecutables callerReferences callerExecutables outer
    current runtime qterm state

/-- Relation after a successful empty clause body has privately scheduled the
immediate caller region.  The retained clause bank remains live for later
backtracking, and every older control region keeps its original barrier. -/
structure SpinedScheduledProductRelatesAt
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
    (state : OpenConf) : Prop where
  ready :
    SpinedReadyTaskRelates freshFrontier alpha support canonical
      referenceBase session current runtime qterm
      ({ barrier := callerBarrier
         references := callerReferences
         executables := callerExecutables } ::
      outer)
      state
  sessionAdvanced :
    SessionHighWatersExtend opened.session session
  retainedAlts :
    state.control.alts =
      altTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts
  retainedAltsZero : PLeaTTa.barrierCount altTail = 0
  retainedBarriers :
    state.control.barriers =
      PLeaTTa.pushBarrierCache pending.outer.barriers
  bodyBarrierTag :
    bodyBarrier =
      pending.outer.barriers.getD
        (PLeaTTa.barrierCount pending.outer.alts) + 1
  frames : state.frames = pending.frames

/-- Exact opener-session specialization of the scheduled relation. -/
abbrev SpinedScheduledProductRelates
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (opened : OpenedCall) (pending : DemandDrivenCallStep.PendingCall)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (altTail : List PLeaTTa.Alt)
    (bodyBarrier callerBarrier : Nat)
    (callerReferences : List PeTTaSpec.PrologCore.Goal)
    (callerExecutables : List PLeaTTa.Goal)
    (outer : List ControlSegment)
    (current : Substitution) (runtime : Subst) (qterm : Atom)
    (state : OpenConf) : Prop :=
  SpinedScheduledProductRelatesAt freshFrontier alpha support canonical
    referenceBase opened opened.session pending finish branch branchTail
    altTail bodyBarrier callerBarrier callerReferences callerExecutables outer
    current runtime qterm state

/-! ## Exact source/executable resource stack -/

/-- Exact active resource ownership, independent of the currently executing
body control.

Both the suspended caller equation and the actual active-state equation are
kept.  The former is stable across body transitions; the latter prevents an
otherwise well-formed proof descriptor from floating free of the running
machine state. -/
structure ActiveProductResourceStackAgrees
    (alpha : List (LogicVar × String)) (qterm : Atom)
    (bodyBarrier callerBarrier : Nat)
    (pending : DemandDrivenCallStep.PendingCall)
    (cursor : PreparedCursor) (executableRest : List PLeaTTa.Goal)
    (altTail : List PLeaTTa.Alt)
    (active : RetainedAlternativeSegment)
    (outer : List ControlSegment)
    (resources : List RetainedAlternativeSegment)
    (callerScope outerScope : CutScopeId)
    (context : ActiveProductContext)
    (baseAlts : List PLeaTTa.Alt) (state : OpenConf) : Prop where
  activeRest : active.rest = executableRest
  activeQuery : active.qterm = qterm
  activeBarrier : active.barrier = bodyBarrier
  activeAlts : active.alts = altTail
  activeFinalCounter :
    active.finalCounter = pending.persistent.counter
  activeOwnership : active.HasIndexedOwnershipAt alpha cursor
  outerAlignment :
    SourceControlResourceContextAgrees alpha qterm callerBarrier outer
      resources callerScope context outerScope
  suspendedOuterAlts :
    pending.outer.alts = flattenOwnedAlts resources baseAlts
  actualAlts :
    state.control.alts =
      flattenOwnedAlts (active :: resources) baseAlts

/-- Exact surviving resource stack after the active predicate has committed.
No descriptor for the consumed cursor remains. -/
structure CommittedProductResourceStackAgrees
    (alpha : List (LogicVar × String)) (qterm : Atom)
    (callerBarrier : Nat)
    (pending : DemandDrivenCallStep.PendingCall)
    (outer : List ControlSegment)
    (resources : List RetainedAlternativeSegment)
    (callerScope outerScope : CutScopeId)
    (context : ActiveProductContext)
    (baseAlts : List PLeaTTa.Alt) (state : OpenConf) : Prop where
  outerAlignment :
    SourceControlResourceContextAgrees alpha qterm callerBarrier outer
      resources callerScope context outerScope
  suspendedOuterAlts :
    pending.outer.alts = flattenOwnedAlts resources baseAlts
  actualAlts :
    state.control.alts = flattenOwnedAlts resources baseAlts

/-- Fully composed active source/executable state.

The literal source search is an index.  Thus the resource and control
certificates cannot be paired with a different focus whose cursor, scope, or
current substitution merely happens to have compatible metadata. -/
structure SpinedActiveProductResourceRelatesAt
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (opened : OpenedCall) (session : Session)
    (pending : DemandDrivenCallStep.PendingCall)
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
    (source : Search) (state : OpenConf) : Prop where
  control :
    SpinedActiveProductRelatesAt freshFrontier alpha support canonical
      referenceBase opened session pending finish branch branchTail altTail
      bodyBarrier callerBarrier bodyReferences bodyExecutables
      callerReferences callerExecutables outer current runtime qterm state
  resourceStack :
    ActiveProductResourceStackAgrees alpha qterm bodyBarrier callerBarrier
      pending (finish.advance branch branchTail)
      (callerExecutables ++ flattenExecutables outer) altTail active outer
      resources callerScope outerScope context baseAlts state
  sourceShape :
    source =
      ActiveProductContext.plug context
        (activeSourceProduct callerScope opened finish branch branchTail
          current bodyReferences callerReferences)

/-- Exact opener-session specialization of the active resource relation. -/
abbrev SpinedActiveProductResourceRelates
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (opened : OpenedCall) (pending : DemandDrivenCallStep.PendingCall)
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
    (source : Search) (state : OpenConf) : Prop :=
  SpinedActiveProductResourceRelatesAt freshFrontier alpha support canonical
    referenceBase opened opened.session pending finish branch branchTail
    altTail bodyBarrier callerBarrier bodyReferences bodyExecutables
    callerReferences callerExecutables outer current runtime qterm active
    resources callerScope outerScope context baseAlts source state

/-- Fully composed post-cut state.  The source focus has no retained clause
choice, and the executable bank has no descriptor or marker for it. -/
structure SpinedCommittedProductResourceRelatesAt
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
    (source : Search) (state : OpenConf) : Prop where
  control :
    SpinedCommittedProductRelatesAt freshFrontier alpha support canonical
      referenceBase opened session pending bodyBarrier callerBarrier bodyReferences
      bodyExecutables callerReferences callerExecutables outer current runtime
      qterm state
  resourceStack :
    CommittedProductResourceStackAgrees alpha qterm callerBarrier pending outer
      resources callerScope outerScope context baseAlts state
  sourceShape :
    source =
      ActiveProductContext.plug context
        (cutSourceProduct callerScope opened current bodyReferences
          callerReferences)

/-- Exact opener-session specialization of the committed resource relation. -/
abbrev SpinedCommittedProductResourceRelates
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (opened : OpenedCall) (pending : DemandDrivenCallStep.PendingCall)
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
    (source : Search) (state : OpenConf) : Prop :=
  SpinedCommittedProductResourceRelatesAt freshFrontier alpha support canonical
    referenceBase opened opened.session pending bodyBarrier callerBarrier
    bodyReferences bodyExecutables callerReferences callerExecutables outer
    current runtime qterm resources callerScope outerScope context baseAlts
    source state

/-- Fully composed post-body-success state.  The source focus records the
private scheduling choice explicitly, while the executable and resource bank
remain literally unchanged. -/
structure SpinedScheduledProductResourceRelatesAt
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
    (source : Search) (state : OpenConf) : Prop where
  control :
    SpinedScheduledProductRelatesAt freshFrontier alpha support canonical
      referenceBase opened session pending finish branch branchTail altTail
      bodyBarrier callerBarrier callerReferences callerExecutables outer
      current runtime qterm state
  resourceStack :
    ActiveProductResourceStackAgrees alpha qterm bodyBarrier callerBarrier
      pending (finish.advance branch branchTail)
      (callerExecutables ++ flattenExecutables outer) altTail active outer
      resources callerScope outerScope context baseAlts state
  sourceShape :
    source =
      ActiveProductContext.plug context
        (scheduledSourceProduct callerScope opened finish branch branchTail
          current callerReferences)

/-- Exact opener-session specialization of the scheduled resource relation. -/
abbrev SpinedScheduledProductResourceRelates
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (opened : OpenedCall) (pending : DemandDrivenCallStep.PendingCall)
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
    (source : Search) (state : OpenConf) : Prop :=
  SpinedScheduledProductResourceRelatesAt freshFrontier alpha support canonical
    referenceBase opened opened.session pending finish branch branchTail
    altTail bodyBarrier callerBarrier callerReferences callerExecutables outer
    current runtime qterm active resources callerScope outerScope context
    baseAlts source state

/-! ## Current-session reindexing and anti-vacuity -/

/-- Exact compatibility: the historical public name is definitionally the
current-session relation specialized at the opener. -/
theorem spinedActiveProduct_specialization_exact
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (opened : OpenedCall) (pending : DemandDrivenCallStep.PendingCall)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (altTail : List PLeaTTa.Alt)
    (bodyBarrier callerBarrier : Nat)
    (bodyReferences : List PeTTaSpec.PrologCore.Goal)
    (bodyExecutables : List PLeaTTa.Goal)
    (callerReferences : List PeTTaSpec.PrologCore.Goal)
    (callerExecutables : List PLeaTTa.Goal)
    (outer : List ControlSegment)
    (current : Substitution) (runtime : Subst) (qterm : Atom)
    (state : OpenConf) :
    SpinedActiveProductRelates freshFrontier alpha support canonical
        referenceBase opened pending finish branch branchTail altTail
        bodyBarrier callerBarrier bodyReferences bodyExecutables
        callerReferences callerExecutables outer current runtime qterm state =
      SpinedActiveProductRelatesAt freshFrontier alpha support canonical
        referenceBase opened opened.session pending finish branch branchTail
        altTail bodyBarrier callerBarrier bodyReferences bodyExecutables
        callerReferences callerExecutables outer current runtime qterm state :=
  rfl

/-- The resource-indexed compatibility name is likewise an exact
specialization, including the literal source focus and retained bank. -/
theorem spinedActiveProductResource_specialization_exact
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (opened : OpenedCall) (pending : DemandDrivenCallStep.PendingCall)
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
    (source : Search) (state : OpenConf) :
    SpinedActiveProductResourceRelates freshFrontier alpha support canonical
        referenceBase opened pending finish branch branchTail altTail
        bodyBarrier callerBarrier bodyReferences bodyExecutables
        callerReferences callerExecutables outer current runtime qterm active
        resources callerScope outerScope context baseAlts source state =
      SpinedActiveProductResourceRelatesAt freshFrontier alpha support canonical
        referenceBase opened opened.session pending finish branch branchTail
        altTail bodyBarrier callerBarrier bodyReferences bodyExecutables
        callerReferences callerExecutables outer current runtime qterm active
        resources callerScope outerScope context baseAlts source state :=
  rfl

/-- Reindex an active state at a later source session.  The caller must provide
the current persistent-state agreement; every control/resource field remains
literal, while opener-to-current chronology composes. -/
theorem SpinedActiveProductRelatesAt.reindex
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {session nextSession : Session}
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
    {state : OpenConf}
    (agreement :
      SpinedActiveProductRelatesAt freshFrontier alpha support canonical
        referenceBase opened session pending finish branch branchTail altTail
        bodyBarrier callerBarrier bodyReferences bodyExecutables
        callerReferences callerExecutables outer current runtime qterm state)
    (persistent :
      SessionRelatesPersistent freshFrontier nextSession state.persistent)
    (advanced : SessionHighWatersExtend session nextSession) :
    SpinedActiveProductRelatesAt freshFrontier alpha support canonical
      referenceBase opened nextSession pending finish branch branchTail altTail
      bodyBarrier callerBarrier bodyReferences bodyExecutables callerReferences
      callerExecutables outer current runtime qterm state := by
  rcases agreement.ready with
    ⟨_oldPersistent, control, queryTerm, payload⟩
  exact
    ⟨⟨persistent, control, queryTerm, payload⟩,
      agreement.sessionAdvanced.trans advanced,
      agreement.retainedAlts, agreement.retainedAltsZero,
      agreement.retainedBarriers, agreement.bodyBarrierTag, agreement.frames⟩

/-- The exact resource-indexed state reindexes without changing its source
focus, retained cursor stack, executable alternative bank, or frames. -/
theorem SpinedActiveProductResourceRelatesAt.reindex
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {session nextSession : Session}
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
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {source : Search} {state : OpenConf}
    (agreement :
      SpinedActiveProductResourceRelatesAt freshFrontier alpha support canonical
        referenceBase opened session pending finish branch branchTail altTail
        bodyBarrier callerBarrier bodyReferences bodyExecutables
        callerReferences callerExecutables outer current runtime qterm active
        resources callerScope outerScope context baseAlts source state)
    (persistent :
      SessionRelatesPersistent freshFrontier nextSession state.persistent)
    (advanced : SessionHighWatersExtend session nextSession) :
    SpinedActiveProductResourceRelatesAt freshFrontier alpha support canonical
      referenceBase opened nextSession pending finish branch branchTail altTail
      bodyBarrier callerBarrier bodyReferences bodyExecutables callerReferences
      callerExecutables outer current runtime qterm active resources callerScope
      outerScope context baseAlts source state :=
  ⟨agreement.control.reindex persistent advanced,
    agreement.resourceStack, agreement.sourceShape⟩

/-- A full active resource state can inhabit a strictly later fresh session
whenever the supplied frontier relates that later source high-water to the
unchanged executable counter.  The source search and complete resource bank
remain exact. -/
theorem SpinedActiveProductResourceRelatesAt.strictFreshReindex
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
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {source : Search} {state : OpenConf}
    (agreement :
      SpinedActiveProductResourceRelatesAt freshFrontier alpha support canonical
        referenceBase opened session pending finish branch branchTail altTail
        bodyBarrier callerBarrier bodyReferences bodyExecutables
        callerReferences callerExecutables outer current runtime qterm active
        resources callerScope outerScope context baseAlts source state)
    (freshAdvanced :
      freshFrontier (session.resolver.nextFresh + 1)
        state.persistent.counter) :
    ∃ nextSession : Session,
      session.resolver.nextFresh < nextSession.resolver.nextFresh ∧
      SpinedActiveProductResourceRelatesAt freshFrontier alpha support canonical
        referenceBase opened nextSession pending finish branch branchTail altTail
        bodyBarrier callerBarrier bodyReferences bodyExecutables
        callerReferences callerExecutables outer current runtime qterm active
        resources callerScope outerScope context baseAlts source state := by
  let nextSession : Session :=
    { session with
      resolver :=
        { session.resolver with
          nextFresh := session.resolver.nextFresh + 1 } }
  have persistent :
      SessionRelatesPersistent freshFrontier nextSession state.persistent := by
    refine ⟨?_, ?_⟩
    · simpa [nextSession] using agreement.control.ready.1.database
    · simpa [nextSession] using freshAdvanced
  have chronology : SessionHighWatersExtend session nextSession := by
    simpa [nextSession] using
      (SessionHighWatersExtend.strict_fresh_witness session).1
  refine ⟨nextSession, ?_, agreement.reindex persistent chronology⟩
  simp [nextSession]

/-- A regressed fresh allocator is rejected by every active state, not merely
by a side theorem about sessions. -/
theorem SpinedActiveProductRelatesAt.rejectsFreshRegression
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
    {state : OpenConf}
    (regressed :
      session.resolver.nextFresh < opened.session.resolver.nextFresh) :
    ¬ SpinedActiveProductRelatesAt freshFrontier alpha support canonical
      referenceBase opened session pending finish branch branchTail altTail
      bodyBarrier callerBarrier bodyReferences bodyExecutables callerReferences
      callerExecutables outer current runtime qterm state := by
  intro agreement
  exact (Nat.not_lt_of_ge agreement.sessionAdvanced.fresh) regressed

/-- The current-session relation retains all four source allocator
chronologies even though only the fresh frontier is projected into the
executable persistent state. -/
theorem SpinedActiveProductRelatesAt.allHighWaters
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
    {state : OpenConf}
    (agreement :
      SpinedActiveProductRelatesAt freshFrontier alpha support canonical
        referenceBase opened session pending finish branch branchTail altTail
        bodyBarrier callerBarrier bodyReferences bodyExecutables
        callerReferences callerExecutables outer current runtime qterm state) :
    opened.session.resolver.nextFresh ≤ session.resolver.nextFresh ∧
      opened.session.nextCutScope ≤ session.nextCutScope ∧
      opened.session.nextExceptionScope ≤ session.nextExceptionScope ∧
      opened.session.nextCollectionScope ≤ session.nextCollectionScope :=
  ⟨agreement.sessionAdvanced.fresh, agreement.sessionAdvanced.cut,
    agreement.sessionAdvanced.exception, agreement.sessionAdvanced.collection⟩

namespace ActiveProductResourceStackAgrees

/-- The active machine bank contains exactly one marker more than the
resource-aligned outer bank. -/
theorem barrierCount_exact
    {alpha : List (LogicVar × String)} {qterm : Atom}
    {bodyBarrier callerBarrier : Nat}
    {pending : DemandDrivenCallStep.PendingCall}
    {cursor : PreparedCursor} {executableRest : List PLeaTTa.Goal}
    {altTail : List PLeaTTa.Alt}
    {active : RetainedAlternativeSegment}
    {outer : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt} {state : OpenConf}
    (agreement :
      ActiveProductResourceStackAgrees alpha qterm bodyBarrier callerBarrier
        pending cursor executableRest altTail active outer resources
        callerScope outerScope context baseAlts state) :
    PLeaTTa.barrierCount state.control.alts =
      (resources.length + 1) + PLeaTTa.barrierCount baseAlts := by
  rw [agreement.actualAlts, flattenOwnedAlts_cons,
    PLeaTTa.barrierCount_append,
      RetainedAlternativeSegment.HasIndexedOwnershipAt.barrierCount_zero
        agreement.activeOwnership,
    PLeaTTa.barrierCount_cons_barrier,
    agreement.outerAlignment.flattenOwnedAlts_barrierCount]
  omega

/-- The bank after consuming the active predicate cannot equal the active
bank.  This is the resource-linearity anti-vacuity guard. -/
theorem surviving_bank_ne_active_bank
    {alpha : List (LogicVar × String)} {qterm : Atom}
    {bodyBarrier callerBarrier : Nat}
    {pending : DemandDrivenCallStep.PendingCall}
    {cursor : PreparedCursor} {executableRest : List PLeaTTa.Goal}
    {altTail : List PLeaTTa.Alt}
    {active : RetainedAlternativeSegment}
    {outer : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt} {state : OpenConf}
    (agreement :
      ActiveProductResourceStackAgrees alpha qterm bodyBarrier callerBarrier
        pending cursor executableRest altTail active outer resources
        callerScope outerScope context baseAlts state) :
    flattenOwnedAlts resources baseAlts ≠
      flattenOwnedAlts (active :: resources) baseAlts := by
  intro equality
  have counts := congrArg PLeaTTa.barrierCount equality
  rw [agreement.outerAlignment.flattenOwnedAlts_barrierCount,
    flattenOwnedAlts_cons, PLeaTTa.barrierCount_append,
      RetainedAlternativeSegment.HasIndexedOwnershipAt.barrierCount_zero
        agreement.activeOwnership,
    PLeaTTa.barrierCount_cons_barrier,
    agreement.outerAlignment.flattenOwnedAlts_barrierCount] at counts
  omega

end ActiveProductResourceStackAgrees

namespace CommittedProductResourceStackAgrees

/-- After commit, only the markers belonging to surviving outer source
frames remain above the arbitrary base bank. -/
theorem barrierCount_exact
    {alpha : List (LogicVar × String)} {qterm : Atom}
    {callerBarrier : Nat}
    {pending : DemandDrivenCallStep.PendingCall}
    {outer : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt} {state : OpenConf}
    (agreement :
      CommittedProductResourceStackAgrees alpha qterm callerBarrier pending
        outer resources callerScope outerScope context baseAlts state) :
    PLeaTTa.barrierCount state.control.alts =
      resources.length + PLeaTTa.barrierCount baseAlts := by
  rw [agreement.actualAlts,
    agreement.outerAlignment.flattenOwnedAlts_barrierCount]

end CommittedProductResourceStackAgrees

/-! ## Construction from the real spined activation -/

/-- A spined representative activation relates its actual fine executable
successor to every independently tagged body/caller control region. -/
theorem
    SpinedRepresentativeProductActivation.spinedActiveProductRelates
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {copied : PLeaTTa.Clause}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {qterm : Atom} {bodyBarrier callerBarrier startCounter : Nat}
    {callerScope : CutScopeId}
    {independentResult : Substitution}
    {representative : TreeSubstitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattenedRepresentative : TreeSubstitution}
    {installed : Subst}
    (activation :
      SpinedRepresentativeProductActivation prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        callerReferences callerExecutables outer qterm bodyBarrier
        callerBarrier startCounter callerScope independentResult representative
        nextAlpha sourceCanonical flattenedRepresentative installed) :
    SpinedActiveProductRelates (AlphaFreshFrontier nextAlpha) nextAlpha support
      (sourceCanonical ++ canonical) referenceBase opened pending finish branch
      branchTail altTail bodyBarrier callerBarrier branch.body copied.body
      callerReferences callerExecutables outer independentResult
      (PLeaTTa.trimFor
        (copied.body ++
          (callerExecutables ++ flattenExecutables outer))
        qterm installed)
      qterm
      (activatedOpenSuccessor pending copied
        (callerExecutables ++ flattenExecutables outer) qterm installed) := by
  refine
    ⟨?_, SessionHighWatersExtend.refl _, ?_, activation.retainedAltsZero,
      ?_, activation.barrierTag, rfl⟩
  · refine
      ⟨?_, rfl, ?_, activation.spinePayload⟩
    · unfold activatedOpenSuccessor OpenConf.stepOpen OpenConf.ofConfWith
        persistentOf
      rw [activation.worldPreserved, activation.counterPreserved]
      exact activation.persistentAgreement
    · rcases activation.retainedCursorOwnership with
        ⟨argsv, args, res, binding, counter, callHead, queryTerm,
          barrierExact, cursorOwnership⟩
      have pulledQuery :
          pending.pulled.toConf.qterm = pending.outer.qterm := by
        unfold DemandDrivenCallStep.PendingCall.pulled
        change
          (PLeaTTa.pull pending.installed.toConf).qterm =
            pending.outer.qterm
        rw [pull_qterm]
        rfl
      exact pulledQuery.trans queryTerm.symm
  · change
      (activatedExecutableSuccessor pending copied
        (callerExecutables ++ flattenExecutables outer)
        qterm installed).alts =
          altTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts
    exact activation.retainedAlts
  · change
      (activatedExecutableSuccessor pending copied
        (callerExecutables ++ flattenExecutables outer)
        qterm installed).barriers =
          PLeaTTa.pushBarrierCache pending.outer.barriers
    exact activation.retainedBarriers

/-- The same real activation constructs the exact cursor/alternative resource
stack for its actual fine state. -/
theorem
    SpinedRepresentativeProductActivation.activeResourceStackAgrees
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {copied : PLeaTTa.Clause}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {qterm : Atom} {bodyBarrier callerBarrier startCounter : Nat}
    {callerScope outerScope : CutScopeId}
    {independentResult : Substitution}
    {representative : TreeSubstitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattenedRepresentative : TreeSubstitution}
    {installed : Subst}
    {resources : List RetainedAlternativeSegment}
    {context : ActiveProductContext}
    (retainedPosition : Nat)
    (positioned :
      CallScopedCursorPosition opened.cursor
        (finish.advance branch branchTail) retainedPosition)
    (activation :
      SpinedRepresentativeProductActivation prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        callerReferences callerExecutables outer qterm bodyBarrier
        callerBarrier startCounter callerScope independentResult representative
        nextAlpha sourceCanonical flattenedRepresentative installed)
    (alignment :
      SourceControlResourceContextAgrees nextAlpha qterm callerBarrier outer
        resources callerScope context outerScope)
    (baseAlts : List PLeaTTa.Alt)
    (outerAlts :
      pending.outer.alts = flattenOwnedAlts resources baseAlts) :
    ∃ active : RetainedAlternativeSegment,
      ActiveProductResourceStackAgrees nextAlpha qterm bodyBarrier
        callerBarrier pending (finish.advance branch branchTail)
        (callerExecutables ++ flattenExecutables outer) altTail active outer
        resources callerScope outerScope context baseAlts
        (activatedOpenSuccessor pending copied
          (callerExecutables ++ flattenExecutables outer) qterm installed) := by
  obtain
    ⟨active, activeRest, activeQuery, activeBarrier, activeAlts,
      activeFinalCounter, activeOwnership, actualAlts, _markerCount,
      _controlAlignment⟩ :=
    activation.resources_throughAlignedContext retainedPosition positioned
      alignment baseAlts outerAlts
  refine
    ⟨active, activeRest, activeQuery, activeBarrier, activeAlts,
      activeFinalCounter,
      ⟨opened.cursor, retainedPosition, activeOwnership⟩,
      alignment, outerAlts, ?_⟩
  exact actualAlts

/-- The real spined activation constructs one fully composed state whose
source focus, exact runtime/query payload, control spine, and executable
resource bank share all load-bearing indices. -/
theorem
    SpinedRepresentativeProductActivation.spinedProductResourceRelates
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {copied : PLeaTTa.Clause}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {qterm : Atom} {bodyBarrier callerBarrier startCounter : Nat}
    {callerScope outerScope : CutScopeId}
    {independentResult : Substitution}
    {representative : TreeSubstitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattenedRepresentative : TreeSubstitution}
    {installed : Subst}
    {resources : List RetainedAlternativeSegment}
    {context : ActiveProductContext}
    (retainedPosition : Nat)
    (positioned :
      CallScopedCursorPosition opened.cursor
        (finish.advance branch branchTail) retainedPosition)
    (activation :
      SpinedRepresentativeProductActivation prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        callerReferences callerExecutables outer qterm bodyBarrier
        callerBarrier startCounter callerScope independentResult representative
        nextAlpha sourceCanonical flattenedRepresentative installed)
    (alignment :
      SourceControlResourceContextAgrees nextAlpha qterm callerBarrier outer
        resources callerScope context outerScope)
    (baseAlts : List PLeaTTa.Alt)
    (outerAlts :
      pending.outer.alts = flattenOwnedAlts resources baseAlts) :
    ∃ active : RetainedAlternativeSegment,
      SpinedActiveProductResourceRelates
        (AlphaFreshFrontier nextAlpha) nextAlpha support
        (sourceCanonical ++ canonical) referenceBase opened pending finish
        branch branchTail altTail bodyBarrier callerBarrier branch.body
        copied.body callerReferences callerExecutables outer independentResult
        (PLeaTTa.trimFor
          (copied.body ++
            (callerExecutables ++ flattenExecutables outer))
          qterm installed)
        qterm active resources callerScope outerScope context baseAlts
        (ActiveProductContext.plug context
          (activatedSourceProduct callerScope opened finish branch branchTail
            independentResult callerReferences))
        (activatedOpenSuccessor pending copied
          (callerExecutables ++ flattenExecutables outer) qterm installed) := by
  obtain ⟨active, resourceStack⟩ :=
    _root_.PLeaTTa.PrologProductResourceTransitionBridge.SpinedRepresentativeProductActivation.activeResourceStackAgrees
      retainedPosition positioned activation alignment baseAlts outerAlts
  refine
    ⟨active,
      _root_.PLeaTTa.PrologProductResourceTransitionBridge.SpinedRepresentativeProductActivation.spinedActiveProductRelates
        activation,
      resourceStack, ?_⟩
  rfl

/-! ## Body success preserves the active resource -/

/-- Successful completion of the selected clause body is one private source
scheduling step and zero executable steps.

The source focus changes from the active product to the explicit
caller-first scheduling choice.  Runtime, query term, executable state,
retained cursor ownership, literal outer spine, and complete alternative bank
are unchanged. -/
theorem SpinedActiveProductResourceRelates.afterBodyAnswer
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
    (agreement :
      SpinedActiveProductResourceRelatesAt freshFrontier alpha support canonical
        referenceBase opened session pending finish branch branchTail altTail
        bodyBarrier callerBarrier [] [] callerReferences callerExecutables
        outer current runtime qterm active resources callerScope outerScope
        context baseAlts source state) :
    RawStep session source [] .none session
        (.running
          (ActiveProductContext.plug context
            (scheduledSourceProduct callerScope opened finish branch
              branchTail current callerReferences))) ∧
      DemandDrivenCallStep.StepsN prog gt 0
        (.ready state) (.ready state) ∧
      SpinedScheduledProductResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened session pending finish branch branchTail
        altTail bodyBarrier callerBarrier callerReferences callerExecutables
        outer current runtime qterm active resources callerScope outerScope
        context baseAlts
        (ActiveProductContext.plug context
          (scheduledSourceProduct callerScope opened finish branch branchTail
            current callerReferences))
        state := by
  rcases agreement.control.ready with
    ⟨persistent, currentControl, queryTerm, payload⟩
  have callerReady :
      SpinedReadyTaskRelates freshFrontier alpha support canonical
        referenceBase session current runtime qterm
        ({ barrier := callerBarrier
           references := callerReferences
           executables := callerExecutables } ::
         outer)
        state := by
    refine
      ⟨persistent, ?_, queryTerm, payload.dropHead⟩
    simpa [flattenExecutables, ControlSegment.executableGoals] using
      currentControl
  have scheduledControl :
      SpinedScheduledProductRelatesAt freshFrontier alpha support canonical
        referenceBase opened session pending finish branch branchTail altTail
        bodyBarrier callerBarrier callerReferences callerExecutables outer
        current runtime qterm state :=
    ⟨callerReady, agreement.control.sessionAdvanced,
      agreement.control.retainedAlts,
      agreement.control.retainedAltsZero,
      agreement.control.retainedBarriers,
      agreement.control.bodyBarrierTag, agreement.control.frames⟩
  have sourceStep :
      RawStep session source [] .none session
        (.running
          (ActiveProductContext.plug context
            (scheduledSourceProduct callerScope opened finish branch
              branchTail current callerReferences))) := by
    rw [agreement.sourceShape]
    exact
      ActiveProductContext.liftProgress context
        (activeSourceProduct_answer callerScope opened finish branch
          branchTail current callerReferences)
        (by simp [Trace.AnswerFree])
  exact
    ⟨sourceStep, .zero (.ready state),
      ⟨scheduledControl, agreement.resourceStack, rfl⟩⟩

/-! ## Cut consumes exactly one active resource -/

/-- One real clause-local cut through an arbitrary active source context:

* emits the exact advanced-cursor prune observation,
* performs one real executable tagged-cut step,
* removes the active cursor's alternatives and exactly one marker,
* preserves every outer source frame, control segment, resource descriptor,
  base alternative, and persistent state.
-/
theorem SpinedActiveProductRelates.afterCutThroughResourceStack
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
    {current : Substitution} {runtime : Subst} {state : OpenConf}
    {qterm : Atom} {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    (agreement :
      SpinedActiveProductRelatesAt freshFrontier alpha support canonical
        referenceBase opened session pending finish branch branchTail altTail
        bodyBarrier callerBarrier (.cut :: bodyRest)
        (.cutAt bodyBarrier :: bodyExecutableTail)
        callerReferences callerExecutables outer current runtime qterm state)
    (resourceStack :
      ActiveProductResourceStackAgrees alpha qterm bodyBarrier callerBarrier
        pending (finish.advance branch branchTail)
        (callerExecutables ++ flattenExecutables outer) altTail active outer
        resources callerScope outerScope context baseAlts state)
    (coherent : PLeaTTa.BarrierCacheCoherent state.toConf) :
    state.control.cur =
        some
          (.cutAt bodyBarrier ::
            (bodyExecutableTail ++
              (callerExecutables ++ flattenExecutables outer)),
            runtime) ∧
      RawStep session
        (ActiveProductContext.plug context
          (activeSourceProduct callerScope opened finish branch branchTail
            current (.cut :: bodyRest) callerReferences))
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
      SpinedCommittedProductRelatesAt freshFrontier alpha support canonical
        referenceBase opened session pending bodyBarrier callerBarrier bodyRest
        bodyExecutableTail callerReferences callerExecutables outer current
        runtime qterm
        (cutSuccessor state bodyBarrier
          (bodyExecutableTail ++
            (callerExecutables ++ flattenExecutables outer))
          runtime) ∧
      CommittedProductResourceStackAgrees alpha qterm callerBarrier pending
        outer resources callerScope outerScope context baseAlts
        (cutSuccessor state bodyBarrier
          (bodyExecutableTail ++
            (callerExecutables ++ flattenExecutables outer))
          runtime) ∧
      PLeaTTa.barrierCount state.control.alts =
        PLeaTTa.barrierCount
          (cutSuccessor state bodyBarrier
            (bodyExecutableTail ++
              (callerExecutables ++ flattenExecutables outer))
            runtime).control.alts + 1 := by
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
      DemandDrivenCallStep.Step prog gt (.ready state)
        (.ready nextState) :=
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
    ⟨payload.data,
      .cons bodyTailControl payload.control.tail⟩
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
  have committed :
      SpinedCommittedProductRelatesAt freshFrontier alpha support canonical
        referenceBase opened session pending bodyBarrier callerBarrier bodyRest
        bodyExecutableTail callerReferences callerExecutables outer current
        runtime qterm
        nextState := by
    refine ⟨nextReady, agreement.sessionAdvanced, ?_, ?_, ?_⟩
    · change
        (PLeaTTa.cutToTracked bodyBarrier state.toConf.barriers
          state.toConf.alts).1 =
          pending.outer.alts
      exact agreement.resources.cutToTracked_alts_eq_outer coherent
    · have nextCoherent :=
        PLeaTTa.BarrierCacheCoherent.cut state.toConf bodyBarrier coherent
      unfold PLeaTTa.BarrierCacheCoherent at nextCoherent ⊢
      simpa [nextState, cutSuccessor] using nextCoherent
    · simpa [nextState, cutSuccessor] using agreement.frames
  have committedResources :
      CommittedProductResourceStackAgrees alpha qterm callerBarrier pending
        outer resources callerScope outerScope context baseAlts nextState :=
    ⟨resourceStack.outerAlignment, resourceStack.suspendedOuterAlts,
      committed.outerAlts.trans resourceStack.suspendedOuterAlts⟩
  have sourceStep :
      RawStep session
        (ActiveProductContext.plug context
          (activeSourceProduct callerScope opened finish branch branchTail
            current (.cut :: bodyRest) callerReferences))
        [.pruned (retainedCursorToken opened finish branch branchTail)]
        .none session
        (.running
          (ActiveProductContext.plug context
            (cutSourceProduct callerScope opened current bodyRest
              callerReferences))) :=
    ActiveProductContext.liftProgress context activeSourceProduct_cut
      (by simp [Trace.AnswerFree])
  have countDrop :
      PLeaTTa.barrierCount state.control.alts =
        PLeaTTa.barrierCount nextState.control.alts + 1 := by
    have beforeCount := resourceStack.barrierCount_exact
    have afterCount := committedResources.barrierCount_exact
    omega
  exact
    ⟨executableHead, sourceStep, executableStep, committed,
      committedResources, countDrop⟩

/-- Fully composed clause-local cut correspondence.

Unlike the lower modular theorem, this statement is indexed by the literal
pre-cut source search.  The conclusion retains the same `bodyBarrier`,
`callerBarrier`, literal `outer`, context, resource list, and base bank while
changing only the body tails and consuming the active cursor resource. -/
theorem SpinedActiveProductResourceRelates.afterCut
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
    (agreement :
      SpinedActiveProductResourceRelatesAt freshFrontier alpha support canonical
        referenceBase opened session pending finish branch branchTail altTail
        bodyBarrier callerBarrier (.cut :: bodyRest)
        (.cutAt bodyBarrier :: bodyExecutableTail)
        callerReferences callerExecutables outer current runtime qterm active
        resources callerScope outerScope context baseAlts source state)
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
      SpinedCommittedProductResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened session pending bodyBarrier callerBarrier
        bodyRest bodyExecutableTail callerReferences callerExecutables outer
        current runtime qterm resources callerScope outerScope context baseAlts
        (ActiveProductContext.plug context
          (cutSourceProduct callerScope opened current bodyRest
            callerReferences))
        (cutSuccessor state bodyBarrier
          (bodyExecutableTail ++
            (callerExecutables ++ flattenExecutables outer))
          runtime) ∧
      PLeaTTa.barrierCount state.control.alts =
        PLeaTTa.barrierCount
          (cutSuccessor state bodyBarrier
            (bodyExecutableTail ++
              (callerExecutables ++ flattenExecutables outer))
            runtime).control.alts + 1 := by
  rcases SpinedActiveProductRelates.afterCutThroughResourceStack
      agreement.control
      agreement.resourceStack coherent with
    ⟨executableHead, sourceStep, executableStep, committedControl,
      committedResources, countDrop⟩
  have indexedSourceStep :
      RawStep session source
        [.pruned (retainedCursorToken opened finish branch branchTail)]
        .none session
        (.running
          (ActiveProductContext.plug context
            (cutSourceProduct callerScope opened current bodyRest
              callerReferences))) := by
    rw [agreement.sourceShape]
    exact sourceStep
  exact
    ⟨executableHead, indexedSourceStep, executableStep,
      ⟨committedControl, committedResources, rfl⟩, countDrop⟩

end PLeaTTa.PrologProductResourceTransitionBridge
