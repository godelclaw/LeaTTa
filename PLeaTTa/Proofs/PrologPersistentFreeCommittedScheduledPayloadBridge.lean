-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologPersistentFreeCommittedScheduledPayloadBridge
Purpose: Consume a successful post-cut clause body without resurrecting the
  clause occurrence or cursor that the cut already pruned.
Trusted boundary: none
Main exports:
  committedScheduledSourceProductAt,
  PersistentFreeCommittedProductPayloadResourceRelatesAt.afterBodyAnswer
-/
import PLeaTTa.Proofs.PrologPersistentFreeCommittedPayloadBridge

namespace PLeaTTa.PrologPersistentFreeCommittedScheduledPayloadBridge

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
open PrologCurrentSessionPayloadTransitionBridge
open PrologMguComposition
open PrologOrdinaryStepBridge
open PrologPersistentFreeCommittedPayloadBridge
open PrologProductResourceContextBridge
open PrologProductResourceTransitionBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
open PrologSourceProductContextBridge
open PrologStateBridge

/-! ## Source control after a committed clause body succeeds -/

/-- Source control after a post-cut clause body succeeds.

The caller continuation runs first.  The right branch contains only the
exhausted predicate boundary: the cut already consumed the selected occurrence
and pruned every later clause, so no cursor or clause branch appears here. -/
def committedScheduledSourceProductAt
    (callerScope predicateScope : CutScopeId)
    (current : Substitution)
    (referenceRest : List PeTTaSpec.PrologCore.Goal) : Search :=
  .choice callerScope
    (.task callerScope referenceRest current)
    (.product callerScope
      (.cutBoundary predicateScope .done)
      referenceRest)

/-- A successful post-cut body answer is private to the surrounding product.
It schedules the caller before the exhausted predicate continuation and emits
no public observation. -/
theorem cutSourceProductAt_answer
    (session : Session) (callerScope predicateScope : CutScopeId)
    (current : Substitution)
    (referenceRest : List PeTTaSpec.PrologCore.Goal) :
    RawStep session
      (cutSourceProductAt callerScope predicateScope current [] referenceRest)
      [] .none session
      (.running
        (committedScheduledSourceProductAt callerScope predicateScope current
          referenceRest)) := by
  apply RawStep.productAnswer
  apply RawStep.cutBoundaryProgress
  exact RawStep.taskAnswer predicateScope current session

/-! ## Packet-free post-commit scheduling relation -/

/-- Exact correspondence after the committed body answer has exposed the
caller continuation.

The payload is still the literal surviving outer zipper.  In particular this
relation contains no selected clause, retained cursor, or activation packet:
all three were consumed by the earlier cut. -/
structure PersistentFreeCommittedScheduledProductPayloadResourceRelatesAt
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (predicateScope : CutScopeId) (session : Session)
    (callerBarrier : Nat)
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
    SpinedReadyTaskRelates freshFrontier alpha support canonical referenceBase
      session current runtime qterm
      ({ barrier := callerBarrier
         references := callerReferences
         executables := callerExecutables } :: outer)
      state
  actualAlts : state.control.alts = flattenOwnedAlts resources baseAlts
  cacheCoherent : PLeaTTa.BarrierCacheCoherent state.toConf
  sourceShape :
    source =
      ActiveProductContext.plug context
        (committedScheduledSourceProductAt callerScope predicateScope current
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

/-- Completing an empty post-cut clause body drops exactly the empty body
segment from the certified executable spine.  The source takes one private
step; the executable takes zero steps and every surviving payload/resource
fact is retained literally. -/
theorem afterBodyAnswer
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {predicateScope : CutScopeId} {session : Session}
    {bodyBarrier callerBarrier : Nat}
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
      PersistentFreeCommittedProductPayloadResourceRelatesAt freshFrontier
        alpha support canonical referenceBase predicateScope session
        bodyBarrier callerBarrier [] [] callerReferences callerExecutables
        outer current runtime qterm resources callerScope outerScope context
        baseAlts source state payloadContext) :
    RawStep session source [] .none session
        (.running
          (ActiveProductContext.plug context
            (committedScheduledSourceProductAt callerScope predicateScope
              current callerReferences))) ∧
      DemandDrivenCallStep.StepsN prog gt 0
        (.ready state) (.ready state) ∧
      PersistentFreeCommittedScheduledProductPayloadResourceRelatesAt
        freshFrontier alpha support canonical referenceBase predicateScope
        session callerBarrier callerReferences callerExecutables outer current
        runtime qterm resources callerScope outerScope context baseAlts
        (ActiveProductContext.plug context
          (committedScheduledSourceProductAt callerScope predicateScope current
            callerReferences))
        state payloadContext := by
  have focusStep :
      RawStep session
        (cutSourceProductAt callerScope predicateScope current []
          callerReferences)
        [] .none session
        (.running
          (committedScheduledSourceProductAt callerScope predicateScope current
            callerReferences)) :=
    cutSourceProductAt_answer session callerScope predicateScope current
      callerReferences
  have sourceStep :
      RawStep session
        (ActiveProductContext.plug context
          (cutSourceProductAt callerScope predicateScope current []
            callerReferences))
        [] .none session
        (.running
          (ActiveProductContext.plug context
            (committedScheduledSourceProductAt callerScope predicateScope
              current callerReferences))) :=
    ActiveProductContext.liftProgress context focusStep (by
      intro _answer membership
      cases membership)
  have oldReady := agreement.ready
  have nextReady :
      SpinedReadyTaskRelates freshFrontier alpha support canonical referenceBase
        session current runtime qterm
        ({ barrier := callerBarrier
           references := callerReferences
           executables := callerExecutables } :: outer)
        state := by
    refine ⟨oldReady.1, ?_, oldReady.2.2.1, ?_⟩
    · simpa only [flattenExecutables_cons, List.nil_append] using oldReady.2.1
    · exact oldReady.2.2.2.dropHead
  have nextAgreement :
      PersistentFreeCommittedScheduledProductPayloadResourceRelatesAt
        freshFrontier alpha support canonical referenceBase predicateScope
        session callerBarrier callerReferences callerExecutables outer current
        runtime qterm resources callerScope outerScope context baseAlts
        (ActiveProductContext.plug context
          (committedScheduledSourceProductAt callerScope predicateScope current
            callerReferences))
        state payloadContext :=
    { ready := nextReady
      actualAlts := agreement.actualAlts
      cacheCoherent := agreement.cacheCoherent
      sourceShape := rfl
      endpointsCurrent := agreement.endpointsCurrent
      activationOrdered := agreement.activationOrdered
      activationOrigins := agreement.activationOrigins
      controlOrigins := agreement.controlOrigins }
  refine ⟨?_, .zero _, nextAgreement⟩
  simpa only [agreement.sourceShape] using sourceStep

end PersistentFreeCommittedProductPayloadResourceRelatesAt

/-! ## Type-valued post-commit scheduled state -/

/-- Every live index after a committed body answer.  Clause-occurrence data
and the consumed body barrier are deliberately absent. -/
structure PersistentFreeCommittedScheduledPayloadIndex where
  freshFrontier : FreshFrontierRelation
  alpha : List (LogicVar × String)
  support : List (LogicVar × String)
  canonical : TreeSubstitution
  referenceBase : Substitution
  predicateScope : CutScopeId
  session : Session
  callerBarrier : Nat
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

namespace PersistentFreeCommittedScheduledPayloadIndex

abbrev PayloadContext
    (index : PersistentFreeCommittedScheduledPayloadIndex) :=
  CommittedProductPayloadContext index.alpha index.support index.qterm
    index.callerBarrier index.outer index.resources index.callerScope
    index.outerScope index.context

abbrev Relates (index : PersistentFreeCommittedScheduledPayloadIndex)
    (payloadContext : index.PayloadContext) :=
  PersistentFreeCommittedScheduledProductPayloadResourceRelatesAt
    index.freshFrontier index.alpha index.support index.canonical
    index.referenceBase index.predicateScope index.session index.callerBarrier
    index.callerReferences index.callerExecutables index.outer index.current
    index.runtime index.qterm index.resources index.callerScope index.outerScope
    index.context index.baseAlts index.source index.openConf payloadContext

end PersistentFreeCommittedScheduledPayloadIndex

/-- One proof-relevant post-commit scheduled state with the literal surviving
outer payload zipper. -/
structure PersistentFreeCommittedScheduledPayloadState where
  index : PersistentFreeCommittedScheduledPayloadIndex
  payloadContext : index.PayloadContext
  agreement : index.Relates payloadContext

namespace PersistentFreeCommittedScheduledPayloadState

def sourceState (state : PersistentFreeCommittedScheduledPayloadState) : State :=
  .running state.index.session state.index.source

def fineState (state : PersistentFreeCommittedScheduledPayloadState) :
    DemandDrivenCallStep.FineConf :=
  .ready state.index.openConf

def cellIdentities (state : PersistentFreeCommittedScheduledPayloadState) :
    List PrologNestedCallChainBridge.PayloadCellIdentity :=
  PrologNestedCallChainBridge.SourceControlResourcePayloadContextAgrees.cellIdentities
    state.payloadContext

def cellCount (state : PersistentFreeCommittedScheduledPayloadState) : Nat :=
  PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount
    state.payloadContext

theorem cellIdentities_length
    (state : PersistentFreeCommittedScheduledPayloadState) :
    state.cellIdentities.length = state.cellCount :=
  PrologNestedCallChainBridge.SourceControlResourcePayloadContextAgrees.cellIdentities_length_eq_cellCount
    state.payloadContext

end PersistentFreeCommittedScheduledPayloadState

/-- A post-commit scheduled state with its literal cumulative residual. -/
structure RepresentativePersistentFreeCommittedScheduledPayloadState where
  carrier : PersistentFreeCommittedScheduledPayloadState
  representative : TreeSubstitution
  cumulative :
    AlphaCumulativeResidualVariantAgreesOnWith carrier.index.alpha
      carrier.index.support carrier.index.canonical carrier.index.referenceBase
      carrier.index.runtime representative

namespace RepresentativePersistentFreeCommittedPayloadState

/-- Exact source focus after the committed body answer. -/
def bodyAnswerSource
    (state : RepresentativePersistentFreeCommittedPayloadState) : Search :=
  ActiveProductContext.plug state.carrier.index.context
    (committedScheduledSourceProductAt state.carrier.index.callerScope
      state.carrier.index.predicateScope state.carrier.index.current
      state.carrier.index.callerReferences)

/-- Compute the unique packet-free post-commit scheduled successor. -/
def afterBodyAnswer
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativePersistentFreeCommittedPayloadState)
    (referenceEmpty : state.carrier.index.bodyReferences = [])
    (executableEmpty : state.carrier.index.bodyExecutables = []) :
    RepresentativePersistentFreeCommittedScheduledPayloadState :=
  let emptyAgreement :
      PersistentFreeCommittedProductPayloadResourceRelatesAt
        state.carrier.index.freshFrontier state.carrier.index.alpha
        state.carrier.index.support state.carrier.index.canonical
        state.carrier.index.referenceBase state.carrier.index.predicateScope
        state.carrier.index.session state.carrier.index.bodyBarrier
        state.carrier.index.callerBarrier [] []
        state.carrier.index.callerReferences
        state.carrier.index.callerExecutables state.carrier.index.outer
        state.carrier.index.current state.carrier.index.runtime
        state.carrier.index.qterm state.carrier.index.resources
        state.carrier.index.callerScope state.carrier.index.outerScope
        state.carrier.index.context state.carrier.index.baseAlts
        state.carrier.index.source state.carrier.index.openConf
        state.carrier.payloadContext := by
    simpa only [PersistentFreeCommittedPayloadIndex.Relates, referenceEmpty,
      executableEmpty] using state.carrier.agreement
  let nextAgreement :=
    (PersistentFreeCommittedProductPayloadResourceRelatesAt.afterBodyAnswer
      (prog := prog) (gt := gt) emptyAgreement).2.2
  let nextIndex : PersistentFreeCommittedScheduledPayloadIndex :=
    { freshFrontier := state.carrier.index.freshFrontier
      alpha := state.carrier.index.alpha
      support := state.carrier.index.support
      canonical := state.carrier.index.canonical
      referenceBase := state.carrier.index.referenceBase
      predicateScope := state.carrier.index.predicateScope
      session := state.carrier.index.session
      callerBarrier := state.carrier.index.callerBarrier
      callerReferences := state.carrier.index.callerReferences
      callerExecutables := state.carrier.index.callerExecutables
      outer := state.carrier.index.outer
      current := state.carrier.index.current
      runtime := state.carrier.index.runtime
      qterm := state.carrier.index.qterm
      resources := state.carrier.index.resources
      callerScope := state.carrier.index.callerScope
      outerScope := state.carrier.index.outerScope
      context := state.carrier.index.context
      baseAlts := state.carrier.index.baseAlts
      source := bodyAnswerSource state
      openConf := state.carrier.index.openConf }
  let nextCarrier : PersistentFreeCommittedScheduledPayloadState :=
    { index := nextIndex
      payloadContext := state.carrier.payloadContext
      agreement := nextAgreement }
  { carrier := nextCarrier
    representative := state.representative
    cumulative := by
      simpa [nextCarrier, nextIndex] using state.cumulative }

@[simp] theorem afterBodyAnswer_sourceState
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativePersistentFreeCommittedPayloadState)
    (referenceEmpty : state.carrier.index.bodyReferences = [])
    (executableEmpty : state.carrier.index.bodyExecutables = []) :
    (afterBodyAnswer prog gt state referenceEmpty executableEmpty).carrier.sourceState =
      .running state.carrier.index.session (bodyAnswerSource state) :=
  rfl

theorem afterBodyAnswer_sourceStep
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativePersistentFreeCommittedPayloadState)
    (referenceEmpty : state.carrier.index.bodyReferences = [])
    (executableEmpty : state.carrier.index.bodyExecutables = []) :
    RawStep state.carrier.index.session state.carrier.index.source [] .none
      state.carrier.index.session
      (.running (bodyAnswerSource state)) := by
  have emptyAgreement :
      PersistentFreeCommittedProductPayloadResourceRelatesAt
        state.carrier.index.freshFrontier state.carrier.index.alpha
        state.carrier.index.support state.carrier.index.canonical
        state.carrier.index.referenceBase state.carrier.index.predicateScope
        state.carrier.index.session state.carrier.index.bodyBarrier
        state.carrier.index.callerBarrier [] []
        state.carrier.index.callerReferences
        state.carrier.index.callerExecutables state.carrier.index.outer
        state.carrier.index.current state.carrier.index.runtime
        state.carrier.index.qterm state.carrier.index.resources
        state.carrier.index.callerScope state.carrier.index.outerScope
        state.carrier.index.context state.carrier.index.baseAlts
        state.carrier.index.source state.carrier.index.openConf
        state.carrier.payloadContext := by
    simpa only [PersistentFreeCommittedPayloadIndex.Relates, referenceEmpty,
      executableEmpty] using state.carrier.agreement
  exact
    (PersistentFreeCommittedProductPayloadResourceRelatesAt.afterBodyAnswer
      (prog := prog) (gt := gt) emptyAgreement).1

@[simp] theorem afterBodyAnswer_fineState
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativePersistentFreeCommittedPayloadState)
    (referenceEmpty : state.carrier.index.bodyReferences = [])
    (executableEmpty : state.carrier.index.bodyExecutables = []) :
    (afterBodyAnswer prog gt state referenceEmpty executableEmpty).carrier.fineState =
      state.carrier.fineState :=
  rfl

/-- Body completion preserves the literal already-pruned payload tail. -/
@[simp] theorem afterBodyAnswer_cellIdentities
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativePersistentFreeCommittedPayloadState)
    (referenceEmpty : state.carrier.index.bodyReferences = [])
    (executableEmpty : state.carrier.index.bodyExecutables = []) :
    (afterBodyAnswer prog gt state referenceEmpty
      executableEmpty).carrier.cellIdentities = state.carrier.cellIdentities :=
  rfl

@[simp] theorem afterBodyAnswer_cellCount
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativePersistentFreeCommittedPayloadState)
    (referenceEmpty : state.carrier.index.bodyReferences = [])
    (executableEmpty : state.carrier.index.bodyExecutables = []) :
    (afterBodyAnswer prog gt state referenceEmpty
      executableEmpty).carrier.cellCount = state.carrier.cellCount :=
  rfl

/-- The post-cut executable bank is indexed by the same literal outer
resource list as the payload zipper; body completion cannot reinsert the
consumed active resource. -/
@[simp] theorem afterBodyAnswer_resources
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativePersistentFreeCommittedPayloadState)
    (referenceEmpty : state.carrier.index.bodyReferences = [])
    (executableEmpty : state.carrier.index.bodyExecutables = []) :
    (afterBodyAnswer prog gt state referenceEmpty
      executableEmpty).carrier.index.resources = state.carrier.index.resources :=
  rfl

@[simp] theorem afterBodyAnswer_baseAlts
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativePersistentFreeCommittedPayloadState)
    (referenceEmpty : state.carrier.index.bodyReferences = [])
    (executableEmpty : state.carrier.index.bodyExecutables = []) :
    (afterBodyAnswer prog gt state referenceEmpty
      executableEmpty).carrier.index.baseAlts = state.carrier.index.baseAlts :=
  rfl

theorem afterBodyAnswer_actualAlts
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (state : RepresentativePersistentFreeCommittedPayloadState)
    (referenceEmpty : state.carrier.index.bodyReferences = [])
    (executableEmpty : state.carrier.index.bodyExecutables = []) :
    (afterBodyAnswer prog gt state referenceEmpty
        executableEmpty).carrier.index.openConf.control.alts =
      flattenOwnedAlts state.carrier.index.resources
        state.carrier.index.baseAlts := by
  exact
    (afterBodyAnswer prog gt state referenceEmpty
      executableEmpty).carrier.agreement.actualAlts

end RepresentativePersistentFreeCommittedPayloadState

end PLeaTTa.PrologPersistentFreeCommittedScheduledPayloadBridge
