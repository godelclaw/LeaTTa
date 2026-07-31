-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologCurrentSessionAdministrativeTransitionBridge
Purpose: Lift an exactly counted compiler-erased administrative prefix through
  the complete active product/resource/payload context.
Trusted boundary: none
Main exports:
  taskPayload_afterAdministrativeSteps,
  administrativeSteps_activeProductContextSourceSteps,
  SpinedActiveProductPayloadResourceRelatesAt.afterAdministrativeSteps
-/
import PLeaTTa.Proofs.PrologCurrentSessionPayloadBridge

namespace PLeaTTa.PrologCurrentSessionAdministrativeTransitionBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologActivatedProductStepBridge
open PrologControlSegmentSpineBridge
open PrologCurrentSessionPayloadBridge
open PrologOrdinaryStepBridge
open PrologProductResourceContextBridge
open PrologProductResourceTransitionBridge
open PrologRetainedPayloadSnapshotBridge
open PrologSourceProductContextBridge
open PrologStateBridge

/-!
The independent local-goal semantics retains `truth` and top-level
`conjunction` nodes as real transitions.  Compilation erases `truth` and
flattens conjunctions before executable control begins.  Consequently an
exact correspondence must retain every source transition while pairing the
whole finite prefix with exactly zero executable steps.

The leaf-level ranked prefix was already proved in
`PrologOrdinaryStepBridge`.  This module lifts that same prefix through the
selected clause product and an arbitrary inner-to-outer stack of older
predicate activations.  The executable state, persistent session bridge,
retained cursor/resource bank, independently tagged control spine, and
immutable payload zipper remain literal.  No stuttering quotient is used.
-/

/-- One compiler-erased source administrative step changes only the control
spelling of an already-related task payload.  The canonical substitution,
cumulative source/runtime valuation, and executable goals remain literal. -/
theorem taskPayload_afterAdministrativeStep
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {before after : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      TaskPayloadAgrees alpha support barrier canonical referenceBase current
        runtime before executables)
    (step : AdministrativeStep before after) :
    TaskPayloadAgrees alpha support barrier canonical referenceBase current
      runtime after executables := by
  apply agreement.data.withControl
  cases step with
  | truth rest =>
      exact agreement.control.afterTruth
  | conjunction nested rest =>
      exact agreement.control.afterConjunction

/-- A finite compiler-erased source administrative prefix preserves every
payload datum except the independently certified source control spelling. -/
theorem taskPayload_afterAdministrativeSteps
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {count : Nat}
    {before after : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      TaskPayloadAgrees alpha support barrier canonical referenceBase current
        runtime before executables)
    (steps : AdministrativeStepsN count before after) :
    TaskPayloadAgrees alpha support barrier canonical referenceBase current
      runtime after executables := by
  induction steps with
  | zero goals =>
      exact agreement
  | succ count before middle after head tail inductionHypothesis =>
      exact inductionHypothesis
        (taskPayload_afterAdministrativeStep agreement head)

/-- Exactly counted compiler-erased administration lifts through the current
predicate product and every older active predicate frame.

Each abstract administrative constructor produces one actual public source
transition with the empty observation list.  The induction therefore retains
the exact count and cannot turn an infinite administrative run into a finite
or zero-step execution. -/
theorem administrativeSteps_activeProductContextSourceSteps
    {count : Nat}
    {beforeBody afterBody : List PeTTaSpec.PrologCore.Goal}
    (steps : AdministrativeStepsN count beforeBody afterBody)
    (context : ActiveProductContext)
    (callerScope : CutScopeId) (opened : OpenedCall)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (current : Substitution)
    (callerReferences : List PeTTaSpec.PrologCore.Goal)
    (session : Session) :
    PeTTaSpec.PrologCore.GoalSemantics.StepsN count
      (.running session
        (ActiveProductContext.plug context
          (activeSourceProduct callerScope opened finish branch branchTail
            current beforeBody callerReferences)))
      []
      (.running session
        (ActiveProductContext.plug context
          (activeSourceProduct callerScope opened finish branch branchTail
            current afterBody callerReferences))) := by
  induction steps with
  | zero goals =>
      exact .zero _
  | succ count before middle after head tail inductionHypothesis =>
      have child :
          RawStep session (.task opened.scope before current) [] .none session
            (.running (.task opened.scope middle current)) :=
        head.rawStep opened.scope current session
      have active :
          RawStep session
            (activeSourceProduct callerScope opened finish branch branchTail
              current before callerReferences)
            [] .none session
            (.running
              (activeSourceProduct callerScope opened finish branch branchTail
                current middle callerReferences)) := by
        simpa using
          ActiveProductFrame.liftProgress
            (ActiveProductFrame.ofActiveProduct callerScope opened finish
              branch branchTail callerReferences)
            child (by simp [Trace.AnswerFree])
      have lifted :
          RawStep session
            (ActiveProductContext.plug context
              (activeSourceProduct callerScope opened finish branch branchTail
                current before callerReferences))
            [] .none session
            (.running
              (ActiveProductContext.plug context
                (activeSourceProduct callerScope opened finish branch
                  branchTail current middle callerReferences))) :=
        ActiveProductContext.liftProgress context active
          (by simp [Trace.AnswerFree])
      have first :
          Transition
            (.running session
              (ActiveProductContext.plug context
                (activeSourceProduct callerScope opened finish branch
                  branchTail current before callerReferences)))
            []
            (.running session
              (ActiveProductContext.plug context
                (activeSourceProduct callerScope opened finish branch
                  branchTail current middle callerReferences))) :=
        .ordinary _ [] session session
          (.running
            (ActiveProductContext.plug context
              (activeSourceProduct callerScope opened finish branch branchTail
                current middle callerReferences)))
          lifted
      simpa using
        PeTTaSpec.PrologCore.GoalSemantics.StepsN.succ count
          (.running session
            (ActiveProductContext.plug context
              (activeSourceProduct callerScope opened finish branch branchTail
                current before callerReferences)))
          (.running session
            (ActiveProductContext.plug context
              (activeSourceProduct callerScope opened finish branch branchTail
                current middle callerReferences)))
          (.running session
            (ActiveProductContext.plug context
              (activeSourceProduct callerScope opened finish branch branchTail
                current after callerReferences)))
          [] [] first inductionHypothesis

namespace SpinedActiveProductPayloadResourceRelatesAt

/-- A finite compiler-erased administrative prefix through the complete
current-session active context.

The source performs exactly `count` real transitions and emits exactly no
observations.  The executable performs exactly zero steps.  Only the active
source body list and its control certificate advance; the shared
substitutions, current executable state, persistent state, all older control
regions, retained resources, alternatives, frames, query term, and payload
endpoints remain identical.  The final rank equation makes the bounded
stutter explicit. -/
theorem afterAdministrativeSteps
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {session : Session}
    {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {beforeBody afterBody : List PeTTaSpec.PrologCore.Goal}
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
    {payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish branch
        branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context}
    (agreement :
      SpinedActiveProductPayloadResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened session pending finish branch branchTail
        altTail bodyBarrier callerBarrier beforeBody bodyExecutables
        callerReferences callerExecutables outer current runtime qterm active
        resources callerScope outerScope context baseAlts source state
        payloadContext)
    {count : Nat}
    (steps : AdministrativeStepsN count beforeBody afterBody) :
    let nextSource :=
      ActiveProductContext.plug context
        (activeSourceProduct callerScope opened finish branch branchTail
          current afterBody callerReferences)
    PeTTaSpec.PrologCore.GoalSemantics.StepsN count
        (.running session source) []
        (.running session nextSource) ∧
      DemandDrivenCallStep.StepsN prog gt 0
        (.ready state) (.ready state) ∧
      SpinedActiveProductPayloadResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened session pending finish branch branchTail
        altTail bodyBarrier callerBarrier afterBody bodyExecutables
        callerReferences callerExecutables outer current runtime qterm active
        resources callerScope outerScope context baseAlts nextSource state
        payloadContext ∧
      administrativeRank beforeBody =
        count + administrativeRank afterBody := by
  dsimp only
  rcases agreement.core.control.ready with
    ⟨persistent, currentControl, queryTerm, spinePayload⟩
  have bodyPayload :
      TaskPayloadAgrees alpha support bodyBarrier canonical referenceBase
        current runtime beforeBody bodyExecutables :=
    spinePayload.headPayload
  have nextBodyPayload :
      TaskPayloadAgrees alpha support bodyBarrier canonical referenceBase
        current runtime afterBody bodyExecutables :=
    taskPayload_afterAdministrativeSteps bodyPayload steps
  have nextSpinePayload :
      TaskSpinePayloadAgrees alpha support canonical referenceBase current
        runtime
        ({ barrier := bodyBarrier
           references := afterBody
           executables := bodyExecutables } ::
         { barrier := callerBarrier
           references := callerReferences
           executables := callerExecutables } ::
         outer) :=
    ⟨nextBodyPayload.data,
      .cons nextBodyPayload.control spinePayload.control.tail⟩
  have nextReady :
      SpinedReadyTaskRelates freshFrontier alpha support canonical
        referenceBase session current runtime qterm
        ({ barrier := bodyBarrier
           references := afterBody
           executables := bodyExecutables } ::
         { barrier := callerBarrier
           references := callerReferences
           executables := callerExecutables } ::
         outer)
        state :=
    ⟨persistent, currentControl, queryTerm, nextSpinePayload⟩
  have nextControl :
      SpinedActiveProductRelatesAt freshFrontier alpha support canonical
        referenceBase opened session pending finish branch branchTail altTail
        bodyBarrier callerBarrier afterBody bodyExecutables callerReferences
        callerExecutables outer current runtime qterm state :=
    ⟨nextReady, agreement.core.control.sessionAdvanced,
      agreement.core.control.retainedAlts,
      agreement.core.control.retainedAltsZero,
      agreement.core.control.retainedBarriers,
      agreement.core.control.bodyBarrierTag,
      agreement.core.control.frames⟩
  let nextSource :=
    ActiveProductContext.plug context
      (activeSourceProduct callerScope opened finish branch branchTail
        current afterBody callerReferences)
  have nextCore :
      SpinedActiveProductResourceRelatesAt freshFrontier alpha support canonical
        referenceBase opened session pending finish branch branchTail altTail
        bodyBarrier callerBarrier afterBody bodyExecutables callerReferences
        callerExecutables outer current runtime qterm active resources
        callerScope outerScope context baseAlts nextSource state :=
    ⟨nextControl, agreement.core.resourceStack, rfl⟩
  have sourceSteps :
      PeTTaSpec.PrologCore.GoalSemantics.StepsN count
        (.running session source) []
        (.running session nextSource) := by
    rw [agreement.core.sourceShape]
    exact
      administrativeSteps_activeProductContextSourceSteps steps context
        callerScope opened finish branch branchTail current callerReferences
        session
  exact
    ⟨sourceSteps, .zero (.ready state),
      ⟨nextCore, agreement.endpointsCurrent,
        agreement.activationOrdered⟩,
      steps.rank_exact⟩

end SpinedActiveProductPayloadResourceRelatesAt

end PLeaTTa.PrologCurrentSessionAdministrativeTransitionBridge
