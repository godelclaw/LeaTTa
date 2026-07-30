-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologProductSchedulingBridge
Purpose: Relate clause-body success to caller-first product scheduling while
  preserving distinct callee and caller cut barriers.
Trusted boundary: none
Main exports:
  SegmentedActiveProductRelates,
  SegmentedRepresentativeProductActivation.segmentedActiveProductRelates,
  SegmentedActiveProductRelates.afterBodyAnswer
-/
import PLeaTTa.Proofs.PrologActivatedProductStepBridge

namespace PLeaTTa.PrologProductSchedulingBridge

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologActivatedProductStepBridge
open PrologAlphaFreshFrontierBridge
open PrologOrdinaryStepBridge
open PrologRepresentativeProductActivationBridge
open PrologRepresentativeStepActivationBridge
open PrologStateBridge

/-! ## Exact source scheduling -/

/-- Source control immediately after one selected clause body succeeds.

The caller continuation is the left branch and therefore runs first under
leftmost DFS.  The still-open predicate continuation remains the right
branch, retaining later clauses for backtracking. -/
def scheduledSourceProduct
    (callerScope : CutScopeId) (opened : OpenedCall)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (current : Substitution)
    (referenceRest : List PeTTaSpec.PrologCore.Goal) : Search :=
  .choice callerScope
    (.task callerScope referenceRest current)
    (.product callerScope
      (.cutBoundary opened.scope
        (.choice opened.scope .done
          (.clauses opened.scope (finish.advance branch branchTail))))
      referenceRest)

/-- Clause-body success is consumed privately by `product`: it schedules the
caller tail before later callee answers, emits no public observation, and
leaves the retained cursor live in the right branch. -/
theorem activeSourceProduct_answer
    {session : Session}
    (callerScope : CutScopeId) (opened : OpenedCall)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (current : Substitution)
    (referenceRest : List PeTTaSpec.PrologCore.Goal) :
    RawStep session
      (activeSourceProduct callerScope opened finish branch branchTail current
        [] referenceRest)
      [] .none session
      (.running
        (scheduledSourceProduct callerScope opened finish branch branchTail
          current referenceRest)) := by
  apply RawStep.productAnswer
  apply RawStep.cutBoundaryProgress
  apply RawStep.choiceProgress
  exact RawStep.taskAnswer opened.scope current session

/-! ## Segmented executable relation -/

/-- Ready executable task relation for a flattened spine whose clause body
and caller continuation have distinct cut-barrier identities. -/
def SegmentedReadyTaskRelates
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (bodyBarrier callerBarrier : Nat)
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (session : Session) (current : Substitution)
    (bodyReferences callerReferences :
      List PeTTaSpec.PrologCore.Goal)
    (state : OpenConf) : Prop :=
  ∃ bodyExecutables callerExecutables : List PLeaTTa.Goal,
    ∃ runtime : Metta.Subst,
      SessionRelatesPersistent freshFrontier session state.persistent ∧
      state.control.cur =
        some (bodyExecutables ++ callerExecutables, runtime) ∧
      SegmentedTaskPayloadAgrees alpha support bodyBarrier callerBarrier
        canonical referenceBase current runtime
        bodyReferences callerReferences bodyExecutables callerExecutables

/-- Relation while a selected clause body is active under its predicate cut
barrier and the caller continuation remains flattened after it at the older
caller barrier. -/
structure SegmentedActiveProductRelates
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (bodyBarrier callerBarrier : Nat)
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (opened : OpenedCall) (pending : DemandDrivenCallStep.PendingCall)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (altTail : List PLeaTTa.Alt)
    (referenceRest : List PeTTaSpec.PrologCore.Goal)
    (current : Substitution)
    (body : List PeTTaSpec.PrologCore.Goal)
    (state : OpenConf) : Prop where
  ready :
    SegmentedReadyTaskRelates freshFrontier alpha support
      bodyBarrier callerBarrier canonical referenceBase opened.session current
      body referenceRest state
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

/-- Relation after the body answer has scheduled the caller continuation.
The executable is already at that continuation and has taken no step; the
retained alternative bank still represents the right source branch. -/
structure ScheduledProductRelates
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (bodyBarrier callerBarrier : Nat)
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (opened : OpenedCall) (pending : DemandDrivenCallStep.PendingCall)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (altTail : List PLeaTTa.Alt)
    (referenceRest : List PeTTaSpec.PrologCore.Goal)
    (current : Substitution) (state : OpenConf) : Prop where
  callerReady :
    ReadyTaskRelates freshFrontier alpha support callerBarrier canonical
      referenceBase opened.session current referenceRest state
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

/-! ## Activation and answer correspondence -/

/-- The exact two-barrier activation package constructs the segmented active
state relation for its actual fine executable successor. -/
theorem
    PrologRepresentativeProductActivationBridge.SegmentedRepresentativeProductActivation.segmentedActiveProductRelates
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {copied : PLeaTTa.Clause}
    {referenceRest : List PeTTaSpec.PrologCore.Goal}
    {executableRest : List PLeaTTa.Goal}
    {qterm : Metta.Atom} {bodyBarrier callerBarrier startCounter : Nat}
    {callerScope : CutScopeId}
    {independentResult : Substitution}
    {representative : TreeSubstitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattenedRepresentative : TreeSubstitution}
    {installed : Metta.Subst}
    (activation :
      SegmentedRepresentativeProductActivation prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        referenceRest executableRest qterm bodyBarrier callerBarrier
        startCounter callerScope independentResult representative nextAlpha
        sourceCanonical flattenedRepresentative installed) :
    SegmentedActiveProductRelates (AlphaFreshFrontier nextAlpha) nextAlpha
      support bodyBarrier callerBarrier (sourceCanonical ++ canonical)
      referenceBase opened pending finish branch branchTail altTail
      referenceRest independentResult branch.body
      (activatedOpenSuccessor pending copied executableRest qterm
        installed) := by
  refine
    ⟨?_, ?_, activation.retainedAltsZero, ?_, activation.barrierTag, rfl⟩
  · refine
      ⟨copied.body, executableRest,
        PLeaTTa.trimFor (copied.body ++ executableRest) qterm installed,
        ?_, rfl, activation.segmentedPayload⟩
    unfold activatedOpenSuccessor OpenConf.ofConf persistentOf
    rw [activation.worldPreserved, activation.counterPreserved]
    exact activation.persistentAgreement
  · change
      (activatedExecutableSuccessor pending copied executableRest qterm
        installed).alts =
        altTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts
    exact activation.retainedAlts
  · change
      (activatedExecutableSuccessor pending copied executableRest qterm
        installed).barriers =
        PLeaTTa.pushBarrierCache pending.outer.barriers
    exact activation.retainedBarriers

/-- Once the selected clause body succeeds, source control performs exactly
one private scheduling step while the executable performs zero steps.  The
caller payload is recovered at `callerBarrier`, and every retained
alternative/cache/frame ownership fact is unchanged. -/
theorem SegmentedActiveProductRelates.afterBodyAnswer
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {bodyBarrier callerBarrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {referenceRest : List PeTTaSpec.PrologCore.Goal}
    {callerScope : CutScopeId}
    {current : Substitution} {state : OpenConf}
    (agreement :
      SegmentedActiveProductRelates freshFrontier alpha support
        bodyBarrier callerBarrier canonical referenceBase opened pending
        finish branch branchTail altTail referenceRest current [] state) :
    RawStep opened.session
        (activeSourceProduct callerScope opened finish branch branchTail
          current [] referenceRest)
        [] .none opened.session
        (.running
          (scheduledSourceProduct callerScope opened finish branch branchTail
            current referenceRest)) ∧
      DemandDrivenCallStep.StepsN prog gt 0
        (.ready state) (.ready state) ∧
      ScheduledProductRelates freshFrontier alpha support
        bodyBarrier callerBarrier canonical referenceBase opened pending finish
        branch branchTail altTail referenceRest current state := by
  rcases agreement.ready with
    ⟨bodyExecutables, callerExecutables, runtime, persistent, currentControl,
      payload⟩
  have bodyExecutablesNil : bodyExecutables = [] := by
    cases payload.body.control
    rfl
  subst bodyExecutables
  have callerControl :
      state.control.cur = some (callerExecutables, runtime) := by
    simpa using currentControl
  refine
    ⟨activeSourceProduct_answer callerScope opened finish branch branchTail
        current referenceRest,
      .zero (.ready state), ?_⟩
  exact
    ⟨⟨callerExecutables, runtime, persistent, callerControl,
        payload.callerPayload⟩,
      agreement.retainedAlts, agreement.retainedAltsZero,
      agreement.retainedBarriers, agreement.bodyBarrierTag,
      agreement.frames⟩

end PLeaTTa.PrologProductSchedulingBridge
