-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologSegmentedProductStepBridge
Purpose: Preserve the two-barrier active local-product relation through
  compiler-erased administration and successful primitive unification.
Trusted boundary: none
Main exports:
  SegmentedTaskPayloadAgrees.afterBodyAdministrativeStep,
  SegmentedActiveProductRelates.afterAdministrativeStep,
  SegmentedActiveProductRelates.afterAdministrativeSteps,
  SegmentedActiveProductRelates.afterUnifySuccess,
  SegmentedActiveProductRelates.afterCut
-/
import PLeaTTa.Proofs.PrologProductSchedulingBridge

namespace PLeaTTa.PrologSegmentedProductStepBridge

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologActivatedProductStepBridge
open PrologAlphaFreshFrontierBridge
open PrologOrdinaryStepBridge
open PrologProductSchedulingBridge
open PrologStateBridge

/-!
The executable machine flattens a selected clause body and its caller
continuation into one goal list, but those two segments do not share a cut
barrier.  The body runs at the newly allocated predicate barrier; the caller
retains its older barrier.  Consequently the uniform `ActiveProductRelates`
step theorems cannot be reused for recursive calls.

This module preserves the segmented relation directly.  Substitution/MGU
reasoning is shared through `TaskDataAgrees`; only control certificates remain
segmented.  In particular, successful unification trims the installed runtime
substitution against the entire executable `bodyTail ++ callerTail` while
rebuilding the two control segments at their original barrier identities.
-/

/-! ## Shared retained resources and post-cut state -/

/-- The segmented active relation projects into the same control-independent
resource certificate as the uniform relation.  Only the callee's body barrier
owns the retained clause alternatives. -/
def SegmentedActiveProductRelates.resources
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {bodyBarrier callerBarrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {referenceRest body : List PeTTaSpec.PrologCore.Goal}
    {current : Substitution} {state : OpenConf}
    (agreement :
      SegmentedActiveProductRelates freshFrontier alpha support
        bodyBarrier callerBarrier canonical referenceBase opened pending
        finish branch branchTail altTail referenceRest current body state) :
    RetainedProductResources bodyBarrier pending altTail state :=
  ⟨agreement.retainedAlts, agreement.retainedAltsZero,
    agreement.retainedBarriers, agreement.bodyBarrierTag⟩

/-- State relation after a clause-local cut has removed the retained
later-clause bank.

The continuing clause body remains certified at `bodyBarrier`; the caller
continuation remains certified independently at `callerBarrier`.  The
executable alternative stack is exactly the suspended caller stack. -/
structure SegmentedCommittedProductRelates
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (bodyBarrier callerBarrier : Nat)
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (opened : OpenedCall) (pending : DemandDrivenCallStep.PendingCall)
    (referenceRest : List PeTTaSpec.PrologCore.Goal)
    (current : Substitution)
    (body : List PeTTaSpec.PrologCore.Goal)
    (state : OpenConf) : Prop where
  ready :
    SegmentedReadyTaskRelates freshFrontier alpha support
      bodyBarrier callerBarrier canonical referenceBase opened.session current
      body referenceRest state
  outerAlts : state.control.alts = pending.outer.alts
  cacheCoherent : PLeaTTa.BarrierCacheCoherent state.toConf
  frames : state.frames = pending.frames

/-! ## Compiler-erased body administration -/

/-- One administrative body step changes only the body's control
certificate.  Shared substitution data and the caller's independently tagged
control certificate remain unchanged. -/
theorem SegmentedTaskPayloadAgrees.afterBodyAdministrativeStep
    {alpha support : List (LogicVar × String)}
    {bodyBarrier callerBarrier : Nat}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {beforeBody afterBody callerReferences :
      List PeTTaSpec.PrologCore.Goal}
    {bodyExecutables callerExecutables : List PLeaTTa.Goal}
    (agreement :
      SegmentedTaskPayloadAgrees alpha support bodyBarrier callerBarrier
        canonical referenceBase current runtime
        beforeBody callerReferences bodyExecutables callerExecutables)
    (step : AdministrativeStep beforeBody afterBody) :
    SegmentedTaskPayloadAgrees alpha support bodyBarrier callerBarrier
      canonical referenceBase current runtime
      afterBody callerReferences bodyExecutables callerExecutables := by
  refine ⟨agreement.body.data.withControl ?_, agreement.caller⟩
  cases step with
  | truth rest =>
      exact agreement.body.control.afterTruth
  | conjunction nested rest =>
      exact agreement.body.control.afterConjunction

/-- One compiler-erased administration step propagates through the actual
source choice/cut/product stack.  The executable takes exactly zero steps,
and every retained resource and barrier identity is unchanged. -/
theorem SegmentedActiveProductRelates.afterAdministrativeStep
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {bodyBarrier callerBarrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {referenceRest beforeBody afterBody :
      List PeTTaSpec.PrologCore.Goal}
    {callerScope : CutScopeId}
    {current : Substitution} {state : OpenConf}
    (agreement :
      SegmentedActiveProductRelates freshFrontier alpha support
        bodyBarrier callerBarrier canonical referenceBase opened pending
        finish branch branchTail altTail referenceRest current beforeBody
        state)
    (step : AdministrativeStep beforeBody afterBody) :
    RawStep opened.session
        (activeSourceProduct callerScope opened finish branch branchTail
          current beforeBody referenceRest)
        [] .none opened.session
        (.running
          (activeSourceProduct callerScope opened finish branch branchTail
            current afterBody referenceRest)) ∧
      DemandDrivenCallStep.StepsN prog gt 0
        (.ready state) (.ready state) ∧
      SegmentedActiveProductRelates freshFrontier alpha support
        bodyBarrier callerBarrier canonical referenceBase opened pending
        finish branch branchTail altTail referenceRest current afterBody
        state := by
  have child := step.rawStep opened.scope current opened.session
  have sourceStep :=
    activeSourceProduct_progress
      (callerScope := callerScope) (finish := finish) (branch := branch)
      (branchTail := branchTail) (referenceRest := referenceRest)
      child (by simp [Trace.AnswerFree])
  rcases agreement.ready with
    ⟨bodyExecutables, callerExecutables, runtime, persistent, currentControl,
      payload⟩
  refine
    ⟨sourceStep, .zero (.ready state),
      ⟨?_, agreement.retainedAlts, agreement.retainedAltsZero,
        agreement.retainedBarriers, agreement.bodyBarrierTag,
        agreement.frames⟩⟩
  exact
    ⟨bodyExecutables, callerExecutables, runtime, persistent, currentControl,
      PLeaTTa.PrologSegmentedProductStepBridge.SegmentedTaskPayloadAgrees.afterBodyAdministrativeStep
        payload step⟩

/-- An exactly counted finite administrative body prefix remains an exactly
counted source prefix with an empty observation trace and exactly zero
executable steps.

This is bounded stutter, not an observation-list quotient:
`AdministrativeStepsN` retains the strict source rank. -/
theorem SegmentedActiveProductRelates.afterAdministrativeSteps
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {bodyBarrier callerBarrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {referenceRest beforeBody afterBody :
      List PeTTaSpec.PrologCore.Goal}
    {callerScope : CutScopeId}
    {current : Substitution} {state : OpenConf} {count : Nat}
    (agreement :
      SegmentedActiveProductRelates freshFrontier alpha support
        bodyBarrier callerBarrier canonical referenceBase opened pending
        finish branch branchTail altTail referenceRest current beforeBody
        state)
    (steps : AdministrativeStepsN count beforeBody afterBody) :
    PeTTaSpec.PrologCore.GoalSemantics.StepsN count
        (.running opened.session
          (activeSourceProduct callerScope opened finish branch branchTail
            current beforeBody referenceRest))
        []
        (.running opened.session
          (activeSourceProduct callerScope opened finish branch branchTail
            current afterBody referenceRest)) ∧
      DemandDrivenCallStep.StepsN prog gt 0
        (.ready state) (.ready state) ∧
      SegmentedActiveProductRelates freshFrontier alpha support
        bodyBarrier callerBarrier canonical referenceBase opened pending
        finish branch branchTail altTail referenceRest current afterBody
        state := by
  induction steps with
  | zero goals =>
      exact ⟨.zero _, .zero _, agreement⟩
  | succ count before middle after head tail inductionHypothesis =>
      rcases
          PLeaTTa.PrologSegmentedProductStepBridge.SegmentedActiveProductRelates.afterAdministrativeStep
            (prog := prog) (gt := gt) (callerScope := callerScope)
            agreement head with
        ⟨firstRaw, _executableZero, middleAgreement⟩
      have first :
          Transition
            (.running opened.session
              (activeSourceProduct callerScope opened finish branch branchTail
                current before referenceRest))
            []
            (.running opened.session
              (activeSourceProduct callerScope opened finish branch branchTail
                current middle referenceRest)) :=
        .ordinary _ [] opened.session opened.session
          (.running
            (activeSourceProduct callerScope opened finish branch branchTail
              current middle referenceRest))
          firstRaw
      rcases inductionHypothesis middleAgreement with
        ⟨remaining, _remainingExecutableZero, finalAgreement⟩
      refine ⟨?_, .zero _, finalAgreement⟩
      simpa using
        PeTTaSpec.PrologCore.GoalSemantics.StepsN.succ count
          (.running opened.session
            (activeSourceProduct callerScope opened finish branch branchTail
              current before referenceRest))
          (.running opened.session
            (activeSourceProduct callerScope opened finish branch branchTail
              current middle referenceRest))
          (.running opened.session
            (activeSourceProduct callerScope opened finish branch branchTail
              current after referenceRest))
          [] [] first remaining

/-! ## Successful primitive body unification -/

/-- One successful primitive unification preserves the segmented active
product relation without retagging the caller.

The MGU/install proof is continuation-independent
(`TaskPayloadAgrees.afterUnifySuccessData`).  Liveness trimming is then
performed once against the actual flattened executable continuation, while
the body and caller control certificates are reconstructed separately at
`bodyBarrier` and `callerBarrier`. -/
theorem SegmentedActiveProductRelates.afterUnifySuccess
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {bodyBarrier callerBarrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {referenceRest bodyRest : List PeTTaSpec.PrologCore.Goal}
    {callerScope : CutScopeId}
    {current result : Substitution} {state : OpenConf}
    {left right : Term}
    (agreement :
      SegmentedActiveProductRelates freshFrontier alpha support
        bodyBarrier callerBarrier canonical referenceBase opened pending
        finish branch branchTail altTail referenceRest current
        (.unify left right :: bodyRest) state)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote right))
    (supportIncluded :
      ∀ pair, pair ∈ support → pair ∈ alpha)
    (safe : ReadyUnifyContinuationSafe support state)
    (resolved : UnifyResolution current left right result) :
    ∃ (spelling :
          NormalizedAlphaGoalsAgree.ExecutableUnifySpelling)
        (executableLeft executableRight : Metta.Atom)
        (bodyExecutableTail callerExecutables : List PLeaTTa.Goal)
        (runtime : Metta.Subst),
      ∃ sourceExtension installed,
        state.control.cur =
            some
              (spelling.goal executableLeft executableRight ::
                (bodyExecutableTail ++ callerExecutables),
                runtime) ∧
        RawStep opened.session
          (activeSourceProduct callerScope opened finish branch branchTail
            current (.unify left right :: bodyRest) referenceRest)
          [] .none opened.session
          (.running
            (activeSourceProduct callerScope opened finish branch branchTail
              result bodyRest referenceRest)) ∧
        DemandDrivenCallStep.Step prog gt (.ready state)
          (.ready
            (unifySuccessor state
              (bodyExecutableTail ++ callerExecutables) installed)) ∧
        SegmentedActiveProductRelates freshFrontier alpha support
          bodyBarrier callerBarrier (sourceExtension ++ canonical)
          referenceBase opened pending finish branch branchTail altTail
          referenceRest result bodyRest
          (unifySuccessor state
            (bodyExecutableTail ++ callerExecutables) installed) := by
  rcases agreement.ready with
    ⟨bodyExecutables, callerExecutables, runtime, persistent, currentControl,
      payload⟩
  rcases payload.body.control.unifyHead with
    ⟨spelling, executableLeft, executableRight, bodyExecutableTail,
      bodyShape, leftAgreement, rightAgreement, bodyTailControl⟩
  have executableHead :
      state.control.cur =
        some
          (spelling.goal executableLeft executableRight ::
            (bodyExecutableTail ++ callerExecutables),
            runtime) := by
    calc
      state.control.cur =
          some (bodyExecutables ++ callerExecutables, runtime) :=
        currentControl
      _ =
          some
            ((spelling.goal executableLeft executableRight ::
                bodyExecutableTail) ++ callerExecutables,
              runtime) := by rw [bodyShape]
      _ =
          some
            (spelling.goal executableLeft executableRight ::
              (bodyExecutableTail ++ callerExecutables),
              runtime) := by rfl
  obtain ⟨runtimeAvoids, live⟩ := safe executableHead
  obtain ⟨sourceExtension, installed, installedExact, nextData⟩ :=
    payload.body.afterUnifySuccessData leftAgreement rightAgreement
      leftSupported rightSupported supportIncluded runtimeAvoids resolved
  have child :
      RawStep opened.session
        (.task opened.scope (.unify left right :: bodyRest) current)
        [] .none opened.session
        (.running (.task opened.scope bodyRest result)) :=
    .taskUnifySuccess opened.scope left right bodyRest current result
      opened.session resolved
  have sourceStep :=
    activeSourceProduct_progress
      (callerScope := callerScope) (finish := finish) (branch := branch)
      (branchTail := branchTail) (referenceRest := referenceRest)
      child (by simp [Trace.AnswerFree])
  have executableStep :
      DemandDrivenCallStep.Step prog gt (.ready state)
        (.ready
          (unifySuccessor state
            (bodyExecutableTail ++ callerExecutables) installed)) :=
    executable_unify_step state spelling executableLeft executableRight
      (bodyExecutableTail ++ callerExecutables) runtime installed
      executableHead installedExact
  let nextState :=
    unifySuccessor state
      (bodyExecutableTail ++ callerExecutables) installed
  have nextReady :
      SegmentedReadyTaskRelates freshFrontier alpha support
        bodyBarrier callerBarrier (sourceExtension ++ canonical)
        referenceBase opened.session result bodyRest referenceRest
        nextState := by
    refine
      ⟨bodyExecutableTail, callerExecutables,
        PLeaTTa.trimFor (bodyExecutableTail ++ callerExecutables)
          state.control.qterm installed,
        ?_, ?_, ?_⟩
    · simpa [nextState] using persistent
    · simp [nextState]
    · refine
        ⟨(nextData.trimFor live).withControl bodyTailControl,
          payload.caller⟩
  refine
    ⟨spelling, executableLeft, executableRight, bodyExecutableTail,
      callerExecutables, runtime, sourceExtension, installed, executableHead,
      sourceStep, executableStep, ?_⟩
  refine
    ⟨nextReady, ?_, agreement.retainedAltsZero, ?_,
      agreement.bodyBarrierTag, ?_⟩
  · change
      state.toConf.alts =
        altTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts
    exact agreement.retainedAlts
  · change
      state.toConf.barriers =
        PLeaTTa.pushBarrierCache pending.outer.barriers
    exact agreement.retainedBarriers
  · simpa [nextState, unifySuccessor] using agreement.frames

/-! ## Clause-local cut -/

/-- One clause-local cut prunes the retained later-clause cursor while
preserving the caller continuation at its independently certified barrier.

The source emits the exact cursor-token prune observation and catches the
commit at the predicate scope.  The executable performs one real tagged-cut
step at `bodyBarrier`, removes exactly the predicate-owned alternatives and
marker, and retains the caller's flattened control at `callerBarrier`. -/
theorem SegmentedActiveProductRelates.afterCut
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {bodyBarrier callerBarrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {referenceRest bodyRest : List PeTTaSpec.PrologCore.Goal}
    {callerScope : CutScopeId}
    {current : Substitution} {state : OpenConf}
    (agreement :
      SegmentedActiveProductRelates freshFrontier alpha support
        bodyBarrier callerBarrier canonical referenceBase opened pending
        finish branch branchTail altTail referenceRest current
        (.cut :: bodyRest) state)
    (coherent : PLeaTTa.BarrierCacheCoherent state.toConf) :
    ∃ bodyExecutableTail callerExecutables runtime,
      state.control.cur =
          some
            (.cutAt bodyBarrier ::
              (bodyExecutableTail ++ callerExecutables),
              runtime) ∧
        RawStep opened.session
          (activeSourceProduct callerScope opened finish branch branchTail
            current (.cut :: bodyRest) referenceRest)
          [.pruned (retainedCursorToken opened finish branch branchTail)]
          .none opened.session
          (.running
            (cutSourceProduct callerScope opened current bodyRest
              referenceRest)) ∧
        DemandDrivenCallStep.Step prog gt (.ready state)
          (.ready
            (cutSuccessor state bodyBarrier
              (bodyExecutableTail ++ callerExecutables) runtime)) ∧
        SegmentedCommittedProductRelates freshFrontier alpha support
          bodyBarrier callerBarrier canonical referenceBase opened pending
          referenceRest current bodyRest
          (cutSuccessor state bodyBarrier
            (bodyExecutableTail ++ callerExecutables) runtime) := by
  rcases agreement.ready with
    ⟨bodyExecutables, callerExecutables, runtime, persistent, currentControl,
      payload⟩
  rcases payload.body.control.cutHead with
    ⟨bodyExecutableTail, bodyShape, bodyTailControl⟩
  have executableHead :
      state.control.cur =
        some
          (.cutAt bodyBarrier ::
            (bodyExecutableTail ++ callerExecutables),
            runtime) := by
    calc
      state.control.cur =
          some (bodyExecutables ++ callerExecutables, runtime) :=
        currentControl
      _ =
          some
            ((.cutAt bodyBarrier :: bodyExecutableTail) ++
              callerExecutables,
              runtime) := by rw [bodyShape]
      _ =
          some
            (.cutAt bodyBarrier ::
              (bodyExecutableTail ++ callerExecutables),
              runtime) := by rfl
  let nextState :=
    cutSuccessor state bodyBarrier
      (bodyExecutableTail ++ callerExecutables) runtime
  have executableStep :
      DemandDrivenCallStep.Step prog gt (.ready state)
        (.ready nextState) :=
    executable_cut_step state bodyBarrier
      (bodyExecutableTail ++ callerExecutables) runtime executableHead
  have nextReady :
      SegmentedReadyTaskRelates freshFrontier alpha support
        bodyBarrier callerBarrier canonical referenceBase opened.session current
        bodyRest referenceRest nextState := by
    refine
      ⟨bodyExecutableTail, callerExecutables, runtime, ?_, ?_, ?_⟩
    · simpa [nextState] using persistent
    · simp [nextState]
    · exact
        ⟨payload.body.data.withControl bodyTailControl, payload.caller⟩
  refine
    ⟨bodyExecutableTail, callerExecutables, runtime, executableHead,
      activeSourceProduct_cut, executableStep, nextReady, ?_, ?_, ?_⟩
  · change
      (PLeaTTa.cutToTracked bodyBarrier state.toConf.barriers
        state.toConf.alts).1 =
        pending.outer.alts
    exact
      (PLeaTTa.PrologSegmentedProductStepBridge.SegmentedActiveProductRelates.resources
        agreement).cutToTracked_alts_eq_outer coherent
  · have nextCoherent :=
      PLeaTTa.BarrierCacheCoherent.cut state.toConf bodyBarrier coherent
    unfold PLeaTTa.BarrierCacheCoherent at nextCoherent ⊢
    simpa [nextState, cutSuccessor] using nextCoherent
  · simpa [nextState, cutSuccessor] using agreement.frames

end PLeaTTa.PrologSegmentedProductStepBridge
