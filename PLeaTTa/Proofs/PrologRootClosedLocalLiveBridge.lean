-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologRootClosedLocalLiveBridge
Purpose: Couple one rooted local source answer's control and trace to the
  exact fine executable answer-and-pull step
Trusted boundary: none
Main exports: RootClosedLocalLiveAnswerRelates,
  RootClosedAnswerReady.localLiveAnswer
-/
import PLeaTTa.Proofs.PrologRootClosedAnswerBridge
import PLeaTTa.Proofs.PrologAnswerSourceCatchupBridge

namespace PLeaTTa.PrologRootClosedLocalLiveBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open DemandDrivenStep
open PrologAnswerPullClassificationBridge
open PrologAnswerSourceCatchupBridge
open PrologFindallAnswerResourceBridge
open PrologHeterogeneousPrefixBridge
open PrologRootClosedAnswerBridge
open PrologScheduledAnswerPropagationBridge
open PrologScheduledPayloadResumeBridge

/-- Exact source/fine correspondence for one rooted scheduled answer whose
eager executable pull selects another locally owned branch.

The source answer substitution and the executable runtime substitution are
deliberately distinct fields of the same `before` carrier.  The carrier's
cumulative residual certificate relates those substitutions on its explicit
support.  This structure does not additionally identify the source answer's
query-term denotation with `subst runtime qterm`: the corresponding
independent query term is not an index of this phase carrier, so that value
statement belongs to the later compiler/observation composition theorem.
The selected `binding` below belongs to the *next* branch and is never used
to emit the current answer.

The independent source crosses every empty outer frame silently, emits one
singleton answer observation, then takes the exact silent origin-prefix
catch-up.  The fine lane takes one real sealed answer step, eagerly pulls the
same selected branch, and preserves all non-backtrackable and open-control
state.

[SPEC metta.pl:251-256, translator.pl:320-321] -/
structure RootClosedLocalLiveAnswerRelates
    (prog : Prog) (gt : Metta.GroundingTable)
    (before : RepresentativeScheduledPayloadState)
    (ready : RootClosedAnswerReady before)
    (selectedGoals : List PLeaTTa.Goal) (selectedBinding : Subst)
    (selectedTail : List PLeaTTa.Alt)
    (count : Nat) (target : Search) : Prop where
  landing :
    OriginPrefixLanding before.carrier.index.alpha
      ready.result.history.resourceAgreement selectedGoals selectedBinding
      selectedTail
  sourceBindingExact :
    ready.result.history.bindings = before.carrier.index.current
  sourceRun :
    PeTTaSpec.PrologCore.GoalSemantics.StepsN
      (before.carrier.index.outer.length + 1 + count)
      before.carrier.sourceState
      [.answer before.carrier.index.current]
      (.running before.carrier.index.session target)
  sourceReady :
    ConservativeReadyPullTarget before.carrier.index.alpha selectedGoals
      selectedBinding selectedTail target
  fineStep :
    DemandDrivenStep.Step prog gt before.carrier.index.openConf
      (privateAnswerTarget before.carrier.index.openConf
        before.carrier.index.runtime)
  fineRun :
    DemandDrivenStep.StepsN prog gt 1 before.carrier.index.openConf
      (privateAnswerTarget before.carrier.index.openConf
        before.carrier.index.runtime)
  fineSelected :
    (privateAnswerTarget before.carrier.index.openConf
        before.carrier.index.runtime).control.cur =
        some (selectedGoals, selectedBinding) ∧
      (privateAnswerTarget before.carrier.index.openConf
        before.carrier.index.runtime).control.alts = selectedTail
  fineFrames :
    (privateAnswerTarget before.carrier.index.openConf
        before.carrier.index.runtime).frames =
      before.carrier.index.openConf.frames
  fineScopes :
    (privateAnswerTarget before.carrier.index.openConf
        before.carrier.index.runtime).scopes =
      before.carrier.index.openConf.scopes
  finePersistent :
    (privateAnswerTarget before.carrier.index.openConf
        before.carrier.index.runtime).persistent =
      before.carrier.index.openConf.persistent
  fineAnswerAccumulator :
    (privateAnswerTarget before.carrier.index.openConf
        before.carrier.index.runtime).control.answers =
      PLeaTTa.subst before.carrier.index.runtime
          before.carrier.index.openConf.control.qterm ::
        before.carrier.index.openConf.control.answers

namespace RootClosedAnswerReady

/-- Compose a locally live rooted pull into one exact source-answer prefix and
one exact fine executable answer step.

The source catch-up target and its transition count are derived from the
branch-indexed `OriginPrefixLanding`; callers cannot provide a compatible but
unrelated endpoint. -/
theorem localLiveAnswer
    {prog : Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeScheduledPayloadState}
    (ready : RootClosedAnswerReady before)
    {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
    {selectedTail : List PLeaTTa.Alt}
    (landing :
      OriginPrefixLanding before.carrier.index.alpha
        ready.result.history.resourceAgreement selectedGoals selectedBinding
        selectedTail) :
    exists count target,
      RootClosedLocalLiveAnswerRelates prog gt before ready selectedGoals
        selectedBinding selectedTail count target := by
  obtain ⟨count, target, catchup, sourceReady⟩ :=
    PLeaTTa.PrologAnswerSourceCatchupBridge.OriginPrefixLanding.sourceStepsN
      landing before.carrier.index.session
  have sourceBindingExact :
      ready.result.history.bindings = before.carrier.index.current := by
    simpa using ready.result.bindingsExact
  have absorption := ready.sourceSteps
  rw [← ready.result.targetSourceExact] at absorption
  have answerTransition :
      Transition
        (.running before.carrier.index.session ready.result.targetSource)
        [.answer ready.result.history.bindings]
        (.running before.carrier.index.session ready.result.targetNext) :=
    .ordinary _ _ _ _ _
      (ready.result.history.sourceStep before.carrier.index.session)
  have answerRun :
      PeTTaSpec.PrologCore.GoalSemantics.StepsN 1
        (.running before.carrier.index.session ready.result.targetSource)
        [.answer ready.result.history.bindings]
        (.running before.carrier.index.session ready.result.targetNext) := by
    simpa using
      (PeTTaSpec.PrologCore.GoalSemantics.StepsN.succ 0 _ _ _
        [.answer ready.result.history.bindings] [] answerTransition
        (.zero _))
  have sourceRunRaw :=
    PeTTaSpec.PrologCore.GoalSemantics.StepsN.trans absorption
      (PeTTaSpec.PrologCore.GoalSemantics.StepsN.trans answerRun catchup)
  have sourceRun :
      PeTTaSpec.PrologCore.GoalSemantics.StepsN
        (before.carrier.index.outer.length + 1 + count)
        before.carrier.sourceState
        [.answer before.carrier.index.current]
        (.running before.carrier.index.session target) := by
    simpa [Nat.add_assoc, sourceBindingExact] using sourceRunRaw
  have fineStep :
      DemandDrivenStep.Step prog gt before.carrier.index.openConf
        (privateAnswerTarget before.carrier.index.openConf
          before.carrier.index.runtime) :=
    answer_is_one_step prog gt before.carrier.index.openConf
      before.carrier.index.runtime ready.fineHead
  have fineRun :
      DemandDrivenStep.StepsN prog gt 1 before.carrier.index.openConf
        (privateAnswerTarget before.carrier.index.openConf
          before.carrier.index.runtime) := by
    simpa using
      DemandDrivenStep.StepsN.succ 0 before.carrier.index.openConf
        (privateAnswerTarget before.carrier.index.openConf
          before.carrier.index.runtime)
        (privateAnswerTarget before.carrier.index.openConf
          before.carrier.index.runtime)
        fineStep (.zero _)
  have selectedPull :
      PLeaTTa.pullAux before.carrier.index.openConf.control.alts =
        some (.branch selectedGoals selectedBinding, selectedTail) := by
    rw [ready.bankExact]
    exact landing.pullAux_exact
  have fineSelected :
      (privateAnswerTarget before.carrier.index.openConf
          before.carrier.index.runtime).control.cur =
          some (selectedGoals, selectedBinding) ∧
        (privateAnswerTarget before.carrier.index.openConf
          before.carrier.index.runtime).control.alts = selectedTail :=
    PullOutcomeAgrees.fields_of_pull_some
      (privateAnswerTarget_pullOutcome before.carrier.index.openConf
        before.carrier.index.runtime)
      selectedPull
  exact
    ⟨count, target,
      { landing := landing
        sourceBindingExact := sourceBindingExact
        sourceRun := sourceRun
        sourceReady := sourceReady
        fineStep := fineStep
        fineRun := fineRun
        fineSelected := fineSelected
        fineFrames := by simp
        fineScopes := by simp
        finePersistent := by simp
        fineAnswerAccumulator := by simp }⟩

/-- Classifying the actual rooted executable bank yields either a fully
coupled local-live answer run or the source origin's genuine terminal
fall-through.  In particular, the local theorem cannot be inhabited by a
landing chosen independently of the bank classifier. -/
theorem classifyPullAndRelate
    {prog : Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeScheduledPayloadState}
    (ready : RootClosedAnswerReady before) :
    (exists selectedGoals selectedBinding selectedTail count target,
        RootClosedLocalLiveAnswerRelates prog gt before ready selectedGoals
          selectedBinding selectedTail count target) ∨
      OriginPrefixFallsThrough before.carrier.index.alpha
        ready.result.history.resourceAgreement := by
  obtain ⟨_events, outcome, _pull⟩ :=
    PLeaTTa.PrologRootClosedAnswerBridge.RootClosedAnswerReady.classifyPull
      ready
  cases outcome with
  | localLive selectedGoals selectedBinding selectedTail landing =>
      obtain ⟨count, target, relates⟩ :=
        PLeaTTa.PrologRootClosedLocalLiveBridge.RootClosedAnswerReady.localLiveAnswer
          ready landing
      exact .inl
        ⟨selectedGoals, selectedBinding, selectedTail, count, target, relates⟩
  | terminal falls =>
      exact .inr falls

end RootClosedAnswerReady

end PLeaTTa.PrologRootClosedLocalLiveBridge
