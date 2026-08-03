-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologScheduledPayloadResumeRegression
Purpose: Inhabit exact multi-frame scheduled-answer absorption with one live
  source-ordered p -> q -> r local-resolution carrier.
Trusted boundary: none
-/
import PLeaTTa.Proofs.PrologNestedCallReadyRegression
import PLeaTTa.Proofs.PrologRootClosedLocalLiveBridge

namespace PLeaTTa.PrologScheduledPayloadResumeRegression

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open DemandDrivenStep
open PrologHeterogeneousPrefixBridge
open PrologNestedCallChainBridge
open PrologNestedCallReadyBridge
open PrologPersistentFreeScheduledPayloadBridge
open PrologRootClosedAnswerBridge
open PrologRootClosedLocalLiveBridge
open PrologScheduledPayloadResumeBridge

/-- The literal depth-two run supplies one rooted scheduled carrier together
with all hypotheses needed by both private absorption and closed public-pull
classification. -/
private theorem groundRootClosedScheduledCarrier
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ before : RepresentativePersistentFreeScheduledPayloadState,
      before.carrier.index.callerReferences = [] ∧
        before.carrier.index.baseAlts = [] ∧
        before.carrier.index.outer.length = 2 ∧
        (∀ segment ∈ before.carrier.index.outer,
          segment.references = []) := by
  obtain
    ⟨_root, _qHead, _middle, _qReady, _qPredicate, _qPayload,
      _rootReferences, _rootExecutables, _rootSourceSteps, _rootFineSteps,
      _qCertificate, _rHead, after, _rReady, _rPredicate, _rPayload,
      _rCertificate, bodyReferencesEmpty, bodyExecutablesEmpty,
      callerReferencesEmpty, baseAltsEmpty, _afterActiveAlts,
      _afterResources, _middleActiveAlts, _rootActiveAlts, outerLength,
      outerAllEmpty⟩ :=
    PrologNestedCallReadyRegression.ground_p_q_r_two_nested_pushes
      (prog := prog) (gt := gt)
  obtain ⟨representative, carrierExact⟩ := after.existsRepresentative
  subst after
  let before :=
    RepresentativeActivePayloadState.afterBodyAnswer prog gt representative
      bodyReferencesEmpty bodyExecutablesEmpty
  exact
    ⟨before, by simpa [before] using callerReferencesEmpty,
      by simpa only [before,
        RepresentativeActivePayloadState.afterBodyAnswer_baseAlts] using
          baseAltsEmpty,
      by simpa [before] using outerLength,
      by simpa [before] using outerAllEmpty⟩

/-- The literal ground `p -> q -> r` run inhabits the exact live two-frame
scheduled-answer theorem.

The same representative scheduled carrier has two older source frames, takes
exactly two silent source transitions to absorb them, and takes exactly zero
fine-machine transitions because those continuations are already flattened
in the executable alternative bank.  This composes the live nested-call
fixture with the general absorption theorem rather than placing the two facts
in separate existentials. -/
theorem ground_two_frame_live_absorption_is_inhabited
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ before : RepresentativePersistentFreeScheduledPayloadState, ∃ target : Search,
      before.carrier.index.outer.length = 2 ∧
      StepsN 2 before.carrier.sourceState []
        (.running before.carrier.index.session target) ∧
      DemandDrivenCallStep.StepsN prog gt 0 before.carrier.fineState
        before.carrier.fineState := by
  obtain
    ⟨before, beforeCallerReferencesEmpty, _beforeBaseAltsEmpty,
      beforeOuterLength, beforeOuterAllEmpty⟩ :=
    groundRootClosedScheduledCarrier (prog := prog) (gt := gt)
  obtain ⟨target, sourceSteps, fineSteps⟩ :=
    before.absorbAllEmptyFrames (prog := prog) (gt := gt)
      beforeCallerReferencesEmpty beforeOuterAllEmpty
  refine ⟨before, target, beforeOuterLength, ?_, fineSteps⟩
  simpa [beforeOuterLength] using sourceSteps

/-- The same concrete carrier inhabits the rooted closed-bank classifier.
The returned outcome is indexed by its computed full history and constrains
the literal executable bank; no independent empty suffix or compatible
history can be supplied. -/
theorem ground_two_frame_root_closed_pull_is_inhabited
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ before : RepresentativePersistentFreeScheduledPayloadState,
      ∃ ready : RootClosedAnswerReady before,
        before.carrier.index.outer.length = 2 ∧
          ∃ events,
            ClosedScheduledPullOutcome ready.result.history events ∧
              ((∃ goals binding rest,
                  events = [] ∧
                    PrologFindallAnswerResourceBridge.PullOutcomeAgrees
                      before.carrier.index.openConf.control.alts
                      (some (goals, binding)) rest) ∨
                (events = [.completed] ∧
                  PrologFindallAnswerResourceBridge.PullOutcomeAgrees
                    before.carrier.index.openConf.control.alts none [])) := by
  obtain
    ⟨before, callerEmpty, baseEmpty, outerLength, outerEmpty⟩ :=
    groundRootClosedScheduledCarrier (prog := prog) (gt := gt)
  let ready :=
    PrologRootClosedAnswerBridge.RepresentativePersistentFreeScheduledPayloadState.rootClosedAnswerReady
      before callerEmpty outerEmpty baseEmpty
  obtain ⟨events, outcome, classified⟩ :=
    PrologRootClosedAnswerBridge.RootClosedAnswerReady.classifyPull ready
  exact ⟨before, ready, outerLength, events, outcome, classified⟩

/-- The literal depth-two carrier consumes the strengthened rooted
classifier: any locally live result is coupled to its exact source answer and
fine answer/pull step, while the only other result is genuine source
fall-through.  This is deliberately a dichotomy because the p/q/r fixture has
one clause per predicate and therefore need not inhabit the local-live arm. -/
theorem ground_two_frame_root_closed_answer_couples_or_terminates
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ before : RepresentativePersistentFreeScheduledPayloadState,
      ∃ ready : RootClosedAnswerReady before,
        before.carrier.index.outer.length = 2 ∧
          ((∃ selectedGoals selectedBinding selectedTail count target,
              RootClosedLocalLiveAnswerRelates prog gt before ready
                selectedGoals selectedBinding selectedTail count target) ∨
            PrologAnswerPullClassificationBridge.OriginPrefixFallsThrough
              before.carrier.index.alpha
              ready.result.history.resourceAgreement) := by
  obtain
    ⟨before, callerEmpty, baseEmpty, outerLength, outerEmpty⟩ :=
    groundRootClosedScheduledCarrier (prog := prog) (gt := gt)
  let ready :=
    PrologRootClosedAnswerBridge.RepresentativePersistentFreeScheduledPayloadState.rootClosedAnswerReady
      before callerEmpty outerEmpty baseEmpty
  have classified :=
    PLeaTTa.PrologRootClosedLocalLiveBridge.RootClosedAnswerReady.classifyPullAndRelate
      (prog := prog) (gt := gt) ready
  exact ⟨before, ready, outerLength, classified⟩

end PLeaTTa.PrologScheduledPayloadResumeRegression
