-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologScheduledPayloadResumeRegression
Purpose: Inhabit exact multi-frame scheduled-answer absorption with one live
  source-ordered p -> q -> r local-resolution carrier.
Trusted boundary: none
-/
import PLeaTTa.Proofs.PrologNestedCallReadyRegression
import PLeaTTa.Proofs.PrologScheduledPayloadResumeBridge

namespace PLeaTTa.PrologScheduledPayloadResumeRegression

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open DemandDrivenStep
open PrologHeterogeneousPrefixBridge
open PrologNestedCallChainBridge
open PrologNestedCallReadyBridge
open PrologScheduledPayloadResumeBridge

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
    ∃ before : RepresentativeScheduledPayloadState, ∃ target : Search,
      before.carrier.index.outer.length = 2 ∧
      StepsN 2 before.carrier.sourceState []
        (.running before.carrier.index.session target) ∧
      DemandDrivenCallStep.StepsN prog gt 0 before.carrier.fineState
        before.carrier.fineState := by
  obtain
    ⟨_root, _qHead, _middle, _qReady, _qPredicate, _qPayload,
      _rootReferences, _rootExecutables, _rootSourceSteps, _rootFineSteps,
      _qCertificate, _rHead, after, _rReady, _rPredicate, _rPayload,
      _rCertificate, bodyReferencesEmpty, bodyExecutablesEmpty,
      callerReferencesEmpty, outerLength, outerAllEmpty⟩ :=
    PrologNestedCallReadyRegression.ground_p_q_r_two_nested_pushes
      (prog := prog) (gt := gt)
  obtain ⟨representative, carrierExact⟩ := after.existsRepresentative
  subst after
  let before :=
    RepresentativeActivePayloadState.afterBodyAnswer prog gt representative
      bodyReferencesEmpty bodyExecutablesEmpty
  have beforeCallerReferencesEmpty :
      before.carrier.index.callerReferences = [] := by
    simpa [before] using callerReferencesEmpty
  have beforeOuterLength : before.carrier.index.outer.length = 2 := by
    simpa [before] using outerLength
  have beforeOuterAllEmpty :
      ∀ segment ∈ before.carrier.index.outer, segment.references = [] := by
    simpa [before] using outerAllEmpty
  obtain ⟨target, sourceSteps, fineSteps⟩ :=
    before.absorbAllEmptyFrames (prog := prog) (gt := gt)
      beforeCallerReferencesEmpty beforeOuterAllEmpty
  refine ⟨before, target, beforeOuterLength, ?_, fineSteps⟩
  simpa [beforeOuterLength] using sourceSteps

end PLeaTTa.PrologScheduledPayloadResumeRegression
