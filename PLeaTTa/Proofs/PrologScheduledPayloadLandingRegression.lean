-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologScheduledPayloadLandingRegression
Purpose: Inhabit exact payload-indexed local landing with a real retained
  sibling selected by the executable resolver
Trusted boundary: none
-/
import PLeaTTa.Proofs.PrologRootClosedLocalLiveRegression
import PLeaTTa.Proofs.PrologScheduledPayloadLandingBridge

namespace PLeaTTa.PrologScheduledPayloadLandingRegression

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PrologAnswerPullClassificationBridge
open PrologHeterogeneousPrefixBridge
open PrologProductResourceContextBridge
open PrologRootClosedAnswerBridge
open PrologScheduledAnswerPropagationBridge
open PrologScheduledHistoryBuildBridge
open PrologScheduledPayloadLandingBridge
open PrologScheduledPayloadPathBridge
open PrologStateBridge

/-!
# A live exact-position witness

The generic landing theorem is total, so a terminal-only implementation
could otherwise inhabit it.  This fixture starts from the actual
source-ordered resolver run with one retained sibling.  Consequently the
classifier must select a local branch and return a path into the literal
history build; the same ordinal recovers the immutable payload snapshot.
-/

/-- The rejected-prefix fixture forces the Type-valued classifier's live arm.
The selected source landing, executable pull, history occurrence, and
immutable payload occurrence are all tied to one result rather than supplied
as independent compatible witnesses.

[SPEC metta.pl:251-256, translator.pl:320-321] -/
theorem rejected_prefix_root_pull_selects_exact_payload_occurrence
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
  exists before : RepresentativeScheduledPayloadState,
      exists ready : RootClosedAnswerReady before,
        exists selection :
            ScheduledLocalSelection ready.result.historyBuild.cells,
          exists landing :
                OriginPrefixLanding before.carrier.index.alpha
                  ready.result.history.resourceAgreement selection.goals
                    selection.binding selection.rest,
              PLeaTTa.PrologScheduledPayloadLandingBridge.ScheduledPayloadAlignment.classifyPull
                  ready.payloadAlignment =
                  ScheduledPayloadPullOutcome.localLive selection landing /\
                ScheduledPayloadPullOutcome.selectedPayloadPath?
                    (PLeaTTa.PrologScheduledPayloadLandingBridge.ScheduledPayloadAlignment.classifyPull
                      ready.payloadAlignment) =
                  some
                    (ready.payloadAlignment.payloadPath selection.path) /\
                (ready.payloadAlignment.payloadPath
                    selection.path).cell.historyCell =
                  selection.path.cell /\
                PLeaTTa.pullAux
                    before.carrier.index.openConf.control.alts =
                  some
                    (.branch selection.goals selection.binding,
                      selection.rest) := by
  obtain
    ⟨before, ready, retainedGoals, retainedBinding, _selectedGoals,
      _selectedBinding, _selectedTail, _count, _target, _relation, bankShape,
      _selectedGoalsExact, _selectedBindingExact, _selectedTailExact,
      _framesEmpty, _qtermExact⟩ :=
    PrologRootClosedLocalLiveRegression.rejected_prefix_then_root_answer_is_genuinely_local_live
      (prog := prog) (gt := gt)
  generalize outcomeExact :
    PLeaTTa.PrologScheduledPayloadLandingBridge.ScheduledPayloadAlignment.classifyPull
      ready.payloadAlignment = outcome
  cases outcome with
  | localLive selection landing =>
      refine ⟨before, ready, selection, landing,
        outcomeExact, ?_,
        ready.payloadAlignment.selected_history_cell_exact selection.path,
        ?_⟩
      · rw [outcomeExact]
        rfl
      · rw [ready.bankExact]
        exact landing.pullAux_exact
  | terminal falls =>
      have pullNone :
          PLeaTTa.pullAux before.carrier.index.openConf.control.alts = none := by
        rw [ready.bankExact]
        simpa [ScheduledAnswerHistory.resources, PLeaTTa.pullAux] using
          falls.pullAux_eq
      rw [bankShape] at pullNone
      simp [PLeaTTa.pullAux] at pullNone

end PLeaTTa.PrologScheduledPayloadLandingRegression
