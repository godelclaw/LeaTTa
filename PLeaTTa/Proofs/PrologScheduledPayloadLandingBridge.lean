-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologScheduledPayloadLandingBridge
Purpose: Classify one rooted local scheduled pull while selecting the exact
  immutable payload occurrence by position
Trusted boundary: none
Main exports:
  ScheduledCellBankPull,
  ScheduledPayloadPullOutcome,
  ScheduledPayloadAlignment.classifyPull
-/
import PLeaTTa.Proofs.PrologRootClosedAnswerBridge

namespace PLeaTTa.PrologScheduledPayloadLandingBridge

open Metta (Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PrologAnswerPullClassificationBridge
open PrologAnswerResourceBridge
open PrologProductResourceContextBridge
open PrologRootClosedAnswerBridge
open PrologScheduledAnswerPropagationBridge
open PrologScheduledHistoryBuildBridge
open PrologScheduledPayloadPathBridge

/-!
# Type-valued local pull selection

The older generic pull classifier returns a proposition.  That is sufficient
for trace facts, but it cannot choose the Type-valued immutable snapshot
needed by a post-answer phase.  This module computes the first branch directly
from the exact local-history occurrence cells.  The source landing remains a
proof field; no source proposition is eliminated to generate data.
-/

/-- Exact eager-pull result for an ordered list of locally owned history
cells.  The selected coordinate is a `Fin` into that literal list. -/
inductive ScheduledCellBankPull
    {alpha : List (LogicVar × String)}
    (cells : List (ScheduledHistoryCell alpha)) : Type where
  | localLive
      (position : Fin cells.length)
      (goals : List PLeaTTa.Goal) (binding : Subst)
      (rest : List PLeaTTa.Alt)
      (pullExact :
        PLeaTTa.pullAux
            (flattenOwnedAlts
              (cells.map ScheduledHistoryCell.resource) []) =
          some (.branch goals binding, rest)) :
      ScheduledCellBankPull cells
  | exhausted
      (pullNone :
        PLeaTTa.pullAux
            (flattenOwnedAlts
              (cells.map ScheduledHistoryCell.resource) []) = none) :
      ScheduledCellBankPull cells

/-- A non-branch at the head of an owned local alternative bank is
impossible.  The existential branch spelling is eliminated only into
`False`; no branch payload is chosen from a proposition. -/
private theorem owned_nonbranch_head_impossible
    {alpha : List (LogicVar × String)}
    (cell : ScheduledHistoryCell alpha)
    {alt : PLeaTTa.Alt} {tail : List PLeaTTa.Alt}
    (altsExact : cell.resource.alts = alt :: tail)
    (notBranch : ∀ goals binding, alt ≠ .br goals binding) : False := by
  rcases cell.ownership.alts_all_branches alt (by rw [altsExact]; simp) with
    ⟨goals, binding, exactBranch⟩
  exact notBranch goals binding exactBranch

/-- Compute the first local branch by source-occurrence order.

Every retained bank is certified branch-only.  Non-branch executable
constructors are inspected as data and discharged through `False`; no
existential ownership witness is eliminated to choose the branch payload. -/
def classifyScheduledCellBank
    {alpha : List (LogicVar × String)} :
    (cells : List (ScheduledHistoryCell alpha)) →
      ScheduledCellBankPull cells
  | [] => .exhausted rfl
  | cell :: cells => by
      cases altsExact : cell.resource.alts with
      | nil =>
          cases classifyScheduledCellBank cells with
          | localLive position goals binding rest pullExact =>
              exact .localLive
                ⟨position.val + 1, by simpa using position.isLt⟩
                goals binding rest (by
                  simpa [flattenOwnedAlts, altsExact, PLeaTTa.pullAux] using
                    pullExact)
          | exhausted pullNone =>
              exact .exhausted (by
                simpa [flattenOwnedAlts, altsExact, PLeaTTa.pullAux] using
                  pullNone)
      | cons alt resourceTail =>
          cases alt with
          | br goals binding =>
              exact .localLive ⟨0, by simp⟩ goals binding
                (resourceTail ++
                  PLeaTTa.Alt.barrier ::
                    flattenOwnedAlts
                      (cells.map ScheduledHistoryCell.resource) [])
                (by simp [altsExact, PLeaTTa.pullAux])
          | barrier =>
              exact False.elim
                (owned_nonbranch_head_impossible cell altsExact
                  (by intros; simp))
          | catchActive frame =>
              exact False.elim
                (owned_nonbranch_head_impossible cell altsExact
                  (by intros; simp))
          | catchDormant frame protectedAlts =>
              exact False.elim
                (owned_nonbranch_head_impossible cell altsExact
                  (by intros; simp))
          | softcutActive frame seenSuccess =>
              exact False.elim
                (owned_nonbranch_head_impossible cell altsExact
                  (by intros; simp))
          | softcutDormant frame protectedAlts =>
              exact False.elim
                (owned_nonbranch_head_impossible cell altsExact
                  (by intros; simp))

/-! ## Source landing proof at the computed data -/

/-- A computed live local bank has the source landing at exactly the same
goals, binding, and residual alternative suffix.  Classification of the
Prop-valued source zipper is used only to prove this proposition; it chooses
no Type-valued payload coordinate. -/
private theorem sourceLanding_of_pull
    {alpha : List (LogicVar × String)}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    {goals : List PLeaTTa.Goal} {binding : Subst}
    {rest : List PLeaTTa.Alt}
    (pullExact :
      PLeaTTa.pullAux (flattenOwnedAlts history.resources []) =
        some (.branch goals binding, rest)) :
    OriginPrefixLanding alpha history.resourceAgreement goals binding rest := by
  rcases AnswerOriginResourceAgrees.classifyPrefix history.resourceAgreement
      with selected | falls
  · rcases selected with ⟨selectedGoals, selectedBinding, selectedRest,
      landing⟩
    have landingPull :
        PLeaTTa.pullAux (flattenOwnedAlts history.resources []) =
          some (.branch selectedGoals selectedBinding, selectedRest) := by
      simpa [ScheduledAnswerHistory.resources] using landing.pullAux_exact
    rw [pullExact] at landingPull
    cases landingPull
    exact landing
  · have none :
        PLeaTTa.pullAux (flattenOwnedAlts history.resources []) = none := by
      simpa [ScheduledAnswerHistory.resources, PLeaTTa.pullAux] using
        falls.pullAux_eq
    rw [pullExact] at none
    contradiction

/-- A computed empty local bank forces source fall-through to the literal
empty endpoint. -/
private theorem sourceFallsThrough_of_pull_none
    {alpha : List (LogicVar × String)}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    (pullNone :
      PLeaTTa.pullAux (flattenOwnedAlts history.resources []) = none) :
    OriginPrefixFallsThrough alpha history.resourceAgreement := by
  rcases AnswerOriginResourceAgrees.classifyPrefix history.resourceAgreement
      with selected | falls
  · rcases selected with ⟨goals, binding, rest, landing⟩
    have some :
        PLeaTTa.pullAux (flattenOwnedAlts history.resources []) =
          some (.branch goals binding, rest) := by
      simpa [ScheduledAnswerHistory.resources] using landing.pullAux_exact
    rw [pullNone] at some
    contradiction
  · exact falls

/-! ## Exact payload-selected outcome -/

/-- One closed local-history pull classified together with the exact
payload/history alignment.  The local constructor stores a history path; its
immutable payload path is the positional image under `alignment`. -/
inductive ScheduledPayloadPullOutcome
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat}
    {segments : List PrologControlSegmentSpineBridge.ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : PrologSourceProductContextBridge.ActiveProductContext}
    {payload :
      PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
        alpha support qterm currentBarrier segments resources inner context
        outer}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    {build : ScheduledHistoryBuild history}
    (alignment : ScheduledPayloadAlignment payload build) : Type where
  | localLive
      (path : ScheduledHistoryBuild.Path build)
      (goals : List PLeaTTa.Goal) (binding : Subst)
      (rest : List PLeaTTa.Alt)
      (landing :
        OriginPrefixLanding alpha history.resourceAgreement goals binding
          rest) :
      ScheduledPayloadPullOutcome alignment
  | terminal
      (falls : OriginPrefixFallsThrough alpha history.resourceAgreement) :
      ScheduledPayloadPullOutcome alignment

namespace ScheduledPayloadAlignment

/-- Total Type-valued classification of one exact local scheduled history. -/
def classifyPull
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat}
    {segments : List PrologControlSegmentSpineBridge.ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : PrologSourceProductContextBridge.ActiveProductContext}
    {payload :
      PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
        alpha support qterm currentBarrier segments resources inner context
        outer}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    {build : ScheduledHistoryBuild history}
    (alignment : ScheduledPayloadAlignment payload build) :
    ScheduledPayloadPullOutcome alignment := by
  cases bankPull : classifyScheduledCellBank build.cells with
  | localLive position goals binding rest pullExact =>
      let path : ScheduledHistoryBuild.Path build := ⟨position⟩
      have historyPull :
          PLeaTTa.pullAux (flattenOwnedAlts history.resources []) =
            some (.branch goals binding, rest) := by
        rw [← build.cells_map_resource]
        exact pullExact
      exact .localLive path goals binding rest
        (sourceLanding_of_pull historyPull)
  | exhausted pullNone =>
      have historyPull :
          PLeaTTa.pullAux (flattenOwnedAlts history.resources []) = none := by
        rw [← build.cells_map_resource]
        exact pullNone
      exact .terminal (sourceFallsThrough_of_pull_none historyPull)

end ScheduledPayloadAlignment

namespace ScheduledPayloadPullOutcome

/-- The exact immutable payload coordinate selected by a local-live outcome;
terminal exhaustion selects no payload cell. -/
def selectedPayloadPath?
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat}
    {segments : List PrologControlSegmentSpineBridge.ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : PrologSourceProductContextBridge.ActiveProductContext}
    {payload :
      PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
        alpha support qterm currentBarrier segments resources inner context
        outer}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    {build : ScheduledHistoryBuild history}
    {alignment : ScheduledPayloadAlignment payload build}
    (outcome : ScheduledPayloadPullOutcome alignment) :
    Option (PayloadPath payload) :=
  match outcome with
  | .localLive path _ _ _ _ => some (alignment.payloadPath path)
  | .terminal _ => none

end ScheduledPayloadPullOutcome

end PLeaTTa.PrologScheduledPayloadLandingBridge
