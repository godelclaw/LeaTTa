-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologAltBankCharacterization
Purpose: Characterize ordinary and cached executable pulls over the exact
  retained-resource alternative-bank layout under the branch-only payload
  invariant. Regions containing control alternatives are outside this scope.
Trusted boundary: none
Main exports:
  BranchOnlyResources,
  BranchOnlyResources.ofPayload,
  source_occurrence_can_emit_zero_alternatives,
  pullAux_flattenOwnedAlts_shape,
  pullAuxTracked_flattenOwnedAlts_all_empty,
  pullAuxTracked_flattenOwnedAlts_local
-/
import PLeaTTa.Proofs.PrologRetainedPayloadSnapshotBridge

namespace PLeaTTa.PrologAltBankCharacterization

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologActivationMacro
open PrologBodyFailureResourceTransitionBridge
open PrologProductResourceContextBridge
open PrologRetainedPayloadSnapshotBridge

/-- Every region owned by a local resolver contains ordinary branches only.
This is the precise structural premise needed to scan by retained segment
rather than by the erased flat list. -/
def BranchOnlyResources
    (resources : List RetainedAlternativeSegment) : Prop :=
  ∀ resource ∈ resources, ∀ alternative ∈ resource.alts,
    ∃ goals binding, alternative = PLeaTTa.Alt.br goals binding

/-- The typed source/resource payload zipper supplies the branch-only premise
for each of its exact retained regions. -/
theorem BranchOnlyResources.ofPayload
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List PrologControlSegmentSpineBridge.ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : PrologSourceProductContextBridge.ActiveProductContext}
    (payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer) :
    BranchOnlyResources resources := by
  induction payload with
  | nil => simp [BranchOnlyResources]
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerPayload
      inductionHypothesis =>
      intro candidate member alternative alternativeMember
      simp only [List.mem_cons] at member
      rcases member with head | tail
      · subst candidate
        exact
          RetainedAlternativeSegment.HasIndexedOwnershipAt.alts_all_branches
            resourceOwnership alternative alternativeMember
      · exact inductionHypothesis candidate tail alternative alternativeMember

/-- A source clause occurrence need not emit an executable alternative.
The prefilter can reject even a same-arity, structurally incompatible source
clause before it reaches the alternative bank, so source occurrences and
runtime alternatives are not in one-to-one correspondence. -/
private def prefilterRejectedClause : PLeaTTa.Clause :=
  { params := [.sym "different"]
    result := .sym "result"
    body := [] }

theorem source_occurrence_can_emit_zero_alternatives :
    (scanResolution [.sym "input"] [.sym "input"] (.sym "result") [] []
      (.sym "query") 0 [prefilterRejectedClause] 0).1 = [] ∧
      (scanResolution [.sym "input"] [.sym "input"] (.sym "result") [] []
        (.sym "query") 0 [prefilterRejectedClause] 0).2 = 0 ∧
      [prefilterRejectedClause] ≠ [] := by
  exact ⟨rfl, rfl, by simp⟩

/-- Pulling a flattened branch-only bank either crosses a concrete prefix of
empty retained regions and consumes the literal head of the next region, or
proves every retained region empty and falls through to the exact older base.

The local residual retains the selected source region and every later region;
it cannot be hidden in a freshly chosen existential base. Consumers that need
the exact number of crossed regions should use the explicit-prefix cached
theorem below rather than erase `earlier` through this disjunction. -/
theorem pullAux_flattenOwnedAlts_shape
    (resources : List RetainedAlternativeSegment)
    (base : List PLeaTTa.Alt)
    (branchOnly : BranchOnlyResources resources) :
    (∃ earlier selected later goals binding localTail,
        resources = earlier ++ selected :: later ∧
          (∀ resource ∈ earlier, resource.alts = []) ∧
          selected.alts = PLeaTTa.Alt.br goals binding :: localTail ∧
          PLeaTTa.pullAux (flattenOwnedAlts resources base) =
            some
              (.branch goals binding,
                flattenOwnedAlts
                  (afterPulledHead selected localTail :: later) base)) ∨
      ((∀ resource ∈ resources, resource.alts = []) ∧
        PLeaTTa.pullAux (flattenOwnedAlts resources base) =
          PLeaTTa.pullAux base) := by
  induction resources with
  | nil =>
      exact .inr ⟨by simp, rfl⟩
  | cons head tail inductionHypothesis =>
      have headBranches :
          ∀ alternative ∈ head.alts,
            ∃ goals binding, alternative = PLeaTTa.Alt.br goals binding := by
        intro alternative member
        exact branchOnly head (by simp) alternative member
      have tailBranches : BranchOnlyResources tail := by
        intro resource member alternative alternativeMember
        exact branchOnly resource (by simp [member]) alternative alternativeMember
      cases headAlts : head.alts with
      | nil =>
          rcases inductionHypothesis tailBranches with landed | exhausted
          · left
            rcases landed with
              ⟨earlier, selected, later, goals, binding, localTail,
                resourcesExact, earlierEmpty, selectedHead, pullExact⟩
            refine
              ⟨head :: earlier, selected, later, goals, binding, localTail,
                ?_, ?_, selectedHead, ?_⟩
            · simp [resourcesExact]
            · intro resource member
              simp only [List.mem_cons] at member
              rcases member with headExact | member
              · simpa [headExact] using headAlts
              · exact earlierEmpty resource member
            · simpa [flattenOwnedAlts, headAlts, PLeaTTa.pullAux] using pullExact
          · right
            refine ⟨?_, ?_⟩
            · intro resource member
              simp only [List.mem_cons] at member
              rcases member with headExact | member
              · simpa [headExact] using headAlts
              · exact exhausted.1 resource member
            · simpa [flattenOwnedAlts, headAlts, PLeaTTa.pullAux] using
                exhausted.2
      | cons alternative localTail =>
          rcases headBranches alternative (by simp [headAlts]) with
            ⟨goals, binding, alternativeExact⟩
          subst alternative
          left
          refine
            ⟨[], head, tail, goals, binding, localTail, rfl, by simp, headAlts,
              ?_⟩
          simp [flattenOwnedAlts, headAlts, PLeaTTa.pullAux, afterPulledHead]

/-- Pop one cached predicate marker for each crossed retained region. This is
the runtime arithmetic for an arbitrary cache value, not a cache-coherence
certificate; coherence remains a separate premise about the incoming state. -/
def popBarrierCacheN : Option Nat → Nat → Option Nat
  | cache, 0 => cache
  | none, _count + 1 => none
  | some depth, count + 1 => popBarrierCacheN (some (depth - 1)) count

@[simp] theorem popBarrierCacheN_none (count : Nat) :
    popBarrierCacheN none count = none := by
  cases count <;> rfl

/-- Cached pulling through a structurally empty retained prefix reaches the
same older base after exactly one cache pop per crossed region. -/
theorem pullAuxTracked_flattenOwnedAlts_all_empty
    (resources : List RetainedAlternativeSegment)
    (base : List PLeaTTa.Alt)
    (allEmpty : ∀ resource ∈ resources, resource.alts = [])
    (cache : Option Nat) :
    PLeaTTa.pullAuxTracked cache (flattenOwnedAlts resources base) =
      PLeaTTa.pullAuxTracked (popBarrierCacheN cache resources.length) base := by
  induction resources generalizing cache with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      have headEmpty : head.alts = [] := allEmpty head (by simp)
      have tailEmpty : ∀ resource ∈ tail, resource.alts = [] := by
        intro resource member
        exact allEmpty resource (by simp [member])
      cases cache with
      | none =>
          have first :=
            congrArg Prod.fst (inductionHypothesis tailEmpty none)
          simpa [flattenOwnedAlts, headEmpty, PLeaTTa.pullAuxTracked,
            PLeaTTa.pullAux, popBarrierCacheN] using first
      | some depth =>
          simpa [flattenOwnedAlts, headEmpty, PLeaTTa.pullAuxTracked,
            PLeaTTa.pullAuxCached, popBarrierCacheN] using
              inductionHypothesis tailEmpty (some (depth - 1))

/-- Cached local selection is closed at the same retained-region split as the
uncached theorem. The selected region remains explicit, and the returned
cache is determined by the number of earlier empty regions. -/
theorem pullAuxTracked_flattenOwnedAlts_local
    (earlier : List RetainedAlternativeSegment)
    (selected : RetainedAlternativeSegment)
    (later : List RetainedAlternativeSegment)
    (base : List PLeaTTa.Alt)
    (goals : List PLeaTTa.Goal) (binding : Subst)
    (localTail : List PLeaTTa.Alt)
    (earlierEmpty : ∀ resource ∈ earlier, resource.alts = [])
    (selectedHead :
      selected.alts = PLeaTTa.Alt.br goals binding :: localTail)
    (cache : Option Nat) :
    PLeaTTa.pullAuxTracked cache
        (flattenOwnedAlts (earlier ++ selected :: later) base) =
      (some
          (.branch goals binding,
            flattenOwnedAlts
              (afterPulledHead selected localTail :: later) base),
        popBarrierCacheN cache earlier.length) := by
  induction earlier generalizing cache with
  | nil =>
      cases cache <;>
        simp [flattenOwnedAlts, selectedHead, PLeaTTa.pullAuxTracked,
          PLeaTTa.pullAux, PLeaTTa.pullAuxCached, afterPulledHead,
          popBarrierCacheN]
  | cons head tail inductionHypothesis =>
      have headEmpty : head.alts = [] := earlierEmpty head (by simp)
      have tailEmpty : ∀ resource ∈ tail, resource.alts = [] := by
        intro resource member
        exact earlierEmpty resource (by simp [member])
      cases cache with
      | none =>
          have first :=
            congrArg Prod.fst (inductionHypothesis tailEmpty none)
          simpa [flattenOwnedAlts, headEmpty, PLeaTTa.pullAuxTracked,
            PLeaTTa.pullAux, popBarrierCacheN] using first
      | some depth =>
          simpa [flattenOwnedAlts, headEmpty, PLeaTTa.pullAuxTracked,
            PLeaTTa.pullAuxCached, popBarrierCacheN] using
              inductionHypothesis tailEmpty (some (depth - 1))

end PLeaTTa.PrologAltBankCharacterization
