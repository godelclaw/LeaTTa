-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologAlphaFreshFrontierBridge
Purpose: Relate independent and executable fresh-name frontiers through the
  finite runtime alpha graph.
Trusted boundary: none
Main exports:
  AlphaFreshFrontier,
  AlphaFreshFrontier.append,
  clauseAlpha_freshFrontier
-/
import PLeaTTa.Proofs.PrologStateBridge
import PLeaTTa.Proofs.ResolutionCounter

namespace PLeaTTa.PrologAlphaFreshFrontierBridge

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Resolver
open OpenBindingAgreement
open PrologStateBridge

/-- The two allocators use different currencies.  Their honest relation is
not numeric equality: every independent generated identity in the finite
alpha graph lies below the independent frontier, and every executable name
in that graph lies below the executable resolution counter. -/
def AlphaFreshFrontier
    (alpha : List (LogicVar × String)) : FreshFrontierRelation :=
  fun referenceFrontier executableFrontier =>
    GeneratedBelow referenceFrontier (alpha.map Prod.fst) ∧
      resolutionSeedHighWaterNames (alpha.map Prod.snd) ≤
        executableFrontier

/-- The empty graph is related at every pair of frontiers. -/
theorem AlphaFreshFrontier.empty
    (referenceFrontier executableFrontier : Nat) :
    AlphaFreshFrontier [] referenceFrontier executableFrontier := by
  simp [AlphaFreshFrontier, GeneratedBelow, resolutionSeedHighWaterNames]

/-- Restricting a finite alpha graph cannot increase either required
frontier. -/
theorem AlphaFreshFrontier.of_subset
    {smaller larger : List (LogicVar × String)}
    {referenceFrontier executableFrontier : Nat}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    (agreement :
      AlphaFreshFrontier larger referenceFrontier executableFrontier) :
    AlphaFreshFrontier smaller referenceFrontier executableFrontier := by
  constructor
  · intro index member
    obtain ⟨pair, pairMember, pairFirst⟩ := List.mem_map.mp member
    apply agreement.1 index
    exact List.mem_map.mpr
      ⟨pair, included pair pairMember, pairFirst⟩
  · exact Nat.le_trans
      (resolutionSeedHighWaterNames_le_of_subset (fun name member => by
        obtain ⟨pair, pairMember, pairSecond⟩ := List.mem_map.mp member
        exact List.mem_map.mpr
          ⟨pair, included pair pairMember, pairSecond⟩))
      agreement.2

/-- Advancing either allocator preserves an already established finite
alpha frontier. -/
theorem AlphaFreshFrontier.mono
    {alpha : List (LogicVar × String)}
    {referenceBefore executableBefore referenceAfter executableAfter : Nat}
    (agreement :
      AlphaFreshFrontier alpha referenceBefore executableBefore)
    (referenceMono : referenceBefore ≤ referenceAfter)
    (executableMono : executableBefore ≤ executableAfter) :
    AlphaFreshFrontier alpha referenceAfter executableAfter :=
  ⟨agreement.1.mono referenceMono,
    Nat.le_trans agreement.2 executableMono⟩

/-- Concatenating two alpha fragments combines their independent and
executable bounds without identifying the allocator currencies. -/
theorem AlphaFreshFrontier.append
    {left right : List (LogicVar × String)}
    {referenceFrontier executableFrontier : Nat}
    (leftAgreement :
      AlphaFreshFrontier left referenceFrontier executableFrontier)
    (rightAgreement :
      AlphaFreshFrontier right referenceFrontier executableFrontier) :
    AlphaFreshFrontier (left ++ right)
      referenceFrontier executableFrontier := by
  constructor
  · intro index member
    rw [List.map_append, List.mem_append] at member
    rcases member with leftMember | rightMember
    · exact leftAgreement.1 index leftMember
    · exact rightAgreement.1 index rightMember
  · rw [List.map_append, resolutionSeedHighWaterNames_append]
    exact Nat.max_le.mpr ⟨leftAgreement.2, rightAgreement.2⟩

/-- Consecutive independent targets lie below the end of their advertised
half-open interval. -/
theorem referenceFreshTargets_generatedBelow
    (seed : Nat) (support : List LogicVar) :
    GeneratedBelow (seed + support.length)
      (referenceFreshTargets seed support) := by
  induction support generalizing seed with
  | nil =>
      simp [GeneratedBelow, referenceFreshTargets]
  | cons head tail inductionHypothesis =>
      intro index member
      simp only [referenceFreshTargets, List.mem_cons] at member
      rcases member with same | later
      · injection same with indexEq
        subst index
        simp
      · have below := inductionHypothesis (seed + 1) index later
        simp only [List.length_cons] at below ⊢
        omega

/-- Every executable target built with the compact suffix for `seed` lies
below the next executable counter value. -/
theorem executableFreshTargets_compact_below
    (seed : Nat) (support : List LogicVar) :
    resolutionSeedHighWaterNames
        (executableFreshTargets (resolutionCompactSuffix seed) support) ≤
      seed + 1 := by
  rw [PersistentSubst.resolutionSeedHighWaterNames_le_iff]
  intro name member
  simp only [executableFreshTargets, List.mem_map] at member
  obtain ⟨source, _sourceMember, rfl⟩ := member
  exact resolutionSeedHighWaterName_append_compact
    (logicVarExecutableName source) seed ▸ Nat.le_refl (seed + 1)

/-- The positional alpha graph for one clause copy is bounded by the exact
endpoints of the independent per-variable interval and executable
per-clause suffix allocation. -/
theorem clauseAlpha_freshFrontier
    (referenceSeed executableSeed : Nat) (support : List LogicVar) :
    AlphaFreshFrontier
      (RuntimeAlpha.graph
        (referenceFreshTargets referenceSeed support)
        (executableFreshTargets
          (resolutionCompactSuffix executableSeed) support))
      (referenceSeed + support.length) (executableSeed + 1) := by
  have cardinality :
      (referenceFreshTargets referenceSeed support).length =
        (executableFreshTargets
          (resolutionCompactSuffix executableSeed) support).length := by
    rw [referenceFreshTargets_length]
    simp [executableFreshTargets]
  constructor
  · rw [RuntimeAlpha.graph,
      List.map_fst_zip (Nat.le_of_eq cardinality)]
    exact referenceFreshTargets_generatedBelow referenceSeed support
  · rw [RuntimeAlpha.graph,
      List.map_snd_zip (Nat.le_of_eq cardinality.symm)]
    exact executableFreshTargets_compact_below executableSeed support

/-! ## Anti-vacuity: each allocator bound carries independent content -/

/-- A reference frontier equal to a live generated index is too low. -/
theorem reference_frontier_cannot_equal_live_index :
    ¬ AlphaFreshFrontier
      [(.generated 2, "plain")] 2 0 := by
  intro agreement
  exact (Nat.lt_irrefl 2) (agreement.1 2 (by simp))

/-- The executable frontier must advance past the compact suffix token; a
source-only alpha entry cannot hide that obligation. -/
theorem executable_frontier_cannot_precede_compact_target :
    ¬ AlphaFreshFrontier
      [(.source "x", logicVarExecutableName (.source "x") ++
        resolutionCompactSuffix 4)] 0 4 := by
  intro agreement
  have bounded :=
    (PersistentSubst.resolutionSeedHighWaterNames_le_iff _ _).mp
      agreement.2
      (logicVarExecutableName (.source "x") ++ resolutionCompactSuffix 4)
      (by simp)
  rw [resolutionSeedHighWaterName_append_compact] at bounded
  omega

end PLeaTTa.PrologAlphaFreshFrontierBridge
