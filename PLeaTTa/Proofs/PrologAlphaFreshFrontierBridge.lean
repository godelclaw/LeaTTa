-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologAlphaFreshFrontierBridge
Purpose: Relate independent and executable fresh-name frontiers through the
  finite runtime alpha graph.
Trusted boundary: none
Main exports:
  AlphaFreshFrontier,
  AlphaFreshFrontier.append,
  AlphaAllocationGap,
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

/-- A shared alpha graph avoids two allocator regions which belong to a
retained resource.

Independent generated identities use half-open intervals
`[referenceStart, referenceEnd)`.  Executable clause-copy seed `n` is
observed through names whose terminal-token high-water is `n + 1`, so its
protected interval is `(executableStart, executableEnd]`.  Entries below an
interval are historical; entries above it were allocated after the complete
retained reservation. -/
def AlphaAllocationGap
    (alpha : List (LogicVar × String))
    (referenceStart referenceEnd executableStart executableEnd : Nat) :
    Prop :=
  (∀ index, .generated index ∈ alpha.map Prod.fst →
      index < referenceStart ∨ referenceEnd ≤ index) ∧
    ∀ name, name ∈ alpha.map Prod.snd →
      resolutionSeedHighWaterName name ≤ executableStart ∨
        executableEnd < resolutionSeedHighWaterName name

/-- Exact chronological extension of a runtime alpha graph.

`larger` consists of the old graph followed by one freshly allocated suffix.
Every independent generated identity in that suffix is at or above the
source floor, while every executable name is strictly above the executable
floor.  Keeping the exact suffix equation prevents a proof from laundering
an unrelated graph through mere old-entry inclusion. -/
def AlphaExtendsAbove
    (smaller larger : List (LogicVar × String))
    (referenceFloor executableFloor : Nat) : Prop :=
  ∃ suffix : List (LogicVar × String),
    larger = smaller ++ suffix ∧
      (∀ index, .generated index ∈ suffix.map Prod.fst →
        referenceFloor ≤ index) ∧
      ∀ name, name ∈ suffix.map Prod.snd →
        executableFloor < resolutionSeedHighWaterName name

namespace AlphaExtendsAbove

/-- An exact chronological extension contains every old alpha pair. -/
theorem included
    {smaller larger : List (LogicVar × String)}
    {referenceFloor executableFloor : Nat}
    (extension :
      AlphaExtendsAbove smaller larger referenceFloor executableFloor) :
    ∀ pair, pair ∈ smaller → pair ∈ larger := by
  rcases extension with ⟨suffix, largerEq, _referenceAbove,
    _executableAbove⟩
  intro pair member
  rw [largerEq]
  exact List.mem_append_left suffix member

end AlphaExtendsAbove

namespace AlphaAllocationGap

/-- A graph entirely below the two lower bounds avoids every protected
interval beginning there. -/
theorem of_frontier
    {alpha : List (LogicVar × String)}
    {referenceStart referenceEnd executableStart executableEnd : Nat}
    (frontier :
      AlphaFreshFrontier alpha referenceStart executableStart) :
    AlphaAllocationGap alpha referenceStart referenceEnd executableStart
      executableEnd := by
  constructor
  · intro index member
    exact Or.inl (frontier.1 index member)
  · intro name member
    exact Or.inl
      ((PersistentSubst.resolutionSeedHighWaterNames_le_iff
        (alpha.map Prod.snd) executableStart).mp frontier.2 name member)

/-- Moving either lower bound forward preserves a gap when the protected
upper bounds stay fixed.  This is the allocator fact used after consuming a
retained alternative. -/
theorem advance
    {alpha : List (LogicVar × String)}
    {referenceStart referenceNext referenceEnd
      executableStart executableNext executableEnd : Nat}
    (gap :
      AlphaAllocationGap alpha referenceStart referenceEnd executableStart
        executableEnd)
    (referenceMono : referenceStart ≤ referenceNext)
    (executableMono : executableStart ≤ executableNext) :
    AlphaAllocationGap alpha referenceNext referenceEnd executableNext
      executableEnd := by
  constructor
  · intro index member
    rcases gap.1 index member with below | above
    · exact Or.inl (Nat.lt_of_lt_of_le below referenceMono)
    · exact Or.inr above
  · intro name member
    rcases gap.2 name member with below | above
    · exact Or.inl (Nat.le_trans below executableMono)
    · exact Or.inr above

/-- Concatenating two fragments which avoid the same regions preserves the
gap. -/
theorem append
    {left right : List (LogicVar × String)}
    {referenceStart referenceEnd executableStart executableEnd : Nat}
    (leftGap :
      AlphaAllocationGap left referenceStart referenceEnd executableStart
        executableEnd)
    (rightGap :
      AlphaAllocationGap right referenceStart referenceEnd executableStart
        executableEnd) :
    AlphaAllocationGap (left ++ right) referenceStart referenceEnd
      executableStart executableEnd := by
  constructor
  · intro index member
    rw [List.map_append, List.mem_append] at member
    rcases member with member | member
    · exact leftGap.1 index member
    · exact rightGap.1 index member
  · intro name member
    rw [List.map_append, List.mem_append] at member
    rcases member with member | member
    · exact leftGap.2 name member
    · exact rightGap.2 name member

/-- Extending the alpha graph strictly after both protected upper bounds
preserves the retained allocation gap.

This is the recursive-call chronology rule: the old graph already avoids the
retained source/runtime regions, and every newly appended pair is allocated
after those regions in both independent allocator currencies. -/
theorem extendAbove
    {smaller larger : List (LogicVar × String)}
    {referenceStart referenceEnd executableStart executableEnd
      referenceFloor executableFloor : Nat}
    (gap :
      AlphaAllocationGap smaller referenceStart referenceEnd executableStart
        executableEnd)
    (extension :
      AlphaExtendsAbove smaller larger referenceFloor executableFloor)
    (referenceDominated : referenceEnd ≤ referenceFloor)
    (executableDominated : executableEnd ≤ executableFloor) :
    AlphaAllocationGap larger referenceStart referenceEnd executableStart
      executableEnd := by
  rcases extension with
    ⟨suffix, largerEq, referenceAbove, executableAbove⟩
  rw [largerEq]
  apply gap.append
  constructor
  · intro index member
    exact Or.inr
      (Nat.le_trans referenceDominated
        (referenceAbove index member))
  · intro name member
    exact Or.inr
      (Nat.lt_of_le_of_lt executableDominated
        (executableAbove name member))

end AlphaAllocationGap

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

/-- An alpha entry allocated above both retained regions is admitted.  This
is the positive chronology witness: later nested work need not remain below
an older call merely to preserve its reservation. -/
theorem allocation_above_both_regions_preserves_gap :
    AlphaAllocationGap
      [(.generated 4, "x" ++ resolutionCompactSuffix 4)]
      2 4 2 4 := by
  constructor
  · intro index member
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at member
    injection member with indexEq
    subst index
    exact Or.inr (Nat.le_refl 4)
  · intro name member
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at member
    subst name
    rw [resolutionSeedHighWaterName_append_compact]
    exact Or.inr (Nat.lt_succ_self 4)

/-- Inserting a generated identity at the protected source interval's lower
endpoint violates the gap. -/
theorem allocation_inside_reference_region_breaks_gap :
    ¬ AlphaAllocationGap [(.generated 2, "plain")] 2 3 0 0 := by
  intro gap
  rcases gap.1 2 (by simp) with below | above <;> omega

/-- Executable seed `2` has observable high-water `3`; inserting it into the
protected runtime interval `(2,3]` violates the gap.  This pins the asymmetric
endpoint convention used by compact suffixes. -/
theorem allocation_inside_executable_region_breaks_gap :
    ¬ AlphaAllocationGap
      [(.source "x", "x" ++ resolutionCompactSuffix 2)]
      0 0 2 3 := by
  intro gap
  have collision :=
    gap.2 ("x" ++ resolutionCompactSuffix 2) (by simp)
  rw [resolutionSeedHighWaterName_append_compact] at collision
  omega

/-- A consumed resource's advanced executable lower bound cannot recover the
strict pre-pull allocation gap.

The same compact seed-`2` name is below the consumed floor `3`, but lies
inside the original protected interval `(2,3]`.  This is why retained-head
reactivation must preserve the old gap as chronology rather than infer it from
the consumed snapshot. -/
theorem consumed_gap_does_not_recover_prePull_gap :
    AlphaAllocationGap
        [(.source "x", "x" ++ resolutionCompactSuffix 2)]
        0 0 3 3 ∧
      ¬ AlphaAllocationGap
        [(.source "x", "x" ++ resolutionCompactSuffix 2)]
        0 0 2 3 := by
  constructor
  · constructor
    · intro index member
      simp at member
    · intro name member
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at member
      subst name
      rw [resolutionSeedHighWaterName_append_compact]
      exact Or.inl (Nat.le_refl 3)
  · exact allocation_inside_executable_region_breaks_gap

end PLeaTTa.PrologAlphaFreshFrontierBridge
