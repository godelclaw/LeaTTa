-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.CompilerFreshness
Purpose: Prove that source-facing compiler counters begin beyond every legal
  source variable in the executable generated-variable namespace.
Trusted boundary: none
Main exports: compilerGeneratedIndex?_name,
  compilerGeneratedName_not_mem_source_vars,
  source_generated_encoding_injective_of_seed
-/
import PLeaTTa.Proofs.OpenBindingAgreement

namespace PLeaTTa.CompilerFreshness

open Metta (Atom)
open PLeaTTa.OpenBindingAgreement

/-- The decoder recognizes every name produced by the compiler's allocator. -/
theorem compilerGeneratedIndex?_name (index : Nat) :
    compilerGeneratedIndex? (compilerGeneratedName index) = some index := by
  rw [show compilerGeneratedName index = "_q" ++ Nat.repr index by rfl]
  unfold compilerGeneratedIndex?
  simp only [String.toList_append, String.reduceToList, Nat.toList_repr,
    List.cons_append, List.nil_append]
  rw [show String.ofList (Nat.toDigits 10 index) = Nat.repr index by
    apply String.ext
    simp]
  exact Nat.toNat?_repr index

/-- Every member's individual reservation is below the list high-water mark. -/
theorem compilerSeedHighWaterName_le_of_mem {name : String}
    {names : List String} (member : name ∈ names) :
    compilerSeedHighWaterName name ≤ compilerSeedHighWaterNames names := by
  induction names with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      simp only [compilerSeedHighWaterNames]
      rcases member with rfl | member
      · exact Nat.le_max_left _ _
      · exact le_trans (ih member) (Nat.le_max_right _ _)

/-- Decoded source index is strictly below the source-list high-water mark. -/
theorem compilerGeneratedIndex_lt_highWaterNames_of_mem {name : String}
    {names : List String} {index : Nat} (member : name ∈ names)
    (decoded : compilerGeneratedIndex? name = some index) :
    index < compilerSeedHighWaterNames names := by
  have bound := compilerSeedHighWaterName_le_of_mem member
  simp [compilerSeedHighWaterName, decoded] at bound
  omega

/-- No generated name at or beyond a high-water-respecting counter occurs in
the source-name list. -/
theorem compilerGeneratedName_not_mem_of_highWater_le {names : List String}
    {counter index : Nat}
    (highWater : compilerSeedHighWaterNames names ≤ counter)
    (allocated : counter ≤ index) :
    compilerGeneratedName index ∉ names := by
  intro member
  have below := compilerGeneratedIndex_lt_highWaterNames_of_mem member
    (compilerGeneratedIndex?_name index)
  omega

/-- The atom wrapper's allocation supply cannot re-enter the source atom's
generated-looking variable names. -/
theorem compilerGeneratedName_not_mem_source_vars (source : Atom)
    (base index : Nat)
    (allocated : compilerFreshCounterForAtom base source ≤ index) :
    compilerGeneratedName index ∉ source.vars := by
  apply compilerGeneratedName_not_mem_of_highWater_le
    (counter := compilerFreshCounterForAtom base source)
  · exact Nat.le_max_right _ _
  · exact allocated

/-- Rule-source counterpart for the combined pattern/body variable set. -/
theorem compilerGeneratedName_not_mem_source_atoms (sources : List Atom)
    (base index : Nat)
    (allocated : compilerFreshCounterForAtoms base sources ≤ index) :
    compilerGeneratedName index ∉ sources.flatMap Atom.vars := by
  apply compilerGeneratedName_not_mem_of_highWater_le
    (counter := compilerFreshCounterForAtoms base sources)
  · exact Nat.le_max_right _ _
  · exact allocated

/-- One source identity and an allocated generated identity have an injective
executable encoding once the source-facing seed bound is known. -/
theorem source_generated_encoding_injective_of_seed (source : Atom)
    (base index : Nat) (name : String) (member : name ∈ source.vars)
    (allocated : compilerFreshCounterForAtom base source ≤ index) :
    EncodingInjectiveOn [.source name, .generated index] := by
  apply source_generated_pair_injective name index
  intro collision
  simp only [generatedExecutableName] at collision
  have forbidden : compilerGeneratedName index ∈ source.vars := by
    rw [← collision]
    exact member
  exact compilerGeneratedName_not_mem_source_vars source base index allocated
    forbidden

/-- Positive allocator example at the first collision observed in the pinned
PettaClaw prelude. -/
example : compilerGeneratedIndex? (compilerGeneratedName 25) = some 25 :=
  compilerGeneratedIndex?_name 25

/-- Negative control: an ordinary source variable is distinct from every
generated slot. -/
example (index : Nat) :
    compilerGeneratedName index ∉ (Atom.var "ordinary").vars := by
  simp only [Atom.vars, List.mem_singleton]
  intro equality
  have decoded := compilerGeneratedIndex?_name index
  rw [equality] at decoded
  simp [compilerGeneratedIndex?] at decoded

end PLeaTTa.CompilerFreshness
