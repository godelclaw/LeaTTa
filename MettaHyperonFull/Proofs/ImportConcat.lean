-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.ImportConcat
Layer: Proofs
Purpose: The import theorem — "import is rule-space concatenation before
  evaluation", per query. Rules imported at runtime into `&self`
  (`world.selfExtra`, the target of the kernel's `import!` instruction) fire
  exactly as if they had been present in the static knowledge base: for any
  head-keyed query, the kernel's runtime-aware candidate firing
  (`candidatesW`) produces precisely MOPS's whole-space QUERY reduct set over
  the CONCATENATED space. Scope: per-query, `&self` imports, static import
  map; the sequencing of imports between queries is the evaluator's
  bookkeeping (`evalSequential` threads `selfExtra` in file order), exactly
  as scheduling is bookkeeping in `Correspondence.lean`.
Imports: MettaHyperonFull.Proofs.Correspondence
Trusted boundary: none (fully proved)
Main exports: extractRules_append, import_concat_query,
  import_concat_irreducible
Open obligations: dynamic-KB restatement of `definedHeadK_eq_definedHead`
  — next Track-2 chunk.
-/
import MettaHyperonFull.Proofs.Correspondence

namespace Metta
open Metta.Minimal

/-- Rule extraction distributes over concatenation. -/
theorem extractRules_append (a b : List Atom) :
    extractRules (a ++ b) = extractRules a ++ extractRules b := by
  simp [extractRules]

/-- **Import is concatenation, per query.** For a head-keyed query, the
kernel's runtime-aware candidates (static index PLUS `&self`-imported rules)
fire exactly the reducts of the published QUERY semantics over the
concatenated knowledge base. Imported rules are neither privileged nor
lost. -/
theorem import_concat_query {atoms : List Atom} {gt : GroundingTable}
    {w : World} {toEval : Atom} {k : String}
    (hk : headKey toEval = some k) (x : Atom) :
    x ∈ firedReducts (candidatesW (MinEnv.ofAtomsGT atoms gt) w toEval) toEval ↔
      x ∈ equalityReductions ⟨atoms ++ w.selfExtra⟩ toEval := by
  rw [equalityReductions_eq_firedReducts, mem_firedReducts, mem_firedReducts,
      extractRules_append]
  constructor
  · rintro ⟨p, hp, b, hb, hx⟩
    rcases List.mem_append.mp hp with hstat | hextra
    · -- a statically-indexed candidate is a genuine rule of `atoms`
      exact ⟨p, List.mem_append.mpr (Or.inl
        (candidates_sound atoms gt toEval p hstat)), b, hb, hx⟩
    · -- a runtime-imported candidate is a genuine `=`-rule of `selfExtra`
      obtain ⟨y, hy, hmatch⟩ := List.mem_filterMap.mp hextra
      have hshape : ∃ lhs rhs, y = Atom.expr [Atom.sym "=", lhs, rhs] ∧ p = (lhs, rhs) := by
        split at hmatch
        · rename_i lhs rhs
          refine ⟨lhs, rhs, rfl, ?_⟩
          split at hmatch <;> (try split at hmatch) <;> simp_all
        · simp at hmatch
      obtain ⟨lhs, rhs, rfl, rfl⟩ := hshape
      refine ⟨(lhs, rhs), List.mem_append.mpr (Or.inr ?_), b, hb, hx⟩
      exact List.mem_filterMap.mpr ⟨_, hy, by simp⟩
  · rintro ⟨⟨l, r⟩, hp, b, hb, hx⟩
    have hm : matchAtoms l toEval ≠ [] := List.ne_nil_of_mem hb
    rcases List.mem_append.mp hp with hstat | hextra
    · -- statically-present rule: offered by the first-argument index
      exact ⟨(l, r), List.mem_append.mpr (Or.inl
        (candidates_complete atoms gt toEval k l r hk hstat hm)), b, hb, hx⟩
    · -- imported rule: it fires, so its head agrees or is head-less
      -- (`matchAtoms_headKey`), hence it passes `candidatesW`'s filter.
      obtain ⟨y, hy, hmatch⟩ := List.mem_filterMap.mp hextra
      have hshape : y = Atom.expr [Atom.sym "=", l, r] := by
        split at hmatch <;> simp_all
      subst hshape
      refine ⟨(l, r), List.mem_append.mpr (Or.inr ?_), b, hb, hx⟩
      refine List.mem_filterMap.mpr ⟨Atom.expr [Atom.sym "=", l, r], hy, ?_⟩
      show (match headKey l, headKey toEval with
        | some k1, some k2 => if k1 == k2 then some (l, r) else none
        | none, _ => some (l, r)
        | _, _ => none) = some (l, r)
      rcases matchAtoms_headKey hk hm with hl | hl <;> rw [hl, hk] <;> simp

/-- **Irreducibility over imports agrees too**: the runtime-aware kernel
finds no reduct iff the concatenated space is insensitive. With
`import_concat_query` this is the full QUERY/OUTPUT dichotomy for imported
knowledge bases. -/
theorem import_concat_irreducible {atoms : List Atom} {gt : GroundingTable}
    {w : World} {toEval : Atom} {k : String} (hk : headKey toEval = some k) :
    firedReducts (candidatesW (MinEnv.ofAtomsGT atoms gt) w toEval) toEval = [] ↔
      equalityReductions ⟨atoms ++ w.selfExtra⟩ toEval = [] := by
  rw [List.eq_nil_iff_forall_not_mem, List.eq_nil_iff_forall_not_mem]
  exact forall_congr' fun x => not_congr (import_concat_query hk x)

end Metta
