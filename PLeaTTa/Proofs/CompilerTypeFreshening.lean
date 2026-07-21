-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.CompilerTypeFreshening
Purpose: Verify the executable fresh-variant algorithm used for variables in
  declared PeTTa arrow chains.
Trusted boundary: none
Main exports: freshenTypeChain_counter_eq,
  compilerTypeFresheningSubst_domain,
  freshenTypeChain_names_generated,
  freshenTypeChain_ranges_disjoint
-/
import PLeaTTa.Compile
import PLeaTTa.Proofs.CompilerFreshness
import MettaHyperonFull.Proofs.Basic
import MettaHyperonFull.Proofs.Substitution

namespace PLeaTTa.CompilerTypeFreshening

open Metta (Atom)

@[simp] theorem compilerTypeFresheningSubst_length
    (counter : Nat) (chain : List Atom) :
    (compilerTypeFresheningSubst counter chain).length =
      (compilerTypeVarNames chain).length := by
  simp [compilerTypeFresheningSubst]

@[simp] theorem freshenTypeChain_counter_eq
    (counter : Nat) (chain : List Atom) :
    (freshenTypeChain counter chain).2 =
      counter + (compilerTypeVarNames chain).length := by
  rfl

theorem freshenTypeChain_counter_le (counter : Nat) (chain : List Atom) :
    counter ≤ (freshenTypeChain counter chain).2 := by
  simp [freshenTypeChain]

theorem compilerTypeVarNames_mem_iff {chain : List Atom} {name : String} :
    name ∈ compilerTypeVarNames chain ↔
      name ∈ chain.flatMap Atom.vars := by
  exact List.mem_eraseDups

/-- The substitution domain is exactly the chain's distinct source-variable
list, in first-occurrence order. -/
theorem compilerTypeFresheningSubst_domain
    (counter : Nat) (chain : List Atom) :
    (compilerTypeFresheningSubst counter chain).map Prod.fst =
      compilerTypeVarNames chain := by
  simp [compilerTypeFresheningSubst, List.mapIdx_eq_zipIdx_map,
    Function.comp_def]

/-- Looking up a key in the indexed generated-variable table returns the
entry at that key's first list occurrence.  This is the reusable bridge from
the independent `idxOf` specification to the executable association list. -/
theorem subst_lookup_mapIdx_generated :
    ∀ (names : List String) (counter : Nat) (source : String),
      source ∈ names →
      Metta.Subst.lookup
          (names.mapIdx (fun index name =>
            (name, Atom.var (compilerGeneratedName (counter + index)))))
          source =
        some (Atom.var
          (compilerGeneratedName (counter + List.idxOf source names)))
  | [], counter, source, member => by simp at member
  | first :: rest, counter, source, member => by
      by_cases equal : source = first
      · subst source
        simp [List.mapIdx_cons, Metta.Subst.lookup]
      · have firstNe : first ≠ source := Ne.symm equal
        have firstBeq : (first == source) = false :=
          beq_eq_false_iff_ne.mpr firstNe
        have restMember : source ∈ rest := by simpa [equal] using member
        rw [List.mapIdx_cons]
        simp only [Metta.Subst.lookup, equal, beq_iff_eq, if_false,
          List.idxOf_cons, firstBeq, cond_false]
        have induction := subst_lookup_mapIdx_generated rest (counter + 1)
          source restMember
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          induction

/-- Exact executable lookup law, stated at the source variable's independent
first-occurrence index. -/
theorem compilerTypeFresheningSubst_lookup_idxOf
    {counter : Nat} {chain : List Atom} {source : String}
    (member : source ∈ compilerTypeVarNames chain) :
    Metta.Subst.lookup (compilerTypeFresheningSubst counter chain) source =
      some (Atom.var (compilerGeneratedName
        (counter + List.idxOf source (compilerTypeVarNames chain)))) := by
  exact subst_lookup_mapIdx_generated (compilerTypeVarNames chain) counter
    source member

/-- A finite association-list lookup succeeds for every key in its domain.
This small generic law avoids re-proving lookup plumbing in every compiler
freshening consumer. -/
theorem subst_lookup_exists_of_domain_mem :
    ∀ (substitution : Metta.Subst) (source : String),
      source ∈ substitution.map Prod.fst →
        ∃ target, Metta.Subst.lookup substitution source = some target
  | [], source => by simp
  | (key, value) :: rest, source => by
      intro member
      by_cases equal : source = key
      · subst source
        exact ⟨value, by simp [Metta.Subst.lookup]⟩
      · have restMember : source ∈ rest.map Prod.fst := by
          simpa [equal] using member
        rcases subst_lookup_exists_of_domain_mem rest source restMember with
          ⟨target, lookup⟩
        exact ⟨target, by simp [Metta.Subst.lookup, equal, lookup]⟩

/-- A successful association-list lookup returns an entry that is present in
the substitution. -/
theorem subst_lookup_eq_some_mem :
    ∀ {substitution : Metta.Subst} {source : String} {target : Atom},
      Metta.Subst.lookup substitution source = some target →
        (source, target) ∈ substitution
  | [], _, _, lookup => by simp [Metta.Subst.lookup] at lookup
  | (key, value) :: rest, source, target, lookup => by
      by_cases equal : source = key
      · subst source
        simp [Metta.Subst.lookup] at lookup
        subst target
        simp
      · simp only [Metta.Subst.lookup, equal, beq_iff_eq, if_false] at lookup
        exact List.mem_cons_of_mem (key, value)
          (subst_lookup_eq_some_mem lookup)

/-- Every substitution entry allocates exactly one generated variable inside
the chain's half-open counter interval. -/
theorem compilerTypeFresheningSubst_mem
    {counter : Nat} {chain : List Atom} {source : String} {target : Atom}
    (member :
      (source, target) ∈ compilerTypeFresheningSubst counter chain) :
    ∃ index, ∃ (_bound : index < (compilerTypeVarNames chain).length),
      source = (compilerTypeVarNames chain)[index] ∧
      target = Atom.var (compilerGeneratedName (counter + index)) := by
  rw [compilerTypeFresheningSubst, List.mem_mapIdx] at member
  rcases member with ⟨index, bound, equality⟩
  refine ⟨index, bound, ?_, ?_⟩
  · exact congrArg Prod.fst equality.symm
  · exact congrArg Prod.snd equality.symm

/-- Every source variable in the chain resolves to one of the freshly
allocated variables. -/
theorem compilerTypeFresheningSubst_lookup
    {counter : Nat} {chain : List Atom} {source : String}
    (member : source ∈ compilerTypeVarNames chain) :
    ∃ index, ∃ (_bound : index < (compilerTypeVarNames chain).length),
      Metta.Subst.lookup (compilerTypeFresheningSubst counter chain) source =
        some (Atom.var (compilerGeneratedName (counter + index))) := by
  have domainMember : source ∈
      (compilerTypeFresheningSubst counter chain).map Prod.fst := by
    rw [compilerTypeFresheningSubst_domain]
    exact member
  rcases subst_lookup_exists_of_domain_mem _ _ domainMember with
    ⟨target, lookupEq⟩
  have pairMember := subst_lookup_eq_some_mem lookupEq
  rcases compilerTypeFresheningSubst_mem pairMember with
    ⟨index, bound, _, targetEq⟩
  subst target
  exact ⟨index, bound, lookupEq⟩

/-- Repeated occurrences of one type variable are replaced by the same
generated variable because they share one substitution lookup. -/
theorem freshenTypeVariable
    {counter : Nat} {chain : List Atom} {source : String}
    (member : source ∈ compilerTypeVarNames chain) :
    ∃ index, ∃ (_bound : index < (compilerTypeVarNames chain).length),
      Metta.Subst.apply (compilerTypeFresheningSubst counter chain)
          (Atom.var source) =
        Atom.var (compilerGeneratedName (counter + index)) := by
  rcases compilerTypeFresheningSubst_lookup (counter := counter) member with
    ⟨index, bound, lookup⟩
  refine ⟨index, bound, ?_⟩
  simp [Metta.Subst.apply, lookup]

/-- Applying a substitution cannot invent an output variable: every output
occurrence comes from the target of a lookup for an input occurrence. -/
theorem subst_apply_var_member_origin
    (substitution : Metta.Subst) :
    ∀ (atom : Atom) (name : String),
      (∀ source, source ∈ atom.vars →
        ∃ target, Metta.Subst.lookup substitution source = some target) →
      name ∈ (Metta.Subst.apply substitution atom).vars →
        ∃ source target,
          source ∈ atom.vars ∧
          Metta.Subst.lookup substitution source = some target ∧
          name ∈ target.vars := by
  intro atom
  induction atom using Metta.Atom.recAux with
  | sym symbol => simp [Metta.Subst.apply, Atom.vars]
  | gnd ground => simp [Metta.Subst.apply, Atom.vars]
  | var source =>
      intro name covered member
      rcases covered source (by simp [Atom.vars]) with ⟨target, lookup⟩
      simp only [Metta.Subst.apply, lookup, Option.getD_some] at member
      exact ⟨source, target, by simp [Atom.vars], lookup, member⟩
  | expr atoms ih =>
      intro name covered member
      have member' : name ∈
          (atoms.map (Metta.Subst.apply substitution)).flatMap Atom.vars := by
        simpa [Metta.Subst.apply, Atom.vars] using member
      rcases List.mem_flatMap.mp member' with
        ⟨renamed, renamedMember, nameMember⟩
      rcases List.mem_map.mp renamedMember with
        ⟨sourceAtom, sourceMember, rfl⟩
      have sourceCovered : ∀ source, source ∈ sourceAtom.vars →
          ∃ target, Metta.Subst.lookup substitution source = some target := by
        intro source sourceVariable
        apply covered source
        simp only [Atom.vars, List.mem_flatten]
        exact ⟨sourceAtom.vars,
          List.mem_map.mpr ⟨sourceAtom, sourceMember, rfl⟩,
          sourceVariable⟩
      rcases ih sourceAtom sourceMember name sourceCovered nameMember with
        ⟨source, target, sourceVariable, lookup, targetMember⟩
      refine ⟨source, target, ?_, lookup, targetMember⟩
      simp only [Atom.vars, List.mem_flatten]
      exact ⟨sourceAtom.vars,
        List.mem_map.mpr ⟨sourceAtom, sourceMember, rfl⟩,
        sourceVariable⟩

/-- Every variable in the freshened chain belongs to the exact allocated
counter interval. In particular, no source type-variable name leaks through. -/
theorem freshenTypeChain_names_generated
    {counter : Nat} {chain : List Atom} {name : String}
    (member :
      name ∈ (freshenTypeChain counter chain).1.flatMap Atom.vars) :
    ∃ index, index < (compilerTypeVarNames chain).length ∧
      name = compilerGeneratedName (counter + index) := by
  simp only [freshenTypeChain] at member
  rcases List.mem_flatMap.mp member with
    ⟨renamedAtom, renamedMember, nameMember⟩
  rcases List.mem_map.mp renamedMember with
    ⟨sourceAtom, sourceMember, rfl⟩
  have covered : ∀ source, source ∈ sourceAtom.vars →
      ∃ target,
        Metta.Subst.lookup (compilerTypeFresheningSubst counter chain)
          source = some target := by
    intro source sourceVariable
    have chainVariable : source ∈ chain.flatMap Atom.vars :=
      List.mem_flatMap.mpr ⟨sourceAtom, sourceMember, sourceVariable⟩
    have typeVariable : source ∈ compilerTypeVarNames chain :=
      List.mem_eraseDups.mpr chainVariable
    rcases compilerTypeFresheningSubst_lookup
        (counter := counter) typeVariable with
      ⟨index, bound, lookup⟩
    exact ⟨Atom.var (compilerGeneratedName (counter + index)), lookup⟩
  rcases subst_apply_var_member_origin
      (compilerTypeFresheningSubst counter chain) sourceAtom name covered
      nameMember with
    ⟨source, target, _, lookup, targetMember⟩
  have pairMember := subst_lookup_eq_some_mem lookup
  rcases compilerTypeFresheningSubst_mem pairMember with
    ⟨index, bound, _, targetEq⟩
  subst target
  simp only [Atom.vars, List.mem_singleton] at targetMember
  exact ⟨index, bound, targetMember⟩

/-- Closed chains are unchanged and consume no compiler names. -/
theorem freshenTypeChain_closed_eq
    (counter : Nat) (chain : List Atom)
    (closed : chain.flatMap Atom.vars = []) :
    freshenTypeChain counter chain = (chain, counter) := by
  have fixed : chain.map (Metta.Subst.apply []) = chain := by
    calc
      chain.map (Metta.Subst.apply []) = chain.map id :=
        List.map_congr_left (fun atom _ => Metta.Subst.apply_nil atom)
      _ = chain := List.map_id chain
  simp only [freshenTypeChain, compilerTypeFresheningSubst,
    compilerTypeVarNames, closed, List.eraseDups_nil, List.mapIdx_nil,
    List.length_nil, Nat.add_zero, fixed]

/-- Consecutive freshening calls have disjoint variable ranges. This is the
branch-local independence law needed by overloaded typed dispatch. -/
theorem freshenTypeChain_ranges_disjoint
    {leftStart rightStart : Nat} {left right : List Atom} {name : String}
    (separated :
      leftStart + (compilerTypeVarNames left).length ≤ rightStart)
    (leftMember :
      name ∈ (freshenTypeChain leftStart left).1.flatMap Atom.vars)
    (rightMember :
      name ∈ (freshenTypeChain rightStart right).1.flatMap Atom.vars) :
    False := by
  rcases freshenTypeChain_names_generated leftMember with
    ⟨leftIndex, leftBound, leftName⟩
  rcases freshenTypeChain_names_generated rightMember with
    ⟨rightIndex, _, rightName⟩
  have encodedEqual :
      compilerGeneratedName (leftStart + leftIndex) =
        compilerGeneratedName (rightStart + rightIndex) := by
    rw [← leftName, ← rightName]
  have decodedEqual := congrArg compilerGeneratedIndex? encodedEqual
  simp only [CompilerFreshness.compilerGeneratedIndex?_name,
    Option.some.injEq] at decodedEqual
  omega

end PLeaTTa.CompilerTypeFreshening
