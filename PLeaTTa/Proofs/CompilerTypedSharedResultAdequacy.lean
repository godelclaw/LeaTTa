/-
Module: PLeaTTa.Proofs.CompilerTypedSharedResultAdequacy
Purpose: Relate PLeaTTa's executable typed-output resolution to the
  independent semantic MGU specification.
Trusted boundary: none
Main exports: unifyTopExact_fresh_variable,
  bindTypedSharedResult_initial_adequate
-/
import PLeaTTa.PeTTaSpec.TypedSharedResult
import PLeaTTa.Proofs.OpenBindingAgreement
import PLeaTTa.Proofs.PrologCoreAdequacy

namespace PLeaTTa.CompilerTypedSharedResultAdequacy

open Metta (Atom Subst)
open PLeaTTa.CompilerAdequacy
open PLeaTTa.OpenBindingAgreement
open PLeaTTa.PeTTaSpec.PrologCore
open PLeaTTa.PeTTaSpec.PrologCore.OpenSubstitution
open PLeaTTa.PeTTaSpec.PrologCore.TypedSharedResult

/-- Boolean occurs-check rejection implies absence from the executable
syntactic variable list.  This direction is kept explicit because the
finite-tree premise is load-bearing at the PeTTa/SWI anchoring seam. -/
theorem not_mem_vars_of_occurs_eq_false (name : String) (atom : Atom)
    (occurs : Metta.Subst.occurs name atom = false) :
    name ∉ atom.vars := by
  induction atom with
  | sym symbol => simp [Atom.vars]
  | var variableName =>
      simpa [Metta.Subst.occurs, Atom.vars] using occurs
  | gnd ground => simp [Atom.vars]
  | expr atoms induction =>
      simp only [Metta.Subst.occurs] at occurs
      simp only [Atom.vars]
      rw [List.mem_flatten]
      intro member
      rcases member with ⟨variableList, variableListMember, nameMember⟩
      rcases List.mem_map.mp variableListMember with
        ⟨child, childMember, rfl⟩
      have childOccurs : Metta.Subst.occurs name child = false := by
        have all := List.any_eq_false.mp occurs
        simpa only [Bool.not_eq_true] using
          (all ⟨child, childMember⟩ (by simp))
      exact induction child childMember childOccurs nameMember

/-- A fresh executable variable is eliminated to its target by the exact
PeTTa wrapper.  This theorem proves success; it does not assume an underlying
unifier result. -/
theorem unifyTopExact_fresh_variable (fresh : String) (target : Atom)
    (occurs : Metta.Subst.occurs fresh target = false) :
    unifyTopExact (.var fresh) target = some [(fresh, target)] := by
  have underlying : Metta.Unify.unifyTop (.var fresh) target =
      some [(fresh, target)] :=
    PLeaTTa.PrologCoreAdequacy.unifyTop_fresh_variable fresh target occurs
  have freshForTarget : fresh ∉ target.vars :=
    not_mem_vars_of_occurs_eq_false fresh target occurs
  have topological : SubstTopological [(fresh, target)] :=
    SubstTopological.cons_of_fresh [] emptySubstTopological fresh target
      (by simp [Metta.Subst.lookup]) freshForTarget
      (by simp [AtomAvoids, Metta.Subst.lookup])
  have lookup : Metta.Subst.lookup [(fresh, target)] fresh = some target := by
    simp [Metta.Subst.lookup]
  have exact : subst [(fresh, target)] (.var fresh) =
      subst [(fresh, target)] target :=
    topological.subst_var_of_lookup [(fresh, target)] fresh target lookup
  exact unifyTopExact_of_underlying_exact (.var fresh) target
    [(fresh, target)] underlying exact

/-- The executable first raw branch binds a fresh shared output to the branch
result exactly.  Later branches are a separate structural-decomposition
obligation rather than being hidden in this initial equation. -/
theorem bindTypedSharedResult_fresh_initial (fresh : String) (target : Atom)
    (goals : List Goal) (different : target ≠ .var fresh)
    (occurs : Metta.Subst.occurs fresh target = false) :
    bindTypedSharedResult (.var fresh) [] (target, goals) =
      .ok [(fresh, target)] := by
  have beqFalse : (target == Atom.var fresh) = false := by
    cases target with
    | sym name => rfl
    | var name =>
        change (name == fresh) = false
        apply beq_eq_false_iff_ne.mpr
        intro equality
        apply different
        cases equality
        rfl
    | gnd ground => rfl
    | expr atoms => rfl
  have sharedFixed : subst [] (.var fresh) = .var fresh := by
    apply subst_eq_self_of_domain_free [] (.var fresh)
    simp [Metta.Subst.lookup]
  have targetFixed : subst [] target = target := by
    apply subst_eq_self_of_domain_free [] target
    simp [Metta.Subst.lookup]
  unfold bindTypedSharedResult
  simp only [beqFalse, Bool.false_eq_true, if_false, sharedFixed, targetFixed,
    unifyTopExact_fresh_variable fresh target occurs, Metta.Subst.compose,
    List.map_nil, List.nil_append]

/-- Independent/executable pair list observed by the first shared-output
binding.  It includes both the shared variable and the target, before and
after substitution. -/
def freshSharedPairs (index : Nat) (referenceValue : Term)
    (executableValue : Atom) : List (Term × Atom) :=
  [(.variable (.generated index), .var (compilerGeneratedName index)),
   (referenceValue, executableValue)]

/-- The independent singleton MGU and executable singleton binding agree on
the complete first-constraint surface.  Neither side is defined through the
other: pre-state `TermAgrees` and both freshness conditions are premises. -/
theorem fresh_singleton_bindings_agree (index : Nat)
    (referenceValue : Term) (executableValue : Atom)
    (agreement : TermAgrees referenceValue executableValue)
    (referenceFresh :
      Term.occurs (.generated index) referenceValue = false)
    (executableFresh :
      compilerGeneratedName index ∉ executableValue.vars) :
    BindingsAgreeOn [(.generated index, referenceValue)]
      [(compilerGeneratedName index, executableValue)]
      (freshSharedPairs index referenceValue executableValue) := by
  let name := compilerGeneratedName index
  let referenceBinding : Substitution :=
    [(.generated index, referenceValue)]
  let executableBinding : Subst := [(name, executableValue)]
  have topological : SubstTopological executableBinding := by
    apply SubstTopological.cons_of_fresh [] emptySubstTopological name
      executableValue
    · simp [Metta.Subst.lookup]
    · exact executableFresh
    · simp [AtomAvoids, Metta.Subst.lookup]
  have lookup : Metta.Subst.lookup executableBinding name =
      some executableValue := by
    simp [executableBinding, Metta.Subst.lookup]
  have executableValueFixed : subst executableBinding executableValue =
      executableValue := by
    apply subst_eq_self_of_domain_free executableBinding executableValue
    intro candidate member
    by_cases same : candidate = name
    · subst candidate
      exact False.elim (executableFresh member)
    · simp [executableBinding, Metta.Subst.lookup, same]
  have executableShared : subst executableBinding (.var name) =
      executableValue := by
    exact (topological.subst_var_of_lookup executableBinding name
      executableValue lookup).trans executableValueFixed
  have referenceValueFixed : referenceBinding.applyTerm referenceValue =
      referenceValue := by
    exact Term.instantiateOne_eq_self_of_occurs_false (.generated index)
      referenceValue referenceValue referenceFresh
  intro pair member
  simp only [freshSharedPairs, List.mem_cons, List.not_mem_nil, or_false]
    at member
  rcases member with rfl | rfl
  · constructor
    · exact TermAgrees.generatedVariable index
    · unfold TermStateAgrees
      change TermAgrees
        (referenceBinding.applyTerm (.variable (.generated index)))
        (subst executableBinding (.var name))
      rw [show referenceBinding.applyTerm (.variable (.generated index)) =
          referenceValue by
            simp [referenceBinding,
              PLeaTTa.PeTTaSpec.PrologCore.OpenSubstitution.Substitution.applyTerm,
              Term.instantiateOne],
        executableShared]
      exact agreement
  · constructor
    · exact agreement
    · unfold TermStateAgrees
      change TermAgrees (referenceBinding.applyTerm referenceValue)
        (subst executableBinding executableValue)
      rw [referenceValueFixed, executableValueFixed]
      exact agreement

/-- First-constraint adequacy for typed shared-output resolution.  The
independent result is a semantic MGU, the executable result is computed
exactly, and their before/after states agree on both relevant terms. -/
theorem bindTypedSharedResult_initial_adequate (index : Nat)
    (referenceValue : Term) (executableValue : Atom) (goals : List Goal)
    (agreement : TermAgrees referenceValue executableValue)
    (referenceFresh :
      Term.occurs (.generated index) referenceValue = false)
    (executableFresh :
      compilerGeneratedName index ∉ executableValue.vars) :
    ∃ referenceBinding : Substitution, ∃ executableBinding : Subst,
      IsMostGeneralUnifier referenceBinding
        [(.variable (.generated index), referenceValue)] ∧
      bindTypedSharedResult (.var (compilerGeneratedName index)) []
          (executableValue, goals) = .ok executableBinding ∧
      BindingsAgreeOn referenceBinding executableBinding
        (freshSharedPairs index referenceValue executableValue) := by
  let name := compilerGeneratedName index
  let referenceBinding : Substitution :=
    [(.generated index, referenceValue)]
  let executableBinding : Subst := [(name, executableValue)]
  have different : executableValue ≠ .var name := by
    intro equality
    subst executableValue
    apply executableFresh
    simp [name, Atom.vars]
  have occurs : Metta.Subst.occurs name executableValue = false :=
    occurs_eq_false_of_not_mem_vars name executableValue executableFresh
  refine ⟨referenceBinding, executableBinding, ?_, ?_, ?_⟩
  · exact singleton_variable_is_mgu (.generated index) referenceValue
      referenceFresh
  · exact bindTypedSharedResult_fresh_initial name executableValue goals
      different occurs
  · exact fresh_singleton_bindings_agree index referenceValue executableValue
      agreement referenceFresh executableFresh

end PLeaTTa.CompilerTypedSharedResultAdequacy
