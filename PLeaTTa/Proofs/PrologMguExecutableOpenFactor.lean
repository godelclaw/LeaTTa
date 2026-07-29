-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologMguExecutableOpenFactor
Purpose: Factor the independently constructed open canonical MGU
  representative through every actual executable MGU result.
Trusted boundary: none
Main exports:
  OpenAlphaResultFactors,
  unifyTopExact_open_factor_of_ordered_shared_alpha,
  unifyB_result_has_open_factor_of_ordered_shared_alpha
-/
import PLeaTTa.Proofs.PrologMguTopology

namespace PLeaTTa.PrologMguExecutableOpenFactor

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PrologMguBridge
open PrologMguOpenAgreement
open PrologMguTopology
open PrologPrefilterBridge

/-- The actual executable result is at least as general as one open runtime
representative of the independent ordered canonical MGU.  The representative
retains its raw alpha spelling, exact deep denotation, and acyclicity
certificate; factorization is semantic rather than association-list equality.
-/
def OpenAlphaResultFactors
    (alpha : List (LogicVar × String))
    (canonical : TreeSubstitution) (result : Subst) : Prop :=
  ∃ representative,
    AlphaTreeSubstitutionAgrees alpha canonical representative ∧
      AlphaValuationAgrees alpha canonical representative ∧
      Nonempty (PLeaTTa.SubstTopological representative) ∧
      PLeaTTa.SubstFactorsThroughWith
        PLeaTTa.prologGroundIdentical representative result

/-- A tree-level canonical unifier and its open alpha valuation make every
runtime equation pair comparator-equivalent.  This avoids reifying the
canonical substitution merely to reuse the source-substitution theorem. -/
theorem SharedAlphaEquationsAgree.atomsEquivalent_of_tree_unifier
    {alpha : List (LogicVar × String)}
    (functional : AlphaForwardFunctional alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    {canonical : TreeSubstitution} {runtime : Subst}
    (valuation :
      AlphaValuationAgrees alpha canonical runtime)
    (unifies :
      TreeUnifiesEquations canonical (denoteEquations equations)) :
    AtomsEquivalentWith PLeaTTa.prologGroundIdentical
      (leftAtoms.map (PLeaTTa.subst runtime))
      (rightAtoms.map (PLeaTTa.subst runtime)) := by
  induction agreement with
  | nil =>
      exact .nil
  | @cons leftTerm rightTerm leftAtom rightAtom equations leftAtoms
      rightAtoms left right tail inductionHypothesis =>
      have leftApplied :=
        canonicalRuntimeAgrees_apply
          (AlphaTermAgrees.canonicalRuntimeAgrees left) valuation
      have rightApplied :=
        canonicalRuntimeAgrees_apply
          (AlphaTermAgrees.canonicalRuntimeAgrees right) valuation
      have headEquality :
          TreeSubstitution.apply canonical (Term.denote leftTerm) =
            TreeSubstitution.apply canonical (Term.denote rightTerm) := by
        apply unifies
          (Term.denote leftTerm, Term.denote rightTerm)
        simp [denoteEquations]
      rw [headEquality] at leftApplied
      exact .cons
        (CanonicalRuntimeAgrees.equivalent_of_same
          functional leftApplied rightApplied)
        (inductionHypothesis (by
          intro denoted member
          exact unifies denoted (by
            simp only [denoteEquations, List.mem_map] at member ⊢
            obtain ⟨equation, equationMember, rfl⟩ := member
            exact
              ⟨equation, List.mem_cons_of_mem _ equationMember, rfl⟩)))

/-- Expression wrapper around
`atomsEquivalent_of_tree_unifier`, in the exact runtime worklist shape
consumed by `unifyTopExact`. -/
theorem SharedAlphaEquationsAgree.deepEquivalentUnifies_of_tree_unifier
    {alpha : List (LogicVar × String)}
    (functional : AlphaForwardFunctional alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    {canonical : TreeSubstitution} {runtime : Subst}
    (valuation :
      AlphaValuationAgrees alpha canonical runtime)
    (unifies :
      TreeUnifiesEquations canonical (denoteEquations equations)) :
    PLeaTTa.DeepEquivalentUnifies PLeaTTa.prologGroundIdentical runtime
      [(.expr leftAtoms, .expr rightAtoms)] := by
  intro equation member
  simp only [List.mem_singleton] at member
  subst equation
  simp only [PLeaTTa.subst_expr]
  exact .expression
    (PLeaTTa.PrologMguExecutableOpenFactor.SharedAlphaEquationsAgree.atomsEquivalent_of_tree_unifier
      functional agreement valuation unifies)

/-- The open representative constructed from an ordered canonical MGU is a
runtime unifier, while retaining its raw spelling and topology witnesses. -/
theorem SharedAlphaEquationsAgree.open_runtime_unifier_exists
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    {canonical : TreeSubstitution}
    (derivation :
      OrderedTreeMgu (denoteEquations equations) canonical) :
    ∃ representative,
      AlphaTreeSubstitutionAgrees alpha canonical representative ∧
        AlphaValuationAgrees alpha canonical representative ∧
        Nonempty (PLeaTTa.SubstTopological representative) ∧
        PLeaTTa.DeepEquivalentUnifies
          PLeaTTa.prologGroundIdentical representative
          [(.expr leftAtoms, .expr rightAtoms)] := by
  obtain
    ⟨representative, spelling, valuation, topological⟩ :=
    PLeaTTa.PrologMguTopology.SharedAlphaEquationsAgree.orderedMgu_open_valuation_exists
      shared agreement derivation
  exact
    ⟨representative, spelling, valuation, topological,
      PLeaTTa.PrologMguExecutableOpenFactor.SharedAlphaEquationsAgree.deepEquivalentUnifies_of_tree_unifier
        shared.forward agreement valuation derivation.isMostGeneral.1⟩

/-- Every actual `unifyTopExact` result admits the independent canonical
MGU's open runtime representative as a semantic instance.  Unlike the older
ground-factor theorem, this result preserves residual variables. -/
theorem unifyTopExact_open_factor_of_ordered_shared_alpha
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    {canonical : TreeSubstitution}
    (derivation :
      OrderedTreeMgu (denoteEquations equations) canonical)
    {result : Subst}
    (returned :
      PLeaTTa.unifyTopExact (.expr leftAtoms) (.expr rightAtoms) =
        some result) :
    OpenAlphaResultFactors alpha canonical result := by
  obtain
    ⟨representative, spelling, valuation, topological,
      representativeUnifies⟩ :=
    PLeaTTa.PrologMguExecutableOpenFactor.SharedAlphaEquationsAgree.open_runtime_unifier_exists
      shared agreement derivation
  have runtimeMgu :=
    PLeaTTa.unifyTopExact_isMgu
      (.expr leftAtoms) (.expr rightAtoms) result returned
  exact
    ⟨representative, spelling, valuation, topological,
      runtimeMgu.2 representative representativeUnifies⟩

/-- The current-binding executable call exposes its generated open MGU and
the exact installation equation, with the canonical open representative
factoring through that generated result before composition with `base`. -/
theorem unifyB_result_has_open_factor_of_ordered_shared_alpha
    (base : Subst)
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations
        (leftAtoms.map (PLeaTTa.subst base))
        (rightAtoms.map (PLeaTTa.subst base)))
    {canonical : TreeSubstitution}
    (derivation :
      OrderedTreeMgu (denoteEquations equations) canonical)
    {result : Subst}
    (returned :
      PLeaTTa.unifyB base (.expr leftAtoms) (.expr rightAtoms) =
        some result) :
    ∃ generated,
      PLeaTTa.unifyTopExact
          (.expr (leftAtoms.map (PLeaTTa.subst base)))
          (.expr (rightAtoms.map (PLeaTTa.subst base))) =
          some generated ∧
        OpenAlphaResultFactors alpha canonical generated ∧
        result =
          match generated with
          | [] => base
          | _ :: _ => Metta.Subst.compose generated base := by
  obtain ⟨generated, generatedEq, _, installed⟩ :=
    PLeaTTa.unifyB_result_has_generated_mgu
      base (.expr leftAtoms) (.expr rightAtoms) result returned
  have normalizedEq :
      PLeaTTa.unifyTopExact
          (.expr (leftAtoms.map (PLeaTTa.subst base)))
          (.expr (rightAtoms.map (PLeaTTa.subst base))) =
          some generated := by
    simpa only [PLeaTTa.subst_expr] using generatedEq
  have factors :=
    unifyTopExact_open_factor_of_ordered_shared_alpha
      shared agreement derivation normalizedEq
  exact ⟨generated, normalizedEq, factors, installed⟩

/-! ### Anti-vacuity: the factor remains open -/

private def openWitnessX : LogicVar := .source "X"

private def openWitnessY : LogicVar := .source "Y"

private def openWitnessAlpha : List (LogicVar × String) :=
  [(openWitnessX, "X"), (openWitnessY, "Y")]

private def openWitnessEquations : List (Term × Term) :=
  [(.variable openWitnessX, .variable openWitnessY)]

private def openWitnessCanonical : TreeSubstitution :=
  [(openWitnessX, .variable openWitnessY)]

/-- On the smallest residual-alias problem, the factor theorem applies to
the concrete open executable result and that result leaves `Y` unresolved.
This distinguishes the new theorem from the older grounded-instance factor.
-/
theorem residual_alias_open_factor_retains_residual :
    ∃ result,
      PLeaTTa.unifyTopExact
          (.expr [.var "X"]) (.expr [.var "Y"]) =
        some result ∧
      OpenAlphaResultFactors
        openWitnessAlpha openWitnessCanonical result ∧
      PLeaTTa.subst result (.var "Y") = .var "Y" := by
  have derivation :
      OrderedTreeMgu
        (denoteEquations openWitnessEquations)
        openWitnessCanonical := by
    apply OrderedTreeMgu.cons
      (.variable openWitnessX) (.variable openWitnessY) []
      openWitnessCanonical []
    · exact .bindLeft openWitnessX (.variable openWitnessY)
        (by simp [openWitnessX, openWitnessY])
        (by simp [Tree.occurs, openWitnessX, openWitnessY])
    · exact .nil
  have shared : SharedRuntimeAlpha openWitnessAlpha := by
    constructor
    · intro identity left right leftMember rightMember
      simp [openWitnessAlpha, openWitnessX, openWitnessY]
        at leftMember rightMember
      rcases leftMember with leftMember | leftMember <;>
        rcases rightMember with rightMember | rightMember <;>
        simp_all
    · intro left right name leftMember rightMember
      simp [openWitnessAlpha, openWitnessX, openWitnessY]
        at leftMember rightMember
      rcases leftMember with leftMember | leftMember <;>
        rcases rightMember with rightMember | rightMember <;>
        simp_all
  have agreement :
      SharedAlphaEquationsAgree openWitnessAlpha
        openWitnessEquations [.var "X"] [.var "Y"] :=
    .cons
      (.variable (by simp [openWitnessAlpha]))
      (.variable (by simp [openWitnessAlpha]))
      .nil
  have returned :
      PLeaTTa.unifyTopExact
          (.expr [.var "X"]) (.expr [.var "Y"]) =
        some [("X", .var "Y")] := by
    unfold PLeaTTa.unifyTopExact
    simp [Metta.Unify.unifyTopWith, Atom.size,
      Metta.Unify.unifyRoundsWith, Metta.Unify.decomposeAllWith,
      Metta.Unify.decomposeEqWith, Metta.Unify.decomposeListWith,
      Metta.Subst.occurs, Metta.Subst.extend, Metta.Subst.erase]
  refine ⟨[("X", .var "Y")], returned, ?_, ?_⟩
  · exact unifyTopExact_open_factor_of_ordered_shared_alpha
      shared agreement derivation returned
  · simp [PLeaTTa.subst, PLeaTTa.substN, Metta.Subst.lookup]

end PLeaTTa.PrologMguExecutableOpenFactor
