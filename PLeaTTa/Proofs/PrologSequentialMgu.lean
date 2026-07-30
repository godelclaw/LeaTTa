-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologSequentialMgu
Purpose: Preserve semantic MGU variation across sequential primitive
  unification without choosing an association-list orientation.
Trusted boundary: none
Main exports:
  TreeIsRelativeMgu,
  TreeIsMgu.relativeCompose,
  sequential_mgu_composites_are_variants
-/
import PLeaTTa.Proofs.PrologMguVariant

namespace PLeaTTa.PrologSequentialMgu

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PrologMguVariant

/-!
An active task carries a substitution chosen by earlier unification.  The
independent ordered resolver and the executable resolver may spell that state
with opposite residual-variable orientations.  A later equality is therefore
not solved against literally equal inputs, and its two returned association
lists need not become equal afterward.

The invariant needed by the step correspondence is relative most-generality.
A result must descend from its carried base, solve the new equations, and be
universal among exactly the base-descending solutions.  This formulation does
not need the earlier equation history or assume that either carried base is
itself an MGU of a remembered worklist.
-/

/-- A principal solution of `equations` relative to an already-carried
substitution.  The first conjunct prevents a solver from discarding the
carried state; the last quantifies over precisely the same descendant cone. -/
def TreeIsRelativeMgu
    (result base : TreeSubstitution)
    (equations : List TreeEquation) : Prop :=
  TreeFactorsThrough result base ∧
    TreeUnifiesEquations result equations ∧
    ∀ candidate,
      TreeFactorsThrough candidate base →
      TreeUnifiesEquations candidate equations →
      TreeFactorsThrough candidate result

namespace TreeIsRelativeMgu

/-- Relative principal solutions over variant bases are themselves variants.
The proof uses only mutual factorization of the bases: no hidden common
equation list or preferred residual orientation is required. -/
theorem variants_of_base_variants
    {firstResult firstBase secondResult secondBase : TreeSubstitution}
    {equations : List TreeEquation}
    (bases : TreeSubstitutionVariants firstBase secondBase)
    (first : TreeIsRelativeMgu firstResult firstBase equations)
    (second : TreeIsRelativeMgu secondResult secondBase equations) :
    TreeSubstitutionVariants firstResult secondResult := by
  constructor
  · exact second.2.2 firstResult
      (TreeFactorsThrough.trans first.1 bases.1)
      first.2.1
  · exact first.2.2 secondResult
      (TreeFactorsThrough.trans second.1 bases.2)
      second.2.1

end TreeIsRelativeMgu

/-- An ordinary MGU of the equations after applying `base` induces the
relative principal solution obtained by prepending that extension to
`base`.  This is the bridge from the existing residual solvers to the
representation-independent sequential interface. -/
theorem TreeIsMgu.relativeCompose
    {base extension : TreeSubstitution}
    {equations : List TreeEquation}
    (extensionMgu :
      TreeIsMgu extension
        (TreeSubstitution.applyEquations base equations)) :
    TreeIsRelativeMgu (extension ++ base) base equations := by
  refine ⟨⟨extension, fun tree => ?_⟩, ?_, ?_⟩
  · exact TreeSubstitution.apply_append extension base tree
  · intro equation member
    have normalized :
        (TreeSubstitution.apply base equation.1,
            TreeSubstitution.apply base equation.2) ∈
          TreeSubstitution.applyEquations base equations :=
      List.mem_map_of_mem member
    simpa [TreeSubstitution.apply_append] using
      extensionMgu.1 _ normalized
  · intro candidate candidateFactors candidateUnifies
    rcases candidateFactors with ⟨residual, factors⟩
    have residualUnifies :
        TreeUnifiesEquations residual
          (TreeSubstitution.applyEquations base equations) := by
      intro normalized normalizedMember
      simp only [TreeSubstitution.applyEquations, List.mem_map]
        at normalizedMember
      obtain ⟨equation, member, rfl⟩ := normalizedMember
      rw [← factors equation.1, ← factors equation.2]
      exact candidateUnifies equation member
    rcases extensionMgu.2 residual residualUnifies with
      ⟨final, residualFactors⟩
    refine ⟨final, ?_⟩
    intro tree
    rw [factors tree,
      residualFactors (TreeSubstitution.apply base tree),
      TreeSubstitution.apply_append]

/-- Sequential residual MGUs preserve semantic variation of their carried
bases.  This is the pushout-shaped algebra needed by repeated equality steps:
the two composites have the same instance cone even when neither extension
nor final association list has the same orientation. -/
theorem sequential_mgu_composites_are_variants
    {firstBase secondBase firstExtension secondExtension : TreeSubstitution}
    {equations : List TreeEquation}
    (bases : TreeSubstitutionVariants firstBase secondBase)
    (firstMgu :
      TreeIsMgu firstExtension
        (TreeSubstitution.applyEquations firstBase equations))
    (secondMgu :
      TreeIsMgu secondExtension
        (TreeSubstitution.applyEquations secondBase equations)) :
    TreeSubstitutionVariants
      (firstExtension ++ firstBase)
      (secondExtension ++ secondBase) :=
  TreeIsRelativeMgu.variants_of_base_variants bases
    (TreeIsMgu.relativeCompose firstMgu)
    (TreeIsMgu.relativeCompose secondMgu)

/-! ## Anti-vacuity: sequential orientation really remains quotiented -/

private def sequentialX : LogicVar := .source "$sequential_x"
private def sequentialY : LogicVar := .source "$sequential_y"
private def sequentialValue : Tree :=
  .node (.atom "$sequential_value") []
private def sequentialFirstBase : TreeSubstitution :=
  [(sequentialX, .variable sequentialY)]
private def sequentialSecondBase : TreeSubstitution :=
  [(sequentialY, .variable sequentialX)]
private def sequentialFirstExtension : TreeSubstitution :=
  [(sequentialY, sequentialValue)]
private def sequentialSecondExtension : TreeSubstitution :=
  [(sequentialX, sequentialValue)]
private def sequentialEquation : List TreeEquation :=
  [(.variable sequentialX, sequentialValue)]

/-- Opposite aliases followed by the same grounding equation produce
unequal composite association lists which are nevertheless sequential
variants and give the same ground values for both variables.  This rejects
replacing the semantic theorem by syntactic substitution equality. -/
theorem sequential_variants_need_not_be_equal :
    TreeSubstitutionVariants sequentialFirstBase sequentialSecondBase ∧
      TreeIsMgu sequentialFirstExtension
        (TreeSubstitution.applyEquations
          sequentialFirstBase sequentialEquation) ∧
      TreeIsMgu sequentialSecondExtension
        (TreeSubstitution.applyEquations
          sequentialSecondBase sequentialEquation) ∧
      TreeSubstitutionVariants
        (sequentialFirstExtension ++ sequentialFirstBase)
        (sequentialSecondExtension ++ sequentialSecondBase) ∧
      (sequentialFirstExtension ++ sequentialFirstBase) ≠
        (sequentialSecondExtension ++ sequentialSecondBase) ∧
      TreeSubstitution.apply
          (sequentialFirstExtension ++ sequentialFirstBase)
          (.variable sequentialX) = sequentialValue ∧
      TreeSubstitution.apply
          (sequentialSecondExtension ++ sequentialSecondBase)
          (.variable sequentialY) = sequentialValue := by
  have firstBaseMgu :
      TreeIsMgu sequentialFirstBase
        [(.variable sequentialX, .variable sequentialY)] := by
    exact tree_singleton_variable_is_mgu sequentialX
      (.variable sequentialY) (by
        simp [Tree.occurs, sequentialX, sequentialY])
  have secondBaseMgu :
      TreeIsMgu sequentialSecondBase
        [(.variable sequentialX, .variable sequentialY)] := by
    exact tree_singleton_right_variable_is_mgu
      (.variable sequentialX) sequentialY (by
        simp [Tree.occurs, sequentialX, sequentialY])
  have bases :
      TreeSubstitutionVariants sequentialFirstBase sequentialSecondBase :=
    PrologMguVariant.TreeIsMgu.variants firstBaseMgu secondBaseMgu
  have firstExtensionMgu :
      TreeIsMgu sequentialFirstExtension
        (TreeSubstitution.applyEquations
          sequentialFirstBase sequentialEquation) := by
    simpa [sequentialFirstExtension, sequentialFirstBase,
      sequentialEquation, sequentialValue, sequentialX, sequentialY,
      TreeSubstitution.applyEquations, TreeSubstitution.apply,
      Tree.instantiateOne, Trees.instantiateOne] using
      (tree_singleton_variable_is_mgu sequentialY sequentialValue (by rfl))
  have secondExtensionMgu :
      TreeIsMgu sequentialSecondExtension
        (TreeSubstitution.applyEquations
          sequentialSecondBase sequentialEquation) := by
    simpa [sequentialSecondExtension, sequentialSecondBase,
      sequentialEquation, sequentialValue, sequentialX, sequentialY,
      TreeSubstitution.applyEquations, TreeSubstitution.apply,
      Tree.instantiateOne, Trees.instantiateOne] using
      (tree_singleton_variable_is_mgu sequentialX sequentialValue (by rfl))
  have composites :=
    sequential_mgu_composites_are_variants bases
      firstExtensionMgu secondExtensionMgu
  refine
    ⟨bases, firstExtensionMgu, secondExtensionMgu, composites, ?_, ?_, ?_⟩
  · simp [sequentialFirstExtension, sequentialFirstBase,
      sequentialSecondExtension, sequentialSecondBase,
      sequentialX, sequentialY]
  · simp [sequentialFirstExtension, sequentialFirstBase,
      sequentialValue, sequentialX, sequentialY,
      TreeSubstitution.apply, Tree.instantiateOne]
  · simp [sequentialSecondExtension, sequentialSecondBase,
      sequentialValue, sequentialX, sequentialY,
      TreeSubstitution.apply, Tree.instantiateOne]

end PLeaTTa.PrologSequentialMgu
