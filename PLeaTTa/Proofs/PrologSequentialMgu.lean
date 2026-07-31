-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologSequentialMgu
Purpose: Preserve semantic MGU variation across sequential primitive
  unification without choosing an association-list orientation.
Trusted boundary: none
Main exports:
  TreeIsRelativeMgu,
  TreeIsMgu.relativeCompose,
  sequential_mgu_composites_are_variants,
  sequential_mgu_composites_are_variants_of_equivalent
-/
import PLeaTTa.Proofs.PrologMguVariant

namespace PLeaTTa.PrologSequentialMgu

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PrologMguOpenAgreement
open PrologMguDirectSimulation
open PrologMguTopology
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

/-- Semantic equivalence of equation worklists transports a relative MGU
without changing its carried base or association-list spelling.  This is
stronger than satisfiability preservation: the same descendant cone remains
principal because every candidate solves one worklist exactly when it solves
the other. -/
theorem of_equivalent
    {result base : TreeSubstitution}
    {first second : List TreeEquation}
    (equivalent : TreeUnificationEquivalent first second)
    (relative : TreeIsRelativeMgu result base first) :
    TreeIsRelativeMgu result base second := by
  refine ⟨relative.1, (equivalent result).1 relative.2.1, ?_⟩
  intro candidate candidateFactors candidateUnifies
  exact relative.2.2 candidate candidateFactors
    ((equivalent candidate).2 candidateUnifies)

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

/-- Relative principal solutions over variant bases and semantically
equivalent worklists are variants.  No operand order, equation-list spelling,
or residual alias orientation is selected by the theorem. -/
theorem variants_of_base_variants_of_equivalent
    {firstResult firstBase secondResult secondBase : TreeSubstitution}
    {firstEquations secondEquations : List TreeEquation}
    (bases : TreeSubstitutionVariants firstBase secondBase)
    (equivalent :
      TreeUnificationEquivalent firstEquations secondEquations)
    (first :
      TreeIsRelativeMgu firstResult firstBase firstEquations)
    (second :
      TreeIsRelativeMgu secondResult secondBase secondEquations) :
    TreeSubstitutionVariants firstResult secondResult :=
  variants_of_base_variants bases (first.of_equivalent equivalent) second

end TreeIsRelativeMgu

namespace TreeFactorsThrough

/-- Extending both representatives by the same older carried state preserves
factorization.  The residual witness acts only after that shared suffix has
been applied, so no commutation or freshness premise is needed. -/
theorem appendRight
    {first second : TreeSubstitution}
    (factors : TreeFactorsThrough first second)
    (carried : TreeSubstitution) :
    TreeFactorsThrough (first ++ carried) (second ++ carried) := by
  rcases factors with ⟨residual, factor⟩
  refine ⟨residual, ?_⟩
  intro tree
  rw [TreeSubstitution.apply_append,
    TreeSubstitution.apply_append, factor]

end TreeFactorsThrough

namespace TreeSubstitutionVariants

/-- A common historical suffix does not choose between variant residual MGU
orientations. -/
theorem appendRight
    {first second : TreeSubstitution}
    (variants : TreeSubstitutionVariants first second)
    (carried : TreeSubstitution) :
    TreeSubstitutionVariants
      (first ++ carried) (second ++ carried) :=
  ⟨TreeFactorsThrough.appendRight variants.1 carried,
    TreeFactorsThrough.appendRight variants.2 carried⟩

/-- One factorization direction transports existence of a residual unifier
from the more-specific carried base to the more-general one. -/
private theorem applied_has_unifier_of_factors
    {specificBase generalBase : TreeSubstitution}
    (factors : TreeFactorsThrough specificBase generalBase)
    (equations : List TreeEquation)
    (specificHas :
      ∃ candidate,
        TreeUnifiesEquations candidate
          (TreeSubstitution.applyEquations specificBase equations)) :
    ∃ candidate,
      TreeUnifiesEquations candidate
        (TreeSubstitution.applyEquations generalBase equations) := by
  rcases specificHas with ⟨specificCandidate, specificUnifies⟩
  have cumulativeUnifies :
      TreeUnifiesEquations (specificCandidate ++ specificBase) equations :=
    (PrologMguDirectSimulation.treeUnifiesEquations_applyEquations_iff
      specificCandidate specificBase equations).1 specificUnifies
  have cumulativeFactorsGeneral :
      TreeFactorsThrough
        (specificCandidate ++ specificBase) generalBase := by
    exact TreeFactorsThrough.trans
      ⟨specificCandidate, fun tree =>
        TreeSubstitution.apply_append specificCandidate specificBase tree⟩
      factors
  rcases cumulativeFactorsGeneral with
    ⟨generalCandidate, generalFactors⟩
  refine ⟨generalCandidate, ?_⟩
  apply
    (PrologMguDirectSimulation.treeUnifiesEquations_applyEquations_iff
      generalCandidate generalBase equations).2
  intro equation member
  rw [TreeSubstitution.apply_append,
    TreeSubstitution.apply_append]
  rw [← generalFactors equation.1, ← generalFactors equation.2]
  exact cumulativeUnifies equation member

/-- Variant carried substitutions leave exactly the same residual
unification problems solvable.

This is deliberately an existence statement rather than equality of the two
normalized equation lists.  Given a residual solution over one base, compose
it with that base to obtain a cumulative solution of the original equations.
Mutual factorization then re-expresses that cumulative solution through the
other base, and the resulting residual solves the other normalized problem.
No residual-variable orientation or association-list spelling is chosen. -/
theorem applied_has_unifier_iff
    {firstBase secondBase : TreeSubstitution}
    (variants : TreeSubstitutionVariants firstBase secondBase)
    (equations : List TreeEquation) :
    (∃ candidate,
        TreeUnifiesEquations candidate
          (TreeSubstitution.applyEquations firstBase equations)) ↔
      ∃ candidate,
        TreeUnifiesEquations candidate
          (TreeSubstitution.applyEquations secondBase equations) := by
  constructor
  · exact applied_has_unifier_of_factors variants.1 equations
  · exact applied_has_unifier_of_factors variants.2 equations

end TreeSubstitutionVariants

/-- Canonical reification preserves the stored extension-before-base order
exactly, not merely after denotation. -/
theorem TreeSubstitution.reify_append
    (extension base : TreeSubstitution) :
    TreeSubstitution.reify (extension ++ base) =
      TreeSubstitution.reify extension ++
        TreeSubstitution.reify base := by
  induction extension with
  | nil =>
      rfl
  | cons entry extension inductionHypothesis =>
      rcases entry with ⟨source, replacement⟩
      simp only [List.cons_append, TreeSubstitution.reify,
        inductionHypothesis]

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

/-- Sequential residual MGUs also preserve semantic equivalence of the two
raw equation worklists.  This is the orientation-insensitive generalization
needed when one compiler lowering emits `x = y` while the independent source
stores the symmetric equation `y = x`: the resulting ordered association
lists may differ, but their cumulative solution cones coincide. -/
theorem sequential_mgu_composites_are_variants_of_equivalent
    {firstBase secondBase firstExtension secondExtension : TreeSubstitution}
    {firstEquations secondEquations : List TreeEquation}
    (bases : TreeSubstitutionVariants firstBase secondBase)
    (equivalent :
      TreeUnificationEquivalent firstEquations secondEquations)
    (firstMgu :
      TreeIsMgu firstExtension
        (TreeSubstitution.applyEquations firstBase firstEquations))
    (secondMgu :
      TreeIsMgu secondExtension
        (TreeSubstitution.applyEquations secondBase secondEquations)) :
    TreeSubstitutionVariants
      (firstExtension ++ firstBase)
      (secondExtension ++ secondBase) :=
  TreeIsRelativeMgu.variants_of_base_variants_of_equivalent bases equivalent
    (TreeIsMgu.relativeCompose firstMgu)
    (TreeIsMgu.relativeCompose secondMgu)

/-- Reversing the two operands of one equation preserves exactly the set of
finite-tree unifiers.  This theorem says nothing about which oriented
association list the deterministic ordered algorithm chooses. -/
theorem singleton_swap_unificationEquivalent (left right : Tree) :
    TreeUnificationEquivalent [(left, right)] [(right, left)] := by
  intro binding
  constructor
  · intro unifies equation member
    simp only [List.mem_singleton] at member
    subst equation
    exact (unifies (left, right) (by simp)).symm
  · intro unifies equation member
    simp only [List.mem_singleton] at member
    subst equation
    exact (unifies (right, left) (by simp)).symm

/-! ### Anti-vacuity boundary for equation equivalence -/

private def sharingWitnessX : LogicVar := .source "$sharing_x"
private def sharingWitnessY : LogicVar := .source "$sharing_y"
private def sharingWitnessA : Tree := .node (.atom "$sharing_a") []
private def sharingWitnessB : Tree := .node (.atom "$sharing_b") []
private def sharingWitnessPair (left right : Tree) : Tree :=
  .node (.compound "$sharing_pair") [left, right]

/-- Semantic equation equivalence does not erase variable sharing.

The split equation permits `X ↦ a, Y ↦ b`; the shared equation repeats `X`
and therefore cannot equal the rigid pair `(a,b)` when `a ≠ b`.  Hence the
equivalence-aware MGU transport admits operand reversal but rejects a
relation that independently renames two occurrences of the same variable. -/
theorem sharing_split_is_not_unificationEquivalent :
    ¬ TreeUnificationEquivalent
      [(sharingWitnessPair (.variable sharingWitnessX)
          (.variable sharingWitnessX),
        sharingWitnessPair sharingWitnessA sharingWitnessB)]
      [(sharingWitnessPair (.variable sharingWitnessX)
          (.variable sharingWitnessY),
        sharingWitnessPair sharingWitnessA sharingWitnessB)] := by
  intro equivalent
  let binding : TreeSubstitution :=
    [(sharingWitnessX, sharingWitnessA),
      (sharingWitnessY, sharingWitnessB)]
  have split : TreeUnifiesEquations binding
      [(sharingWitnessPair (.variable sharingWitnessX)
          (.variable sharingWitnessY),
        sharingWitnessPair sharingWitnessA sharingWitnessB)] := by
    intro equation member
    simp only [List.mem_singleton] at member
    subst equation
    simp [binding, sharingWitnessPair, sharingWitnessX, sharingWitnessY,
      sharingWitnessA, sharingWitnessB, TreeSubstitution.apply,
      Tree.instantiateOne, Trees.instantiateOne]
  have shared := (equivalent binding).2 split
  have contradiction := shared
    (sharingWitnessPair (.variable sharingWitnessX)
        (.variable sharingWitnessX),
      sharingWitnessPair sharingWitnessA sharingWitnessB) (by simp)
  simp [binding, sharingWitnessPair, sharingWitnessX, sharingWitnessY,
    sharingWitnessA, sharingWitnessB, TreeSubstitution.apply,
    Tree.instantiateOne, Trees.instantiateOne] at contradiction

/-- An ordered extension whose input equations avoid an older topological
base may be prepended without creating a cycle.  This is the topological
counterpart of relative MGU composition: the ordered solver cannot invent a
key or replacement variable outside the normalized equation support. -/
theorem OrderedTreeMgu.prepend_topological_of_equations_avoid
    {base extension : TreeSubstitution}
    {equations : List TreeEquation}
    (baseTopological : TreeSubstitutionTopological base)
    (derivation : OrderedTreeMgu equations extension)
    (equationsAvoid :
      TreeEquationsVariablesSatisfy
        (fun identity =>
          identity ∉ TreeSubstitution.keys base)
        equations) :
    TreeSubstitutionTopological (extension ++ base) := by
  exact baseTopological.append
    (PrologMguTopology.OrderedTreeMgu.binding_topological derivation)
    (orderedTreeMgu_binding_variablesSatisfy derivation equationsAvoid)

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

/-- The ordered solver genuinely chooses opposite raw aliases for the two
orientations of a variable-variable equation.  The results are unequal yet
the equivalence-aware sequential theorem recognizes them as variants. -/
theorem swapped_singleton_ordered_mgus_need_not_be_equal :
    let forward : TreeSubstitution :=
      [(sequentialX, .variable sequentialY)]
    let reverse : TreeSubstitution :=
      [(sequentialY, .variable sequentialX)]
    OrderedTreeMgu
        [(.variable sequentialX, .variable sequentialY)] forward ∧
      OrderedTreeMgu
        [(.variable sequentialY, .variable sequentialX)] reverse ∧
      TreeSubstitutionVariants forward reverse ∧
      forward ≠ reverse := by
  dsimp only
  have forward :
      OrderedTreeMgu
        [(.variable sequentialX, .variable sequentialY)]
        [(sequentialX, .variable sequentialY)] := by
    exact .cons (.variable sequentialX) (.variable sequentialY) []
      [(sequentialX, .variable sequentialY)] []
      (.bindLeft sequentialX (.variable sequentialY) (by
        simp [sequentialX, sequentialY]) (by
        simp [Tree.occurs, sequentialX, sequentialY])) .nil
  have reverse :
      OrderedTreeMgu
        [(.variable sequentialY, .variable sequentialX)]
        [(sequentialY, .variable sequentialX)] := by
    exact .cons (.variable sequentialY) (.variable sequentialX) []
      [(sequentialY, .variable sequentialX)] []
      (.bindLeft sequentialY (.variable sequentialX) (by
        simp [sequentialX, sequentialY]) (by
        simp [Tree.occurs, sequentialX, sequentialY])) .nil
  have variants :
      TreeSubstitutionVariants
        [(sequentialX, .variable sequentialY)]
        [(sequentialY, .variable sequentialX)] := by
    have cumulative :=
      sequential_mgu_composites_are_variants_of_equivalent
        (firstBase := []) (secondBase := [])
        (firstExtension := [(sequentialX, .variable sequentialY)])
        (secondExtension := [(sequentialY, .variable sequentialX)])
        (firstEquations :=
          [(.variable sequentialX, .variable sequentialY)])
        (secondEquations :=
          [(.variable sequentialY, .variable sequentialX)])
        (TreeSubstitutionVariants.refl [])
        (singleton_swap_unificationEquivalent
          (.variable sequentialX) (.variable sequentialY))
        (by simpa [TreeSubstitution.applyEquations,
            TreeSubstitution.apply, Tree.instantiateOne,
            Trees.instantiateOne] using
          forward.isMostGeneral)
        (by simpa [TreeSubstitution.applyEquations,
            TreeSubstitution.apply, Tree.instantiateOne,
            Trees.instantiateOne] using
          reverse.isMostGeneral)
    simpa using cumulative
  exact ⟨forward, reverse, variants, by
    simp [sequentialX, sequentialY]⟩

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
