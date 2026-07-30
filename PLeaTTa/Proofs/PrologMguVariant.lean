-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologMguVariant
Purpose: Quotient residual MGU orientation by semantic mutual instantiation,
  while retaining exact executable valuation on observable alpha support.
Trusted boundary: none
Main exports:
  TreeSubstitutionVariants,
  AlphaResidualVariantAgreesOn,
  OrderedTreeMgu.unifyTopExact_exists_residual_variant
-/
import PLeaTTa.Proofs.PrologMguDirectSimulation

namespace PLeaTTa.PrologMguVariant

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PrologMguBridge
open PrologMguOpenAgreement
open PrologMguTopology
open PrologMguDirectSimulation
open PrologPrefilterBridge
open PrologStateBridge

/-! ## Semantic residual variants

The ordered source MGU and the executable worklist MGU can orient a residual
alias in opposite directions.  Equality of their association lists is
therefore false even when both are principal solutions.  Mutual
instantiation is the representation-independent invariant: each
substitution denotes an instance of the other over every finite canonical
tree.  No answer-set, grounding, or association-list quotient is used.
-/

/-- Two canonical substitutions are residual variants when each factors
through the other.  This is the semantic mutual-instantiation
characterization; it deliberately does not claim identical list spelling. -/
def TreeSubstitutionVariants
    (first second : TreeSubstitution) : Prop :=
  TreeFactorsThrough first second ∧
    TreeFactorsThrough second first

namespace TreeFactorsThrough

/-- Every canonical substitution factors through itself. -/
theorem refl (binding : TreeSubstitution) :
    TreeFactorsThrough binding binding := by
  exact ⟨[], fun _ => rfl⟩

/-- Canonical factorization composes in the same order as sequential
substitution application. -/
theorem trans
    {first second third : TreeSubstitution}
    (firstSecond : TreeFactorsThrough first second)
    (secondThird : TreeFactorsThrough second third) :
    TreeFactorsThrough first third := by
  rcases firstSecond with ⟨firstResidual, firstFactors⟩
  rcases secondThird with ⟨secondResidual, secondFactors⟩
  refine ⟨firstResidual ++ secondResidual, ?_⟩
  intro tree
  rw [firstFactors tree, secondFactors tree,
    TreeSubstitution.apply_append]

/-- Applying a more-specific substitution preserves every equation unified
by the more-general substitution. -/
theorem unifies
    {specific general : TreeSubstitution}
    (factors : TreeFactorsThrough specific general)
    {equations : List TreeEquation}
    (generalUnifies : TreeUnifiesEquations general equations) :
    TreeUnifiesEquations specific equations := by
  rcases factors with ⟨residual, factor⟩
  intro equation member
  rw [factor equation.1, factor equation.2,
    generalUnifies equation member]

end TreeFactorsThrough

namespace TreeSubstitutionVariants

/-- Residual variation is reflexive. -/
theorem refl (binding : TreeSubstitution) :
    TreeSubstitutionVariants binding binding :=
  ⟨TreeFactorsThrough.refl binding,
    TreeFactorsThrough.refl binding⟩

/-- Residual variation is symmetric by construction. -/
theorem symm
    {first second : TreeSubstitution}
    (variants : TreeSubstitutionVariants first second) :
    TreeSubstitutionVariants second first :=
  ⟨variants.2, variants.1⟩

/-- Residual variation is transitive, so intermediate verified
representatives can be hidden without weakening the relation. -/
theorem trans
    {first second third : TreeSubstitution}
    (firstSecond : TreeSubstitutionVariants first second)
    (secondThird : TreeSubstitutionVariants second third) :
    TreeSubstitutionVariants first third :=
  ⟨TreeFactorsThrough.trans firstSecond.1 secondThird.1,
    TreeFactorsThrough.trans secondThird.2 firstSecond.2⟩

/-- Residual variants unify exactly the same ordered finite-tree
equations. -/
theorem unifies_iff
    {first second : TreeSubstitution}
    (variants : TreeSubstitutionVariants first second)
    (equations : List TreeEquation) :
    TreeUnifiesEquations first equations ↔
      TreeUnifiesEquations second equations := by
  constructor
  · exact TreeFactorsThrough.unifies variants.2
  · exact TreeFactorsThrough.unifies variants.1

end TreeSubstitutionVariants

/-- Any two MGUs of one canonical equation list are residual variants. -/
theorem TreeIsMgu.variants
    {equations : List TreeEquation}
    {first second : TreeSubstitution}
    (firstMgu : TreeIsMgu first equations)
    (secondMgu : TreeIsMgu second equations) :
    TreeSubstitutionVariants first second :=
  ⟨secondMgu.2 first firstMgu.1,
    firstMgu.2 second secondMgu.1⟩

/-! ## Ground observations erase only residual names -/

/-- A canonical tree is ground when no logical variable can occur in it. -/
def TreeGround (tree : Tree) : Prop :=
  TreeVariablesSatisfy (fun _ => False) tree

/-- Every canonical substitution leaves a ground tree literally unchanged. -/
theorem TreeGround.apply_eq_self
    {tree : Tree} (ground : TreeGround tree)
    (binding : TreeSubstitution) :
    TreeSubstitution.apply binding tree = tree := by
  exact
    TreeSubstitution.apply_eq_self_of_variables_outside
      (TreeVariablesSatisfy.mono
        (fun _ impossible => False.elim impossible)
        ground)

/-- If the first image is ground, residual variants give exactly the same
image, not merely another instance. -/
theorem TreeSubstitutionVariants.apply_eq_of_first_ground
    {first second : TreeSubstitution}
    (variants : TreeSubstitutionVariants first second)
    (tree : Tree)
    (ground : TreeGround (TreeSubstitution.apply first tree)) :
    TreeSubstitution.apply first tree =
      TreeSubstitution.apply second tree := by
  rcases variants.2 with ⟨residual, factor⟩
  calc
    TreeSubstitution.apply first tree =
        TreeSubstitution.apply residual
          (TreeSubstitution.apply first tree) :=
      (ground.apply_eq_self residual).symm
    _ = TreeSubstitution.apply second tree :=
      (factor tree).symm

/-- Symmetric ground-collapse form. -/
theorem TreeSubstitutionVariants.apply_eq_of_second_ground
    {first second : TreeSubstitution}
    (variants : TreeSubstitutionVariants first second)
    (tree : Tree)
    (ground : TreeGround (TreeSubstitution.apply second tree)) :
    TreeSubstitution.apply first tree =
      TreeSubstitution.apply second tree := by
  rcases variants.1 with ⟨residual, factor⟩
  calc
    TreeSubstitution.apply first tree =
        TreeSubstitution.apply residual
          (TreeSubstitution.apply second tree) :=
      factor tree
    _ = TreeSubstitution.apply second tree :=
      ground.apply_eq_self residual

/-! ## Support-indexed executable agreement -/

/-- A canonical MGU and an executable substitution agree through one
topological residual representative.  The full alpha graph interprets
residual variables; `support` names only variables observable by the current
continuation.  The representative is existential so neither its orientation
nor its association-list spelling becomes observable. -/
def AlphaResidualVariantAgreesOn
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (runtime : Subst) : Prop :=
  ∃ representative : TreeSubstitution,
    TreeSubstitutionVariants canonical representative ∧
    TreeSubstitutionTopological canonical ∧
    TreeSubstitutionTopological representative ∧
    TreeSubstitutionVariablesSatisfy
      (AlphaCovers alpha) representative ∧
    Nonempty (PLeaTTa.SubstTopological runtime) ∧
    AlphaValuationAgreesOn alpha support representative runtime

/-- Full-support residual-variant agreement. -/
def AlphaResidualVariantAgrees
    (alpha : List (LogicVar × String))
    (canonical : TreeSubstitution) (runtime : Subst) : Prop :=
  AlphaResidualVariantAgreesOn alpha alpha canonical runtime

/-- Full residual-variant agreement restricts to any observable subgraph. -/
theorem AlphaResidualVariantAgrees.on
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {runtime : Subst}
    (agreement :
      AlphaResidualVariantAgrees alpha canonical runtime)
    (included : ∀ pair, pair ∈ support → pair ∈ alpha) :
    AlphaResidualVariantAgreesOn alpha support canonical runtime := by
  rcases agreement with
    ⟨representative, variants, canonicalTopological,
      representativeTopological, representativeCovered,
      runtimeTopological, valuation⟩
  exact
    ⟨representative, variants, canonicalTopological,
      representativeTopological, representativeCovered,
      runtimeTopological,
      AlphaValuationAgrees.on valuation included⟩

/-- Liveness trimming preserves residual-variant agreement on exactly the
observed support.  The canonical variant relation is unchanged; only the
acyclic executable spelling is filtered. -/
theorem AlphaResidualVariantAgreesOn.trimFor
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {runtime : Subst}
    (agreement :
      AlphaResidualVariantAgreesOn alpha support canonical runtime)
    {goals : List PLeaTTa.Goal} {qterm : Atom}
    (live : AlphaRuntimeNamesLive support goals qterm) :
    AlphaResidualVariantAgreesOn alpha support canonical
      (PLeaTTa.trimFor goals qterm runtime) := by
  rcases agreement with
    ⟨representative, variants, canonicalTopological,
      representativeTopological, representativeCovered,
      ⟨runtimeTopological⟩, valuation⟩
  exact
    ⟨representative, variants, canonicalTopological,
      representativeTopological, representativeCovered,
      ⟨PLeaTTa.SubstTopological.trimFor
        goals qterm runtime runtimeTopological⟩,
      AlphaValuationAgreesOn.trimFor valuation runtimeTopological live⟩

/-- Residual-variant agreement lifts any supported source/runtime term
through the hidden representative.  Answer content is still generated by
the certified substitution; the theorem does not ask an oracle to choose a
renaming. -/
theorem AlphaResidualVariantAgrees.apply
    {alpha : List (LogicVar × String)}
    {canonical : TreeSubstitution} {runtime : Subst}
    (agreement :
      AlphaResidualVariantAgrees alpha canonical runtime)
    {tree : Tree} {atom : Atom}
    (termAgreement : CanonicalRuntimeAgrees alpha tree atom) :
    ∃ representative,
      TreeSubstitutionVariants canonical representative ∧
      CanonicalRuntimeAgrees alpha
        (TreeSubstitution.apply representative tree)
        (PLeaTTa.subst runtime atom) := by
  rcases agreement with
    ⟨representative, variants, _canonicalTopological,
      _representativeTopological, _representativeCovered,
      _runtimeTopological, valuation⟩
  exact
    ⟨representative, variants,
      canonicalRuntimeAgrees_apply termAgreement valuation⟩

/-- On a ground canonical observation the existential representative
disappears and residual-variant agreement becomes exact canonical/runtime
agreement. -/
theorem AlphaResidualVariantAgrees.apply_of_canonical_ground
    {alpha : List (LogicVar × String)}
    {canonical : TreeSubstitution} {runtime : Subst}
    (agreement :
      AlphaResidualVariantAgrees alpha canonical runtime)
    {tree : Tree} {atom : Atom}
    (termAgreement : CanonicalRuntimeAgrees alpha tree atom)
    (ground : TreeGround (TreeSubstitution.apply canonical tree)) :
    CanonicalRuntimeAgrees alpha
      (TreeSubstitution.apply canonical tree)
      (PLeaTTa.subst runtime atom) := by
  rcases agreement.apply termAgreement with
    ⟨representative, variants, representativeAgreement⟩
  rw [variants.apply_eq_of_first_ground tree ground]
  exact representativeAgreement

/-! ## Direct executable construction -/

/-- The real executable unifier is related to the independently ordered MGU
by one support-complete residual variant.  Both canonical representatives
are topological, the runtime result is acyclic, and ground observations agree
exactly. -/
theorem OrderedTreeMgu.unifyTopExact_exists_residual_variant
    {alpha : List (LogicVar × String)}
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    {canonical : TreeSubstitution}
    (shared : SharedRuntimeAlpha alpha)
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    (derivation :
      OrderedTreeMgu (denoteEquations equations) canonical) :
    ∃ runtimeResult,
      PLeaTTa.unifyTopExact
          (.expr leftAtoms) (.expr rightAtoms) =
        some runtimeResult ∧
      AlphaResidualVariantAgrees alpha canonical runtimeResult := by
  rcases
    PLeaTTa.PrologMguDirectSimulation.OrderedTreeMgu.unifyTopExact_exists_alpha_mgu
      shared agreement derivation with
    ⟨representative, runtimeResult, runtimeExact, representativeAgreement,
      representativeTopological, runtimeTopological, valuation,
      _representativeMgu, representativeFactorsCanonical,
      canonicalFactorsRepresentative⟩
  have canonicalTopological :
      TreeSubstitutionTopological canonical :=
    PrologMguTopology.OrderedTreeMgu.binding_topological derivation
  exact
    ⟨runtimeResult, runtimeExact,
      ⟨representative,
        ⟨canonicalFactorsRepresentative,
          representativeFactorsCanonical⟩,
        canonicalTopological, representativeTopological,
        representativeAgreement.variablesSatisfy,
        runtimeTopological, valuation⟩⟩

/-! ## Anti-vacuity: orientation is genuinely quotiented -/

private def variantLeft : LogicVar := .source "left"
private def variantRight : LogicVar := .source "right"

/-- Two unequal association lists can be MGUs of the same equation and hence
residual variants.  This prevents the semantic relation from degenerating
back into syntactic equality. -/
theorem residual_variants_need_not_be_equal :
    ∃ first second : TreeSubstitution,
      TreeSubstitutionVariants first second ∧
      first ≠ second := by
  let first : TreeSubstitution :=
    [(variantLeft, .variable variantRight)]
  let second : TreeSubstitution :=
    [(variantRight, .variable variantLeft)]
  have leftMgu :
      TreeIsMgu first
        [(.variable variantLeft, .variable variantRight)] := by
    exact tree_singleton_variable_is_mgu
      variantLeft (.variable variantRight) (by
        simp [Tree.occurs, variantLeft, variantRight])
  have rightMgu :
      TreeIsMgu second
        [(.variable variantLeft, .variable variantRight)] := by
    exact tree_singleton_right_variable_is_mgu
      (.variable variantLeft) variantRight (by
        simp [Tree.occurs, variantLeft, variantRight])
  refine
    ⟨first, second,
      PLeaTTa.PrologMguVariant.TreeIsMgu.variants leftMgu rightMgu, ?_⟩
  simp [first, second, variantLeft, variantRight]

end PLeaTTa.PrologMguVariant
