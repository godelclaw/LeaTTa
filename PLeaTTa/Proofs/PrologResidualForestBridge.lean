-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologResidualForestBridge
Purpose: Materialize an ordered supported term forest through one shared
  residual-MGU alpha rather than independent per-leaf witnesses
Trusted boundary: none
Main exports: TaskDataAgrees.runtimeTermsAgreesWith
-/
import PLeaTTa.Proofs.PrologFindallBagAlphaBridge

namespace PLeaTTa.PrologResidualForestBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.OpenSubstitution
open PrologFindallBagAlphaBridge
open PrologFindallCopyBridge
open PrologMguVariant
open PrologMguVariantRenaming
open PrologOrdinaryStepBridge
open PrologPrefilterBridge
open PrologRecursiveCallPayloadBridge
open PrologStateBridge

/-!
Applying `runtimeTermAgrees_of_variants` independently to every term is too
weak for a continuation: each leaf may choose a different finite alpha and
therefore forget sharing between distinct goal fields.  This module packages
the complete ordered term forest as one proper-list tree, obtains one mutual
instance renaming for that tree, and only then projects the shared relation
back to its leaves.
-/

/-- Canonical substitution distributes through the ordinary proper-list
tree constructor without changing order or multiplicity. -/
theorem TreeSubstitution.apply_prologList_none
    (binding : TreeSubstitution) :
    ∀ trees : List Tree,
      TreeSubstitution.apply binding (Tree.prologList trees none) =
        Tree.prologList (trees.map (TreeSubstitution.apply binding)) none
  | [] => by
      simp [Tree.prologList]
  | head :: tail => by
      simp [Tree.prologList,
        TreeSubstitution.apply_prologList_none binding tail]

/-- Ordered source substitution commutes with canonical denotation. -/
theorem Substitution.denote_applyTerms
    (binding : Substitution) : ∀ terms : List Term,
    Terms.denote (binding.applyTerms terms) =
      (Terms.denote terms).map
        (TreeSubstitution.apply (Substitution.denote binding))
  | [] => by
      rw [OpenSubstitution.Substitution.applyTerms_empty]
      rfl
  | head :: tail => by
      simp only [Substitution.applyTerms_cons, Terms.denote,
        List.map_cons]
      rw [Substitution.denote_applyTerm,
        Substitution.denote_applyTerms binding tail]

/-- The independent ordered denotation is ordinary pointwise mapping. -/
theorem Terms.denote_eq_map : ∀ terms : List Term,
    Terms.denote terms = terms.map Term.denote
  | [] => rfl
  | head :: tail => by
      simp only [Terms.denote, List.map_cons, Terms.denote_eq_map tail]

/-- Mapping the runtime substitution over the right side of a pointwise
canonical reading preserves its exact left order. -/
private theorem canonical_forall₂_map_runtime
    {alpha : List (LogicVar × String)} {binding : Subst} :
    ∀ {references : List Term} {executables : List Atom}
      {representative : TreeSubstitution},
      List.Forall₂
          (fun term atom =>
            CanonicalRuntimeAgrees alpha
              (TreeSubstitution.apply representative (Term.denote term))
              (PLeaTTa.subst binding atom))
          references executables →
        List.Forall₂ (CanonicalRuntimeAgrees alpha)
          (references.map fun term =>
            TreeSubstitution.apply representative (Term.denote term))
          (executables.map (PLeaTTa.subst binding))
  | _, _, _, .nil => .nil
  | _, _, _, .cons head tail =>
      .cons head (canonical_forall₂_map_runtime tail)

/-- Pointwise canonical readings induce a canonical reading of their proper
list wrapper.  Every pointwise step remains present in the same order. -/
theorem CanonicalRuntimeAgrees.prologList_of_forall₂
    {alpha : List (LogicVar × String)} :
    ∀ {trees : List Tree} {atoms : List Atom},
      List.Forall₂ (CanonicalRuntimeAgrees alpha) trees atoms →
        CanonicalRuntimeAgrees alpha
          (Tree.prologList trees none) (chainOf atoms)
  | _, _, .nil => by
      simpa [Tree.prologList, chainOf] using
        (CanonicalRuntimeAgrees.nil (alpha := alpha))
  | _, _, .cons head tail => by
      simpa [Tree.prologList, chainOf] using
        (CanonicalRuntimeAgrees.cons head
          (CanonicalRuntimeAgrees.prologList_of_forall₂ tail))

/-- A canonical reading of one literal proper-list pair exposes the ordered
pointwise readings under the same alpha.  This is the non-laundering inverse
of `prologList_of_forall₂`: no leaf may choose a private alpha. -/
theorem CanonicalRuntimeAgrees.forall₂_of_prologList :
    ∀ {alpha : List (LogicVar × String)}
      {terms : List Term} {atoms : List Atom},
      CanonicalRuntimeAgrees alpha
          (Term.denote (.list terms none)) (chainOf atoms) →
        List.Forall₂
          (fun term atom =>
            CanonicalRuntimeAgrees alpha (Term.denote term) atom)
          terms atoms
  | _, [], [], agreement => by
      exact .nil
  | _, [], _ :: _, agreement => by
      cases agreement
  | _, _ :: _, [], agreement => by
      cases agreement
  | _, head :: tail, atom :: atoms, agreement => by
      cases agreement with
      | cons headAgreement tailAgreement =>
          exact .cons headAgreement
            (CanonicalRuntimeAgrees.forall₂_of_prologList tailAgreement)

/-- One cumulative residual representative materializes a complete ordered
term forest under one finite runtime alpha.

The result is strictly stronger than `List.Forall₂ RuntimeTermAgrees`:
sharing between variables occurring in different list positions remains
observable in the single `RuntimeAlpha.graph`. -/
theorem TaskDataAgrees.runtimeTermsAgreesWith
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Subst}
    (data :
      TaskDataAgrees alpha support canonical referenceBase current runtime)
    {references : List Term} {executables : List Atom}
    (leaves : AlphaTermsAgree alpha references executables)
    (supported : AlphaTermsSupported alpha support references) :
    ∃ referenceSupport executableSupport,
      RuntimeTermsAgreesWith referenceSupport executableSupport
        (current.applyTerms references)
        (executables.map (PLeaTTa.subst runtime)) := by
  obtain ⟨representative, cumulative⟩ := data.valuation.existsWith
  have runtimeLeaves :=
    PLeaTTa.PrologRecursiveCallPayloadBridge.AlphaCumulativeResidualVariantAgreesOnWith.applyTerms
      cumulative leaves supported
  have runtimeTrees :
      List.Forall₂ (CanonicalRuntimeAgrees alpha)
        (references.map fun term =>
          TreeSubstitution.apply
            (representative ++ Substitution.denote referenceBase)
            (Term.denote term))
        (executables.map (PLeaTTa.subst runtime)) :=
    canonical_forall₂_map_runtime runtimeLeaves
  have runtimeList :
      CanonicalRuntimeAgrees alpha
        (TreeSubstitution.apply
          (representative ++ Substitution.denote referenceBase)
          (Term.denote (.list references none)))
        (chainOf (executables.map (PLeaTTa.subst runtime))) := by
    rw [Term.denote]
    rw [TreeSubstitution.apply_prologList_none]
    have treesEq :
        (Terms.denote references).map
            (TreeSubstitution.apply
              (representative ++ Substitution.denote referenceBase)) =
          references.map fun term =>
            TreeSubstitution.apply
              (representative ++ Substitution.denote referenceBase)
              (Term.denote term) := by
      simp [Terms.denote_eq_map, List.map_map]
    rw [treesEq]
    exact CanonicalRuntimeAgrees.prologList_of_forall₂ runtimeTrees
  obtain ⟨forward, backward, pairs, witness⟩ :=
    TreeSubstitutionVariants.apply_has_mutualInstanceRenaming
      cumulative.variants (Term.denote (.list references none))
  let referenceSupport := mutualInstanceReferenceSupport pairs
  let executableSupport := mutualInstanceExecutableSupport alpha pairs
  have sharedAlpha : RuntimeAlpha referenceSupport executableSupport := by
    exact mutualInstance_runtimeAlpha witness data.alphaShared runtimeList
  have materializedList :
      CanonicalRuntimeAgrees
        (RuntimeAlpha.graph referenceSupport executableSupport)
        (Term.denote (.list (current.applyTerms references) none))
        (chainOf (executables.map (PLeaTTa.subst runtime))) := by
    have transported :=
      canonicalRuntimeAgrees_of_mutualInstanceRenaming
        witness data.alphaShared runtimeList
    have currentDenotes :
        Substitution.denote current =
          canonical ++ Substitution.denote referenceBase :=
      data.denoteCurrent
    have listDenotes :
        Term.denote (.list (current.applyTerms references) none) =
          TreeSubstitution.apply
            (canonical ++ Substitution.denote referenceBase)
            (Term.denote (.list references none)) := by
      rw [← currentDenotes]
      simp only [Term.denote]
      rw [TreeSubstitution.apply_prologList_none,
        Substitution.denote_applyTerms]
    rw [listDenotes]
    exact transported
  exact
    ⟨referenceSupport, executableSupport, sharedAlpha,
      CanonicalRuntimeAgrees.forall₂_of_prologList materializedList⟩

/-- One shared forest alpha preserves aliasing *between* positions.

The positive half inhabits the relation with two occurrences of one source
variable and one runtime name.  The negative half rejects the same source
forest when the two occurrences are spuriously separated onto distinct
runtime names.  A per-leaf existential relation would accept both. -/
theorem shared_forest_alias_is_preserved :
    let identity : LogicVar := .source "shared"
    let references : List Term :=
      [.variable identity, .variable identity]
    RuntimeTermsAgrees references [.var "same", .var "same"] ∧
      ¬ RuntimeTermsAgrees references [.var "left", .var "right"] := by
  let identity : LogicVar := .source "shared"
  let references : List Term :=
    [.variable identity, .variable identity]
  have alpha : RuntimeAlpha [identity] ["same"] :=
    ⟨rfl, by simp, by simp⟩
  have linked :
      (identity, "same") ∈ RuntimeAlpha.graph [identity] ["same"] := by
    simp [RuntimeAlpha.graph]
  constructor
  · exact
      ⟨[identity], ["same"],
        ⟨alpha,
          .cons (.variable linked) (.cons (.variable linked) .nil)⟩⟩
  · rintro ⟨referenceSupport, executableSupport, agreement⟩
    have shared := agreement.shared
    cases agreement.terms with
    | cons first tail =>
        cases tail with
        | cons second empty =>
            cases first with
            | «variable» firstLinked =>
                cases second with
                | «variable» secondLinked =>
                    have sameName := shared.forward firstLinked secondLinked
                    exact (by decide : ("left" : String) ≠ "right") sameName

end PLeaTTa.PrologResidualForestBridge
