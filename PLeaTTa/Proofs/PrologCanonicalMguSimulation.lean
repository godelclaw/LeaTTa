-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologCanonicalMguSimulation
Purpose: Run the certified executable unifier directly from source-guided
  canonical-tree/runtime agreement, without decoding runtime atoms or
  re-syntaxing canonical trees as source terms.
Trusted boundary: none
Main exports:
  CanonicalRuntimePair.canonicalFuelLe,
  OrderedTreeMgu.unifyTopExact_exists_canonical_alpha_mgu
-/
import PLeaTTa.Proofs.PrologMguDirectSimulation

namespace PLeaTTa.PrologCanonicalMguSimulation

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PrologMguBridge
open PrologMguDirectSimulation
open PrologMguOpenAgreement
open PrologMguTopology
open PrologPrefilterBridge

/-!
The direct executable-MGU simulation was originally exposed only through
`SharedAlphaEquationsAgree`, whose canonical side is a list of source
`Term`s.  Ordinary task execution already has substituted canonical trees.
Converting those trees back through source syntax would require a global
inverse for ambiguous runtime encodings such as `True`, exactly the
source-guidedness restriction the proof architecture avoids.

This module exposes the canonical core already used internally.  It accepts
one canonical equation and its two runtime atoms under a shared alpha graph,
proves the same structural fuel bound, and invokes the existing flattened
Robinson-round simulation directly.
-/

namespace CanonicalRuntimePair

/-- One canonical equation contains no more distinct variables than the
structural fuel of its two aligned executable atoms. -/
theorem canonicalFuelLe
    {alpha : List (LogicVar × String)}
    {leftTree rightTree : Tree} {leftAtom rightAtom : Atom}
    (left :
      CanonicalRuntimeAgrees alpha leftTree leftAtom)
    (right :
      CanonicalRuntimeAgrees alpha rightTree rightAtom) :
    (treeEquationsLogicVariables [(leftTree, rightTree)]).eraseDups.length ≤
      leftAtom.size + rightAtom.size := by
  have dedupBound :=
    logicVar_eraseDups_length_le
      (treeEquationsLogicVariables [(leftTree, rightTree)])
  have leftVariables :=
    treeLogicVariables_length_le_weight leftTree
  have rightVariables :=
    treeLogicVariables_length_le_weight rightTree
  have leftRuntime :=
    PLeaTTa.PrologMguDirectSimulation.CanonicalRuntimeAgrees.weight_le_size
      left
  have rightRuntime :=
    PLeaTTa.PrologMguDirectSimulation.CanonicalRuntimeAgrees.weight_le_size
      right
  have variablesExact :
      treeEquationsLogicVariables [(leftTree, rightTree)] =
        treeLogicVariables leftTree ++ treeLogicVariables rightTree := by
    simp [treeEquationsLogicVariables]
  rw [variablesExact] at dedupBound ⊢
  simp only [List.length_append] at dedupBound
  omega

end CanonicalRuntimePair

/-- A canonical ordered MGU over one source-guided runtime equation forces
the actual executable top-level unifier to succeed.  The returned
association list is related to a verified flattened canonical spelling;
association-list orientation is deliberately not identified with
`canonical`. -/
theorem OrderedTreeMgu.unifyTopExact_exists_canonical_alpha
    {alpha : List (LogicVar × String)}
    {leftTree rightTree : Tree} {leftAtom rightAtom : Atom}
    {canonical : TreeSubstitution}
    (shared : SharedRuntimeAlpha alpha)
    (left :
      CanonicalRuntimeAgrees alpha leftTree leftAtom)
    (right :
      CanonicalRuntimeAgrees alpha rightTree rightAtom)
    (derivation :
      OrderedTreeMgu [(leftTree, rightTree)] canonical) :
    ∃ flattened runtimeResult,
      TreeUnifyRounds
        (leftAtom.size + rightAtom.size)
        [(leftTree, rightTree)] [] flattened ∧
      PLeaTTa.unifyTopExact leftAtom rightAtom = some runtimeResult ∧
      AlphaTreeSubstitutionAgrees alpha flattened runtimeResult := by
  obtain ⟨flattened, smallRounds⟩ :=
    PLeaTTa.PrologMguDirectSimulation.OrderedTreeMgu.treeUnifyRounds_exists
      derivation
  have rounds :
      TreeUnifyRounds
        (leftAtom.size + rightAtom.size)
        [(leftTree, rightTree)] [] flattened :=
    smallRounds.mono
      (CanonicalRuntimePair.canonicalFuelLe left right)
  have equationsAgreement :
      AlphaTreeEquationsAgree alpha
        [(leftTree, rightTree)] [(leftAtom, rightAtom)] :=
    .cons ⟨left, right⟩ .nil
  obtain ⟨runtimeResult, runtimeExact, runtimeAgreement⟩ :=
    rounds.runtime shared equationsAgreement
      (AlphaTreeSubstitutionAgrees.nil (alpha := alpha))
  refine ⟨flattened, runtimeResult, rounds, ?_, runtimeAgreement⟩
  exact runtimeExact

/-- Canonical one-pair simulation with the full semantic result contract:
the generated executable result is acyclic, has a source-guided open
valuation, is most-general, and its canonical spelling is a mutual
factorization variant of the independently ordered MGU. -/
theorem OrderedTreeMgu.unifyTopExact_exists_canonical_alpha_mgu
    {alpha : List (LogicVar × String)}
    {leftTree rightTree : Tree} {leftAtom rightAtom : Atom}
    {canonical : TreeSubstitution}
    (shared : SharedRuntimeAlpha alpha)
    (left :
      CanonicalRuntimeAgrees alpha leftTree leftAtom)
    (right :
      CanonicalRuntimeAgrees alpha rightTree rightAtom)
    (derivation :
      OrderedTreeMgu [(leftTree, rightTree)] canonical) :
    ∃ flattened runtimeResult,
      PLeaTTa.unifyTopExact leftAtom rightAtom = some runtimeResult ∧
      AlphaTreeSubstitutionAgrees alpha flattened runtimeResult ∧
      TreeSubstitutionTopological flattened ∧
      Nonempty (PLeaTTa.SubstTopological runtimeResult) ∧
      AlphaValuationAgrees alpha flattened runtimeResult ∧
      TreeIsMgu flattened [(leftTree, rightTree)] ∧
      TreeFactorsThrough flattened canonical ∧
      TreeFactorsThrough canonical flattened := by
  obtain
    ⟨flattened, runtimeResult, rounds, runtimeExact, runtimeAgreement⟩ :=
    PLeaTTa.PrologCanonicalMguSimulation.OrderedTreeMgu.unifyTopExact_exists_canonical_alpha
      shared left right derivation
  have flattenedMgu :
      TreeIsMgu flattened [(leftTree, rightTree)] :=
    rounds.isMostGeneral
  have canonicalMgu :
      TreeIsMgu canonical [(leftTree, rightTree)] :=
    derivation.isMostGeneral
  have flattenedTopological :
      TreeSubstitutionTopological flattened :=
    rounds.result_topological TreeSubstitutionTopological.nil
  have runtimeTopological :
      PLeaTTa.SubstTopological runtimeResult :=
    AlphaTreeSubstitutionAgrees.runtime_topological
      shared runtimeAgreement flattenedTopological
  have flattenedValuation :
      AlphaValuationAgrees alpha flattened runtimeResult :=
    AlphaTreeSubstitutionAgrees.valuation
      shared runtimeAgreement flattenedTopological
  exact
    ⟨flattened, runtimeResult, runtimeExact, runtimeAgreement,
      flattenedTopological, ⟨runtimeTopological⟩, flattenedValuation,
      flattenedMgu,
      canonicalMgu.2 flattened flattenedMgu.1,
      flattenedMgu.2 canonical canonicalMgu.1⟩

end PLeaTTa.PrologCanonicalMguSimulation
