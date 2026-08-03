-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologPartialCompoundProvenanceRegression
Purpose: Pin the current mixed-provenance partial/2 mismatch before repairing
  the executable representation.
Trusted boundary: none
[SPEC metta.pl:275,279; translator.pl:335-346]
-/
import PLeaTTa.Proofs.PrologRuntimeDecode

namespace PLeaTTa.PrologPartialCompoundProvenanceRegression

open Metta (Atom)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PrologRuntimeDecode

private def compiledPartial : Atom :=
  partialC "f" nilA

private def predicatePartial : Atom :=
  prologCompoundC "partial" (chainOf [.sym "f", nilA])

private def openPredicatePartial : Atom :=
  prologCompoundC "partial"
    (chainOf [.var "functor", .var "arguments"])

private def sourceIdentity (name : String) : LogicVar :=
  .source name

/-- The current executable distinguishes two encodings of the same pinned
Prolog `partial/2` term.  The decoder equality rules out a mere observation
spelling difference, while failed unification exposes the operational bug
that prevents retract/1 from selecting the clause. -/
theorem mixed_partial_provenance_decodes_equal_but_does_not_unify :
    decodeRuntimeAtom sourceIdentity compiledPartial =
        decodeRuntimeAtom sourceIdentity predicatePartial ∧
      PLeaTTa.unifyTopExact compiledPartial predicatePartial = none := by
  constructor
  · simp [compiledPartial, predicatePartial,
      decodeRuntimeAtom, RuntimeShape.ofAtom, RuntimeShape.ofAtoms,
      RuntimeShape.normalize, PLeaTTa.PrologGroundIdentity.ofGround,
      properListItems?, partialC, partialTagA, prologCompoundC,
      prologCompoundTagA, chainOf, consC, nilA]
  · unfold compiledPartial predicatePartial partialC partialTagA
      prologCompoundC prologCompoundTagA chainOf consC nilA
      PLeaTTa.unifyTopExact
    simp [Metta.Unify.unifyTopWith, Atom.size,
      Metta.Unify.unifyRoundsWith,
      Metta.Unify.decomposeAllWith, Metta.Unify.decomposeEqWith,
      Metta.Unify.decomposeListWith]

/-- The same representation split is observable before unification: dynamic
dispatch recognizes only the compiler spelling even though pinned Prolog
applies either occurrence of the same `partial/2` term. -/
theorem mixed_partial_provenance_dynamic_view_disagrees :
    partialView? compiledPartial = some ("f", nilA) ∧
      partialView? predicatePartial = none := by
  simp [compiledPartial, predicatePartial, partialView?, partialC,
    partialTagA, prologCompoundC, prologCompoundTagA, chainOf, consC, nilA]

/-- The open occurrence is a stronger discriminator than the ground probe:
the independent finite-tree algebra has an ordered MGU binding both fields,
whereas the current executable rejects before either binding is visible. -/
theorem open_partial_provenance_has_source_mgu_but_no_runtime_mgu :
    (∃ binding,
      OrderedTreeMgu
        [(decodeRuntimeAtom sourceIdentity compiledPartial,
          decodeRuntimeAtom sourceIdentity openPredicatePartial)] binding) ∧
      PLeaTTa.unifyTopExact compiledPartial openPredicatePartial = none := by
  constructor
  · apply OrderedTreeMgu.complete
      [(.source "functor", .node (.atom "f") []),
       (.source "arguments", .node .nil [])]
    intro equation member
    simp only [List.mem_singleton] at member
    subst equation
    simp only [compiledPartial, openPredicatePartial]
    simp [sourceIdentity, decodeRuntimeAtom, RuntimeShape.ofAtom,
      RuntimeShape.ofAtoms, RuntimeShape.normalize,
      PLeaTTa.PrologGroundIdentity.ofGround, properListItems?, partialC,
      partialTagA, prologCompoundC, prologCompoundTagA, chainOf, consC,
      nilA,
      TreeSubstitution.apply, Tree.instantiateOne, Trees.instantiateOne]
  · unfold compiledPartial openPredicatePartial partialC partialTagA
      prologCompoundC prologCompoundTagA chainOf consC nilA
      PLeaTTa.unifyTopExact
    simp [Metta.Unify.unifyTopWith, Atom.size,
      Metta.Unify.unifyRoundsWith,
      Metta.Unify.decomposeAllWith, Metta.Unify.decomposeEqWith,
      Metta.Unify.decomposeListWith]

end PLeaTTa.PrologPartialCompoundProvenanceRegression
