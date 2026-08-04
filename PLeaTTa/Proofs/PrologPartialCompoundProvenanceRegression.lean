-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologPartialCompoundProvenanceRegression
Purpose: Pin the repaired compiler/Predicate partial/2 runtime identity and
  the corresponding ground/open unification behavior.
Trusted boundary: none
[SPEC metta.pl:275,279; translator.pl:335-346]
-/
import PLeaTTa.Proofs.PrologRuntimeDecode
import PLeaTTa.Proofs.PredicateAdequacy
import PLeaTTa.Proofs.Specialize

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

private def malformedPredicatePartial : Atom :=
  prologCompoundC "partial" (chainOf [.sym "f", .sym "malformed"])

private def ordinaryPredicateCompound : Atom :=
  prologCompoundC "probe" (chainOf [.sym "value"])

private def oneFieldPartialCompound : Atom :=
  prologCompoundC "partial" (chainOf [.sym "only-one-field"])

private def threeFieldPartialCompound : Atom :=
  prologCompoundC "partial" (chainOf [.sym "one", .sym "two", .sym "three"])

private def sourcePartialList : Atom :=
  chainOf [.sym "partial", .sym "f", nilA]

private def sourceIdentity (name : String) : LogicVar :=
  .source name

/-- Compiler and `Predicate/2` construction now produce the same raw atom.
The empty unifier is therefore reflexive for the right reason: exact runtime
identity, not a decoder quotient over two incompatible encodings. -/
theorem compiler_and_predicate_partial_are_identical :
    compiledPartial = predicatePartial ∧
      decodeRuntimeAtom sourceIdentity compiledPartial =
        decodeRuntimeAtom sourceIdentity predicatePartial ∧
      PLeaTTa.unifyTopExact compiledPartial predicatePartial = some [] := by
  have identity : compiledPartial = predicatePartial := by
    rfl
  exact ⟨identity, congrArg (decodeRuntimeAtom sourceIdentity) identity,
    identity ▸ PLeaTTa.unifyTopExact_self predicatePartial⟩

/-- Dynamic dispatch recognizes the exact arity-two value regardless of
whether the compiler or `Predicate/2` produced it. -/
theorem compiler_and_predicate_partial_dynamic_views_agree :
    partialView? compiledPartial = some ("f", nilA) ∧
      partialView? predicatePartial = some ("f", nilA) := by
  simp [compiledPartial, predicatePartial, partialView?, partialC,
    prologCompoundC, prologCompoundTagA, chainOf, consC, nilA]

/-- The open occurrence is the stronger parity witness: both the independent
finite-tree algebra and the executable expose the two field bindings, in the
executable's exact elimination order. -/
theorem open_partial_provenance_has_source_and_runtime_mgu :
    (∃ binding,
      OrderedTreeMgu
        [(decodeRuntimeAtom sourceIdentity compiledPartial,
          decodeRuntimeAtom sourceIdentity openPredicatePartial)] binding) ∧
      PLeaTTa.unifyTopExact compiledPartial openPredicatePartial =
        some [("arguments", nilA), ("functor", .sym "f")] := by
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
      prologCompoundC, prologCompoundTagA, chainOf, consC, nilA,
      TreeSubstitution.apply, Tree.instantiateOne, Trees.instantiateOne]
  · unfold compiledPartial openPredicatePartial partialC
      prologCompoundC prologCompoundTagA chainOf consC nilA
      PLeaTTa.unifyTopExact
    simp [Metta.Unify.unifyTopWith, Atom.size,
      Metta.Unify.unifyRoundsWith,
      Metta.Unify.decomposeAllWith, Metta.Unify.decomposeEqWith,
      Metta.Unify.decomposeListWith, Metta.Subst.occurs,
      Metta.Subst.apply, Metta.Subst.lookup, Metta.Subst.extend,
      Metta.Subst.erase]

/-- The ordinary `partial/2` representation preserves a malformed second
field at the surface, but its bound-argument view is not a proper list. -/
theorem malformed_partial_surface_and_append_boundary :
    malformedPredicatePartial = partialC "f" (.sym "malformed") ∧
      partialView? malformedPredicatePartial =
        some ("f", .sym "malformed") ∧
      chainListM (.sym "malformed") = none ∧
      unchainify 10000 malformedPredicatePartial =
        .expr [.sym "partial", .sym "f", .sym "malformed"] := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · have rendered :=
      PLeaTTa.PredicateAdequacy.unchainify_compound 9999 "partial"
        [.sym "f", .sym "malformed"]
    norm_num at rendered
    simpa only [malformedPredicatePartial] using rendered

/-- Dynamic application of the malformed value takes the executable failure
transition.  This rules out the historical `getD []` behavior that invented
an empty bound prefix and called `f/1`. -/
theorem malformed_partial_application_fails
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable) (fuel : Nat)
    (c : PLeaTTa.Conf) (args : List Atom) (res : Atom)
    (rest : List PLeaTTa.Goal) (binding : Metta.Subst)
    (current : c.cur = some
      (PLeaTTa.Goal.callDyn malformedPredicatePartial args res :: rest,
        binding)) :
    PLeaTTa.step prog gt fuel c = PLeaTTa.pull { c with cur := none } := by
  apply PLeaTTa.step_callDyn_malformed_partial_eq_failure prog gt fuel c
      malformedPredicatePartial "f" (.sym "malformed") args res rest binding
      current
  · simp [malformedPredicatePartial, partialView?, prologCompoundC,
      prologCompoundTagA, chainOf, consC, nilA]
  · rfl

/-! Runtime `eval/2` provenance boundary. -/

/-- Exact `partial/2` compounds, including malformed bound-argument fields,
remain live compounds when passed back through runtime eval. -/
theorem exact_partial_eval_inputs_are_preserved :
    prepareEvalInput? runtimeEvalUnchainifyFuel compiledPartial =
        some compiledPartial ∧
      prepareEvalInput? runtimeEvalUnchainifyFuel malformedPredicatePartial =
        some malformedPredicatePartial := by
  constructor
  · change prepareEvalInput? runtimeEvalUnchainifyFuel (partialC "f" nilA) =
      some (partialC "f" nilA)
    exact prepareEvalInput?_partialC runtimeEvalUnchainifyFuel "f" nilA
  · change prepareEvalInput? runtimeEvalUnchainifyFuel
      (partialC "f" (.sym "malformed")) =
      some (partialC "f" (.sym "malformed"))
    exact prepareEvalInput?_partialC runtimeEvalUnchainifyFuel "f"
      (.sym "malformed")

/-- An ordinary Predicate-built compound and same-named `partial` compounds
of the wrong arity all take the rejection side of the pinned eval boundary. -/
theorem nonpartial_eval_inputs_are_rejected :
    prepareEvalInput? runtimeEvalUnchainifyFuel ordinaryPredicateCompound = none ∧
      prepareEvalInput? runtimeEvalUnchainifyFuel oneFieldPartialCompound = none ∧
      prepareEvalInput? runtimeEvalUnchainifyFuel threeFieldPartialCompound = none := by
  constructor
  · apply prepareEvalInput?_prologCompound_of_not_partial
    rfl
  constructor
  · apply prepareEvalInput?_prologCompound_of_not_partial
    rfl
  · apply prepareEvalInput?_prologCompound_of_not_partial
    rfl

/-- A forgeable source list visibly spelled `partial` follows the ordinary
list path and remains distinct from the live `partial/2` compound. -/
theorem source_partial_list_cannot_forge_eval_compound :
    prepareEvalInput? runtimeEvalUnchainifyFuel sourcePartialList =
        some (unchainify runtimeEvalUnchainifyFuel sourcePartialList) ∧
      sourcePartialList ≠ compiledPartial := by
  constructor
  · simpa [sourcePartialList] using
      prepareEvalInput?_chainOf runtimeEvalUnchainifyFuel
        [.sym "partial", .sym "f", nilA]
  · intro equality
    have distinguished := congrArg chainListM equality
    simp [sourcePartialList, compiledPartial] at distinguished

/-- Runtime variables cross the classifier unchanged; it does not ground or
rename them before the live compiler receives the code value. -/
theorem variable_eval_input_is_preserved :
    prepareEvalInput? runtimeEvalUnchainifyFuel (.var "unbound") =
      some (.var "unbound") := by
  rfl

/-- The executable takes exactly the ordinary failure/backtracking transition
for a non-partial compound.  No identity fallback can manufacture an answer. -/
theorem nonpartial_compound_eval_step_exact
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable) (fuel : Nat)
    (c : PLeaTTa.Conf) (res : Atom) (rest : List PLeaTTa.Goal)
    (current : c.cur = some
      (PLeaTTa.Goal.evalg ordinaryPredicateCompound res :: rest,
        ([] : Metta.Subst))) :
    PLeaTTa.step prog gt fuel c = PLeaTTa.pull { c with cur := none } := by
  unfold PLeaTTa.step
  rw [current]
  simp only [PLeaTTa.subst_nil, nonpartial_eval_inputs_are_rejected]

/-- The concrete rejection transition is also an inhabitant of the sealed
relational semantics, rather than an executable-only special case. -/
theorem nonpartial_compound_eval_step_is_licensed
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (c : PLeaTTa.Conf) (res : Atom) (rest : List PLeaTTa.Goal)
    (current : c.cur = some
      (PLeaTTa.Goal.evalg ordinaryPredicateCompound res :: rest,
        ([] : Metta.Subst))) :
    PLeaTTa.Step prog gt c (PLeaTTa.pull { c with cur := none }) := by
  apply PLeaTTa.Step.evalg_compound_reject c ordinaryPredicateCompound res
    rest [] current
  simpa only [PLeaTTa.subst_nil] using
    nonpartial_eval_inputs_are_rejected.1

end PLeaTTa.PrologPartialCompoundProvenanceRegression
