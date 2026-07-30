-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologActivationBridge
Purpose: Relate executable conservative clause filtering to the independent
  canonical Prolog resolver before constructing the ranked activation macro.
Trusted boundary: none
Main exports: TreeMayUnify,
  nonreflexive_float_refutes_legacy_matchCompat_conservativity,
  nonreflexive_float_legacy_filter_is_repaired
-/
import PLeaTTa.Proofs.PrologActivationMacro

namespace PLeaTTa.PrologActivationBridge

open Metta (Atom)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PrologStateBridge

/-!
`prologMatchCompat` is the conservative executable prefilter for local
clauses.  It may retain a doomed repeated-variable or occurs-check case, but
it must never discard a head pair that the independent canonical resolver
can unify.  The generic-space `matchCompat` remains below only as the
anti-regression foil that exposed non-reflexive NaN handling.

The proof is factored through a representation-free structural relation on
canonical trees.  Variables are wildcards; rigid nodes must have the same
symbol and pointwise-compatible children.  This prevents the desired
conclusion from being smuggled into a cross-representation contract.
-/

mutual

/-- Two canonical trees have no immediate rigid clash.  This is deliberately
weaker than unifiability: repeated-variable and occurs-check constraints are
not represented here. -/
inductive TreeMayUnify : Tree → Tree → Prop where
  | leftVariable (identity : LogicVar) (right : Tree) :
      TreeMayUnify (.variable identity) right
  | rightVariable (left : Tree) (identity : LogicVar) :
      TreeMayUnify left (.variable identity)
  | node (symbol : RigidSymbol) {left right : List Tree}
      (children : TreesMayUnify left right) :
      TreeMayUnify (.node symbol left) (.node symbol right)

/-- Ordered child-list counterpart of `TreeMayUnify`.  Equal arity is part of
the relation, so a rigid arity mismatch is a clash. -/
inductive TreesMayUnify : List Tree → List Tree → Prop where
  | nil : TreesMayUnify [] []
  | cons {leftHead rightHead : Tree} {leftTail rightTail : List Tree}
      (head : TreeMayUnify leftHead rightHead)
      (tail : TreesMayUnify leftTail rightTail) :
      TreesMayUnify (leftHead :: leftTail) (rightHead :: rightTail)

end

mutual

/-- Equality after one canonical substitution can only arise from
structurally compatible pre-substitution trees. -/
theorem TreeMayUnify.of_apply_eq (bindings : TreeSubstitution) :
    ∀ left right,
      TreeSubstitution.apply bindings left =
        TreeSubstitution.apply bindings right →
      TreeMayUnify left right
  | .variable identity, right, _ =>
      .leftVariable identity right
  | left, .variable identity, _ =>
      .rightVariable left identity
  | .node leftSymbol leftChildren, .node rightSymbol rightChildren,
      equality => by
      simp only [TreeSubstitution.apply_node] at equality
      injection equality with symbolEquality childrenEquality
      subst rightSymbol
      exact .node leftSymbol
        (TreesMayUnify.of_applyTrees_eq bindings leftChildren rightChildren
          childrenEquality)

/-- Ordered child-list companion to `TreeMayUnify.of_apply_eq`. -/
theorem TreesMayUnify.of_applyTrees_eq (bindings : TreeSubstitution) :
    ∀ left right,
      TreeSubstitution.applyTrees bindings left =
        TreeSubstitution.applyTrees bindings right →
      TreesMayUnify left right
  | [], [], _ => .nil
  | [], _ :: _, equality => by
      simp only [TreeSubstitution.applyTrees_nil,
        TreeSubstitution.applyTrees_cons] at equality
      contradiction
  | _ :: _, [], equality => by
      simp only [TreeSubstitution.applyTrees_nil,
        TreeSubstitution.applyTrees_cons] at equality
      contradiction
  | leftHead :: leftTail, rightHead :: rightTail, equality => by
      simp only [TreeSubstitution.applyTrees_cons] at equality
      injection equality with headEquality tailEquality
      exact .cons
        (TreeMayUnify.of_apply_eq bindings leftHead rightHead headEquality)
        (TreesMayUnify.of_applyTrees_eq bindings leftTail rightTail
          tailEquality)

end

/-- Every independent denotational unifier witnesses structural
compatibility before substitution. -/
theorem TreeMayUnify.of_denotationalUnifier
    {binding : PeTTaSpec.PrologCore.OpenSubstitution.Substitution}
    {left right : Term}
    (unifies : DenotationalUnifier binding left right) :
    TreeMayUnify (Term.denote left) (Term.denote right) := by
  exact TreeMayUnify.of_apply_eq
    (PeTTaSpec.PrologCore.Canonical.Substitution.denote binding)
    (Term.denote left) (Term.denote right) unifies

mutual

/-- Removing an instantiation from the left operand preserves structural
compatibility.  Substitution can expose a rigid clash hidden behind a
variable, but it cannot make the original, more-general tree less able to
match the unchanged right operand. -/
theorem TreeMayUnify.of_left_apply (bindings : TreeSubstitution) :
    ∀ left right,
      TreeMayUnify (TreeSubstitution.apply bindings left) right →
      TreeMayUnify left right
  | .variable identity, right, _ =>
      .leftVariable identity right
  | .node leftSymbol leftChildren, .variable identity, _ =>
      .rightVariable (.node leftSymbol leftChildren) identity
  | .node leftSymbol leftChildren, .node rightSymbol rightChildren,
      compatible => by
      simp only [TreeSubstitution.apply_node] at compatible
      cases compatible with
      | node _ children =>
          exact .node leftSymbol
            (TreesMayUnify.of_left_apply bindings
              leftChildren rightChildren children)

/-- Ordered child-list companion to `TreeMayUnify.of_left_apply`. -/
theorem TreesMayUnify.of_left_apply (bindings : TreeSubstitution) :
    ∀ left right,
      TreesMayUnify (TreeSubstitution.applyTrees bindings left) right →
      TreesMayUnify left right
  | [], [], _ =>
      .nil
  | [], _ :: _, compatible => by
      simp only [TreeSubstitution.applyTrees_nil] at compatible
      cases compatible
  | _ :: _, [], compatible => by
      simp only [TreeSubstitution.applyTrees_cons] at compatible
      cases compatible
  | leftHead :: leftTail, rightHead :: rightTail, compatible => by
      simp only [TreeSubstitution.applyTrees_cons] at compatible
      cases compatible with
      | cons head tail =>
          exact .cons
            (TreeMayUnify.of_left_apply bindings
              leftHead rightHead head)
            (TreesMayUnify.of_left_apply bindings
              leftTail rightTail tail)

end

/-- Inversion for a compatible pair of two-child rigid nodes. -/
theorem TreeMayUnify.node₂
    {symbol : RigidSymbol}
    {leftHead leftTail rightHead rightTail : Tree}
    (compatible :
      TreeMayUnify (.node symbol [leftHead, leftTail])
        (.node symbol [rightHead, rightTail])) :
    TreeMayUnify leftHead rightHead ∧
      TreeMayUnify leftTail rightTail := by
  cases compatible with
  | node _ children =>
      cases children with
      | cons head tail =>
          cases tail with
          | cons second rest =>
              cases rest
              exact ⟨head, second⟩

/-- Compatible rigid atom nodes carry the same source atom name. -/
theorem TreeMayUnify.atom_name_eq {left right : String}
    (compatible :
      TreeMayUnify (.node (.atom left) []) (.node (.atom right) [])) :
    left = right := by
  cases compatible
  rfl

/-- Rigid compatibility preserves the exact outer symbol. -/
theorem TreeMayUnify.node_symbol_eq
    {leftSymbol rightSymbol : RigidSymbol}
    {leftChildren rightChildren : List Tree}
    (compatible :
      TreeMayUnify (.node leftSymbol leftChildren)
        (.node rightSymbol rightChildren)) :
    leftSymbol = rightSymbol := by
  cases compatible
  rfl

/-- Once rigid outer symbols agree, compatibility exposes the ordered child
relation. -/
theorem TreeMayUnify.node_children
    {symbol : RigidSymbol} {leftChildren rightChildren : List Tree}
    (compatible :
      TreeMayUnify (.node symbol leftChildren)
        (.node symbol rightChildren)) :
    TreesMayUnify leftChildren rightChildren := by
  cases compatible
  assumption

/-- Executable proper-list cells expose exactly their element and tail
compatibility tests. -/
@[simp] theorem matchCompat_consC (leftHead leftTail rightHead rightTail : Atom) :
    matchCompat (consC leftHead leftTail) (consC rightHead rightTail) =
      (matchCompat leftHead rightHead &&
        matchCompat leftTail rightTail) := by
  simp [consC, matchCompat, matchCompatList]

@[simp] theorem matchCompat_nilA :
    matchCompat nilA nilA = true := by
  rfl

/-- The retired generic-space prefilter is not conservative on the full
independent float domain: IEEE equality rejects a reflexive NaN payload,
while canonical Prolog term identity and SWI unification accept it.  Keeping
this witness prevents the resolver from silently regressing to `matchCompat`. -/
theorem nonreflexive_float_refutes_legacy_matchCompat_conservativity
    (value : Float)
    (nonreflexive :
      Metta.Ground.equiv (.float value) (.float value) = false) :
    AlphaTermAgrees []
        (.float (PLeaTTa.PrologFloatIdentity.ofFloat value))
        (.gnd (.float value)) ∧
      TreeMayUnify
        (Term.denote (.float (PLeaTTa.PrologFloatIdentity.ofFloat value)))
        (Term.denote (.float (PLeaTTa.PrologFloatIdentity.ofFloat value))) ∧
      matchCompat (.gnd (.float value))
        (.gnd (.float value)) = false ∧
      ∃ binding,
        DenotationalUnifier binding
          (.float (PLeaTTa.PrologFloatIdentity.ofFloat value))
          (.float (PLeaTTa.PrologFloatIdentity.ofFloat value)) := by
  refine ⟨.float value, ?_, ?_, [], ?_⟩
  · exact TreeMayUnify.of_denotationalUnifier (binding := []) rfl
  · simpa [matchCompat] using nonreflexive
  · rfl

/-- The exact Prolog resolver repairs the legacy NaN false negative at both
gates.  On the same non-reflexive runtime payload, the generic-space filter
still rejects (the anti-regression witness), while the Prolog-specific filter
accepts, the executable exact unifier succeeds with the empty substitution,
and the independent canonical semantics has a denotational unifier. -/
theorem nonreflexive_float_legacy_filter_is_repaired
    (value : Float)
    (nonreflexive :
      Metta.Ground.equiv (.float value) (.float value) = false) :
    matchCompat (.gnd (.float value)) (.gnd (.float value)) = false ∧
      prologMatchCompat (.gnd (.float value)) (.gnd (.float value)) = true ∧
      PLeaTTa.unifyTopExact
        (.gnd (.float value)) (.gnd (.float value)) = some [] ∧
      ∃ binding,
        DenotationalUnifier binding
          (.float (PLeaTTa.PrologFloatIdentity.ofFloat value))
          (.float (PLeaTTa.PrologFloatIdentity.ofFloat value)) := by
  refine ⟨?_, ?_, ?_, [], rfl⟩
  · simpa [matchCompat] using nonreflexive
  · simp [prologMatchCompat, PLeaTTa.prologGroundIdentical]
  · simp [PLeaTTa.unifyTopExact, Metta.Unify.unifyTopWith, Metta.Atom.size,
      Metta.Unify.unifyRoundsWith,
      Metta.Unify.decomposeAllWith, Metta.Unify.decomposeEqWith,
      PLeaTTa.prologGroundIdentical]

end PLeaTTa.PrologActivationBridge
