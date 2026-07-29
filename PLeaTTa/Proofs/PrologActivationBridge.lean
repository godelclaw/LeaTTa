-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologActivationBridge
Purpose: Relate executable conservative clause filtering to the independent
  canonical Prolog resolver before constructing the ranked activation macro.
Trusted boundary: none
Main exports: TreeMayUnify,
  nonreflexive_float_refutes_matchCompat_conservativity,
  nonreflexive_float_separates_current_and_prolog_unifiers
-/
import PLeaTTa.Proofs.PrologActivationMacro

namespace PLeaTTa.PrologActivationBridge

open Metta (Atom)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PrologStateBridge

/-!
`matchCompat` is only a conservative executable prefilter.  It may retain a
doomed repeated-variable or occurs-check case, but it must never discard a
head pair that the independent canonical resolver can unify.

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

/-- The current executable prefilter is not conservative on the full
independent float domain: IEEE equality rejects a reflexive NaN payload,
while canonical Prolog term identity and SWI unification accept it.  This is
the concrete blocker that `RESOLVER.float_identity` records; a later repair
must use bitwise float identity at every unification decomposition round. -/
theorem nonreflexive_float_refutes_matchCompat_conservativity
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

/-- The same non-reflexive runtime float separates the current executable
unifier from the comparator-parametric repair itself.  The first conjunct is
the shipped defect exercised by the typed-host differential fixture; the
second shows that changing only the ground comparator makes the identical
ground equation succeed with the empty substitution. -/
theorem nonreflexive_float_separates_current_and_prolog_unifiers
    (value : Float)
    (nonreflexive :
      Metta.Ground.equiv (.float value) (.float value) = false) :
    PLeaTTa.unifyTopExact
        (.gnd (.float value)) (.gnd (.float value)) = none ∧
      Metta.Unify.unifyTopWith PLeaTTa.prologGroundIdentical
        (.gnd (.float value)) (.gnd (.float value)) = some [] := by
  have identitySelf :
      (PLeaTTa.PrologFloatIdentity.ofFloat value ==
        PLeaTTa.PrologFloatIdentity.ofFloat value) = true := by
    exact PLeaTTa.PrologFloatIdentity.beq_self _
  constructor
  · simp [PLeaTTa.unifyTopExact, Metta.Unify.unifyTop,
      Metta.Atom.size, Metta.Unify.unifyRounds, Metta.Unify.decomposeAll,
      Metta.Unify.decomposeEq, nonreflexive]
  · simp [Metta.Unify.unifyTopWith, Metta.Atom.size,
      Metta.Unify.unifyRoundsWith,
      Metta.Unify.decomposeAllWith, Metta.Unify.decomposeEqWith,
      PLeaTTa.prologGroundIdentical, identitySelf]

end PLeaTTa.PrologActivationBridge
