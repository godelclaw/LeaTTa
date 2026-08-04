-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologRetractOpenFactor
Purpose: Factor the actual executable retract unifier through the independent
  open canonical MGU while keeping private syntax metadata inert.
Trusted boundary: none
Main exports:
  RetractSyntaxRuntimeAgrees.mguRuntimePair,
  unifyTopExact_open_factor_of_ordered_retract,
  unifyB_result_has_open_factor_of_ordered_retract
[SPEC metta.pl:279-280]
-/
import PLeaTTa.Proofs.PrologMguFramedOpenFactor
import PLeaTTa.Proofs.PrologRetractEncodingBridge

namespace PLeaTTa.PrologRetractOpenFactor

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PrologMguExecutableOpenFactor
open PrologMguFramedOpenFactor
open PrologMguBridge
open PrologMguOpenAgreement
open PrologMguTopology
open PrologMguValuation
open PrologPrefilterBridge
open PrologRetractEncodingBridge
open PrologStateBridge

/-- Literal predicate/functor metadata is either exactly inert or a visible
rigid clash.  In particular, it is never interpreted through the Boolean
value normalization used by `CanonicalRuntimeAgrees`. -/
def literalMetadataPair (alpha : List (LogicVar × String))
    (left right : String) :
    MguRuntimePair alpha
      (.node (.atom left) []) (.node (.atom right) []) := by
  by_cases same : left = right
  · subst right
    exact .equal _
  · apply MguRuntimePair.rigidClash
    intro symbols
    injection symbols with names
    exact same names

mutual

/-- Reserved retract syntax is a frame around ordinary value pairs.  Different
reserved constructors remain explicit rigid clashes, so this relation cannot
launder a source failure into a representable output. -/
def RetractSyntaxRuntimeAgrees.mguRuntimePair
    {alpha : List (LogicVar × String)}
    {leftTree rightTree : Tree} {leftAtom rightAtom : Atom}
    (left : RetractSyntaxRuntimeAgrees alpha leftTree leftAtom)
    (right : RetractSyntaxRuntimeAgrees alpha rightTree rightAtom) :
    MguRuntimePair alpha leftTree rightTree := by
  cases left with
  | @goalUnify leftValueTree rightValueTree leftValueAtom rightValueAtom
      leftValue rightValue =>
      cases right with
      | @goalUnify otherLeftTree otherRightTree otherLeftAtom otherRightAtom
          otherLeft otherRight =>
          exact .node (.compound "$goal.unify")
            (.cons (.values ⟨_, leftValue⟩ ⟨_, otherLeft⟩)
              (.cons (.values ⟨_, rightValue⟩ ⟨_, otherRight⟩) .nil))
      | goalCall arguments =>
          exact .rigidClash _ _ _ _ (by decide)
      | clause arguments body =>
          exact .rigidClash _ _ _ _ (by decide)
  | @goalCall predicate argumentsTree argumentsAtom arguments =>
      cases right with
      | goalUnify leftValue rightValue =>
          exact .rigidClash _ _ _ _ (by decide)
      | @goalCall otherPredicate otherArgumentsTree otherArgumentsAtom
          otherArguments =>
          exact .node (.compound "$goal.call")
            (.cons (literalMetadataPair alpha predicate otherPredicate)
              (.cons (.values ⟨_, arguments⟩ ⟨_, otherArguments⟩) .nil))
      | clause otherArguments otherBody =>
          exact .rigidClash _ _ _ _ (by decide)
  | @clause predicate argumentsTree bodyTree argumentsAtom bodyAtom arguments
      body =>
      cases right with
      | goalUnify leftValue rightValue =>
          exact .rigidClash _ _ _ _ (by decide)
      | goalCall otherArguments =>
          exact .rigidClash _ _ _ _ (by decide)
      | @clause otherPredicate otherArgumentsTree otherBodyTree
          otherArgumentsAtom otherBodyAtom otherArguments otherBody =>
          exact .node (.compound "$clause")
            (.cons (literalMetadataPair alpha predicate otherPredicate)
              (.cons (.values ⟨_, arguments⟩ ⟨_, otherArguments⟩)
                (.cons
                  (PLeaTTa.PrologRetractOpenFactor.RetractSyntaxListRuntimeAgrees.mguRuntimePairs
                    body otherBody)
                  .nil)))

/-- Proper reserved-goal lists preserve every occurrence and recurse through
the same frame relation. -/
def RetractSyntaxListRuntimeAgrees.mguRuntimePairs
    {alpha : List (LogicVar × String)}
    {leftTree rightTree : Tree} {leftAtom rightAtom : Atom}
    (left : RetractSyntaxListRuntimeAgrees alpha leftTree leftAtom)
    (right : RetractSyntaxListRuntimeAgrees alpha rightTree rightAtom) :
    MguRuntimePair alpha leftTree rightTree := by
  cases left with
  | nil =>
      cases right with
      | nil => exact .equal _
      | cons head tail => exact .rigidClash _ _ _ _ (by decide)
  | cons head tail =>
      cases right with
      | nil => exact .rigidClash _ _ _ _ (by decide)
      | cons otherHead otherTail =>
          exact .node .cons
            (.cons
              (PLeaTTa.PrologRetractOpenFactor.RetractSyntaxRuntimeAgrees.mguRuntimePair
                head otherHead)
              (.cons
                (PLeaTTa.PrologRetractOpenFactor.RetractSyntaxListRuntimeAgrees.mguRuntimePairs
                  tail otherTail)
                .nil))

end

/-- The ordered canonical MGU over one source-guided reserved equation has an
open executable spelling which is itself a semantic runtime unifier.  Private
tags and predicate metadata are traversed as frames, never as values. -/
theorem RetractSyntaxRuntimeAgrees.open_runtime_unifier_exists
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {leftTree rightTree : Tree} {leftAtom rightAtom : Atom}
    (left : RetractSyntaxRuntimeAgrees alpha leftTree leftAtom)
    (right : RetractSyntaxRuntimeAgrees alpha rightTree rightAtom)
    {canonical : TreeSubstitution}
    (derivation : OrderedTreeMgu [(leftTree, rightTree)] canonical) :
    ∃ representative,
      AlphaTreeSubstitutionAgrees alpha canonical representative ∧
        AlphaValuationAgrees alpha canonical representative ∧
        Nonempty (PLeaTTa.SubstTopological representative) ∧
        PLeaTTa.DeepEquivalentUnifies PLeaTTa.prologGroundIdentical
          representative [(leftAtom, rightAtom)] := by
  have openable :=
    PLeaTTa.PrologMguFramedOpenFactor.OrderedTreeMgu.singleton_binding_alphaOpenable
      derivation
      (PLeaTTa.PrologRetractOpenFactor.RetractSyntaxRuntimeAgrees.mguRuntimePair
        left right)
  obtain ⟨representative, spelling⟩ :=
    alphaTreeSubstitutionAgrees_exists openable.1 openable.2
  have canonicalTopological :=
    OrderedTreeMgu.binding_topological derivation
  have runtimeTopological :=
    AlphaTreeSubstitutionAgrees.runtime_topological
      shared spelling canonicalTopological
  have valuation :
      AlphaValuationAgrees alpha canonical representative :=
    PLeaTTa.PrologMguTopology.AlphaTreeSubstitutionAgrees.valuation
      shared spelling canonicalTopological
  have canonicalUnifies :
      TreeSubstitution.apply canonical leftTree =
        TreeSubstitution.apply canonical rightTree :=
    derivation.isMostGeneral.1 (leftTree, rightTree) (by simp)
  have equivalent :=
    RetractSyntaxRuntimeAgrees.equivalent_of_tree_eq
      shared.forward (left.apply valuation) (right.apply valuation)
        canonicalUnifies
  refine ⟨representative, spelling, valuation, ⟨runtimeTopological⟩, ?_⟩
  intro equation member
  simp only [List.mem_singleton] at member
  subst equation
  exact equivalent

/-- Every actual executable MGU over one source-guided reserved equation is at
least as general as the independently constructed open canonical MGU. -/
theorem unifyTopExact_open_factor_of_ordered_retract
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {leftTree rightTree : Tree} {leftAtom rightAtom : Atom}
    (left : RetractSyntaxRuntimeAgrees alpha leftTree leftAtom)
    (right : RetractSyntaxRuntimeAgrees alpha rightTree rightAtom)
    {canonical : TreeSubstitution}
    (derivation : OrderedTreeMgu [(leftTree, rightTree)] canonical)
    {result : Subst}
    (returned : PLeaTTa.unifyTopExact leftAtom rightAtom = some result) :
    OpenAlphaResultFactors alpha canonical result := by
  obtain
    ⟨representative, spelling, valuation, topological,
      representativeUnifies⟩ :=
    PLeaTTa.PrologRetractOpenFactor.RetractSyntaxRuntimeAgrees.open_runtime_unifier_exists
      shared left right derivation
  have runtimeMgu :=
    PLeaTTa.unifyTopExact_isMgu leftAtom rightAtom result returned
  exact
    ⟨representative, spelling, valuation, topological,
      runtimeMgu.2 representative representativeUnifies⟩

/-- The actual `unifyB` result exposes its generated component, the open
canonical factor through that component, and the exact installation equation
over the incoming binding. -/
theorem unifyB_result_has_open_factor_of_ordered_retract
    (base : Subst)
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {leftTree rightTree : Tree} {leftAtom rightAtom : Atom}
    (left : RetractSyntaxRuntimeAgrees alpha leftTree
      (PLeaTTa.subst base leftAtom))
    (right : RetractSyntaxRuntimeAgrees alpha rightTree
      (PLeaTTa.subst base rightAtom))
    {canonical : TreeSubstitution}
    (derivation : OrderedTreeMgu [(leftTree, rightTree)] canonical)
    {result : Subst}
    (returned : PLeaTTa.unifyB base leftAtom rightAtom = some result) :
    ∃ generated,
      PLeaTTa.unifyTopExact
          (PLeaTTa.subst base leftAtom)
          (PLeaTTa.subst base rightAtom) = some generated ∧
        OpenAlphaResultFactors alpha canonical generated ∧
        result =
          match generated with
          | [] => base
          | _ :: _ => Metta.Subst.compose generated base := by
  obtain ⟨generated, generatedEq, _runtimeMgu, installed⟩ :=
    PLeaTTa.unifyB_result_has_generated_mgu
      base leftAtom rightAtom result returned
  have factors :=
    unifyTopExact_open_factor_of_ordered_retract
      shared left right derivation generatedEq
  exact ⟨generated, generatedEq, factors, installed⟩

/-- Source-facing specialization: a computed retract MGU and one actual
executable success expose the canonical binding and its open factor without
asserting association-list equality across representations. -/
theorem unifyB_result_has_open_factor_of_computed_retract
    (base : Subst)
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {leftTerm rightTerm : Term} {leftAtom rightAtom : Atom}
    (left : RetractSyntaxRuntimeAgrees alpha (Term.denote leftTerm)
      (PLeaTTa.subst base leftAtom))
    (right : RetractSyntaxRuntimeAgrees alpha (Term.denote rightTerm)
      (PLeaTTa.subst base rightAtom))
    {sourceBinding : OpenSubstitution.Substitution}
    (computed :
      ComputesDenotationalMgu [(leftTerm, rightTerm)] sourceBinding)
    {result : Subst}
    (returned : PLeaTTa.unifyB base leftAtom rightAtom = some result) :
    ∃ canonical generated,
      sourceBinding = TreeSubstitution.reify canonical ∧
        PLeaTTa.unifyTopExact
          (PLeaTTa.subst base leftAtom)
          (PLeaTTa.subst base rightAtom) = some generated ∧
        OpenAlphaResultFactors alpha canonical generated ∧
        result =
          match generated with
          | [] => base
          | _ :: _ => Metta.Subst.compose generated base := by
  obtain ⟨canonical, derivation, sourceEq⟩ := computed
  obtain ⟨generated, generatedEq, factors, installed⟩ :=
    unifyB_result_has_open_factor_of_ordered_retract
      base shared left right derivation returned
  exact ⟨canonical, generated, sourceEq, generatedEq, factors, installed⟩

end PLeaTTa.PrologRetractOpenFactor
