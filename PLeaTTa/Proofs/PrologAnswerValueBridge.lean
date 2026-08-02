-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologAnswerValueBridge
Purpose: Derive one source/runtime answer-value agreement from the carried
  residual-MGU simulation invariants
Trusted boundary: none
Main exports: AnswerValueProducerAgrees,
  AnswerValueProducerAgrees.runtimeTermAgrees
-/
import PLeaTTa.Proofs.PrologFindallCopyBridge
import PLeaTTa.Proofs.PrologRecursiveCallPayloadBridge

namespace PLeaTTa.PrologAnswerValueBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.OpenSubstitution
open CompilerAdequacy
open PrologFindallCopyBridge
open PrologMguBridge
open PrologMguComposition
open PrologOrdinaryStepBridge
open PrologRecursiveCallPayloadBridge
open PrologStateBridge

/-- Pre-substitution producer data for one observable source/runtime value.

Every field is already maintained by the local-task simulation: cumulative
source/runtime valuation, structural term agreement, and occurrence-sensitive
observable support.  The relation carries neither the desired
post-substitution `RuntimeTermAgrees` conclusion nor a copied value. -/
def AnswerValueProducerAgrees
    (alpha support : List (LogicVar × String))
    (sourceBindings : Substitution) (runtimeBindings : Subst)
    (sourceTerm : Term) (runtimeAtom : Atom) : Prop :=
  ∃ canonical : TreeSubstitution,
    ∃ referenceBase : Substitution,
      TaskDataAgrees alpha support canonical referenceBase sourceBindings
          runtimeBindings ∧
        AlphaTermAgrees alpha sourceTerm runtimeAtom ∧
        AlphaTermsSupported alpha support [sourceTerm]

namespace AnswerValueProducerAgrees

/-- Package the three existing simulation facts without manufacturing a
post-substitution value relation. -/
theorem ofTaskData
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {sourceBindings : Substitution} {runtimeBindings : Subst}
    {sourceTerm : Term} {runtimeAtom : Atom}
    (data :
      TaskDataAgrees alpha support canonical referenceBase sourceBindings
        runtimeBindings)
    (term : AlphaTermAgrees alpha sourceTerm runtimeAtom)
    (supported : AlphaTermsSupported alpha support [sourceTerm]) :
    AnswerValueProducerAgrees alpha support sourceBindings runtimeBindings
      sourceTerm runtimeAtom :=
  ⟨canonical, referenceBase, data, term, supported⟩

/-- The carried local-task invariants determine one complete finite runtime
alpha relating the two materialized values.  Residual MGU orientation is
eliminated by mutual finite instantiation; the conclusion is derived rather
than supplied by the caller. -/
theorem runtimeTermAgrees
    {alpha support : List (LogicVar × String)}
    {sourceBindings : Substitution} {runtimeBindings : Subst}
    {sourceTerm : Term} {runtimeAtom : Atom}
    (producer :
      AnswerValueProducerAgrees alpha support sourceBindings runtimeBindings
        sourceTerm runtimeAtom) :
    RuntimeTermAgrees (sourceBindings.applyTerm sourceTerm)
      (PLeaTTa.subst runtimeBindings runtimeAtom) := by
  rcases producer with
    ⟨canonical, referenceBase, data,
      termAgreement, termSupported⟩
  obtain
    ⟨representative, variants, _representativeCovered, leaves⟩ :=
    PLeaTTa.PrologRecursiveCallPayloadBridge.AlphaCumulativeResidualVariantAgreesOn.applyTerms
      data.valuation (.cons termAgreement .nil) termSupported
  cases leaves with
  | cons representativeRuntime _tail =>
      apply runtimeTermAgrees_of_variants
        (first := canonical ++ Substitution.denote referenceBase)
        (second := representative ++ Substitution.denote referenceBase)
        (tree := Term.denote sourceTerm)
        (alpha := alpha)
      · rw [Substitution.denote_applyTerm, data.bindingShape,
          Substitution.denote_append,
          TreeSubstitution.denote_reify data.canonicalWellFormed]
      · exact variants
      · exact data.alphaShared
      · exact representativeRuntime

end AnswerValueProducerAgrees

end PLeaTTa.PrologAnswerValueBridge
