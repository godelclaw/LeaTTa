-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologFindallResidualVariantBridge
Purpose: Isolate the residual-MGU orientation seam at findall collection.
Trusted boundary: none
Main exports: residual_alias_breaks_exact_materialization,
  residual_alias_copies_still_runtime_agree
-/
import PLeaTTa.Proofs.PrologAnswerValueBridge

namespace PLeaTTa.PrologFindallResidualVariantBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.Copy
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open CompilerAdequacy
open PrologAnswerValueBridge
open PrologMguBridge
open PrologMguComposition
open PrologMguOpenAgreement
open PrologMguTopology
open PrologMguVariant
open PrologOrdinaryStepBridge
open PrologPrefilterBridge
open PrologRecursiveCallPayloadBridge
open PrologStateBridge
open PrologFindallCopyBridge

/-!
# Residual aliases at the collection seam

Ordered MGUs may orient one residual equality in opposite directions.  The
independent result can therefore materialize a template as one surviving
variable while the executable result exposes its equivalent alias.  Requiring
compiler-time `TermAgrees` between those two raw values is too strong: it fixes
the source spelling even though the local collector immediately copies the
residual value into a fresh runtime support.

The witnesses below separate those facts.  Exact raw agreement is false, but
an explicit finite runtime alpha relates both the raw values and their two
independently allocated copies at every pair of allocator counters.
-/

/-- Pre-substitution producer data for one findall template value.

Every field already belongs to the child task simulation: cumulative source
and runtime valuation, structural template agreement, and occurrence-sensitive
liveness support.  In particular this relation carries neither a post-
substitution `RuntimeTermAgrees` fact nor any copied value. -/
abbrev FindallMaterializationProducerAgrees
    (sourceBindings : Substitution) (runtimeBindings : Subst)
    (sourceTemplate : Term) (runtimeTemplate : Atom) : Prop :=
  ∃ alpha support : List (LogicVar × String),
    AnswerValueProducerAgrees alpha support sourceBindings runtimeBindings
      sourceTemplate runtimeTemplate

namespace FindallMaterializationProducerAgrees

/-- The actual child-simulation invariants construct materialized runtime
agreement.  Residual MGU orientation is eliminated by finite mutual
instantiation; no caller supplies the post-substitution result. -/
theorem runtimeTermAgrees
    {sourceBindings : Substitution} {runtimeBindings : Subst}
    {sourceTemplate : Term} {runtimeTemplate : Atom}
    (producer :
      FindallMaterializationProducerAgrees sourceBindings runtimeBindings
        sourceTemplate runtimeTemplate) :
    RuntimeTermAgrees (sourceBindings.applyTerm sourceTemplate)
      (PLeaTTa.subst runtimeBindings runtimeTemplate) := by
  rcases producer with ⟨alpha, support, producer⟩
  exact AnswerValueProducerAgrees.runtimeTermAgrees producer

end FindallMaterializationProducerAgrees

private def residualAliasX : LogicVar := .source "$findall_x"
private def residualAliasY : LogicVar := .source "$findall_y"

private def residualSourceBindings : Substitution :=
  [(residualAliasX, .variable residualAliasY)]

private def residualRuntimeBindings : Subst :=
  [("$findall_y", .var "$findall_x")]

private def residualAlpha : List (LogicVar × String) :=
  [(residualAliasX, "$findall_x"),
   (residualAliasY, "$findall_y")]

private def residualCanonical : TreeSubstitution :=
  [(residualAliasX, .variable residualAliasY)]

private def residualRepresentative : TreeSubstitution :=
  [(residualAliasY, .variable residualAliasX)]

private def residualTemplate : Term := .variable residualAliasX
private def residualRuntimeTemplate : Atom := .var "$findall_x"

private theorem source_materialized :
    residualSourceBindings.applyTerm residualTemplate =
      .variable residualAliasY := by
  simp [residualSourceBindings, residualTemplate, residualAliasX,
    residualAliasY, Term.instantiateOne]

private theorem runtime_materialized :
    PLeaTTa.subst residualRuntimeBindings residualRuntimeTemplate =
      .var "$findall_x" := by
  exact
    PLeaTTa.subst_var_of_lookup_none residualRuntimeBindings "$findall_x" (by
      simp [residualRuntimeBindings, Metta.Subst.lookup])

private theorem source_bindings_denote :
    Substitution.denote residualSourceBindings = residualCanonical := by
  rfl

/-- The opposite orientations arise inside the actual cumulative
residual-variant relation used by active local calls. -/
theorem residual_alias_cumulative_agrees :
    AlphaCumulativeResidualVariantAgreesOn
      residualAlpha residualAlpha residualCanonical []
      residualRuntimeBindings := by
  have canonicalMgu :
      TreeIsMgu residualCanonical
        [(.variable residualAliasX, .variable residualAliasY)] := by
    exact tree_singleton_variable_is_mgu residualAliasX
      (.variable residualAliasY) (by
        simp [Tree.occurs, residualAliasX, residualAliasY])
  have representativeMgu :
      TreeIsMgu residualRepresentative
        [(.variable residualAliasX, .variable residualAliasY)] := by
    exact tree_singleton_right_variable_is_mgu
      (.variable residualAliasX) residualAliasY (by
        simp [Tree.occurs, residualAliasX, residualAliasY])
  have variants :
      TreeSubstitutionVariants residualCanonical residualRepresentative :=
    PrologMguVariant.TreeIsMgu.variants canonicalMgu representativeMgu
  have canonicalTopological :
      TreeSubstitutionTopological residualCanonical :=
    TreeSubstitutionTopological.singleton residualAliasX
      (.variable residualAliasY) (by
        simp [Tree.occurs, residualAliasX, residualAliasY])
  have runtimeTopological :
      PLeaTTa.SubstTopological residualRuntimeBindings :=
    PLeaTTa.SubstTopological.cons_of_fresh []
      PLeaTTa.emptySubstTopological "$findall_y" (.var "$findall_x")
      (by simp [Metta.Subst.lookup])
      (by simp [Atom.vars])
      (by simp [PLeaTTa.AtomAvoids, Metta.Subst.lookup])
  have representativeX :
      TreeSubstitution.apply residualRepresentative
          (.variable residualAliasX) =
        .variable residualAliasX := by
    simp [residualRepresentative, residualAliasX, residualAliasY,
      TreeSubstitution.apply, Tree.instantiateOne]
  have representativeY :
      TreeSubstitution.apply residualRepresentative
          (.variable residualAliasY) =
        .variable residualAliasX := by
    simp [residualRepresentative, residualAliasX, residualAliasY,
      TreeSubstitution.apply, Tree.instantiateOne]
  have runtimeX :
      PLeaTTa.subst residualRuntimeBindings (.var "$findall_x") =
        .var "$findall_x" :=
    PLeaTTa.subst_var_of_lookup_none
      residualRuntimeBindings "$findall_x" (by
        simp [residualRuntimeBindings, Metta.Subst.lookup])
  have runtimeY :
      PLeaTTa.subst residualRuntimeBindings (.var "$findall_y") =
        .var "$findall_x" := by
    rw [runtimeTopological.subst_var_of_lookup
      residualRuntimeBindings "$findall_y" (.var "$findall_x")
      (by simp [residualRuntimeBindings, Metta.Subst.lookup])]
    exact runtimeX
  have valuation :
      AlphaValuationAgreesOn residualAlpha residualAlpha
        residualRepresentative residualRuntimeBindings := by
    intro identity name member
    simp only [residualAlpha, List.mem_cons, List.not_mem_nil, or_false]
      at member
    rcases member with member | member
    · have identityEq : identity = residualAliasX := by
        simpa using congrArg Prod.fst member
      have nameEq : name = "$findall_x" := by
        simpa using congrArg Prod.snd member
      subst identity
      subst name
      rw [representativeX, runtimeX]
      exact
        CanonicalRuntimeAgrees.variable
          (by simp [residualAlpha, residualAliasX])
    · have identityEq : identity = residualAliasY := by
        simpa using congrArg Prod.fst member
      have nameEq : name = "$findall_y" := by
        simpa using congrArg Prod.snd member
      subst identity
      subst name
      rw [representativeY, runtimeY]
      exact
        CanonicalRuntimeAgrees.variable
          (by simp [residualAlpha, residualAliasX, residualAliasY])
  have representativeCovered :
      TreeSubstitutionVariablesSatisfy
        (AlphaCovers residualAlpha) residualRepresentative := by
    intro entry member
    have entryEq :
        entry = (residualAliasY, .variable residualAliasX) := by
      simpa [residualRepresentative] using member
    subst entry
    exact
      ⟨⟨"$findall_y",
          by simp [residualAlpha, residualAliasY]⟩,
        ⟨"$findall_x",
          by simp [residualAlpha, residualAliasX]⟩⟩
  exact
    ⟨residualRepresentative, variants, canonicalTopological,
      representativeCovered, ⟨runtimeTopological⟩, valuation⟩

/-- Opposite residual aliases cannot satisfy compiler-time exact spelling at
the findall collection seam. -/
theorem residual_alias_breaks_exact_materialization :
    ¬ TermAgrees
      (residualSourceBindings.applyTerm residualTemplate)
      (PLeaTTa.subst residualRuntimeBindings residualRuntimeTemplate) := by
  rw [source_materialized, runtime_materialized]
  have sourceVariableNamesEqual
      {left right : String}
      (agreement :
        TermAgrees (.variable (.source left)) (.var right)) :
      left = right := by
    cases agreement
    rfl
  intro agreement
  have impossible := sourceVariableNamesEqual agreement
  simp at impossible

/-- The same opposite-orientation state is produced by the actual upstream
task invariants.  This is the end-to-end anti-vacuity witness for eliminating
the former post-materialization premise. -/
theorem residual_alias_materialization_producer :
    FindallMaterializationProducerAgrees
      residualSourceBindings residualRuntimeBindings residualTemplate
      residualRuntimeTemplate := by
  refine
    ⟨residualAlpha, residualAlpha, residualCanonical, [], ?_, ?_, ?_⟩
  · refine
      { alphaShared := ?_
        canonicalWellFormed :=
          TreeSubstitution.WellFormed.singleton residualAliasX
            (Tree.WellFormed.variable residualAliasY)
        bindingShape := ?_
        valuation := residual_alias_cumulative_agrees }
    · constructor
      · intro identity left right leftMember rightMember
        simp [residualAlpha, residualAliasX, residualAliasY]
          at leftMember rightMember
        rcases leftMember with leftMember | leftMember <;>
          rcases rightMember with rightMember | rightMember <;>
          simp_all
      · intro left right name leftMember rightMember
        simp [residualAlpha, residualAliasX, residualAliasY]
          at leftMember rightMember
        rcases leftMember with leftMember | leftMember <;>
          rcases rightMember with rightMember | rightMember <;>
          simp_all
    · simp [residualSourceBindings, residualCanonical,
        TreeSubstitution.reify, Tree.reify]
  · exact AlphaTermAgrees.variable (by
      simp [residualAlpha, residualAliasX])
  · intro term member
    simp only [List.mem_singleton] at member
    subst term
    simp [AlphaTreeSupported, TreeVariablesSatisfy, Term.denote,
      residualAlpha, residualTemplate, residualAliasX]

/-- The same raw values do agree through an explicit one-variable runtime
alpha.  Thus the failed exact premise does not denote an observable semantic
difference. -/
theorem residual_alias_raw_runtime_agrees :
    RuntimeTermAgrees
      (residualSourceBindings.applyTerm residualTemplate)
      (PLeaTTa.subst residualRuntimeBindings residualRuntimeTemplate) := by
  exact residual_alias_materialization_producer.runtimeTermAgrees

/-- The current exact copy-debt premise excludes a state accepted by the
cumulative local-call semantics, even though the raw values have a finite
runtime alpha. -/
theorem residual_alias_exact_debt_excludes_valid_state :
    Substitution.denote residualSourceBindings = residualCanonical ∧
      AlphaCumulativeResidualVariantAgreesOn
        residualAlpha residualAlpha residualCanonical []
        residualRuntimeBindings ∧
      RuntimeTermAgrees
        (residualSourceBindings.applyTerm residualTemplate)
        (PLeaTTa.subst residualRuntimeBindings residualRuntimeTemplate) ∧
      ¬ TermAgrees
        (residualSourceBindings.applyTerm residualTemplate)
        (PLeaTTa.subst residualRuntimeBindings residualRuntimeTemplate) :=
  ⟨source_bindings_denote, residual_alias_cumulative_agrees,
    residual_alias_raw_runtime_agrees,
    residual_alias_breaks_exact_materialization⟩

private theorem source_copy_variable (firstFresh : Nat) :
    copyTerm firstFresh
        (residualSourceBindings.applyTerm residualTemplate) =
      .variable (.generated firstFresh) := by
  rw [source_materialized]
  simp [copyTerm, copyRename, copyVariables, residualAliasY,
    Term.renameVariables, Resolver.termVariables, List.eraseDups_cons]

private theorem runtime_copy_variable (counter : Nat) :
    (copyFindallAtom counter
        (PLeaTTa.subst residualRuntimeBindings
          residualRuntimeTemplate)).value =
      .var
        ("$findall_x" ++
          resolutionCompactSuffix
            (advanceCounterPastAtoms counter [.var "$findall_x"])) := by
  rw [runtime_materialized]
  simp [copyFindallAtom, resolutionAtomClosed,
    PersistentSubst.atomClosed, renameAtomSuffix_var]

/-- Independent answer-time copying and executable collection-time copying
remain runtime-alpha-equivalent for every pair of allocator counters, despite
the false raw `TermAgrees` premise. -/
theorem residual_alias_copies_still_runtime_agree
    (firstFresh counter : Nat) :
    RuntimeTermAgrees
      (copyTerm firstFresh
        (residualSourceBindings.applyTerm residualTemplate))
      (copyFindallAtom counter
        (PLeaTTa.subst residualRuntimeBindings
          residualRuntimeTemplate)).value := by
  rw [source_copy_variable, runtime_copy_variable]
  let copiedName :=
    "$findall_x" ++
      resolutionCompactSuffix
        (advanceCounterPastAtoms counter [.var "$findall_x"])
  refine ⟨[.generated firstFresh], [copiedName], ?_, ?_⟩
  · exact
      { cardinality := rfl
        referenceInjective := by simp
        executableInjective := by simp }
  · exact
      CanonicalRuntimeAgrees.variable (by
        simp [RuntimeAlpha.graph, copiedName])

private def sharedSourceValue : Term :=
  .list
    [.variable residualAliasX, .variable residualAliasX]
    none

private def splitRuntimeValue : Atom :=
  consC (.var "$split_left")
    (consC (.var "$split_right") nilA)

private theorem sharedSourceValue_links
    {alpha : List (LogicVar × String)}
    (agreement :
      CanonicalRuntimeAgrees alpha
        (Term.denote sharedSourceValue) splitRuntimeValue) :
    (residualAliasX, "$split_left") ∈ alpha ∧
      (residualAliasX, "$split_right") ∈ alpha := by
  cases agreement with
  | cons left rest =>
      cases left with
      | «variable» leftLink =>
          cases rest with
          | cons right tail =>
              cases right with
              | «variable» rightLink =>
                  exact ⟨leftLink, rightLink⟩

/-- Runtime-alpha agreement still rejects a sharing change: two occurrences
of one source variable cannot be related to two distinct executable
variables.  This is the lower bound on the premise generalization. -/
theorem runtimeTermAgrees_rejects_split_sharing :
    ¬ RuntimeTermAgrees sharedSourceValue splitRuntimeValue := by
  intro agreement
  rcases agreement with
    ⟨referenceSupport, executableSupport, alpha, values⟩
  have links := sharedSourceValue_links values
  have impossible :=
    runtimeAlpha_graph_left_unique alpha links.1 links.2
  simp at impossible

end PLeaTTa.PrologFindallResidualVariantBridge
