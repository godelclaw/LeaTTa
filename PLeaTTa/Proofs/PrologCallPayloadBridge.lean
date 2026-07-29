-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologCallPayloadBridge
Purpose: Construct normalized call-head agreement from the real independent
  clause copier, call-entry substitution, and executable candidate payload.
Trusted boundary: none
Main exports: NormalizedCallAgrees,
  SupportedPreparedCandidateAgrees,
  supportedPreparedCandidate_normalizedHeadAgrees
-/
import PLeaTTa.Proofs.PrologPrefilterScanBridge

namespace PLeaTTa.PrologCallPayloadBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open CompilerAdequacy
open CompilerSubstitutionAdequacy
open OpenBindingAgreement
open PrologStateBridge
open PrologCallEntryBridge
open PrologPrefilterBridge

/-! ## Representation lemmas used at the prefilter seam -/

private theorem payloadAtomSize_le_sum_of_mem {atom : Atom} :
    (atoms : List Atom) → atom ∈ atoms →
      atom.size ≤ (atoms.map Atom.size).sum
  | [], member => by simp at member
  | head :: tail, member => by
      simp only [List.mem_cons] at member
      rcases member with rfl | later
      · simp
      · simp only [List.map_cons, List.sum_cons]
        exact Nat.le_trans (payloadAtomSize_le_sum_of_mem tail later)
          (Nat.le_add_left _ _)

@[elab_as_elim, induction_eliminator]
private def payloadAtomRecAux {motive : Atom → Prop}
    (sym : ∀ name, motive (.sym name))
    («variable» : ∀ name, motive (.var name))
    (ground : ∀ value, motive (.gnd value))
    (expression :
      ∀ atoms, (∀ atom ∈ atoms, motive atom) → motive (.expr atoms)) :
    (atom : Atom) → motive atom
  | .sym name => sym name
  | .var name => «variable» name
  | .gnd value => ground value
  | .expr atoms =>
      expression atoms fun atom _member =>
        payloadAtomRecAux sym «variable» ground expression atom
termination_by atom => atom.size
decreasing_by
  simp only [Atom.size]
  simpa [Nat.add_comm] using
    Nat.lt_add_one_of_le
      (payloadAtomSize_le_sum_of_mem atoms _member)

/-- Renaming runtime variables by the empty suffix is extensionally the
identity on the complete atom tree. -/
@[simp] theorem renameAtomSuffix_empty (atom : Atom) :
    renameAtomSuffix "" atom = atom := by
  induction atom using payloadAtomRecAux with
  | sym name =>
      simp [renameAtomSuffix_sym]
  | «variable» name =>
      simp [renameAtomSuffix_var]
  | ground value =>
      simp [renameAtomSuffix_gnd]
  | expression atoms inductionHypothesis =>
      rw [renameAtomSuffix_expr]
      have mapped :
          atoms.map (renameAtomSuffix "") = atoms.map id :=
        List.map_congr_left fun child member =>
          inductionHypothesis child member
      rw [mapped, List.map_id]

@[simp] theorem map_renameAtomSuffix_empty (atoms : List Atom) :
    atoms.map (renameAtomSuffix "") = atoms := by
  have mapped :
      atoms.map (renameAtomSuffix "") = atoms.map id :=
    List.map_congr_left fun atom _member =>
      renameAtomSuffix_empty atom
  rw [mapped, List.map_id]

/-- Empty-suffix graph used only for the conservative prefilter.  Unlike the
later executable freshened body, the prefilter sees the stored clause before
the per-alternative suffix has been installed. -/
def prefilterAlpha (reference : LocalClause) (freshSeed : Nat) :
    List (LogicVar × String) :=
  RuntimeAlpha.graph
    (referenceFreshTargets
      (reference.freshCopy freshSeed).firstFresh reference.variables)
    (executableFreshTargets "" reference.variables)

/-- The actual independent fresh clause head is alpha-related directly to
the original executable candidate inspected by `resolutionClauseRetained`.
No executable scan result appears in the proof. -/
theorem freshCopy_prefilter_head_alpha_agrees
    {reference : LocalClause} {executablePredicate : String}
    {executable : PLeaTTa.Clause}
    (base :
      LocalClauseAgrees reference (executablePredicate, executable))
    (freshSeed : Nat) :
    LocalClauseHeadAlphaAgrees
      (prefilterAlpha reference freshSeed)
      (reference.freshCopy freshSeed).clause
      (executablePredicate, executable) := by
  rcases base.outputLast with
    ⟨referenceParameters, referenceResult, arguments,
      parameters, resultAgreement⟩
  have argumentsSupported := LocalClause.arguments_supported reference
  rw [arguments, termsVariablesIn_append] at argumentsSupported
  have resultSupported :
      termVariablesIn reference.variables referenceResult := by
    simpa [termsVariablesIn] using argumentsSupported.2
  have variableAgreement :
      ∀ identity, identity ∈ reference.variables →
        ∃ target,
          (reference.freshCopy freshSeed).freshSubstitution.applyTerm
              (.variable identity) =
            .variable target ∧
          (target, logicVarExecutableName identity ++ "") ∈
            prefilterAlpha reference freshSeed := by
    intro identity member
    exact LocalClause.freshCopy_alpha_variable
      reference freshSeed "" member
  constructor
  · simpa only [LocalClause.freshCopy_predicate] using base.predicate
  · refine ⟨
      (reference.freshCopy freshSeed).freshSubstitution.applyTerms
        referenceParameters,
      (reference.freshCopy freshSeed).freshSubstitution.applyTerm
        referenceResult,
      ?_, ?_, ?_⟩
    · change
        (reference.freshCopy freshSeed).freshSubstitution.applyTerms
            reference.arguments =
          (reference.freshCopy freshSeed).freshSubstitution.applyTerms
              referenceParameters ++
            [(reference.freshCopy freshSeed).freshSubstitution.applyTerm
              referenceResult]
      rw [arguments, applyTerms_append]
      simp
    · have transported :=
        termsAgree_alpha_freshen variableAgreement parameters
          argumentsSupported.1
      simpa only [prefilterAlpha, map_renameAtomSuffix_empty]
        using transported
    · have transported :=
        termAgrees_alpha_freshen variableAgreement resultAgreement
          resultSupported
      simpa only [prefilterAlpha, renameAtomSuffix_empty] using transported

/-- An injective source encoding makes the empty-suffix alpha graph a genuine
bijection, so every reference identity appearing in it lies in the reserved
generated interval. -/
theorem prefilterAlpha_generated_range
    {reference : LocalClause} {freshSeed : Nat}
    (encoding : EncodingInjectiveOn reference.variables) :
    ∀ identity name,
      (identity, name) ∈ prefilterAlpha reference freshSeed →
        ∃ index, identity = .generated index ∧
          (reference.freshCopy freshSeed).firstFresh ≤ index := by
  intro identity name member
  have alpha :=
    freshenClause_alpha_agrees reference freshSeed "" encoding
  have identityMember :
      identity ∈
        referenceFreshTargets
          (reference.freshCopy freshSeed).firstFresh
          reference.variables := by
    have graphMember :
        identity ∈
          (RuntimeAlpha.graph
            (referenceFreshTargets
              (reference.freshCopy freshSeed).firstFresh
              reference.variables)
            (executableFreshTargets "" reference.variables)).map Prod.fst := by
      exact List.mem_map.mpr ⟨(identity, name), member, rfl⟩
    simpa [RuntimeAlpha.graph_reference alpha] using graphMember
  exact referenceFreshTargets_generated_lower identityMember

/-- Pointwise version of the generated-bound substitution stability theorem.
-/
theorem Substitution.applyTerms_eq_self_of_generatedAtLeast
    {lower : Nat} {bindings : Substitution} {terms : List Term}
    (domains : Substitution.DomainsBelow lower bindings)
    (above : Terms.GeneratedAtLeast lower terms) :
    bindings.applyTerms terms = terms := by
  induction terms with
  | nil =>
      simp
  | cons term terms inductionHypothesis =>
      rw [Substitution.applyTerms_cons]
      exact congrArg₂ List.cons
        (Substitution.applyTerm_eq_self_of_generatedAtLeast
          domains above.1)
        (inductionHypothesis above.2)

@[simp] theorem Substitution.applyTerms_length
    (bindings : Substitution) (terms : List Term) :
    (bindings.applyTerms terms).length = terms.length := by
  induction terms with
  | nil =>
      simp
  | cons term terms inductionHypothesis =>
      simp [inductionHypothesis]

/-- Applying one substitution to both sides of every pointwise equation is
exactly `argumentEquations` over the two substituted lists. -/
theorem map_argumentEquations_applyTerm_of_length_eq
    (bindings : Substitution) :
    ∀ left right, left.length = right.length →
      (argumentEquations left right).map (fun equation =>
        (bindings.applyTerm equation.1,
          bindings.applyTerm equation.2)) =
        argumentEquations
          (bindings.applyTerms left) (bindings.applyTerms right)
  | [], [], _ => by simp [argumentEquations]
  | [], _ :: _, lengths => by simp at lengths
  | _ :: _, [], lengths => by simp at lengths
  | left :: lefts, right :: rights, lengths => by
      have tailLengths : lefts.length = rights.length := by
        simpa using Nat.succ.inj lengths
      simp [argumentEquations,
        map_argumentEquations_applyTerm_of_length_eq
          bindings lefts rights tailLengths]

/-! ## Constructing the normalized head contract -/

/-- Complete call-entry payload relation after applying the carried
substitutions.  It relates the independent output-last call arguments to the
exact executable values inspected by `resolutionClauseRetained`; it says
nothing about any candidate or scan decision. -/
structure NormalizedCallAgrees
    (alpha : List (LogicVar × String))
    (cursor : PreparedCursor) (argsv : List Atom) (resv : Atom) : Prop where
  arguments :
    AlphaTermsAgree alpha
      (cursor.bindings.applyTerms cursor.arguments)
      (argsv ++ [resv])

/-- Normalizing the head equations of one concrete eagerly prepared branch
is exactly pointwise equation construction over the two normalized argument
lists.  The equal-length premise is explicit because `argumentEquations`
deliberately has malformed-arity fallback cases, whereas `List.map` does not
commute through those cases. -/
theorem preparedBranchOf_normalizedHeadEquations_eq
    (callGeneration : Generation) (arguments : List Term)
    (bindings : Substitution) (freshSeed : Nat)
    (reference : VersionedClause)
    (lengths :
      arguments.length =
        (reference.clause.freshCopy freshSeed).clause.arguments.length) :
    (preparedBranchOf callGeneration arguments bindings freshSeed reference
        ).normalizedHeadEquations =
      argumentEquations
        (bindings.applyTerms arguments)
        (bindings.applyTerms
          (reference.clause.freshCopy freshSeed).clause.arguments) := by
  change
    (argumentEquations arguments
        (reference.clause.freshCopy freshSeed).clause.arguments).map
        (fun equation =>
          (bindings.applyTerm equation.1,
            bindings.applyTerm equation.2)) =
      argumentEquations
        (bindings.applyTerms arguments)
        (bindings.applyTerms
          (reference.clause.freshCopy freshSeed).clause.arguments)
  exact map_argumentEquations_applyTerm_of_length_eq
    bindings arguments
      (reference.clause.freshCopy freshSeed).clause.arguments lengths

/-- Supported-source strengthening of `PreparedCandidateAgrees`.  The
executable string encoding is not globally injective, so the finite
per-clause premise is explicit and the known source/generated collision stays
outside the theorem. -/
inductive SupportedPreparedCandidateAgrees
    (callGeneration : Generation) (predicate : String)
    (arguments : List Term) (bindings : Substitution) :
    ClauseBranch → PLeaTTa.Clause → Prop where
  | intro (reference : VersionedClause) (freshSeed : Nat)
      (executable : PLeaTTa.Clause)
      (base : CandidateClauseAgrees predicate reference executable)
      (encoding : EncodingInjectiveOn reference.clause.variables)
      (bodySupported :
        CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
          reference.clause.variables reference.clause.variables base.body) :
      SupportedPreparedCandidateAgrees callGeneration predicate
        arguments bindings
        (preparedBranchOf callGeneration arguments bindings freshSeed
          reference)
        executable

/-- Forgetting the supported-source certificate recovers the exact candidate
spine relation used at call entry. -/
theorem SupportedPreparedCandidateAgrees.prepared
    {callGeneration : Generation} {predicate : String}
    {arguments : List Term} {bindings : Substitution}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    (agreement :
      SupportedPreparedCandidateAgrees callGeneration predicate
        arguments bindings branch clause) :
    PreparedCandidateAgrees callGeneration predicate arguments bindings
      branch clause := by
  cases agreement with
  | intro reference freshSeed executable base encoding bodySupported =>
      exact .intro reference freshSeed clause base

/-- One real prepared occurrence satisfies the normalized-head contract.
The proof uses the cursor reservation to show that the call-entry
substitution cannot touch the freshly copied clause variables. -/
theorem supportedPreparedCandidate_normalizedHeadAgrees
    {queryAlpha : List (LogicVar × String)}
    {cursor : PreparedCursor} {argsv : List Atom} {resv : Atom}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    (query : NormalizedCallAgrees queryAlpha cursor argsv resv)
    (wellFormed : cursor.WellFormed)
    (member : branch ∈ cursor.remaining)
    (agreement :
      SupportedPreparedCandidateAgrees cursor.callGeneration
        cursor.predicate cursor.arguments cursor.bindings branch clause)
    (arity : clause.params.length = argsv.length) :
    NormalizedHeadAgrees branch argsv resv clause := by
  cases agreement with
  | intro reference freshSeed executable base encoding bodySupported =>
      have startsAbove :
          cursor.reservationStart ≤
            (reference.clause.freshCopy freshSeed).firstFresh := by
        have starts :=
          wellFormed.1.start_le_member_first member
        simpa [preparedBranchOf] using starts
      have bindingBelowStart :
          GeneratedBelow cursor.reservationStart
            (substitutionVariables cursor.bindings) := by
        intro index indexMember
        exact wellFormed.2.1 index (by
          exact List.mem_append_right _ indexMember)
      have bindingBelowFresh :
          GeneratedBelow
            (reference.clause.freshCopy freshSeed).firstFresh
            (substitutionVariables cursor.bindings) :=
        bindingBelowStart.mono startsAbove
      have domains :
          Substitution.DomainsBelow
            (reference.clause.freshCopy freshSeed).firstFresh
            cursor.bindings :=
        Substitution.domainsBelow_of_generatedBelow bindingBelowFresh
      have headAgreement :=
        freshCopy_prefilter_head_alpha_agrees base freshSeed
      rcases headAgreement.outputLast with
        ⟨referenceParameters, referenceResult, referenceArguments,
          parameterAgreement, resultAgreement⟩
      have fullClauseAgreement :
          AlphaTermsAgree
            (prefilterAlpha reference.clause freshSeed)
            (reference.clause.freshCopy freshSeed).clause.arguments
            (clause.params ++ [clause.result]) := by
        rw [referenceArguments]
        exact
          PLeaTTa.PrologPrefilterBridge.AlphaTermsAgree.append_singleton
            parameterAgreement resultAgreement
      have generated :
          Terms.GeneratedAtLeast
            (reference.clause.freshCopy freshSeed).firstFresh
            (reference.clause.freshCopy freshSeed).clause.arguments :=
        PLeaTTa.PrologPrefilterBridge.AlphaTermsAgree.generatedAtLeast_of_graph
          fullClauseAgreement (prefilterAlpha_generated_range encoding)
      have stable :
          cursor.bindings.applyTerms
              (reference.clause.freshCopy freshSeed).clause.arguments =
            (reference.clause.freshCopy freshSeed).clause.arguments :=
        Substitution.applyTerms_eq_self_of_generatedAtLeast domains generated
      have normalizedLengths :
          (cursor.bindings.applyTerms cursor.arguments).length =
            (reference.clause.freshCopy freshSeed).clause.arguments.length := by
        have queryLength :=
          PLeaTTa.PrologPrefilterBridge.AlphaTermsAgree.length_eq
            query.arguments
        have clauseLength :=
          PLeaTTa.PrologPrefilterBridge.AlphaTermsAgree.length_eq
            fullClauseAgreement
        simp only [List.length_append, List.length_singleton] at queryLength clauseLength
        omega
      have rawLengths :
          cursor.arguments.length =
            (reference.clause.freshCopy freshSeed).clause.arguments.length := by
        simpa only [Substitution.applyTerms_length] using normalizedLengths
      have normalizedEquations :
          (preparedBranchOf cursor.callGeneration cursor.arguments
              cursor.bindings freshSeed reference).normalizedHeadEquations =
            argumentEquations
              (cursor.bindings.applyTerms cursor.arguments)
              (cursor.bindings.applyTerms
                (reference.clause.freshCopy freshSeed).clause.arguments) := by
        exact preparedBranchOf_normalizedHeadEquations_eq
          cursor.callGeneration cursor.arguments cursor.bindings freshSeed
          reference rawLengths
      constructor
      · exact arity
      · rw [normalizedEquations, stable]
        exact
          PLeaTTa.PrologPrefilterBridge.AlphaTermsAgree.alphaEquationsAgree
            query.arguments fullClauseAgreement normalizedLengths

end PLeaTTa.PrologCallPayloadBridge
