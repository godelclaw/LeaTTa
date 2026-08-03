-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologRepresentativeCallPrefilterBridge
Purpose: Preserve conservative local-clause filtering when recursive calls
  carry semantically variant residual-MGU orientations.
Trusted boundary: none
Main exports:
  RepresentativeNormalizedCallAgrees.retained_of_headResolution,
  RepresentativeNormalizedCallAgrees.no_headResolution_of_rejected
-/
import PLeaTTa.Proofs.PrologRecursiveCallPayloadBridge

namespace PLeaTTa.PrologRepresentativeCallPrefilterBridge

open Metta (Atom)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open PrologActivationBridge
open PrologActivationMacro
open PrologCallEntryBridge
open PrologCallPayloadBridge
open PrologMguOpenAgreement
open PrologMguVariant
open PrologPrefilterBridge
open PrologRecursiveCallPayloadBridge
open PrologStateBridge

/-!
The independently ordered resolver and executable resolver may orient a
residual variable alias in opposite directions.  The executable prefilter,
however, observes only immediate rigid clashes.  If the actual source call
is an instance of one hidden representative call, then every structural
match available to the source remains available to that more-general
representative.  This is the exact semantic weakening needed to retain
recursive candidates without choosing an association-list orientation.
-/

/-- Pointwise semantic call/head agreement is sufficient for the exact
runtime compatibility scan.

`factor` says that the actual source binding is an instance of the hidden
representative.  The independently resolved normalized equations therefore
give structural compatibility for the more-general representative query.
The right payload is fixed by the source binding because it is one eagerly
freshened clause head above the cursor reservation. -/
private theorem representative_prologMatchCompatList_of_pointwise_unifiable
    {queryAlpha clauseAlpha : List (LogicVar × String)}
    {sourceBindings : Substitution}
    {representative residual : TreeSubstitution}
    (factor :
      ∀ tree,
        TreeSubstitution.apply (Substitution.denote sourceBindings) tree =
          TreeSubstitution.apply residual
            (TreeSubstitution.apply representative tree))
    {leftTerms rightTerms : List Term}
    {leftAtoms rightAtoms : List Atom}
    (left :
      List.Forall₂
        (fun term atom =>
          CanonicalRuntimeAgrees queryAlpha
            (TreeSubstitution.apply representative (Term.denote term))
            atom)
        leftTerms leftAtoms)
    (right :
      AlphaTermsAgree clauseAlpha rightTerms rightAtoms)
    (lengths : leftTerms.length = rightTerms.length)
    (stable :
      sourceBindings.applyTerms rightTerms = rightTerms)
    (unifies :
      ∀ equation,
        equation ∈
            argumentEquations
              (sourceBindings.applyTerms leftTerms)
              (sourceBindings.applyTerms rightTerms) →
          ∃ candidate : Substitution,
            DenotationalUnifier candidate equation.1 equation.2) :
    PLeaTTa.prologMatchCompatList leftAtoms rightAtoms = true := by
  induction left generalizing rightTerms rightAtoms with
  | nil =>
      cases right with
      | nil =>
          rfl
      | cons =>
          simp at lengths
  | @cons leftTerm leftAtom leftTerms leftAtoms leftHead leftTail
      inductionHypothesis =>
      cases right with
      | nil =>
          simp at lengths
      | @cons rightTerm rightAtom rightTerms rightAtoms rightHead rightTail =>
          have tailLengths :
              leftTerms.length = rightTerms.length := by
            simpa using Nat.succ.inj lengths
          have stableParts :
              sourceBindings.applyTerm rightTerm = rightTerm ∧
                sourceBindings.applyTerms rightTerms = rightTerms := by
            simpa only [Substitution.applyTerms_cons, List.cons.injEq] using
              stable
          obtain ⟨candidate, headUnifies⟩ :=
            unifies
              (sourceBindings.applyTerm leftTerm,
                sourceBindings.applyTerm rightTerm)
              (by simp [argumentEquations])
          have sourceCompatible :
              TreeMayUnify
                (TreeSubstitution.apply residual
                  (TreeSubstitution.apply representative
                    (Term.denote leftTerm)))
                (Term.denote rightTerm) := by
            have compatible :=
              TreeMayUnify.of_denotationalUnifier headUnifies
            rw [Substitution.denote_applyTerm,
              factor (Term.denote leftTerm),
              stableParts.1] at compatible
            exact compatible
          have representativeCompatible :
              TreeMayUnify
                (TreeSubstitution.apply representative
                  (Term.denote leftTerm))
                (Term.denote rightTerm) :=
            TreeMayUnify.of_left_apply residual _ _ sourceCompatible
          have headRetained :
              PLeaTTa.prologMatchCompat leftAtom rightAtom = true :=
            CanonicalRuntimeAgrees.prologMatchCompat_of_treeMayUnify
              leftHead
              (PLeaTTa.PrologPrefilterBridge.AlphaTermAgrees.canonicalRuntimeAgrees
                rightHead)
              representativeCompatible
          have tailUnifies :
              ∀ equation,
                equation ∈
                    argumentEquations
                      (sourceBindings.applyTerms leftTerms)
                      (sourceBindings.applyTerms rightTerms) →
                  ∃ candidate : Substitution,
                    DenotationalUnifier candidate equation.1 equation.2 := by
            intro equation member
            exact unifies equation (by
              simp only [Substitution.applyTerms_cons, argumentEquations,
                List.mem_cons]
              exact Or.inr member)
          simp only [PLeaTTa.prologMatchCompatList]
          rw [headRetained,
            inductionHypothesis rightTail tailLengths stableParts.2
              tailUnifies]
          rfl

/-- Common-unifier specialization retained for the existing full-head
conservativity theorem. -/
private theorem representative_prologMatchCompatList_of_unifier
    {queryAlpha clauseAlpha : List (LogicVar × String)}
    {sourceBindings : Substitution}
    {representative residual : TreeSubstitution}
    (factor :
      ∀ tree,
        TreeSubstitution.apply (Substitution.denote sourceBindings) tree =
          TreeSubstitution.apply residual
            (TreeSubstitution.apply representative tree))
    {leftTerms rightTerms : List Term}
    {leftAtoms rightAtoms : List Atom}
    (left :
      List.Forall₂
        (fun term atom =>
          CanonicalRuntimeAgrees queryAlpha
            (TreeSubstitution.apply representative (Term.denote term)) atom)
        leftTerms leftAtoms)
    (right : AlphaTermsAgree clauseAlpha rightTerms rightAtoms)
    (lengths : leftTerms.length = rightTerms.length)
    (stable : sourceBindings.applyTerms rightTerms = rightTerms)
    {candidate : Substitution}
    (unifies :
      DenotationalUnifiesEquations candidate
        (argumentEquations
          (sourceBindings.applyTerms leftTerms)
          (sourceBindings.applyTerms rightTerms))) :
    PLeaTTa.prologMatchCompatList leftAtoms rightAtoms = true := by
  exact representative_prologMatchCompatList_of_pointwise_unifiable factor
    left right lengths stable (fun equation member =>
      ⟨candidate, unifies equation member⟩)

/-- A semantic normalized call and one supported prepared clause occurrence
make the executable prefilter conservative even when the carried residual
MGUs use opposite association-list orientations. -/
theorem RepresentativeNormalizedCallAgrees.retained_of_headResolution
    {queryAlpha : List (LogicVar × String)}
    {cursor : PreparedCursor} {argsv : List Atom} {resv : Atom}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    (query :
      RepresentativeNormalizedCallAgrees queryAlpha cursor argsv resv)
    (wellFormed : cursor.WellFormed)
    (member : branch ∈ cursor.remaining)
    (agreement :
      SupportedPreparedCandidateAgrees cursor.callGeneration
        cursor.predicate cursor.arguments cursor.bindings branch clause)
    (arity : clause.params.length = argsv.length)
    (resolves : ∃ result, HeadResolution branch result) :
    resolutionClauseRetained argsv resv clause = true := by
  rcases query with
    ⟨residualRepresentative, olderBase, variants,
      _residualCovered, _olderBaseIncluded, queryArguments⟩
  let representative :=
    residualRepresentative ++ Substitution.denote olderBase
  cases agreement with
  | intro reference freshSeed executable base encoding bodySupported =>
      have startsAbove :
          cursor.reservationStart ≤
            (reference.clause.freshCopy freshSeed).firstFresh := by
        have starts := wellFormed.1.start_le_member_first member
        simpa [preparedBranchOf] using starts
      have bindingBelowStart :
          GeneratedBelow cursor.reservationStart
            (substitutionVariables cursor.bindings) := by
        intro index indexMember
        exact wellFormed.2.1 index
          (List.mem_append_right _ indexMember)
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
        exact AlphaTermsAgree.append_singleton
          parameterAgreement resultAgreement
      have generated :
          Terms.GeneratedAtLeast
            (reference.clause.freshCopy freshSeed).firstFresh
            (reference.clause.freshCopy freshSeed).clause.arguments :=
        AlphaTermsAgree.generatedAtLeast_of_graph
          fullClauseAgreement (prefilterAlpha_generated_range encoding)
      have stable :
          cursor.bindings.applyTerms
              (reference.clause.freshCopy freshSeed).clause.arguments =
            (reference.clause.freshCopy freshSeed).clause.arguments :=
        Substitution.applyTerms_eq_self_of_generatedAtLeast domains generated
      have rawLengths :
          cursor.arguments.length =
            (reference.clause.freshCopy freshSeed).clause.arguments.length := by
        have queryLength := queryArguments.length_eq
        have clauseLength := AlphaTermsAgree.length_eq fullClauseAgreement
        simp only [List.length_append, List.length_singleton] at queryLength
        simp only [List.length_append, List.length_singleton] at clauseLength
        calc
          cursor.arguments.length = argsv.length + 1 := queryLength
          _ = clause.params.length + 1 := by rw [arity]
          _ =
              (reference.clause.freshCopy
                freshSeed).clause.arguments.length :=
            clauseLength.symm
      have normalizedEquations :
          (preparedBranchOf cursor.callGeneration cursor.arguments
              cursor.bindings freshSeed reference).normalizedHeadEquations =
            argumentEquations
              (cursor.bindings.applyTerms cursor.arguments)
              (cursor.bindings.applyTerms
                (reference.clause.freshCopy freshSeed).clause.arguments) :=
        preparedBranchOf_normalizedHeadEquations_eq
          cursor.callGeneration cursor.arguments cursor.bindings freshSeed
          reference rawLengths
      obtain ⟨candidate, candidateUnifies⟩ :=
        HeadResolution.exists_iff_unifiable.mp resolves
      have normalizedUnifies :
          DenotationalUnifiesEquations candidate
            (argumentEquations
              (cursor.bindings.applyTerms cursor.arguments)
              (cursor.bindings.applyTerms
                (reference.clause.freshCopy freshSeed).clause.arguments)) := by
        simpa only [normalizedEquations] using candidateUnifies
      rcases variants.1 with ⟨residual, factor⟩
      have fullCompatibility :
          PLeaTTa.prologMatchCompatList
              (argsv ++ [resv]) (clause.params ++ [clause.result]) =
            true :=
        representative_prologMatchCompatList_of_unifier factor
          queryArguments fullClauseAgreement rawLengths stable
          normalizedUnifies
      rw [prologMatchCompatList_append_singleton_of_length_eq
          argsv clause.params resv clause.result arity.symm]
          at fullCompatibility
      have split :
          PLeaTTa.prologMatchCompatList argsv clause.params = true ∧
            PLeaTTa.prologMatchCompat resv clause.result = true := by
        simpa only [Bool.and_eq_true] using fullCompatibility
      exact resolutionClauseRetained_true_iff argsv resv clause |>.mpr
        ⟨arity, split.1, split.2⟩

/-- Pointwise-unifiability strengthening of recursive-call prefilter
conservativity.  It captures genuine conservative false positives: each
normalized equation may have its own witness even when no single
substitution solves the complete head. -/
theorem RepresentativeNormalizedCallAgrees.retained_of_pointwise_unifiable
    {queryAlpha : List (LogicVar × String)}
    {cursor : PreparedCursor} {argsv : List Atom} {resv : Atom}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    (query :
      RepresentativeNormalizedCallAgrees queryAlpha cursor argsv resv)
    (wellFormed : cursor.WellFormed)
    (member : branch ∈ cursor.remaining)
    (agreement :
      SupportedPreparedCandidateAgrees cursor.callGeneration
        cursor.predicate cursor.arguments cursor.bindings branch clause)
    (arity : clause.params.length = argsv.length)
    (unifies :
      ∀ equation, equation ∈ branch.normalizedHeadEquations →
        ∃ candidate : Substitution,
          DenotationalUnifier candidate equation.1 equation.2) :
    resolutionClauseRetained argsv resv clause = true := by
  rcases query with
    ⟨residualRepresentative, olderBase, variants,
      _residualCovered, _olderBaseIncluded, queryArguments⟩
  let representative :=
    residualRepresentative ++ Substitution.denote olderBase
  cases agreement with
  | intro reference freshSeed executable base encoding bodySupported =>
      have startsAbove :
          cursor.reservationStart ≤
            (reference.clause.freshCopy freshSeed).firstFresh := by
        have starts := wellFormed.1.start_le_member_first member
        simpa [preparedBranchOf] using starts
      have bindingBelowStart :
          GeneratedBelow cursor.reservationStart
            (substitutionVariables cursor.bindings) := by
        intro index indexMember
        exact wellFormed.2.1 index
          (List.mem_append_right _ indexMember)
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
        exact AlphaTermsAgree.append_singleton
          parameterAgreement resultAgreement
      have generated :
          Terms.GeneratedAtLeast
            (reference.clause.freshCopy freshSeed).firstFresh
            (reference.clause.freshCopy freshSeed).clause.arguments :=
        AlphaTermsAgree.generatedAtLeast_of_graph
          fullClauseAgreement (prefilterAlpha_generated_range encoding)
      have stable :
          cursor.bindings.applyTerms
              (reference.clause.freshCopy freshSeed).clause.arguments =
            (reference.clause.freshCopy freshSeed).clause.arguments :=
        Substitution.applyTerms_eq_self_of_generatedAtLeast domains generated
      have rawLengths :
          cursor.arguments.length =
            (reference.clause.freshCopy freshSeed).clause.arguments.length := by
        have queryLength := queryArguments.length_eq
        have clauseLength := AlphaTermsAgree.length_eq fullClauseAgreement
        simp only [List.length_append, List.length_singleton] at queryLength
        simp only [List.length_append, List.length_singleton] at clauseLength
        calc
          cursor.arguments.length = argsv.length + 1 := queryLength
          _ = clause.params.length + 1 := by rw [arity]
          _ =
              (reference.clause.freshCopy
                freshSeed).clause.arguments.length :=
            clauseLength.symm
      have normalizedEquations :
          (preparedBranchOf cursor.callGeneration cursor.arguments
              cursor.bindings freshSeed reference).normalizedHeadEquations =
            argumentEquations
              (cursor.bindings.applyTerms cursor.arguments)
              (cursor.bindings.applyTerms
                (reference.clause.freshCopy freshSeed).clause.arguments) :=
        preparedBranchOf_normalizedHeadEquations_eq
          cursor.callGeneration cursor.arguments cursor.bindings freshSeed
          reference rawLengths
      have normalizedUnifies :
          ∀ equation,
            equation ∈
                argumentEquations
                  (cursor.bindings.applyTerms cursor.arguments)
                  (cursor.bindings.applyTerms
                    (reference.clause.freshCopy freshSeed).clause.arguments) →
              ∃ candidate : Substitution,
                DenotationalUnifier candidate equation.1 equation.2 := by
        simpa only [normalizedEquations] using unifies
      rcases variants.1 with ⟨residual, factor⟩
      have fullCompatibility :
          PLeaTTa.prologMatchCompatList
              (argsv ++ [resv]) (clause.params ++ [clause.result]) = true :=
        representative_prologMatchCompatList_of_pointwise_unifiable factor
          queryArguments fullClauseAgreement rawLengths stable
          normalizedUnifies
      rw [prologMatchCompatList_append_singleton_of_length_eq
          argsv clause.params resv clause.result arity.symm]
          at fullCompatibility
      have split :
          PLeaTTa.prologMatchCompatList argsv clause.params = true ∧
            PLeaTTa.prologMatchCompat resv clause.result = true := by
        simpa only [Bool.and_eq_true] using fullCompatibility
      exact resolutionClauseRetained_true_iff argsv resv clause |>.mpr
        ⟨arity, split.1, split.2⟩

/-- Contrapositive used by ordered scan alignment: semantic residual
variation cannot turn an executable prefilter rejection into a lost source
head solution. -/
theorem RepresentativeNormalizedCallAgrees.no_headResolution_of_rejected
    {queryAlpha : List (LogicVar × String)}
    {cursor : PreparedCursor} {argsv : List Atom} {resv : Atom}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    (query :
      RepresentativeNormalizedCallAgrees queryAlpha cursor argsv resv)
    (wellFormed : cursor.WellFormed)
    (member : branch ∈ cursor.remaining)
    (agreement :
      SupportedPreparedCandidateAgrees cursor.callGeneration
        cursor.predicate cursor.arguments cursor.bindings branch clause)
    (arity : clause.params.length = argsv.length)
    (rejected : resolutionClauseRetained argsv resv clause = false) :
    ¬ ∃ result, HeadResolution branch result := by
  intro resolves
  have retained :=
    PLeaTTa.PrologRepresentativeCallPrefilterBridge.RepresentativeNormalizedCallAgrees.retained_of_headResolution
      query wellFormed member agreement arity resolves
  rw [rejected] at retained
  contradiction

end PLeaTTa.PrologRepresentativeCallPrefilterBridge
