-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologRetractScanRegression
Purpose: Inhabit the decision-coupled retract scan with one real rejection
  followed by one real match, while discriminating its two fresh currencies.
Trusted boundary: none
[SPEC metta.pl:279-280]
-/
import PLeaTTa.Proofs.PrologRetractScanBridge

namespace PLeaTTa.PrologRetractScanRegression

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.DatabaseActions
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open PrologAlphaFreshFrontierBridge
open PrologMguBridge
open PrologRetractEncodingBridge
open PrologRetractScanBridge
open PrologStateBridge

/-! ## Literal two-occurrence frozen scan -/

def referenceClause (value : Int) : LocalClause :=
  { predicate := "p"
    arguments := [.integer value]
    body := [] }

def executableClause (value : Int) : PLeaTTa.Clause :=
  { params := []
    result := .gnd (.int value)
    body := [] }

def versionedClause (id : Nat) (value : Int) : VersionedClause :=
  { id := id
    clause := referenceClause value
    created := 0 }

def candidate (value : Int) : RetractClauseCandidate :=
  (("p", executableClause value), clauseAlphaKey (executableClause value))

def pattern : LocalClause := referenceClause 0

def executablePattern : Atom :=
  retractClauseSyntaxAtom "p" (executableClause 0)

def rejectedSource : VersionedClause := versionedClause 0 1
def selectedSource : VersionedClause := versionedClause 1 0
def rejectedCandidate : RetractClauseCandidate := candidate 1
def selectedCandidate : RetractClauseCandidate := candidate 0

@[simp] theorem ground_freshCopy_clause (id : Nat) (value : Int) :
    ((versionedClause id value).clause.freshCopy 0).clause =
      referenceClause value := by
  rfl

@[simp] theorem ground_freshCopy_next (id : Nat) (value : Int) :
    ((versionedClause id value).clause.freshCopy 0).nextFresh = 0 := by
  rfl

private theorem clauseAgrees (id : Nat) (value : Int) :
    RetractOccurrenceAgrees (versionedClause id value) (candidate value) := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := .nil
      support := ?_ }
  · exact
      ⟨[], .integer value, rfl, CompilerAdequacy.TermsAgree.nil,
        CompilerAdequacy.TermAgrees.integer value⟩
  · intro name
    simp [versionedClause, referenceClause, candidate, executableClause,
      LocalClause.variables, resolutionClauseVars, Metta.Atom.vars,
      specializationGoalsVars, termsVariables, termVariables, goalsVariables]

private theorem clauseReading (value : Int) :
    RetractSyntaxRuntimeReading []
      (Term.denote (clauseSyntaxTerm (referenceClause value)))
      (retractClauseSyntaxAtom "p" (executableClause value)) := by
  exact .clause (.cons (.integer value) .nil) .nil

private theorem copiedClauseReading (id counter : Nat) (value : Int) :
    RetractSyntaxRuntimeReading []
      (Term.denote
        (clauseSyntaxTerm
          ((versionedClause id value).clause.freshCopy 0).clause))
      (PLeaTTa.subst [] (executableRetractCopy counter (candidate value))) := by
  have closed :
      resolutionAtomClosed
          (retractClauseSyntaxAtom "p" (executableClause value)) = true := by
    simp [resolutionAtomClosed, PersistentSubst.atomClosed,
      PersistentSubst.atomsClosed, retractClauseSyntaxAtom,
      retractGoalsSyntaxAtom, executableClause, reservedSyntaxC,
      reservedSyntaxTagA, chainOf, consC, nilA]
  have renamed :=
    renameAtomSuffix_eq_self_of_resolutionAtomClosed
      (resolutionCompactSuffix counter)
      (retractClauseSyntaxAtom "p" (executableClause value)) closed
  simpa [executableRetractCopy, candidate, ground_freshCopy_clause,
    PLeaTTa.subst_nil, renamed] using clauseReading value

private theorem emptyAlphaShared : SharedRuntimeAlpha [] := by
  constructor <;> intro <;> simp_all

private theorem emptyFreshFrontier (reference executable : Nat) :
    AlphaFreshFrontier [] reference executable := by
  constructor
  · intro index member
    simp at member
  · simp [resolutionSeedHighWaterNames]

private theorem rejectedClash :
    ¬ ∃ binding,
      ComputesDenotationalMgu
        [(clauseSyntaxTerm pattern,
          clauseSyntaxTerm
            (rejectedSource.clause.freshCopy 0).clause)] binding := by
  rintro ⟨binding, computed⟩
  have unifies := computed.isMostGeneral.1
    (clauseSyntaxTerm pattern,
      clauseSyntaxTerm (rejectedSource.clause.freshCopy 0).clause)
    (by simp)
  unfold DenotationalUnifier at unifies
  let integerAtArgument : Tree → Option Int := fun tree =>
    match tree with
    | .node (.compound "$clause")
        [_predicate, .node .cons [.node (.integer value) [], _tail], _body] =>
        some value
    | _ => none
  have values := congrArg integerAtArgument unifies
  simp [pattern, rejectedSource, ground_freshCopy_clause,
    clauseSyntaxTerm, referenceClause, Term.denote, Terms.denote,
    goalsSyntaxTerms, Tree.prologList, TreeSubstitution.applyTrees_cons,
    TreeSubstitution.apply_node, integerAtArgument] at values

private theorem selectedComputed :
    ∃ binding,
      ComputesDenotationalMgu
        [(clauseSyntaxTerm pattern,
          clauseSyntaxTerm
            (selectedSource.clause.freshCopy 0).clause)] binding := by
  apply ComputesDenotationalMgu.exists_of_unifier []
  intro equation member
  simp only [List.mem_singleton] at member
  subst equation
  rfl

private def rejectedInspection :
    RetractCandidateInspection [] pattern executablePattern []
      0 7 rejectedSource rejectedCandidate := by
  refine
    { inspectionAlpha := []
      occurrence := clauseAgrees 0 1
      alphaExtension := AlphaExtendsAbove.refl [] 0 7
      freshFrontier := ?_
      shared := emptyAlphaShared
      patternReading := ?_
      copiedReading := ?_
      sourceComplete := ?_ }
  · change AlphaFreshFrontier [] 0 8
    exact emptyFreshFrontier 0 8
  · simpa [pattern, executablePattern] using clauseReading 0
  · simpa [rejectedSource, rejectedCandidate] using
      copiedClauseReading 0 7 1
  · intro binding computed
    exact False.elim (rejectedClash ⟨binding, computed⟩)

private theorem selectedExecutableComputed :
    PLeaTTa.unifyB [] executablePattern
        (executableRetractCopy 8 selectedCandidate) = some [] := by
  have closed :
      resolutionAtomClosed
          (retractClauseSyntaxAtom "p" (executableClause 0)) = true := by
    simp [resolutionAtomClosed, PersistentSubst.atomClosed,
      PersistentSubst.atomsClosed, retractClauseSyntaxAtom,
      retractGoalsSyntaxAtom, executableClause, reservedSyntaxC,
      reservedSyntaxTagA, chainOf, consC, nilA]
  have renamed :=
    renameAtomSuffix_eq_self_of_resolutionAtomClosed
      (resolutionCompactSuffix 8)
      (retractClauseSyntaxAtom "p" (executableClause 0)) closed
  simp [executablePattern, executableRetractCopy, selectedCandidate,
    candidate, renamed, PLeaTTa.unifyB, PLeaTTa.unifyTopExact_self]

private def selectedInspection :
    RetractCandidateInspection [] pattern executablePattern []
      0 8 selectedSource selectedCandidate := by
  refine
    { inspectionAlpha := []
      occurrence := clauseAgrees 1 0
      alphaExtension := AlphaExtendsAbove.refl [] 0 8
      freshFrontier := ?_
      shared := emptyAlphaShared
      patternReading := ?_
      copiedReading := ?_
      sourceComplete := ?_ }
  · change AlphaFreshFrontier [] 0 9
    exact emptyFreshFrontier 0 9
  · simpa [pattern, executablePattern] using clauseReading 0
  · simpa [selectedSource, selectedCandidate] using
      copiedClauseReading 1 8 0
  · intro binding computed
    exact ⟨[], selectedExecutableComputed⟩

private def spine :
    RetractScanSpine [] pattern executablePattern [] 0 7
      [rejectedSource, selectedSource]
      [rejectedCandidate, selectedCandidate] :=
  .cons rejectedInspection
    (.cons selectedInspection (.nil 0 9))

/-! ## Exact inhabited coupling and anti-forgery discriminators -/

/-- The single traversal is inhabited by a genuine rejected occurrence and
then the literal selected occurrence.  The source frontier remains zero
because both clauses are ground, while the executable frontier records both
inspections and reaches nine. -/
theorem rejected_then_selected_exact :
    ∃ sourceBinding,
      ∃ sourceScan : RetractScan pattern 0
          [rejectedSource, selectedSource]
          (.matched selectedSource sourceBinding 0),
        sourceScan.rejectedPrefix = [rejectedSource] ∧
          (spine.couple sourceScan).1 =
            (.matched [rejectedCandidate] selectedCandidate [] [] 9 :
              RetractClauseScanOutcome Subst) := by
  obtain ⟨sourceBinding, computed⟩ := selectedComputed
  let selectedScan : RetractScan pattern 0 [selectedSource]
      (.matched selectedSource sourceBinding 0) := by
    simpa [selectedSource, ground_freshCopy_next] using
      RetractScan.matched 0 selectedSource [] sourceBinding computed
  let sourceScan : RetractScan pattern 0
      [rejectedSource, selectedSource]
      (.matched selectedSource sourceBinding 0) :=
    .skipped 0 rejectedSource [selectedSource]
      (.matched selectedSource sourceBinding 0) rejectedClash selectedScan
  refine ⟨sourceBinding, sourceScan, ?_, ?_⟩
  · rfl
  · have projected := (spine.couple sourceScan).2.executableScan
    have rejectedExecutable :=
      rejectedInspection.executableRejects rejectedClash
    have expected :
        retractClauseScanWith PLeaTTa.unifyB executablePattern 7 []
            [rejectedCandidate, selectedCandidate] =
          (.matched [rejectedCandidate] selectedCandidate [] [] 9 :
            RetractClauseScanOutcome Subst) := by
      simp only [retractClauseScanWith]
      have rejectedRaw :
          PLeaTTa.unifyB [] executablePattern
              (renameAtomSuffix (resolutionCompactSuffix 7)
                (retractClauseSyntaxAtom rejectedCandidate.1.1
                  rejectedCandidate.1.2)) = none := by
        simpa only [executableRetractCopy] using rejectedExecutable
      rw [rejectedRaw]
      have selectedRaw :
          PLeaTTa.unifyB [] executablePattern
              (renameAtomSuffix (resolutionCompactSuffix 8)
                (retractClauseSyntaxAtom selectedCandidate.1.1
                  selectedCandidate.1.2)) = some [] := by
        simpa only [executableRetractCopy] using selectedExecutableComputed
      rw [selectedRaw]
    exact projected.symm.trans expected

/-- The open-factor handoff follows the same literal selected occurrence.  In
particular, one rejected occurrence moves the executable copy counter from
seven to eight while the two ground source clauses keep the source fresh seed
at zero; neither counter can be borrowed from the rejected head. -/
theorem rejected_then_selected_open_factor_has_exact_frontiers :
    ∃ sourceBinding,
      ∃ selectedAlpha canonical generated,
        AlphaExtendsAbove [] selectedAlpha 0 8 ∧
          AlphaFreshFrontier selectedAlpha 0 9 ∧
          SharedRuntimeAlpha selectedAlpha ∧
          sourceBinding = TreeSubstitution.reify canonical ∧
          PLeaTTa.unifyTopExact
              (PLeaTTa.subst [] executablePattern)
              (PLeaTTa.subst []
                (executableRetractCopy 8 selectedCandidate)) =
            some generated ∧
          PrologMguExecutableOpenFactor.OpenAlphaResultFactors
            selectedAlpha canonical generated := by
  obtain ⟨sourceBinding, computed⟩ := selectedComputed
  let selectedScan : RetractScan pattern 0 [selectedSource]
      (.matched selectedSource sourceBinding 0) := by
    simpa [selectedSource, ground_freshCopy_next] using
      RetractScan.matched 0 selectedSource [] sourceBinding computed
  let sourceScan : RetractScan pattern 0
      [rejectedSource, selectedSource]
      (.matched selectedSource sourceBinding 0) :=
    .skipped 0 rejectedSource [selectedSource]
      (.matched selectedSource sourceBinding 0) rejectedClash selectedScan
  let packed := spine.couple sourceScan
  obtain ⟨executableOutcome, coupled⟩ := packed
  have projected := coupled.executableScan
  have rejectedExecutable :=
    rejectedInspection.executableRejects rejectedClash
  have outcomeEq :
      executableOutcome =
        (.matched [rejectedCandidate] selectedCandidate [] [] 9 :
          RetractClauseScanOutcome Subst) := by
    have expected :
        retractClauseScanWith PLeaTTa.unifyB executablePattern 7 []
            [rejectedCandidate, selectedCandidate] =
          (.matched [rejectedCandidate] selectedCandidate [] [] 9 :
            RetractClauseScanOutcome Subst) := by
      simp only [retractClauseScanWith]
      have rejectedRaw :
          PLeaTTa.unifyB [] executablePattern
              (renameAtomSuffix (resolutionCompactSuffix 7)
                (retractClauseSyntaxAtom rejectedCandidate.1.1
                  rejectedCandidate.1.2)) = none := by
        simpa only [executableRetractCopy] using rejectedExecutable
      rw [rejectedRaw]
      have selectedRaw :
          PLeaTTa.unifyB [] executablePattern
              (renameAtomSuffix (resolutionCompactSuffix 8)
                (retractClauseSyntaxAtom selectedCandidate.1.1
                  selectedCandidate.1.2)) = some [] := by
        simpa only [executableRetractCopy] using selectedExecutableComputed
      rw [selectedRaw]
    exact projected.symm.trans expected
  rw [outcomeEq] at coupled
  obtain ⟨selectedAlpha, canonical, generated,
    selectedSourceSeed, selectedExecutableCounter,
    sourceSeedEq, executableCounterEq, alphaExtension,
    freshFrontier, selectedShared, sourceEq, derivation,
    generatedEq, factors, installed⟩ := coupled.matchedOpenFactor
  have rejectedPrefixLength :
      coupled.sourceScan.rejectedPrefix.length = 1 := by
    simpa using coupled.matched_rejected_length_eq
  have rejectedPrefixEq :
      coupled.sourceScan.rejectedPrefix = [rejectedSource] := by
    cases prefixEq : coupled.sourceScan.rejectedPrefix with
    | nil =>
        simp [prefixEq] at rejectedPrefixLength
    | cons head tail =>
        cases tail with
        | nil =>
            have partition := coupled.sourceScan.matched_partition
            simp [prefixEq] at partition
            have headEq := partition.1
            subst head
            rfl
        | cons second rest =>
            simp [prefixEq] at rejectedPrefixLength
  have selectedSourceSeedEq : selectedSourceSeed = 0 := by
    rw [rejectedPrefixEq] at sourceSeedEq
    simpa [RetractScan.freshAfterPrefix, rejectedSource,
      ground_freshCopy_next] using sourceSeedEq
  have selectedExecutableCounterEq : selectedExecutableCounter = 8 := by
    simpa using executableCounterEq
  have alphaExtensionExact :
      AlphaExtendsAbove [] selectedAlpha 0 8 := by
    rw [selectedSourceSeedEq, selectedExecutableCounterEq] at alphaExtension
    exact alphaExtension
  have generatedEqExact :
      PLeaTTa.unifyTopExact
          (PLeaTTa.subst [] executablePattern)
          (PLeaTTa.subst []
            (executableRetractCopy 8 selectedCandidate)) =
        some generated := by
    rw [selectedExecutableCounterEq] at generatedEq
    simpa using generatedEq
  subst selectedSourceSeed
  subst selectedExecutableCounter
  exact
    ⟨sourceBinding, selectedAlpha, canonical, generated,
      alphaExtensionExact, freshFrontier, selectedShared,
      sourceEq, generatedEqExact, factors⟩

end PLeaTTa.PrologRetractScanRegression
