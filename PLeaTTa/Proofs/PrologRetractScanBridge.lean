-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologRetractScanBridge
Purpose: Couple the independent and executable first-match retract scans by
  one Type-valued traversal of the occurrence-aligned live database.
Trusted boundary: none
Main exports: RetractCandidateInspection, RetractScanSpine,
  CoupledRetractScan, RetractScanSpine.couple
[SPEC metta.pl:279-280]
-/
import PLeaTTa.Proofs.PrologAlphaFreshFrontierBridge
import PLeaTTa.Proofs.PrologRetractOpenFactor

namespace PLeaTTa.PrologRetractScanBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.DatabaseActions
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open PrologAlphaFreshFrontierBridge
open PrologMguBridge
open PrologMguValuation
open PrologRetractEncodingBridge
open PrologRetractOpenFactor
open PrologStateBridge

/-!
The two scans allocate in different currencies: the independent scan reserves
one generated identity per distinct variable of every inspected clause, while
the executable scan consumes one resolution suffix per inspected occurrence.
Consequently the coupling below never equates the two counters.

More importantly, it does not accept two completed scans and then assume that
their prefixes agree.  `CoupledRetractScan` is the traversal.  Every skipped
constructor contains both exact clash decisions, and the matched constructor
contains both exact successes at the same aligned occurrence.  The source and
executable scans are projections proved from that single value.

Rejected copies use a temporary inspection alpha but contribute no surviving
binding, so the recursive constructor discards that alpha while advancing both
frontiers.  Only the matched inspection alpha is retained by the outcome.
-/

/-- Executable syntax copied for one inspected occurrence at its literal scan
counter. -/
def executableRetractCopy (counter : Nat)
    (candidate : RetractClauseCandidate) : Atom :=
  renameAtomSuffix (resolutionCompactSuffix counter)
    (retractClauseSyntaxAtom candidate.1.1 candidate.1.2)

/-- Positional source/executable occurrence agreement.  The executable key is
operational metadata; clause content and order are related by its first field.
-/
def RetractOccurrenceAgrees (source : VersionedClause)
    (executable : RetractClauseCandidate) : Prop :=
  VersionedClauseAgrees source executable.1

/-- Representation and completeness evidence for inspecting one aligned
occurrence.

`inspectionAlpha` may be temporary for a rejected occurrence.  Its exact
chronological extension and frontier certify the two real copies.  The strict
source-guided readings make executable success imply source success, while
`sourceComplete` is the explicit converse producer needed to rule out an
executable false negative.  Keeping that producer visible avoids hiding the
still-separate compiler-to-retract-encoding obligation inside the scan.
-/
structure RetractCandidateInspection
    (baseAlpha : List (LogicVar × String))
    (pattern : LocalClause) (executablePattern : Atom) (runtime : Subst)
    (sourceSeed executableCounter : Nat)
    (source : VersionedClause)
    (executable : RetractClauseCandidate) : Type where
  inspectionAlpha : List (LogicVar × String)
  occurrence : RetractOccurrenceAgrees source executable
  alphaExtension :
    AlphaExtendsAbove baseAlpha inspectionAlpha sourceSeed executableCounter
  freshFrontier :
    AlphaFreshFrontier inspectionAlpha
      (source.clause.freshCopy sourceSeed).nextFresh
      (executableCounter + 1)
  shared : SharedRuntimeAlpha inspectionAlpha
  patternReading :
    RetractSyntaxRuntimeReading inspectionAlpha
      (Term.denote (clauseSyntaxTerm pattern))
      (PLeaTTa.subst runtime executablePattern)
  copiedReading :
    RetractSyntaxRuntimeReading inspectionAlpha
      (Term.denote
        (clauseSyntaxTerm (source.clause.freshCopy sourceSeed).clause))
      (PLeaTTa.subst runtime
        (executableRetractCopy executableCounter executable))
  sourceComplete :
    ∀ sourceBinding,
      ComputesDenotationalMgu
          [(clauseSyntaxTerm pattern,
            clauseSyntaxTerm (source.clause.freshCopy sourceSeed).clause)]
          sourceBinding →
        ∃ executableBinding,
          PLeaTTa.unifyB runtime executablePattern
              (executableRetractCopy executableCounter executable) =
            some executableBinding

namespace RetractCandidateInspection

/-- An independently proved clash fixes the executable decision to `none`.
This is the reverse direction that prevents the executable scan from selecting
an occurrence which the source traversal rejected. -/
theorem executableRejects
    {baseAlpha : List (LogicVar × String)}
    {pattern : LocalClause} {executablePattern : Atom} {runtime : Subst}
    {sourceSeed executableCounter : Nat}
    {source : VersionedClause} {executable : RetractClauseCandidate}
    (inspection :
      RetractCandidateInspection baseAlpha pattern executablePattern runtime
        sourceSeed executableCounter source executable)
    (clash :
      ¬ ∃ sourceBinding,
        ComputesDenotationalMgu
          [(clauseSyntaxTerm pattern,
            clauseSyntaxTerm (source.clause.freshCopy sourceSeed).clause)]
          sourceBinding) :
    PLeaTTa.unifyB runtime executablePattern
        (executableRetractCopy executableCounter executable) = none := by
  exact
    unifyB_none_of_no_computed_retract_mgu runtime inspection.shared
      inspection.patternReading inspection.copiedReading clash

/-- A computed source success rules out executable rejection.  The theorem is
stated negatively because `unifyB` itself supplies the successful result as
Type-valued data when the coupled traversal inspects it. -/
theorem executableCannotReject
    {baseAlpha : List (LogicVar × String)}
    {pattern : LocalClause} {executablePattern : Atom} {runtime : Subst}
    {sourceSeed executableCounter : Nat}
    {source : VersionedClause} {executable : RetractClauseCandidate}
    (inspection :
      RetractCandidateInspection baseAlpha pattern executablePattern runtime
        sourceSeed executableCounter source executable)
    {sourceBinding : Substitution}
    (computed :
      ComputesDenotationalMgu
        [(clauseSyntaxTerm pattern,
          clauseSyntaxTerm (source.clause.freshCopy sourceSeed).clause)]
        sourceBinding) :
    PLeaTTa.unifyB runtime executablePattern
        (executableRetractCopy executableCounter executable) ≠ none := by
  intro rejected
  obtain ⟨executableBinding, accepted⟩ :=
    inspection.sourceComplete sourceBinding computed
  rw [rejected] at accepted
  cases accepted

/-- A selected aligned occurrence exposes the independent canonical MGU, the
actual generated executable component, semantic open factorization, and the
exact installation equation.  No equality between source and executable
association lists is asserted. -/
theorem selectedOpenFactor
    {baseAlpha : List (LogicVar × String)}
    {pattern : LocalClause} {executablePattern : Atom} {runtime : Subst}
    {sourceSeed executableCounter : Nat}
    {source : VersionedClause} {executable : RetractClauseCandidate}
    (inspection :
      RetractCandidateInspection baseAlpha pattern executablePattern runtime
        sourceSeed executableCounter source executable)
    {sourceBinding : Substitution}
    (sourceComputed :
      ComputesDenotationalMgu
        [(clauseSyntaxTerm pattern,
          clauseSyntaxTerm (source.clause.freshCopy sourceSeed).clause)]
        sourceBinding)
    {executableBinding : Subst}
    (executableComputed :
      PLeaTTa.unifyB runtime executablePattern
          (executableRetractCopy executableCounter executable) =
        some executableBinding) :
    ∃ canonical generated,
      sourceBinding = TreeSubstitution.reify canonical ∧
        OrderedTreeMgu
          [(Term.denote (clauseSyntaxTerm pattern),
            Term.denote
              (clauseSyntaxTerm
                (source.clause.freshCopy sourceSeed).clause))]
          canonical ∧
        PLeaTTa.unifyTopExact
            (PLeaTTa.subst runtime executablePattern)
            (PLeaTTa.subst runtime
              (executableRetractCopy executableCounter executable)) =
          some generated ∧
        PrologMguExecutableOpenFactor.OpenAlphaResultFactors
          inspection.inspectionAlpha canonical generated ∧
        executableBinding =
          match generated with
          | [] => runtime
          | _ :: _ => Metta.Subst.compose generated runtime := by
  obtain ⟨canonical, derivation, sourceEq⟩ := sourceComputed
  obtain ⟨generated, generatedEq, factors, installed⟩ :=
    unifyB_result_has_open_factor_of_ordered_retract
      runtime inspection.shared
      inspection.patternReading.toAgrees inspection.copiedReading.toAgrees
      (by simpa [denoteEquations] using derivation)
      executableComputed
  exact
    ⟨canonical, generated, sourceEq,
      by simpa [denoteEquations] using derivation,
      generatedEq, factors, installed⟩

end RetractCandidateInspection

/-- Candidate alignment plus the exact two-currency frontiers at every
position of a frozen retract scan.  Each tail starts after both real copies;
no arithmetic equality between the resulting frontiers is asserted. -/
inductive RetractScanSpine
    (baseAlpha : List (LogicVar × String))
    (pattern : LocalClause) (executablePattern : Atom) (runtime : Subst) :
    Nat → Nat → List VersionedClause → List RetractClauseCandidate → Type where
  | nil (sourceSeed executableCounter : Nat) :
      RetractScanSpine baseAlpha pattern executablePattern runtime
        sourceSeed executableCounter [] []
  | cons
      {sourceSeed executableCounter : Nat}
      {source : VersionedClause} {sources : List VersionedClause}
      {executable : RetractClauseCandidate}
      {executables : List RetractClauseCandidate}
      (inspection :
        RetractCandidateInspection baseAlpha pattern executablePattern runtime
          sourceSeed executableCounter source executable)
      (tail :
        RetractScanSpine baseAlpha pattern executablePattern runtime
          (source.clause.freshCopy sourceSeed).nextFresh
          (executableCounter + 1) sources executables) :
      RetractScanSpine baseAlpha pattern executablePattern runtime
        sourceSeed executableCounter (source :: sources)
        (executable :: executables)

namespace RetractScanSpine

/-- Forget freshness and decision evidence to the exact positional occurrence
relation used by the database bridge. -/
theorem occurrences
    {baseAlpha : List (LogicVar × String)}
    {pattern : LocalClause} {executablePattern : Atom} {runtime : Subst}
    {sourceSeed executableCounter : Nat}
    {sources : List VersionedClause}
    {executables : List RetractClauseCandidate}
    (spine :
      RetractScanSpine baseAlpha pattern executablePattern runtime sourceSeed
        executableCounter sources executables) :
    List.Forall₂ RetractOccurrenceAgrees sources executables := by
  induction spine with
  | nil => exact .nil
  | cons inspection tail inductionHypothesis =>
      exact .cons inspection.occurrence inductionHypothesis

end RetractScanSpine

/-- Prepend one rejected executable occurrence to a recursively computed scan
outcome.  A missing tail remains missing; a matched tail retains the literal
selected occurrence and grows only its rejected prefix. -/
def prependRetractRejection (candidate : RetractClauseCandidate) :
    RetractClauseScanOutcome Subst → RetractClauseScanOutcome Subst
  | .matched before selected after binding nextCounter =>
      .matched (candidate :: before) selected after binding nextCounter
  | .missing nextCounter => .missing nextCounter

/-- One decision-coupled traversal.  This is the proof-relevant object from
which both completed scans are projected; it is not a relation between two
separately supplied scan results. -/
inductive CoupledRetractScan
    (baseAlpha : List (LogicVar × String))
    (pattern : LocalClause) (executablePattern : Atom) (runtime : Subst) :
    (sourceSeed executableCounter : Nat) →
    (sources : List VersionedClause) →
    (executables : List RetractClauseCandidate) →
    RetractOutcome → RetractClauseScanOutcome Subst → Type where
  | exhausted (sourceSeed executableCounter : Nat) :
      CoupledRetractScan baseAlpha pattern executablePattern runtime
        sourceSeed executableCounter [] []
        (.missing sourceSeed) (.missing executableCounter)
  | matched
      {sourceSeed executableCounter : Nat}
      {source : VersionedClause} {sources : List VersionedClause}
      {executable : RetractClauseCandidate}
      {executables : List RetractClauseCandidate}
      (inspection :
        RetractCandidateInspection baseAlpha pattern executablePattern runtime
          sourceSeed executableCounter source executable)
      (tail :
        RetractScanSpine baseAlpha pattern executablePattern runtime
          (source.clause.freshCopy sourceSeed).nextFresh
          (executableCounter + 1) sources executables)
      (sourceBinding : Substitution)
      (sourceComputed :
        ComputesDenotationalMgu
          [(clauseSyntaxTerm pattern,
            clauseSyntaxTerm (source.clause.freshCopy sourceSeed).clause)]
          sourceBinding)
      (executableBinding : Subst)
      (executableComputed :
        PLeaTTa.unifyB runtime executablePattern
            (executableRetractCopy executableCounter executable) =
          some executableBinding) :
      CoupledRetractScan baseAlpha pattern executablePattern runtime
        sourceSeed executableCounter (source :: sources)
        (executable :: executables)
        (.matched source sourceBinding
          (source.clause.freshCopy sourceSeed).nextFresh)
        (.matched [] executable executables executableBinding
          (executableCounter + 1))
  | skipped
      {sourceSeed executableCounter : Nat}
      {source : VersionedClause} {sources : List VersionedClause}
      {executable : RetractClauseCandidate}
      {executables : List RetractClauseCandidate}
      {sourceOutcome : RetractOutcome}
      {executableOutcome : RetractClauseScanOutcome Subst}
      (inspection :
        RetractCandidateInspection baseAlpha pattern executablePattern runtime
          sourceSeed executableCounter source executable)
      (sourceClash :
        ¬ ∃ sourceBinding,
          ComputesDenotationalMgu
            [(clauseSyntaxTerm pattern,
              clauseSyntaxTerm (source.clause.freshCopy sourceSeed).clause)]
            sourceBinding)
      (executableClash :
        PLeaTTa.unifyB runtime executablePattern
            (executableRetractCopy executableCounter executable) = none)
      (tail :
        CoupledRetractScan baseAlpha pattern executablePattern runtime
          (source.clause.freshCopy sourceSeed).nextFresh
          (executableCounter + 1) sources executables sourceOutcome
          executableOutcome) :
      CoupledRetractScan baseAlpha pattern executablePattern runtime
        sourceSeed executableCounter (source :: sources)
        (executable :: executables) sourceOutcome
        (prependRetractRejection executable executableOutcome)

namespace CoupledRetractScan

/-- Project the actual Type-valued independent scan. -/
noncomputable def sourceScan
    {baseAlpha : List (LogicVar × String)}
    {pattern : LocalClause} {executablePattern : Atom} {runtime : Subst}
    {sourceSeed executableCounter : Nat}
    {sources : List VersionedClause}
    {executables : List RetractClauseCandidate}
    {sourceOutcome : RetractOutcome}
    {executableOutcome : RetractClauseScanOutcome Subst}
    (coupled :
      CoupledRetractScan baseAlpha pattern executablePattern runtime sourceSeed
        executableCounter sources executables sourceOutcome
        executableOutcome) :
    RetractScan pattern sourceSeed sources sourceOutcome := by
  induction coupled with
  | exhausted sourceSeed executableCounter =>
      exact .exhausted sourceSeed
  | matched inspection tail sourceBinding sourceComputed executableBinding
      executableComputed =>
      exact .matched _ _ _ sourceBinding sourceComputed
  | skipped inspection sourceClash executableClash tail inductionHypothesis =>
      exact .skipped _ _ _ _ sourceClash inductionHypothesis

/-- Project the exact executable scan equation. -/
theorem executableScan
    {baseAlpha : List (LogicVar × String)}
    {pattern : LocalClause} {executablePattern : Atom} {runtime : Subst}
    {sourceSeed executableCounter : Nat}
    {sources : List VersionedClause}
    {executables : List RetractClauseCandidate}
    {sourceOutcome : RetractOutcome}
    {executableOutcome : RetractClauseScanOutcome Subst}
    (coupled :
      CoupledRetractScan baseAlpha pattern executablePattern runtime sourceSeed
        executableCounter sources executables sourceOutcome
        executableOutcome) :
    retractClauseScanWith PLeaTTa.unifyB executablePattern executableCounter
        runtime executables = executableOutcome := by
  induction coupled with
  | exhausted sourceSeed executableCounter =>
      rfl
  | @matched sourceSeed executableCounter source sources executable executables
      inspection tail sourceBinding sourceComputed executableBinding
      executableComputed =>
      simp only [retractClauseScanWith]
      have computed :
          PLeaTTa.unifyB runtime executablePattern
              (renameAtomSuffix (resolutionCompactSuffix executableCounter)
                (retractClauseSyntaxAtom executable.1.1 executable.1.2)) =
            some executableBinding := by
        simpa only [executableRetractCopy] using executableComputed
      rw [computed]
  | @skipped sourceSeed executableCounter source sources executable
      executables sourceOutcome executableOutcome inspection sourceClash
      executableClash tail inductionHypothesis =>
      simp only [retractClauseScanWith]
      have rejected :
          PLeaTTa.unifyB runtime executablePattern
              (renameAtomSuffix (resolutionCompactSuffix executableCounter)
                (retractClauseSyntaxAtom executable.1.1 executable.1.2)) =
            none := by
        simpa only [executableRetractCopy] using executableClash
      rw [rejected, inductionHypothesis]
      cases executableOutcome <;> rfl

/-- Both decisions occur at the same source-order position.  On success the
rejected prefixes and retained suffixes are occurrence-related and the two
selected entries are the aligned heads; on exhaustion both scans rejected the
entire aligned input. -/
def OutcomesAgree
    {baseAlpha : List (LogicVar × String)}
    {pattern : LocalClause} {executablePattern : Atom} {runtime : Subst}
    {sourceSeed executableCounter : Nat}
    {sources : List VersionedClause}
    {executables : List RetractClauseCandidate}
    {sourceOutcome : RetractOutcome}
    {executableOutcome : RetractClauseScanOutcome Subst}
    (coupled :
      CoupledRetractScan baseAlpha pattern executablePattern runtime sourceSeed
        executableCounter sources executables sourceOutcome
        executableOutcome) : Prop :=
  match sourceOutcome, executableOutcome with
  | .matched source _ _, .matched before selected after _ _ =>
      List.Forall₂ RetractOccurrenceAgrees
          coupled.sourceScan.rejectedPrefix before ∧
        RetractOccurrenceAgrees source selected ∧
        List.Forall₂ RetractOccurrenceAgrees
          coupled.sourceScan.selectedAfter after
  | .missing _, .missing _ =>
      List.Forall₂ RetractOccurrenceAgrees
        coupled.sourceScan.rejectedPrefix executables
  | _, _ => False

/-- Structural traversal proves exact outcome agreement; no prefix equality is
accepted as a premise. -/
theorem outcomesAgree
    {baseAlpha : List (LogicVar × String)}
    {pattern : LocalClause} {executablePattern : Atom} {runtime : Subst}
    {sourceSeed executableCounter : Nat}
    {sources : List VersionedClause}
    {executables : List RetractClauseCandidate}
    {sourceOutcome : RetractOutcome}
    {executableOutcome : RetractClauseScanOutcome Subst}
    (coupled :
      CoupledRetractScan baseAlpha pattern executablePattern runtime sourceSeed
        executableCounter sources executables sourceOutcome
        executableOutcome) :
    coupled.OutcomesAgree := by
  induction coupled with
  | exhausted sourceSeed executableCounter =>
      exact .nil
  | matched inspection tail sourceBinding sourceComputed executableBinding
      executableComputed =>
      exact ⟨.nil, inspection.occurrence, tail.occurrences⟩
  | @skipped sourceSeed executableCounter source sources executable
      executables sourceOutcome executableOutcome inspection sourceClash
      executableClash tail inductionHypothesis =>
      cases sourceOutcome with
      | matched source sourceBinding sourceNext =>
          cases executableOutcome with
          | matched before selected after executableBinding executableNext =>
              simp only [OutcomesAgree, sourceScan,
                RetractScan.rejectedPrefix, RetractScan.selectedAfter,
                prependRetractRejection] at inductionHypothesis ⊢
              exact
                ⟨.cons inspection.occurrence inductionHypothesis.1,
                  inductionHypothesis.2.1, inductionHypothesis.2.2⟩
          | missing executableNext =>
              simp only [OutcomesAgree] at inductionHypothesis
      | missing sourceNext =>
          cases executableOutcome with
          | matched before selected after executableBinding executableNext =>
              simp only [OutcomesAgree] at inductionHypothesis
          | missing executableNext =>
              simp only [OutcomesAgree, sourceScan] at inductionHypothesis
              simp only [OutcomesAgree, sourceScan,
                RetractScan.rejectedPrefix, prependRetractRejection]
              exact .cons inspection.occurrence inductionHypothesis

/-- Complete selected-result handoff retained by one decision-coupled scan.
The selected alpha graph starts at the exact source/executable frontiers after
the rejected prefix, reaches the two returned next-frontiers, and relates the
independent canonical MGU to the concrete generated executable component by
semantic factorization rather than raw substitution equality. -/
def MatchedOpenFactor
    {baseAlpha : List (LogicVar × String)}
    {pattern : LocalClause} {executablePattern : Atom} {runtime : Subst}
    {sourceSeed executableCounter sourceNext executableNext : Nat}
    {sources : List VersionedClause}
    {executables before after : List RetractClauseCandidate}
    {source : VersionedClause} {sourceBinding : Substitution}
    {selected : RetractClauseCandidate} {executableBinding : Subst}
    (coupled :
      CoupledRetractScan baseAlpha pattern executablePattern runtime sourceSeed
        executableCounter sources executables
        (.matched source sourceBinding sourceNext)
        (.matched before selected after executableBinding executableNext)) :
    Prop :=
  ∃ selectedAlpha canonical generated
      selectedSourceSeed selectedExecutableCounter,
    selectedSourceSeed =
        RetractScan.freshAfterPrefix sourceSeed
          coupled.sourceScan.rejectedPrefix ∧
      selectedExecutableCounter = executableCounter + before.length ∧
      AlphaExtendsAbove baseAlpha selectedAlpha
        selectedSourceSeed selectedExecutableCounter ∧
      AlphaFreshFrontier selectedAlpha sourceNext executableNext ∧
      SharedRuntimeAlpha selectedAlpha ∧
      sourceBinding = TreeSubstitution.reify canonical ∧
      OrderedTreeMgu
        [(Term.denote (clauseSyntaxTerm pattern),
          Term.denote
            (clauseSyntaxTerm
              (source.clause.freshCopy selectedSourceSeed).clause))]
        canonical ∧
      PLeaTTa.unifyTopExact
          (PLeaTTa.subst runtime executablePattern)
          (PLeaTTa.subst runtime
            (executableRetractCopy selectedExecutableCounter selected)) =
        some generated ∧
      PrologMguExecutableOpenFactor.OpenAlphaResultFactors
        selectedAlpha canonical generated ∧
      executableBinding =
        match generated with
        | [] => runtime
        | _ :: _ => Metta.Subst.compose generated runtime

private theorem selectedOpenFactorGeneral
    {baseAlpha : List (LogicVar × String)}
    {pattern : LocalClause} {executablePattern : Atom} {runtime : Subst}
    {sourceSeed executableCounter : Nat}
    {sources : List VersionedClause}
    {executables : List RetractClauseCandidate}
    {sourceOutcome : RetractOutcome}
    {executableOutcome : RetractClauseScanOutcome Subst}
    (coupled :
      CoupledRetractScan baseAlpha pattern executablePattern runtime sourceSeed
        executableCounter sources executables sourceOutcome executableOutcome) :
    match sourceOutcome, executableOutcome with
    | .matched _ _ _, .matched _ _ _ _ _ =>
        coupled.MatchedOpenFactor
    | _, _ => True := by
  induction coupled with
  | exhausted sourceSeed executableCounter =>
      trivial
  | @matched sourceSeed executableCounter source sources executable executables
      inspection tail sourceBinding sourceComputed executableBinding
      executableComputed =>
      obtain ⟨canonical, generated, sourceEq, derivation, generatedEq,
        factors, installed⟩ :=
        inspection.selectedOpenFactor sourceComputed executableComputed
      exact
        ⟨inspection.inspectionAlpha, canonical, generated,
          sourceSeed, executableCounter,
          rfl, by simp, inspection.alphaExtension,
          inspection.freshFrontier, inspection.shared,
          sourceEq, derivation, generatedEq, factors, installed⟩
  | @skipped sourceSeed executableCounter skipped sources executable
      executables sourceOutcome executableOutcome inspection sourceClash
      executableClash tail inductionHypothesis =>
      cases sourceOutcome with
      | missing sourceNext =>
          trivial
      | matched source sourceBinding sourceNext =>
          cases executableOutcome with
          | missing executableNext =>
              trivial
          | matched tailBefore selected after executableBinding executableNext =>
              obtain ⟨selectedAlpha, canonical, generated,
                selectedSourceSeed, selectedExecutableCounter,
                sourceSeedEq, executableCounterEq, alphaExtension,
                freshFrontier, selectedShared, sourceEq, derivation,
                generatedEq, factors, installed⟩ := inductionHypothesis
              refine
                ⟨selectedAlpha, canonical, generated,
                  selectedSourceSeed, selectedExecutableCounter,
                  ?_, ?_, alphaExtension, freshFrontier, selectedShared,
                  sourceEq, derivation, generatedEq, factors, installed⟩
              · simpa [sourceScan, RetractScan.rejectedPrefix,
                  RetractScan.freshAfterPrefix] using sourceSeedEq
              · simp only [List.length_cons]
                omega

/-- The single scan traversal constructs the complete selected-result handoff;
no separately supplied prefix, occurrence, MGU, alpha graph, or executable
result can be paired with it. -/
theorem matchedOpenFactor
    {baseAlpha : List (LogicVar × String)}
    {pattern : LocalClause} {executablePattern : Atom} {runtime : Subst}
    {sourceSeed executableCounter sourceNext executableNext : Nat}
    {sources : List VersionedClause}
    {executables before after : List RetractClauseCandidate}
    {source : VersionedClause} {sourceBinding : Substitution}
    {selected : RetractClauseCandidate} {executableBinding : Subst}
    (coupled :
      CoupledRetractScan baseAlpha pattern executablePattern runtime sourceSeed
        executableCounter sources executables
        (.matched source sourceBinding sourceNext)
        (.matched before selected after executableBinding executableNext)) :
    coupled.MatchedOpenFactor := by
  exact selectedOpenFactorGeneral coupled

/-- Matching positions have identical rejected-occurrence counts despite the
different fresh-name currencies. -/
theorem matched_rejected_length_eq
    {baseAlpha : List (LogicVar × String)}
    {pattern : LocalClause} {executablePattern : Atom} {runtime : Subst}
    {sourceSeed executableCounter sourceNext executableNext : Nat}
    {sources : List VersionedClause}
    {executables before after : List RetractClauseCandidate}
    {source : VersionedClause} {sourceBinding : Substitution}
    {selected : RetractClauseCandidate} {executableBinding : Subst}
    (coupled :
      CoupledRetractScan baseAlpha pattern executablePattern runtime sourceSeed
        executableCounter sources executables
        (.matched source sourceBinding sourceNext)
        (.matched before selected after executableBinding executableNext)) :
    coupled.sourceScan.rejectedPrefix.length = before.length := by
  exact coupled.outcomesAgree.1.length_eq

/-- Anti-forgery discriminator: a source match at the first occurrence cannot
be paired with an executable result claiming any nonempty rejected prefix. -/
theorem head_match_rejects_executable_prefix
    {baseAlpha : List (LogicVar × String)}
    {pattern : LocalClause} {executablePattern : Atom} {runtime : Subst}
    {sourceSeed executableCounter sourceNext executableNext : Nat}
    {sources : List VersionedClause}
    {executables after : List RetractClauseCandidate}
    {source : VersionedClause} {sourceBinding : Substitution}
    {selected rejected : RetractClauseCandidate} {before : List RetractClauseCandidate}
    {executableBinding : Subst}
    (coupled :
      CoupledRetractScan baseAlpha pattern executablePattern runtime sourceSeed
        executableCounter (source :: sources) executables
        (.matched source sourceBinding sourceNext)
        (.matched (rejected :: before) selected after executableBinding
          executableNext))
    (sourceHead : coupled.sourceScan.rejectedPrefix = []) : False := by
  have lengths := coupled.matched_rejected_length_eq
  rw [sourceHead] at lengths
  simp at lengths

end CoupledRetractScan

namespace RetractScanSpine

/-- Couple one actual source scan by inspecting the executable unifier at the
same aligned occurrence.  Successful executable result data comes from the
real computation; the only impossible branch is ruled out by the explicit
source-completeness certificate. -/
noncomputable def couple
    {baseAlpha : List (LogicVar × String)}
    {pattern : LocalClause} {executablePattern : Atom} {runtime : Subst}
    {sourceSeed executableCounter : Nat}
    {sources : List VersionedClause}
    {executables : List RetractClauseCandidate}
    (spine :
      RetractScanSpine baseAlpha pattern executablePattern runtime sourceSeed
        executableCounter sources executables)
    {sourceOutcome : RetractOutcome}
    (sourceScan : RetractScan pattern sourceSeed sources sourceOutcome) :
    Sigma fun executableOutcome =>
      CoupledRetractScan baseAlpha pattern executablePattern runtime sourceSeed
        executableCounter sources executables sourceOutcome
        executableOutcome :=
  match spine, sourceScan with
  | .nil sourceSeed executableCounter, .exhausted _ =>
      ⟨.missing executableCounter, .exhausted _ _⟩
  | @RetractScanSpine.cons _ _ _ _ sourceSeed executableCounter source
        sources executable executables inspection tail,
      .matched _ _ _ sourceBinding sourceComputed =>
      match executableDecision :
          PLeaTTa.unifyB runtime executablePattern
            (executableRetractCopy executableCounter executable) with
      | none =>
          False.elim
            (inspection.executableCannotReject sourceComputed
              executableDecision)
      | some executableBinding =>
          ⟨.matched [] executable executables executableBinding
              (executableCounter + 1),
            .matched inspection tail sourceBinding sourceComputed
              executableBinding executableDecision⟩
  | @RetractScanSpine.cons _ _ _ _ sourceSeed executableCounter source
        sources executable executables inspection tail,
      .skipped _ _ _ _ sourceClash tailScan =>
      let executableClash := inspection.executableRejects sourceClash
      let coupledTail := couple tail tailScan
      ⟨prependRetractRejection executable coupledTail.1,
        .skipped inspection sourceClash executableClash coupledTail.2⟩
termination_by sources.length

end RetractScanSpine

end PLeaTTa.PrologRetractScanBridge
