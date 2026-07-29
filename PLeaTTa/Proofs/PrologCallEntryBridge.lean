-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologCallEntryBridge
Purpose: Relate one independent logical-update call snapshot to the
  executable local-clause candidate bank before head unification.
Trusted boundary: none
Main exports: CandidateClauseAgrees,
  DatabaseRelatesWorld.currentCandidates, PreparedBankRelates
-/
import PLeaTTa.Proofs.PrologStateBridge
import PLeaTTa.Proofs.PrologActivationMacro

namespace PLeaTTa.PrologCallEntryBridge

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Resolver
open PrologStateBridge
open PrologActivationMacro

/-!
Call entry is the first state-step seam at which the independent and
executable freshness frontiers both move.  Before relating the two allocation
schemes, this file pins the occurrence bank on which they operate.

The independent logical-update store filters output-last predicate clauses by
the complete Prolog arity.  The executable world stores the output separately
and indexes by input arity.  `currentCandidates` proves that these are exactly
the same source-ordered occurrences, with duplicates retained.  It does not
mention either unifier: full head equality is a later step on both sides.
-/

/-- One current independent occurrence and one executable candidate clause
are the same output-last predicate occurrence. -/
def CandidateClauseAgrees (predicate : String)
    (reference : VersionedClause) (executable : PLeaTTa.Clause) : Prop :=
  LocalClauseAgrees reference.clause (predicate, executable)

/-- Predicate and output-last arity selection agree for one related clause.
The executable arity omits the final output slot by construction. -/
theorem LocalClauseAgrees.candidateTest_eq
    {reference : LocalClause}
    {executable : String × PLeaTTa.Clause}
    (agreement : LocalClauseAgrees reference executable)
    (predicate : String) (inputArity : Nat) :
    (reference.predicate == predicate &&
        reference.arguments.length == inputArity + 1) =
      (executable.1 == predicate &&
        executable.2.params.length == inputArity) := by
  rw [agreement.predicate, agreement.arity]
  simp

/-- Filtering the current logical-update projection is definitionally the
call-start view at that same generation. -/
theorem visibleClausesAt_current_eq_filter
    (database : Database) (predicate : String) (inputArity : Nat) :
    database.visibleClausesAt database.generation predicate (inputArity + 1) =
      (currentVisibleEntries database).filter fun entry =>
        entry.clause.predicate == predicate &&
          entry.clause.arguments.length == inputArity + 1 := by
  simp only [Database.visibleClausesAt, currentVisibleEntries,
    List.filter_filter]
  apply List.filter_congr
  intro entry _member
  cases visible : entry.visibleAt database.generation <;>
    cases predicateMatches : entry.clause.predicate == predicate <;>
    cases arityMatches :
        entry.clause.arguments.length == inputArity + 1 <;>
    simp

/-- Canonical executable head-and-arity selection is one ordered filter-map
over the live occurrence list. -/
theorem clauseCandidates_eq_filterMap
    (world : PWorld) (predicate : String) (inputArity : Nat)
    (coherent : world.ClauseIndexCoherent) :
    world.clauseCandidates predicate inputArity =
      world.progClauses.filterMap fun entry =>
        if entry.1 == predicate &&
            entry.2.params.length == inputArity then
          some entry.2
        else
          none := by
  rw [world.clauseCandidates_eq_filter predicate inputArity coherent]
  unfold PWorld.clausesOf
  induction world.progClauses with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
      rcases entry with ⟨name, clause⟩
      simp only [List.filterMap_cons]
      by_cases nameMatches : name == predicate
      · simp only [nameMatches, if_true, Bool.true_and]
        by_cases arityMatches : clause.params.length == inputArity
        · simp only [arityMatches, List.filter_cons, if_true]
          exact congrArg (List.cons clause) inductionHypothesis
        · simp only [arityMatches, Bool.false_eq_true, List.filter_cons,
            if_false]
          exact inductionHypothesis
      · simp only [nameMatches, Bool.false_eq_true, if_false,
          Bool.false_and]
        exact inductionHypothesis

/-- Ordered filtering transports a global occurrence correspondence to the
exact head-and-arity candidate bank. -/
private theorem candidateFilter_forall₂
    (predicate : String) (inputArity : Nat) :
    ∀ {references : List VersionedClause}
      {executables : List (String × PLeaTTa.Clause)},
      List.Forall₂ VersionedClauseAgrees references executables →
      List.Forall₂ (CandidateClauseAgrees predicate)
        (references.filter fun entry =>
          entry.clause.predicate == predicate &&
            entry.clause.arguments.length == inputArity + 1)
        (executables.filterMap fun entry =>
          if entry.1 == predicate &&
              entry.2.params.length == inputArity then
            some entry.2
          else
            none)
  | [], [], .nil => .nil
  | reference :: references, executable :: executables,
      .cons head tail => by
      rcases executable with ⟨name, clause⟩
      have tests :=
        LocalClauseAgrees.candidateTest_eq head predicate inputArity
      cases referenceTest :
          (reference.clause.predicate == predicate &&
            reference.clause.arguments.length == inputArity + 1)
      · have executableTest :
            (name == predicate &&
              clause.params.length == inputArity) = false := by
          rw [← tests, referenceTest]
        simp only [List.filter_cons, referenceTest, Bool.false_eq_true,
          if_false, List.filterMap_cons, executableTest]
        exact candidateFilter_forall₂ predicate inputArity tail
      · have executableTest :
            (name == predicate &&
              clause.params.length == inputArity) = true := by
          rw [← tests, referenceTest]
        have nameMatches : (name == predicate) = true := by
          cases nameTest : name == predicate
          · simp [nameTest] at executableTest
          · rfl
        have nameEquality : name = predicate := by
          simpa using nameMatches
        subst name
        simp only [List.filter_cons, referenceTest, if_true,
          List.filterMap_cons, executableTest]
        exact .cons head
          (candidateFilter_forall₂ predicate inputArity tail)

/-- The independent call-start snapshot and executable indexed candidate bank
contain exactly the same source-ordered occurrences.  The independent arity
includes the output slot; the executable arity does not. -/
theorem DatabaseRelatesWorld.currentCandidates
    {database : Database} {world : PWorld}
    (agreement : DatabaseRelatesWorld database world)
    (predicate : String) (inputArity : Nat) :
    List.Forall₂ (CandidateClauseAgrees predicate)
      (database.visibleClausesAt database.generation predicate
        (inputArity + 1))
      (world.clauseCandidates predicate inputArity) := by
  rw [visibleClausesAt_current_eq_filter database predicate inputArity,
    clauseCandidates_eq_filterMap world predicate inputArity
      agreement.clauseIndex]
  exact candidateFilter_forall₂ predicate inputArity agreement.liveClauses

/-- Exact occurrence accounting is a consequence, not an extra set-level
assumption: indexed selection neither drops duplicate occurrences nor
manufactures candidates. -/
theorem DatabaseRelatesWorld.currentCandidates_length_eq
    {database : Database} {world : PWorld}
    (agreement : DatabaseRelatesWorld database world)
    (predicate : String) (inputArity : Nat) :
    (database.visibleClausesAt database.generation predicate
        (inputArity + 1)).length =
      (world.clauseCandidates predicate inputArity).length :=
  (PLeaTTa.PrologCallEntryBridge.DatabaseRelatesWorld.currentCandidates
    agreement predicate inputArity).length_eq

/-- When the executable derived index is enabled, the actual
`Step.call_resolve` candidate function is exactly the candidate bank above.
The disabled-index fallback deliberately remains a later ranked-scan case:
it includes wrong-arity head matches which `resolveAlts` then skips. -/
theorem DatabaseRelatesWorld.currentResolutionCandidates
    {database : Database} {world : PWorld}
    (agreement : DatabaseRelatesWorld database world)
    (ready : world.clauseIndexReady = true)
    (predicate : String) (inputArity : Nat) :
    List.Forall₂ (CandidateClauseAgrees predicate)
      (database.visibleClausesAt database.generation predicate
        (inputArity + 1))
      (world.resolutionCandidates predicate inputArity) := by
  rw [world.resolutionCandidates_eq predicate inputArity
      agreement.clauseIndex]
  simpa [ready, world.clauseCandidates_eq_filter predicate inputArity
      agreement.clauseIndex] using
    (PLeaTTa.PrologCallEntryBridge.DatabaseRelatesWorld.currentCandidates
      agreement predicate inputArity)

theorem DatabaseRelatesWorld.currentResolutionCandidates_length_eq
    {database : Database} {world : PWorld}
    (agreement : DatabaseRelatesWorld database world)
    (ready : world.clauseIndexReady = true)
    (predicate : String) (inputArity : Nat) :
    (database.visibleClausesAt database.generation predicate
        (inputArity + 1)).length =
      (world.resolutionCandidates predicate inputArity).length :=
  (currentResolutionCandidates agreement ready predicate inputArity).length_eq

/-- A nonempty independent call-start snapshot satisfies both dispatch guards
of the sealed `Step.call_resolve` constructor.  This theorem is deliberately
upstream of `resolveAlts` and of head unification: it only establishes that
the exact ordered occurrence bank reaches the local-resolution branch. -/
theorem DatabaseRelatesWorld.callResolve_dispatch
    {database : Database} {world : PWorld}
    (agreement : DatabaseRelatesWorld database world)
    (ready : world.clauseIndexReady = true)
    (predicate : String) (inputArity : Nat)
    (nonempty :
      database.visibleClausesAt database.generation predicate
        (inputArity + 1) ≠ []) :
    world.clauseHeadCandidates predicate ≠ [] ∧
      (world.resolutionCandidates predicate inputArity).any
        (fun clause => clause.params.length == inputArity) := by
  have lengths :=
    currentResolutionCandidates_length_eq agreement ready predicate inputArity
  have executableNonempty :
      world.resolutionCandidates predicate inputArity ≠ [] := by
    intro executableEmpty
    have referenceLengthZero :
        (database.visibleClausesAt database.generation predicate
          (inputArity + 1)).length = 0 := by
      simpa [executableEmpty] using lengths
    exact nonempty
      (List.eq_nil_of_length_eq_zero referenceLengthZero)
  constructor
  · intro headEmpty
    have clausesEmpty : world.clausesOf predicate = [] := by
      rw [← world.clauseHeadCandidates_eq_clausesOf predicate
        agreement.clauseIndex]
      exact headEmpty
    have resolutionEmpty :
        world.resolutionCandidates predicate inputArity = [] := by
      rw [world.resolutionCandidates_eq predicate inputArity
          agreement.clauseIndex]
      simp [ready, clausesEmpty]
    exact executableNonempty resolutionEmpty
  · obtain ⟨clause, rest, resolutionShape⟩ :=
      List.exists_cons_of_ne_nil executableNonempty
    have member :
        clause ∈ world.resolutionCandidates predicate inputArity := by
      rw [resolutionShape]
      simp
    have filteredMember :
        clause ∈
          (world.clausesOf predicate).filter fun candidate =>
            candidate.params.length == inputArity := by
      rw [world.resolutionCandidates_eq predicate inputArity
          agreement.clauseIndex] at member
      simpa [ready] using member
    have arityMatches :
        clause.params.length == inputArity := by
      simpa using (List.mem_filter.mp filteredMember).2
    exact List.any_eq_true.mpr ⟨clause, member, arityMatches⟩

/-! ## Prepared cursor versus executable scan -/

/-- The exact branch minted by the independent eager reservation pass for one
visible occurrence at one independent fresh high-water.  This is a named
presentation of the constructor already used by `reserveVisible`, not a
second allocation algorithm. -/
def preparedBranchOf (callGeneration : Generation) (arguments : List Term)
    (bindings : PeTTaSpec.PrologCore.OpenSubstitution.Substitution)
    (freshSeed : Nat)
    (entry : VersionedClause) : ClauseBranch :=
  let copied := entry.clause.freshCopy freshSeed
  { sourceId := entry.id
    callGeneration := callGeneration
    freshSubstitution := copied.freshSubstitution
    headEquations := argumentEquations arguments copied.clause.arguments
    body := copied.clause.body
    bindings := bindings
    firstFresh := copied.firstFresh
    nextFresh := copied.nextFresh }

/-- One prepared independent branch and one executable candidate originate
from the same source occurrence.  The existential seed is intentionally in
the independent allocator's currency; no equation to the executable suffix
counter is asserted. -/
inductive PreparedCandidateAgrees (callGeneration : Generation)
    (predicate : String) (arguments : List Term)
    (bindings : PeTTaSpec.PrologCore.OpenSubstitution.Substitution) :
    ClauseBranch → PLeaTTa.Clause → Prop where
  | intro (reference : VersionedClause) (freshSeed : Nat)
      (executable : PLeaTTa.Clause)
      (base : CandidateClauseAgrees predicate reference executable) :
      PreparedCandidateAgrees callGeneration predicate arguments bindings
        (preparedBranchOf callGeneration arguments bindings freshSeed
          reference)
        executable

/-- Eager reservation preserves the exact occurrence correspondence while
standardizing every independent clause.  Duplicate source occurrences remain
distinct list entries and keep their original order. -/
theorem reserveVisible_candidates
    (callGeneration : Generation) (predicate : String)
    (arguments : List Term)
    (bindings : PeTTaSpec.PrologCore.OpenSubstitution.Substitution)
    (freshSeed : Nat)
    {references : List VersionedClause}
    {executables : List PLeaTTa.Clause}
    (agreement :
      List.Forall₂ (CandidateClauseAgrees predicate)
        references executables) :
    List.Forall₂
      (PreparedCandidateAgrees callGeneration predicate arguments bindings)
      (reserveVisible callGeneration arguments bindings freshSeed
        references).1
      executables := by
  induction agreement generalizing freshSeed with
  | nil =>
      exact .nil
  | @cons reference executable references executables head tail
      inductionHypothesis =>
      simp only [reserveVisible]
      exact .cons
        (.intro reference freshSeed executable head)
        (inductionHypothesis
          (reference.clause.freshCopy freshSeed).nextFresh)

/-- The prepared cursor and executable alternative bank share one exact
ordered candidate spine.  The independent side reserves every occurrence;
the constructor-sensitive executable scan records which occurrences are
conservatively skipped or retained.  Head MGU success is deliberately absent:
it is the next transition on both sides. -/
structure PreparedBankRelates
    (cursor : PreparedCursor)
    (argsv args : List Metta.Atom) (res : Metta.Atom)
    (rest : List PLeaTTa.Goal)
    (binding : Metta.Subst) (qterm : Metta.Atom) (barrier : Nat)
    (candidates : List PLeaTTa.Clause) (counter : Nat)
    (alts : List Alt) (finalCounter : Nat) : Prop where
  candidateSpine :
    List.Forall₂
      (PreparedCandidateAgrees cursor.callGeneration cursor.predicate
        cursor.arguments cursor.bindings)
      cursor.remaining candidates
  scan :
    ResolutionScan argsv args res rest binding qterm barrier
      candidates counter alts finalCounter

/-- The cursor owns one prepared branch per executable candidate occurrence,
including candidates that the conservative executable scan later skips. -/
theorem PreparedBankRelates.candidate_length_eq
    {cursor : PreparedCursor}
    {argsv args : List Metta.Atom} {res : Metta.Atom}
    {rest : List PLeaTTa.Goal} {binding : Metta.Subst}
    {qterm : Metta.Atom} {barrier : Nat}
    {candidates : List PLeaTTa.Clause} {counter : Nat}
    {alts : List Alt} {finalCounter : Nat}
    (agreement : PreparedBankRelates cursor argsv args res rest binding qterm
      barrier candidates counter alts finalCounter) :
    cursor.remaining.length = candidates.length :=
  agreement.candidateSpine.length_eq

/-- Alternative multiplicity is the exact retained-candidate count, never a
set cardinality or a successful-MGU count. -/
theorem PreparedBankRelates.alt_length_exact
    {cursor : PreparedCursor}
    {argsv args : List Metta.Atom} {res : Metta.Atom}
    {rest : List PLeaTTa.Goal} {binding : Metta.Subst}
    {qterm : Metta.Atom} {barrier : Nat}
    {candidates : List PLeaTTa.Clause} {counter : Nat}
    {alts : List Alt} {finalCounter : Nat}
    (agreement : PreparedBankRelates cursor argsv args res rest binding qterm
      barrier candidates counter alts finalCounter) :
    alts.length =
      retainedClauseCount argsv (PLeaTTa.subst binding res) candidates :=
  agreement.scan.length_exact

/-- The executable counter advances exactly once per retained occurrence,
while the independent cursor's distinct allocation currency remains
unidentified numerically. -/
theorem PreparedBankRelates.counter_exact
    {cursor : PreparedCursor}
    {argsv args : List Metta.Atom} {res : Metta.Atom}
    {rest : List PLeaTTa.Goal} {binding : Metta.Subst}
    {qterm : Metta.Atom} {barrier : Nat}
    {candidates : List PLeaTTa.Clause} {counter : Nat}
    {alts : List Alt} {finalCounter : Nat}
    (agreement : PreparedBankRelates cursor argsv args res rest binding qterm
      barrier candidates counter alts finalCounter) :
    finalCounter =
      counter +
        retainedClauseCount argsv (PLeaTTa.subst binding res) candidates :=
  agreement.scan.counter_exact

/-- Preparing the independent call and scanning the actual executable
candidate bank produce `PreparedBankRelates`.  The only cross-machine
premises are the already-audited database projection, an enabled coherent
index, and the output-last arity equation.  No unifier or body-support premise
is used. -/
theorem DatabaseRelatesWorld.prepareCall_resolveAlts
    {session : LocalSession} {world : PWorld}
    (agreement : DatabaseRelatesWorld session.database world)
    (ready : world.clauseIndexReady = true)
    (request : CallRequest) (argsv args : List Metta.Atom)
    (res : Metta.Atom)
    (rest : List PLeaTTa.Goal) (binding : Metta.Subst)
    (qterm : Metta.Atom) (barrier counter : Nat)
    (arity :
      request.arguments.length = args.length + 1) :
    PreparedBankRelates
      (prepareCall session request).1
      argsv args res rest binding qterm barrier
      (world.resolutionCandidates request.predicate args.length)
      counter
      (resolveAlts
        (world.resolutionCandidates request.predicate args.length)
        argsv args res rest binding qterm barrier counter).1
      (resolveAlts
        (world.resolutionCandidates request.predicate args.length)
        argsv args res rest binding qterm barrier counter).2 := by
  constructor
  · have visible :=
      currentResolutionCandidates agreement ready request.predicate
        args.length
    have reserved :=
      reserveVisible_candidates session.database.generation
        request.predicate request.arguments request.bindings
        (max session.nextFresh request.generatedCeiling) visible
    simpa only [prepareCall, arity] using reserved
  · exact resolveAlts_scan
      (world.resolutionCandidates request.predicate args.length)
      argsv args res rest binding qterm barrier counter

end PLeaTTa.PrologCallEntryBridge
