-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologPrefilterScanBridge
Purpose: Relate executable conservative clause skips to exact independent
  head-resolution rejection on the shared source-ordered candidate spine.
Trusted boundary: none
Main exports: PreparedPrefilterBankRelates,
  ConservativeResolutionScan, preparedPrefilterScan
-/
import PLeaTTa.Proofs.PrologPrefilterBridge
import PLeaTTa.Proofs.PrologCallEntryBridge

namespace PLeaTTa.PrologPrefilterScanBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore.Resolver
open PeTTaSpec.PrologCore.GoalSemantics
open PrologActivationMacro
open PrologCallEntryBridge
open PrologPrefilterBridge
open PrologStateBridge

/-!
The executable scan may discard a rigidly incompatible clause before making
an alternative.  The independent cursor has already reserved that occurrence,
so it consumes the same occurrence as one silent rejected pull.  This file
relates those decisions without assuming that a retained candidate actually
unifies: conservative false positives remain explicit for the later
`unifyB`/ordered-MGU bridge.
-/

/-- Call-entry bank plus exact normalized-head agreement for every occurrence
in the shared candidate spine.  This is the semantic payload deliberately
left open by `PreparedBankRelates`; no scan decision is copied into the new
field. -/
structure PreparedPrefilterBankRelates
    (cursor : PreparedCursor)
    (argsv args : List Atom) (res : Atom)
    (rest : List PLeaTTa.Goal)
    (binding : Subst) (qterm : Atom) (barrier : Nat)
    (candidates : List PLeaTTa.Clause) (counter : Nat)
    (alts : List Alt) (finalCounter : Nat) : Prop where
  bank :
    PreparedBankRelates cursor argsv args res rest binding qterm barrier
      candidates counter alts finalCounter
  normalizedHeads :
    List.Forall₂
      (fun branch clause =>
        NormalizedHeadAgrees branch argsv (PLeaTTa.subst binding res) clause)
      cursor.remaining candidates

/-- Source-ordered decision alignment.  A skipped executable occurrence
stores the independently derived clash certificate.  A retained occurrence
stores no success claim: it may still be a conservative false positive.
Every constructor consumes exactly one occurrence, so the relation itself is
the finite rank used by the later stuttering simulation. -/
inductive ConservativeResolutionScan (argsv : List Atom) (resv : Atom) :
    List ClauseBranch → List PLeaTTa.Clause → Prop where
  | nil : ConservativeResolutionScan argsv resv [] []
  | skipped (branch : ClauseBranch) (clause : PLeaTTa.Clause)
      (branches : List ClauseBranch) (clauses : List PLeaTTa.Clause)
      (agreement : NormalizedHeadAgrees branch argsv resv clause)
      (rejected : resolutionClauseRetained argsv resv clause = false)
      (clash : ¬ ∃ result, HeadResolution branch result)
      (tail : ConservativeResolutionScan argsv resv branches clauses) :
      ConservativeResolutionScan argsv resv
        (branch :: branches) (clause :: clauses)
  | retained (branch : ClauseBranch) (clause : PLeaTTa.Clause)
      (branches : List ClauseBranch) (clauses : List PLeaTTa.Clause)
      (agreement : NormalizedHeadAgrees branch argsv resv clause)
      (kept : resolutionClauseRetained argsv resv clause = true)
      (tail : ConservativeResolutionScan argsv resv branches clauses) :
      ConservativeResolutionScan argsv resv
        (branch :: branches) (clause :: clauses)

/-- A skipped decision is an actual independent silent pull of the same
first prepared occurrence. -/
theorem NormalizedHeadAgrees.localPull_of_rejected
    {cursor : PreparedCursor} {branch : ClauseBranch}
    {branches : List ClauseBranch} {argsv : List Atom} {resv : Atom}
    {clause : PLeaTTa.Clause}
    (agreement : NormalizedHeadAgrees branch argsv resv clause)
    (remaining : cursor.remaining = branch :: branches)
    (rejected : resolutionClauseRetained argsv resv clause = false) :
    LocalPull cursor
      (.silent (cursor.advance branch branches)) := by
  exact .rejected cursor branch branches remaining
    (agreement.no_headResolution_of_rejected rejected)

/-- The exact executable scan and the pointwise normalized-head relation
determine a conservative decision alignment.  Skips cannot lose an
independently resolvable clause; retained false positives remain untouched.
-/
theorem conservativeResolutionScan_of_forall₂
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst}
    {qterm : Atom} {barrier : Nat}
    {branches : List ClauseBranch}
    {clauses : List PLeaTTa.Clause}
    {counter : Nat} {alts : List Alt} {finalCounter : Nat}
    (heads :
      List.Forall₂
        (fun branch clause =>
          NormalizedHeadAgrees branch argsv
            (PLeaTTa.subst binding res) clause)
        branches clauses)
    (scan :
      ResolutionScan argsv args res rest binding qterm barrier
        clauses counter alts finalCounter) :
    ConservativeResolutionScan argsv (PLeaTTa.subst binding res)
      branches clauses := by
  induction scan generalizing branches with
  | nil counter =>
      cases heads
      exact .nil
  | skipped clause clauses counter finalCounter alts rejected tail
      inductionHypothesis =>
      cases heads with
      | cons agreement remainingHeads =>
          exact .skipped _ _ _ _ agreement rejected
            (agreement.no_headResolution_of_rejected rejected)
            (inductionHypothesis remainingHeads)
  | retained clause clauses counter finalCounter alts kept tail
      inductionHypothesis =>
      cases heads with
      | cons agreement remainingHeads =>
          exact .retained _ _ _ _ agreement kept
            (inductionHypothesis remainingHeads)

/-- A prepared semantic bank produces the exact ranked decision alignment;
the result depends on the declarative scan certificate, not on re-running a
second filter. -/
theorem preparedPrefilterScan
    {cursor : PreparedCursor}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst}
    {qterm : Atom} {barrier : Nat}
    {candidates : List PLeaTTa.Clause} {counter : Nat}
    {alts : List Alt} {finalCounter : Nat}
    (agreement :
      PreparedPrefilterBankRelates cursor argsv args res rest binding qterm
        barrier candidates counter alts finalCounter) :
    ConservativeResolutionScan argsv (PLeaTTa.subst binding res)
      cursor.remaining candidates :=
  conservativeResolutionScan_of_forall₂
    agreement.normalizedHeads agreement.bank.scan

/-! ## Exact execution of the rejected prefix -/

/-- Exactly `count` independently rejected prepared clauses.

Every constructor consumes the current cursor head and advances to its
already-reserved tail.  No provider result, fresh allocation, or executable
state appears in this relation: it is the finite semantic work that the
executable conservative scan performed during call entry. -/
inductive RejectedPullsN :
    Nat → PreparedCursor → PreparedCursor → Prop where
  | zero (cursor : PreparedCursor) :
      RejectedPullsN 0 cursor cursor
  | succ (count : Nat) (cursor : PreparedCursor) (branch : ClauseBranch)
      (branches : List ClauseBranch) (finish : PreparedCursor)
      (remaining : cursor.remaining = branch :: branches)
      (clash : ¬ ∃ result, HeadResolution branch result)
      (tail :
        RejectedPullsN count (cursor.advance branch branches) finish) :
      RejectedPullsN (count + 1) cursor finish

/-- A zero-length rejected prefix preserves the complete prepared cursor,
not merely its remaining-clause list.  Naming this inversion avoids dependent
elimination of a cursor embedded inside a larger proof-relevant carrier. -/
theorem RejectedPullsN.eq_of_count_zero
    {before after : PreparedCursor}
    (pulls : RejectedPullsN 0 before after) :
    after = before := by
  cases pulls
  rfl

/-- The endpoint of an exact rejected-prefix execution is the literal
unconsumed suffix of the starting cursor.  This is the positional fact that
keeps duplicate clause payloads occurrence-sensitive: the transition count,
not value equality, determines which frozen occurrence is now at the front.
-/
theorem RejectedPullsN.remaining_eq_drop
    {count : Nat} {before after : PreparedCursor}
    (pulls : RejectedPullsN count before after) :
    after.remaining = before.remaining.drop count := by
  induction pulls with
  | zero cursor => simp
  | succ count cursor branch branches finish remaining clash tail
      inductionHypothesis =>
      rw [inductionHypothesis]
      simp [PreparedCursor.advance, remaining]

/-- An exact rejected-prefix execution cannot consume more occurrences than
the frozen cursor contains. -/
theorem RejectedPullsN.count_le_remaining_length
    {count : Nat} {before after : PreparedCursor}
    (pulls : RejectedPullsN count before after) :
    count ≤ before.remaining.length := by
  induction pulls with
  | zero cursor => simp
  | succ count cursor branch branches finish remaining clash tail
      inductionHypothesis =>
      rw [remaining]
      simp only [List.length_cons]
      have tailBound : count ≤ branches.length := by
        simpa [PreparedCursor.advance] using inductionHypothesis
      omega

/-- A conservative scan is ready exactly when it is exhausted or its first
paired occurrence was retained.  The retained constructor carries the
complete remaining decision alignment, so later activation cannot swap or
reorder the suffix. -/
inductive PrefilterReady (argsv : List Atom) (resv : Atom) :
    List ClauseBranch → List PLeaTTa.Clause → Prop where
  | exhausted : PrefilterReady argsv resv [] []
  | retained (branch : ClauseBranch) (clause : PLeaTTa.Clause)
      (branches : List ClauseBranch) (clauses : List PLeaTTa.Clause)
      (agreement : NormalizedHeadAgrees branch argsv resv clause)
      (kept : resolutionClauseRetained argsv resv clause = true)
      (tail : ConservativeResolutionScan argsv resv branches clauses) :
      PrefilterReady argsv resv
        (branch :: branches) (clause :: clauses)

/-- Rejected cursor pulls are genuine, exactly counted public transitions.
Their observation trace is exactly empty and their non-backtrackable session
is definitionally unchanged.  Thus prefiltering is a bounded silent
expansion, not a zero-step observation quotient. -/
theorem RejectedPullsN.stepsN
    {count : Nat} {before after : PreparedCursor}
    (pulls : RejectedPullsN count before after)
    (scope : CutScopeId) (session : Session) :
    StepsN count
      (.running session (.clauses scope before)) []
      (.running session (.clauses scope after)) := by
  induction pulls with
  | zero cursor =>
      exact .zero _
  | succ count cursor branch branches finish remaining clash tail
      inductionHypothesis =>
      have pulled :
          LocalPull cursor
            (.silent (cursor.advance branch branches)) :=
        .rejected cursor branch branches remaining clash
      have raw :
          RawStep session (.clauses scope cursor) [] .none session
            (.running (.clauses scope (cursor.advance branch branches))) := by
        simpa [localPullEvents, localPullTarget] using
          (RawStep.clausesPull scope cursor
            (.silent (cursor.advance branch branches)) session pulled)
      have first :
          Transition
            (.running session (.clauses scope cursor)) []
            (.running session
              (.clauses scope (cursor.advance branch branches))) :=
        .ordinary _ _ _ _ _ raw
      simpa using
        (StepsN.succ count
          (.running session (.clauses scope cursor))
          (.running session
            (.clauses scope (cursor.advance branch branches)))
          (.running session (.clauses scope finish))
          [] [] first inductionHypothesis)

/-- Every conservative decision alignment factors uniquely by construction
into a maximal rejected prefix and a ready suffix.

The skipped source and executable occurrence lists are returned explicitly,
with exact equal lengths and exact reconstruction equations.  Consequently
the step count cannot be shortened, padded, or justified by reflexivity, and
the ready suffix remains a literal source-order suffix of both input banks. -/
theorem ConservativeResolutionScan.decomposeRejectedPrefix
    {argsv : List Atom} {resv : Atom}
    {branches : List ClauseBranch} {clauses : List PLeaTTa.Clause}
    (scan : ConservativeResolutionScan argsv resv branches clauses)
    (cursor : PreparedCursor) (remaining : cursor.remaining = branches) :
    ∃ count skippedBranches skippedClauses finish
        readyBranches readyClauses,
      branches = skippedBranches ++ readyBranches ∧
      clauses = skippedClauses ++ readyClauses ∧
      skippedBranches.length = count ∧
      skippedClauses.length = count ∧
      RejectedPullsN count cursor finish ∧
      finish.remaining = readyBranches ∧
      PrefilterReady argsv resv readyBranches readyClauses := by
  induction scan generalizing cursor with
  | nil =>
      exact ⟨0, [], [], cursor, [], [],
        rfl, rfl, rfl, rfl, .zero cursor, remaining, .exhausted⟩
  | skipped branch clause branches clauses agreement rejected clash tail
      inductionHypothesis =>
      let next := cursor.advance branch branches
      have nextRemaining : next.remaining = branches := by
        simp [next, PreparedCursor.advance]
      obtain
        ⟨count, skippedBranches, skippedClauses, finish,
          readyBranches, readyClauses, branchesEq, clausesEq,
          branchCount, clauseCount, pulls, finishRemaining, ready⟩ :=
        inductionHypothesis next nextRemaining
      refine
        ⟨count + 1, branch :: skippedBranches, clause :: skippedClauses,
          finish, readyBranches, readyClauses, ?_, ?_, ?_, ?_, ?_,
          finishRemaining, ready⟩
      · simp [branchesEq]
      · simp [clausesEq]
      · simp [branchCount]
      · simp [clauseCount]
      · exact .succ count cursor branch branches finish remaining clash pulls
  | retained branch clause branches clauses agreement kept tail =>
      exact
        ⟨0, [], [], cursor, branch :: branches, clause :: clauses,
          rfl, rfl, rfl, rfl, .zero cursor, remaining,
          .retained branch clause branches clauses agreement kept tail⟩

/-- The decomposition above immediately yields the exact empty-observation
execution prefix demanded by finite-prefix bisimulation.  The count and both
literal suffix equations remain in the result; no internal work is erased. -/
theorem ConservativeResolutionScan.rejectedPrefixSteps
    {argsv : List Atom} {resv : Atom}
    {branches : List ClauseBranch} {clauses : List PLeaTTa.Clause}
    (scan : ConservativeResolutionScan argsv resv branches clauses)
    (cursor : PreparedCursor) (remaining : cursor.remaining = branches)
    (scope : CutScopeId) (session : Session) :
    ∃ count skippedBranches skippedClauses finish
        readyBranches readyClauses,
      branches = skippedBranches ++ readyBranches ∧
      clauses = skippedClauses ++ readyClauses ∧
      skippedBranches.length = count ∧
      skippedClauses.length = count ∧
      StepsN count
        (.running session (.clauses scope cursor)) []
        (.running session (.clauses scope finish)) ∧
      finish.remaining = readyBranches ∧
      PrefilterReady argsv resv readyBranches readyClauses := by
  obtain
    ⟨count, skippedBranches, skippedClauses, finish,
      readyBranches, readyClauses, branchesEq, clausesEq,
      branchCount, clauseCount, pulls, finishRemaining, ready⟩ :=
    scan.decomposeRejectedPrefix cursor remaining
  exact
    ⟨count, skippedBranches, skippedClauses, finish,
      readyBranches, readyClauses, branchesEq, clausesEq,
      branchCount, clauseCount, pulls.stepsN scope session,
      finishRemaining, ready⟩

/-! ### Anti-vacuity: a real rigid clash is consumed silently -/

private def rejectedReferenceBranch : ClauseBranch :=
  { sourceId := 0
    callGeneration := 0
    freshSubstitution := []
    headEquations :=
      [(.integer 1, .integer 2), (.atom "out", .atom "out")]
    body := []
    bindings := []
    firstFresh := 0
    nextFresh := 0 }

private def rejectedExecutableClause : PLeaTTa.Clause :=
  { params := [.gnd (.int 2)]
    result := .sym "out"
    body := [] }

/-- Concrete discriminator: the semantic relation is inhabited, the
executable prefilter rejects on the first rigid argument, and therefore the
independent ordered MGU protocol has no head resolution. -/
theorem rigid_clash_filter_and_head_rejection :
    NormalizedHeadAgrees rejectedReferenceBranch
        [.gnd (.int 1)] (.sym "out") rejectedExecutableClause ∧
      resolutionClauseRetained
        [.gnd (.int 1)] (.sym "out") rejectedExecutableClause = false ∧
      ¬ ∃ result, HeadResolution rejectedReferenceBranch result := by
  have agreement :
      NormalizedHeadAgrees rejectedReferenceBranch
        [.gnd (.int 1)] (.sym "out") rejectedExecutableClause := by
    constructor
    · rfl
    · exact AlphaEquationsAgree.cons
        (AlphaTermAgrees.integer (alpha := []) 1)
        (AlphaTermAgrees.integer (alpha := []) 2)
        (AlphaEquationsAgree.cons
          (AlphaTermAgrees.atom (alpha := []) (by decide) (by decide))
          (AlphaTermAgrees.atom (alpha := []) (by decide) (by decide))
          .nil)
  have rejected :
      resolutionClauseRetained
        [.gnd (.int 1)] (.sym "out") rejectedExecutableClause = false := by
    rfl
  exact ⟨agreement, rejected,
    agreement.no_headResolution_of_rejected rejected⟩

private def secondRejectedReferenceBranch : ClauseBranch :=
  { sourceId := 1
    callGeneration := 0
    freshSubstitution := []
    headEquations :=
      [(.integer 1, .integer 3), (.atom "out", .atom "out")]
    body := []
    bindings := []
    firstFresh := 0
    nextFresh := 0 }

private def secondRejectedExecutableClause : PLeaTTa.Clause :=
  { params := [.gnd (.int 3)]
    result := .sym "out"
    body := [] }

private def retainedReferenceBranch : ClauseBranch :=
  { sourceId := 2
    callGeneration := 0
    freshSubstitution := []
    headEquations :=
      [(.integer 1, .integer 1), (.atom "out", .atom "out")]
    body := []
    bindings := []
    firstFresh := 0
    nextFresh := 0 }

private def retainedExecutableClause : PLeaTTa.Clause :=
  { params := [.gnd (.int 1)]
    result := .sym "out"
    body := [] }

private theorem secondRejectedHeadAgrees :
    NormalizedHeadAgrees secondRejectedReferenceBranch
      [.gnd (.int 1)] (.sym "out") secondRejectedExecutableClause := by
  constructor
  · rfl
  · exact AlphaEquationsAgree.cons
      (AlphaTermAgrees.integer (alpha := []) 1)
      (AlphaTermAgrees.integer (alpha := []) 3)
      (AlphaEquationsAgree.cons
        (AlphaTermAgrees.atom (alpha := []) (by decide) (by decide))
        (AlphaTermAgrees.atom (alpha := []) (by decide) (by decide))
        .nil)

private theorem retainedHeadAgrees :
    NormalizedHeadAgrees retainedReferenceBranch
      [.gnd (.int 1)] (.sym "out") retainedExecutableClause := by
  constructor
  · rfl
  · exact AlphaEquationsAgree.cons
      (AlphaTermAgrees.integer (alpha := []) 1)
      (AlphaTermAgrees.integer (alpha := []) 1)
      (AlphaEquationsAgree.cons
        (AlphaTermAgrees.atom (alpha := []) (by decide) (by decide))
        (AlphaTermAgrees.atom (alpha := []) (by decide) (by decide))
        .nil)

private def twoRejectedCursor : PreparedCursor :=
  { callGeneration := 0
    predicate := "ranked"
    arguments := [.integer 1, .atom "out"]
    bindings := []
    reservationStart := 0
    remaining :=
      [rejectedReferenceBranch, secondRejectedReferenceBranch,
        retainedReferenceBranch]
    reservedUntil := 0 }

private def afterTwoRejected : PreparedCursor :=
  (twoRejectedCursor.advance rejectedReferenceBranch
      [secondRejectedReferenceBranch, retainedReferenceBranch]).advance
    secondRejectedReferenceBranch [retainedReferenceBranch]

/-- Concrete anti-vacuity witness: two rigid source-ranked rejections are two
actual silent transitions before the retained occurrence becomes active.
The witness fixes the final cursor and the retained executable suffix, so the
claim cannot be satisfied by the zero-step constructor or by skipping past
the first retained clause. -/
theorem two_rigid_prefilter_skips_are_exact_two_steps
    (scope : CutScopeId) (session : Session) :
    ConservativeResolutionScan [.gnd (.int 1)] (.sym "out")
        [rejectedReferenceBranch, secondRejectedReferenceBranch,
          retainedReferenceBranch]
        [rejectedExecutableClause, secondRejectedExecutableClause,
          retainedExecutableClause] ∧
      StepsN 2
        (.running session (.clauses scope twoRejectedCursor)) []
        (.running session (.clauses scope afterTwoRejected)) ∧
      afterTwoRejected.remaining = [retainedReferenceBranch] ∧
      PrefilterReady [.gnd (.int 1)] (.sym "out")
        afterTwoRejected.remaining [retainedExecutableClause] := by
  have firstAgreement := rigid_clash_filter_and_head_rejection.1
  have firstRejected := rigid_clash_filter_and_head_rejection.2.1
  have firstClash := rigid_clash_filter_and_head_rejection.2.2
  have secondRejected :
      resolutionClauseRetained
        [.gnd (.int 1)] (.sym "out")
        secondRejectedExecutableClause = false := by
    rfl
  have secondClash :
      ¬ ∃ result, HeadResolution secondRejectedReferenceBranch result :=
    secondRejectedHeadAgrees.no_headResolution_of_rejected secondRejected
  have retained :
      resolutionClauseRetained
        [.gnd (.int 1)] (.sym "out")
        retainedExecutableClause = true := by
    rfl
  have scan :
      ConservativeResolutionScan [.gnd (.int 1)] (.sym "out")
        [rejectedReferenceBranch, secondRejectedReferenceBranch,
          retainedReferenceBranch]
        [rejectedExecutableClause, secondRejectedExecutableClause,
          retainedExecutableClause] :=
    .skipped _ _ _ _ firstAgreement firstRejected firstClash
      (.skipped _ _ _ _ secondRejectedHeadAgrees secondRejected secondClash
        (.retained _ _ _ _ retainedHeadAgrees retained .nil))
  have pulls : RejectedPullsN 2 twoRejectedCursor afterTwoRejected := by
    exact
      .succ 1 twoRejectedCursor rejectedReferenceBranch
        [secondRejectedReferenceBranch, retainedReferenceBranch]
        afterTwoRejected rfl firstClash
        (.succ 0
          (twoRejectedCursor.advance rejectedReferenceBranch
            [secondRejectedReferenceBranch, retainedReferenceBranch])
          secondRejectedReferenceBranch [retainedReferenceBranch]
          afterTwoRejected rfl secondClash (.zero afterTwoRejected))
  refine ⟨scan, pulls.stepsN scope session, rfl, ?_⟩
  exact .retained _ _ _ _ retainedHeadAgrees retained .nil

end PLeaTTa.PrologPrefilterScanBridge
