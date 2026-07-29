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

end PLeaTTa.PrologPrefilterScanBridge
