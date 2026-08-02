-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologRetainedCursorOwnershipBridge
Purpose: Keep the exact retained source cursor and executable alternative
  suffix owned by the same pending local call.
Trusted boundary: none
Main exports:
  RetainedCursorAlternativeOwnership,
  PendingRetainedCursorAlternativeOwnership,
  RepresentativeRetainedCallFrontier.tailOwnership
-/
import PLeaTTa.Proofs.PrologRepresentativeCallFrontierBridge
import PLeaTTa.Proofs.PrologRepresentativeTaskActivationBridge

namespace PLeaTTa.PrologRetainedCursorOwnershipBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open PrologActivationMacro
open PrologCallPayloadBridge
open PrologCursorAlternativeBridge
open PrologRecursiveCallPayloadBridge
open PrologRepresentativeCallFrontierBridge
open PrologSupportedCursorAlternativeBridge

/-!
The retained-clause activation theorem previously kept the source cursor and
the executable `altTail`, but only as unrelated fields.  That is insufficient
for recursive control: a later proof could pair the right cursor with a
same-length but differently ordered alternative bank, or could existentially
change the caller continuation or cut barrier baked into every alternative.

The relation below exposes every observable input to `resolutionAlt` as an
index.  Only the compiler candidate list remains existential.  The
pending-state wrapper then pins those indices to the actual suspended call
head, query term, barrier depth, and persistent counter.  In particular,
`cursor.bindings` is not equated with the executable `binding`: their semantic
relationship is carried by `RepresentativeNormalizedCallAgrees`.
-/

/-- Exact occurrence-preserving ownership of one retained cursor by one
executable alternative suffix.

`rest`, `binding`, `qterm`, and `barrier` are deliberately indices rather
than existential fields: all four are embedded in each concrete
`resolutionAlt`.  `argsv`, `args`, and `res` are likewise explicit, while the
semantic query certificate ties them to the independent cursor. -/
def RetainedCursorAlternativeOwnership
    (queryAlpha : List (LogicVar × String))
    (cursor : PreparedCursor)
    (argsv args : List Atom) (res : Atom)
    (rest : List PLeaTTa.Goal) (binding : Subst)
    (qterm : Atom) (barrier counter : Nat)
    (alts : List PLeaTTa.Alt) (finalCounter : Nat) : Prop :=
  ∃ candidates : List PLeaTTa.Clause,
    cursor.WellFormed ∧
    RepresentativeNormalizedCallAgrees queryAlpha cursor argsv
      (PLeaTTa.subst binding res) ∧
    argsv = args.map (PLeaTTa.subst binding) ∧
    List.Forall₂
      (SupportedPreparedCandidateAgrees cursor.callGeneration
        cursor.predicate cursor.arguments cursor.bindings)
      cursor.remaining candidates ∧
    (∀ clause, clause ∈ candidates →
      clause.params.length = argsv.length) ∧
    ResolutionScan argsv args res rest binding qterm barrier candidates
      counter alts finalCounter

/-- A semantic representative selected on a smaller shared alpha graph
remains valid when every old link is embedded in a larger graph.  No
representative, substitution, or runtime atom is changed. -/
theorem RepresentativeNormalizedCallAgrees.mono
    {smaller larger : List (LogicVar × String)}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    {cursor : PreparedCursor} {argsv : List Atom} {resv : Atom}
    (agreement :
      RepresentativeNormalizedCallAgrees smaller cursor argsv resv) :
    RepresentativeNormalizedCallAgrees larger cursor argsv resv := by
  rcases agreement with
    ⟨residualRepresentative, olderBase, variants, residualCovered,
      olderBaseIncluded, arguments⟩
  refine
    ⟨residualRepresentative, olderBase, variants, ?_, olderBaseIncluded,
      ?_⟩
  · exact
      PLeaTTa.PrologRepresentativeTaskActivationBridge.TreeSubstitutionVariablesSatisfy.monoAlpha
        included residualCovered
  · exact
      List.Forall₂.imp
        (fun _term _atom agreement =>
          PLeaTTa.PrologRepresentativeActivationBridge.CanonicalRuntimeAgrees.mono
            included agreement)
        arguments

/-- Exact retained ownership is monotone only in its representation graph;
the cursor, candidate occurrences, alternative list, continuation, barrier,
and both counter endpoints remain definitionally identical. -/
theorem RetainedCursorAlternativeOwnership.mono
    {smaller larger : List (LogicVar × String)}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    {cursor : PreparedCursor}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst}
    {qterm : Atom} {barrier counter : Nat}
    {alts : List PLeaTTa.Alt} {finalCounter : Nat}
    (ownership :
      RetainedCursorAlternativeOwnership smaller cursor argsv args res rest
        binding qterm barrier counter alts finalCounter) :
    RetainedCursorAlternativeOwnership larger cursor argsv args res rest
      binding qterm barrier counter alts finalCounter := by
  rcases ownership with
    ⟨candidates, wellFormed, query, substitutedArgs, supported, arities,
      scan⟩
  exact
    ⟨candidates, wellFormed,
      RepresentativeNormalizedCallAgrees.mono included query,
      substitutedArgs, supported, arities, scan⟩

/-- An executable resolution scan owns no more alternatives than source
candidate occurrences.  This is proved from the scan constructors directly,
without characterizing the filter a second time. -/
theorem resolutionScan_alts_length_le_clauses
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst}
    {qterm : Atom} {barrier counter : Nat}
    {clauses : List PLeaTTa.Clause}
    {alts : List PLeaTTa.Alt} {finalCounter : Nat}
    (scan :
      ResolutionScan argsv args res rest binding qterm barrier clauses
        counter alts finalCounter) :
    alts.length ≤ clauses.length := by
  induction scan with
  | nil =>
      exact Nat.le_refl 0
  | skipped clause clauses counter finalCounter alts skipped tail
      inductionHypothesis =>
      exact Nat.le_succ_of_le inductionHypothesis
  | retained clause clauses counter finalCounter alts retained tail
      inductionHypothesis =>
      simpa using Nat.succ_le_succ inductionHypothesis

/-- Every owned executable alternative is one retained source occurrence;
conservative skips are the exact reason the converse count can fail. -/
theorem RetainedCursorAlternativeOwnership.alts_length_le
    {queryAlpha : List (LogicVar × String)}
    {cursor : PreparedCursor}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst}
    {qterm : Atom} {barrier counter : Nat}
    {alts : List PLeaTTa.Alt} {finalCounter : Nat}
    (ownership :
      RetainedCursorAlternativeOwnership queryAlpha cursor argsv args res
        rest binding qterm barrier counter alts finalCounter) :
    alts.length ≤ cursor.remaining.length := by
  rcases ownership with
    ⟨candidates, wellFormed, query, substitutedArgs, supported, arities,
      scan⟩
  exact
    (resolutionScan_alts_length_le_clauses scan).trans_eq
      supported.length_eq.symm

/-- Resolution-owned suffixes contain no anonymous control marker.  The
predicate marker is installed once, separately, by the call transition. -/
theorem RetainedCursorAlternativeOwnership.barrierCount_zero
    {queryAlpha : List (LogicVar × String)}
    {cursor : PreparedCursor}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst}
    {qterm : Atom} {barrier counter : Nat}
    {alts : List PLeaTTa.Alt} {finalCounter : Nat}
    (ownership :
      RetainedCursorAlternativeOwnership queryAlpha cursor argsv args res
        rest binding qterm barrier counter alts finalCounter) :
    PLeaTTa.barrierCount alts = 0 := by
  rcases ownership with
    ⟨candidates, wellFormed, query, substitutedArgs, supported, arities,
      scan⟩
  exact scan.barrierCount_zero

/-- Exact ownership retains the stronger scan invariant that every stored
alternative is an ordinary branch.  In particular, neither active nor
dormant catch markers can occur in a clause-owned resource bank. -/
theorem RetainedCursorAlternativeOwnership.alts_all_branches
    {queryAlpha : List (LogicVar × String)}
    {cursor : PreparedCursor}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst}
    {qterm : Atom} {barrier counter : Nat}
    {alts : List PLeaTTa.Alt} {finalCounter : Nat}
    (ownership :
      RetainedCursorAlternativeOwnership queryAlpha cursor argsv args res
        rest binding qterm barrier counter alts finalCounter) :
    ∀ alt ∈ alts,
      ∃ goals branchBinding, alt = PLeaTTa.Alt.br goals branchBinding := by
  rcases ownership with
    ⟨_candidates, _wellFormed, _query, _substitutedArgs, _supported,
      _arities, scan⟩
  exact scan.alts_all_branches

/-! ## Anti-vacuity at the exact executable ownership seam -/

private def ownershipWitnessCutClause : PLeaTTa.Clause :=
  { params := []
    result := .sym "out"
    body := [.cut] }

private def ownershipWitnessPlainClause : PLeaTTa.Clause :=
  { params := []
    result := .sym "out"
    body := [] }

/-- Two retained alternatives cannot be swapped merely because the source
cursor and executable bank have the same length.  The contradiction is
against `ResolutionScan.deterministic`, hence it tests the exact ordered
resource stored by `RetainedCursorAlternativeOwnership`. -/
theorem equal_length_alternative_swap_is_rejected
    (barrier seed : Nat) :
    let first :=
      resolutionAlt [] [] (.sym "out") [] [] (.sym "query") barrier seed
        ownershipWitnessCutClause
    let second :=
      resolutionAlt [] [] (.sym "out") [] [] (.sym "query") barrier
        (seed + 1) ownershipWitnessPlainClause
    ¬ ResolutionScan [] [] (.sym "out") [] [] (.sym "query") barrier
      [ownershipWitnessCutClause, ownershipWitnessPlainClause] seed
      [second, first] (seed + 2) := by
  dsimp only
  intro swapped
  have cutRetained :
      resolutionClauseRetained [] (.sym "out")
        ownershipWitnessCutClause = true := by
    rfl
  have plainRetained :
      resolutionClauseRetained [] (.sym "out")
        ownershipWitnessPlainClause = true := by
    rfl
  have ordered :
      ResolutionScan [] [] (.sym "out") [] [] (.sym "query") barrier
        [ownershipWitnessCutClause, ownershipWitnessPlainClause] seed
        [resolutionAlt [] [] (.sym "out") [] [] (.sym "query") barrier seed
            ownershipWitnessCutClause,
         resolutionAlt [] [] (.sym "out") [] [] (.sym "query") barrier
            (seed + 1) ownershipWitnessPlainClause]
        (seed + 2) := by
    exact
      .retained ownershipWitnessCutClause [ownershipWitnessPlainClause]
        seed (seed + 2) _ (by simpa using cutRetained)
        (.retained ownershipWitnessPlainClause [] (seed + 1) (seed + 2) []
          (by simpa using plainRetained)
          (by simpa using ResolutionScan.nil (seed + 2)))
  have same := (ordered.deterministic swapped).1
  simp [resolutionAlt, ownershipWitnessCutClause,
    ownershipWitnessPlainClause, PLeaTTa.freshenResolutionClause,
    PLeaTTa.renameGoalSuffix] at same

/-- A cut-bearing retained alternative records exactly the predicate barrier
at which it was generated.  A differently tagged alternative cannot satisfy
the same scan, so existentially hiding the barrier would be unsound. -/
theorem wrong_cut_barrier_scan_is_rejected
    {expected actual : Nat} (different : expected ≠ actual)
    (seed : Nat) :
    ¬ ResolutionScan [] [] (.sym "out") [] [] (.sym "query") expected
      [ownershipWitnessCutClause] seed
      [resolutionAlt [] [] (.sym "out") [] [] (.sym "query") actual seed
        ownershipWitnessCutClause]
      (seed + 1) := by
  intro wrong
  have retained :
      resolutionClauseRetained [] (.sym "out")
        ownershipWitnessCutClause = true := by
    rfl
  have correct :
      ResolutionScan [] [] (.sym "out") [] [] (.sym "query") expected
        [ownershipWitnessCutClause] seed
        [resolutionAlt [] [] (.sym "out") [] [] (.sym "query") expected seed
          ownershipWitnessCutClause]
        (seed + 1) := by
    exact
      .retained ownershipWitnessCutClause [] seed (seed + 1) []
        (by simpa using retained)
        (by simpa using ResolutionScan.nil (seed + 1))
  have same := (correct.deterministic wrong).1
  simp [resolutionAlt, ownershipWitnessCutClause,
    PLeaTTa.freshenResolutionClause, PLeaTTa.renameGoalSuffix] at same
  exact different same

/-- Transport compiler support from a fixed call identity to the current
advanced cursor, occurrence by occurrence. -/
theorem supportedCandidates_at_cursor
    {cursor : PreparedCursor}
    {callGeneration : Generation} {predicate : String}
    {referenceArguments : List Term}
    {referenceBindings : Substitution}
    {branches : List ClauseBranch} {clauses : List PLeaTTa.Clause}
    (context :
      CursorCallContext cursor callGeneration predicate referenceArguments
        referenceBindings)
    (supported :
      List.Forall₂
        (SupportedPreparedCandidateAgrees callGeneration predicate
          referenceArguments referenceBindings)
        branches clauses) :
    List.Forall₂
      (SupportedPreparedCandidateAgrees cursor.callGeneration
        cursor.predicate cursor.arguments cursor.bindings)
      branches clauses := by
  induction supported with
  | nil =>
      exact .nil
  | cons head tail inductionHypothesis =>
      exact .cons (context.supportedPreparedCandidate head)
        inductionHypothesis

/-- Build exact retained ownership from the original supported occurrence
spine and the original executable scan.  Constructor choices come solely
from `scan`; this theorem does not introduce a second filter. -/
theorem retainedCursorAlternativeOwnership_of_scan
    {queryAlpha : List (LogicVar × String)}
    {cursor : PreparedCursor}
    {callGeneration : Generation} {predicate : String}
    {referenceArguments : List Term}
    {referenceBindings : Substitution}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst}
    {qterm : Atom} {barrier counter : Nat}
    {branches : List ClauseBranch} {clauses : List PLeaTTa.Clause}
    {alts : List PLeaTTa.Alt} {finalCounter : Nat}
    (remaining : cursor.remaining = branches)
    (context :
      CursorCallContext cursor callGeneration predicate referenceArguments
        referenceBindings)
    (wellFormed : cursor.WellFormed)
    (query :
      RepresentativeNormalizedCallAgrees queryAlpha cursor argsv
        (PLeaTTa.subst binding res))
    (substitutedArgs : argsv = args.map (PLeaTTa.subst binding))
    (supported :
      List.Forall₂
        (SupportedPreparedCandidateAgrees callGeneration predicate
          referenceArguments referenceBindings)
        branches clauses)
    (arities :
      ∀ clause, clause ∈ clauses → clause.params.length = argsv.length)
    (scan :
      ResolutionScan argsv args res rest binding qterm barrier clauses
        counter alts finalCounter) :
    RetainedCursorAlternativeOwnership queryAlpha cursor argsv args res rest
      binding qterm barrier counter alts finalCounter := by
  have supportedAtCursor :
      List.Forall₂
        (SupportedPreparedCandidateAgrees cursor.callGeneration
          cursor.predicate cursor.arguments cursor.bindings)
        branches clauses :=
    supportedCandidates_at_cursor context supported
  refine
    ⟨clauses, wellFormed, query, substitutedArgs, ?_, arities, scan⟩
  simpa [remaining] using supportedAtCursor

/-- Ownership indexed by an actual pending call.

Although the lower relation exposes `args`, `res`, and `binding` directly,
this wrapper avoids widening every activation theorem: `callHead` pins those
witnesses to the literal suspended executable task.  `qterm` and `barrier`
are separately fixed because both affect generated alternative content. -/
def PendingRetainedCursorAlternativeOwnership
    (queryAlpha : List (LogicVar × String))
    (pending : DemandDrivenCallStep.PendingCall)
    (cursor : PreparedCursor)
    (rest : List PLeaTTa.Goal) (qterm : Atom) (barrier : Nat)
    (alts : List PLeaTTa.Alt) : Prop :=
  ∃ argsv args : List Atom, ∃ res : Atom, ∃ binding : Subst, ∃ counter : Nat,
    pending.outer.cur =
      some (PLeaTTa.Goal.call cursor.predicate args res :: rest, binding) ∧
    qterm = pending.outer.qterm ∧
    barrier =
      pending.outer.barriers.getD
        (PLeaTTa.barrierCount pending.outer.alts) + 1 ∧
    RetainedCursorAlternativeOwnership queryAlpha cursor argsv args res rest
      binding qterm barrier counter alts pending.persistent.counter

/-- Pending-state ownership survives alpha extension while remaining tied to
the same literal suspended call head and barrier depth. -/
theorem PendingRetainedCursorAlternativeOwnership.mono
    {smaller larger : List (LogicVar × String)}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    {pending : DemandDrivenCallStep.PendingCall}
    {cursor : PreparedCursor}
    {rest : List PLeaTTa.Goal} {qterm : Atom} {barrier : Nat}
    {alts : List PLeaTTa.Alt}
    (ownership :
      PendingRetainedCursorAlternativeOwnership smaller pending cursor rest
        qterm barrier alts) :
    PendingRetainedCursorAlternativeOwnership larger pending cursor rest
      qterm barrier alts := by
  rcases ownership with
    ⟨argsv, args, res, binding, counter, callHead, queryTerm, barrierExact,
      cursorOwnership⟩
  exact
    ⟨argsv, args, res, binding, counter, callHead, queryTerm, barrierExact,
      cursorOwnership.mono included⟩

/-- The retained semantic frontier owns the exact executable suffix left
after its selected head alternative.  The cursor is advanced once because
the selected branch now executes on the left; its remaining siblings are the
owned backtracking resource. -/
theorem
    RepresentativeRetainedCallFrontier.tailOwnership
    {queryAlpha : List (LogicVar × String)}
    {opened : OpenedCall} {before : DemandDrivenStep.OpenConf}
    {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    {branchTail : List ClauseBranch} {clauseTail : List PLeaTTa.Clause}
    {altTail : List PLeaTTa.Alt} {copied : PLeaTTa.Clause}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst}
    {qterm : Atom} {barrier startCounter : Nat}
    (entry :
      RepresentativeSupportedCallEntryRelates queryAlpha opened before
        pending argsv args res rest binding qterm barrier startCounter)
    (frontier :
      RepresentativeRetainedCallFrontier queryAlpha opened before pending
        finish branch clause branchTail clauseTail altTail copied argsv args
        res rest binding qterm barrier startCounter) :
    PendingRetainedCursorAlternativeOwnership queryAlpha pending
      (finish.advance branch branchTail) rest qterm barrier altTail := by
  let advanced := finish.advance branch branchTail
  have advancedRemaining : advanced.remaining = branchTail := by
    simp [advanced, PreparedCursor.advance]
  have advancedContext :
      CursorCallContext advanced opened.cursor.callGeneration
        opened.cursor.predicate opened.cursor.arguments
        opened.cursor.bindings :=
    frontier.finishContext.advance branch branchTail
  have advancedWellFormed : advanced.WellFormed :=
    finish.advance_wellFormed frontier.finishWellFormed
      frontier.finishRemaining
  have queryAtAdvanced :
      RepresentativeNormalizedCallAgrees queryAlpha advanced argsv
        (PLeaTTa.subst binding res) :=
    PLeaTTa.PrologRepresentativeCallFrontierBridge.CursorCallContext.representativeNormalizedCallAgrees
      advancedContext frontier.finishContext frontier.query
  have ownership :
      RetainedCursorAlternativeOwnership queryAlpha advanced argsv args res
        rest binding qterm barrier (startCounter + 1) altTail
        pending.persistent.counter :=
    retainedCursorAlternativeOwnership_of_scan advancedRemaining
      advancedContext advancedWellFormed queryAtAdvanced
      frontier.substitutedArgs frontier.tailSupported frontier.tailArities
      frontier.tailScan
  have callHead :
      pending.outer.cur =
        some
          (PLeaTTa.Goal.call advanced.predicate args res :: rest, binding) := by
    have beforeHead :
        before.control.cur =
          some
            (PLeaTTa.Goal.call opened.cursor.predicate args res :: rest,
              binding) := by
      simpa [DemandDrivenStep.OpenConf.toConf,
        DemandDrivenStep.Control.toConf] using entry.entry.callHead
    rw [entry.entry.outer]
    rw [advancedContext.predicate_eq]
    exact beforeHead
  have queryTerm : qterm = pending.outer.qterm := by
    have beforeQuery : qterm = before.control.qterm := by
      simpa [DemandDrivenStep.OpenConf.toConf,
        DemandDrivenStep.Control.toConf] using frontier.queryTerm
    rw [entry.entry.outer]
    exact beforeQuery
  have barrierExact :
      barrier =
        pending.outer.barriers.getD
          (PLeaTTa.barrierCount pending.outer.alts) + 1 := by
    rw [entry.entry.barrierExact, entry.entry.outer]
    rfl
  exact
    ⟨argsv, args, res, binding, startCounter + 1, callHead, queryTerm,
      barrierExact, ownership⟩

end PLeaTTa.PrologRetainedCursorOwnershipBridge
