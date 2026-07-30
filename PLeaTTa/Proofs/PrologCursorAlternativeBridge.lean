-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologCursorAlternativeBridge
Purpose: Relate the independent prepared clause cursor to the exact
  source-ordered executable alternative bank after conservative prefiltering.
Trusted boundary: none
Main exports: CursorAlternativeSpine, CursorAlternativeReady,
  CursorAlternativeSpine.decomposeRejectedPrefix
-/
import PLeaTTa.Proofs.PrologPrefilterCallBridge

namespace PLeaTTa.PrologCursorAlternativeBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore.Resolver
open PeTTaSpec.PrologCore.GoalSemantics
open PrologActivationMacro
open PrologCallEntryBridge
open PrologPrefilterBridge
open PrologPrefilterCallBridge
open PrologPrefilterScanBridge

/-!
The independent call cursor and the executable alternative bank are
deliberately not equal lists.  The cursor retains every frozen call-start
occurrence.  `resolveAlts` omits a conservatively rejected occurrence and
allocates one executable suffix only for each retained occurrence.

`CursorAlternativeSpine` synchronizes those two representations over their
shared source-ordered executable clause spine.  Its `skipped` constructor
advances only the source occurrence lists and leaves both the executable
counter and alternative bank unchanged.  Its `retained` constructor consumes
one source/executable occurrence, allocates exactly the current executable
seed, and prepends exactly one `resolutionAlt`.

This is the ownership relation needed after a branch succeeds or fails:
dropping the current retained constructor exposes the exact source cursor
tail and executable `alts` tail together, while a maximal source-only rejected
prefix is paid by the already-proved `RejectedPullsN` finite expansion.
-/

/-- Exact occurrence-preserving relation between a frozen independent cursor
suffix and the source-ordered executable alternatives produced for the same
clause occurrences.

The final counter is indexed explicitly.  Thus the relation records both
freshness currencies honestly: a skipped independent branch still advances
its own pre-reserved interval when pulled, while the executable seed advances
only in the `retained` constructor. -/
inductive CursorAlternativeSpine
    (argsv args : List Atom) (res : Atom)
    (rest : List PLeaTTa.Goal) (binding : Subst) (qterm : Atom)
    (barrier : Nat) :
    List ClauseBranch → List PLeaTTa.Clause →
      Nat → List Alt → Nat → Prop where
  | nil (counter : Nat) :
      CursorAlternativeSpine argsv args res rest binding qterm barrier
        [] [] counter [] counter
  | skipped (branch : ClauseBranch) (clause : PLeaTTa.Clause)
      (branches : List ClauseBranch) (clauses : List PLeaTTa.Clause)
      (counter finalCounter : Nat) (alts : List Alt)
      (agreement :
        NormalizedHeadAgrees branch argsv (PLeaTTa.subst binding res) clause)
      (rejected :
        resolutionClauseRetained argsv (PLeaTTa.subst binding res) clause =
          false)
      (clash : ¬ ∃ result, HeadResolution branch result)
      (tail :
        CursorAlternativeSpine argsv args res rest binding qterm barrier
          branches clauses counter alts finalCounter) :
      CursorAlternativeSpine argsv args res rest binding qterm barrier
        (branch :: branches) (clause :: clauses)
        counter alts finalCounter
  | retained (branch : ClauseBranch) (clause : PLeaTTa.Clause)
      (branches : List ClauseBranch) (clauses : List PLeaTTa.Clause)
      (counter finalCounter : Nat) (alts : List Alt)
      (agreement :
        NormalizedHeadAgrees branch argsv (PLeaTTa.subst binding res) clause)
      (kept :
        resolutionClauseRetained argsv (PLeaTTa.subst binding res) clause =
          true)
      (tail :
        CursorAlternativeSpine argsv args res rest binding qterm barrier
          branches clauses (counter + 1) alts finalCounter) :
      CursorAlternativeSpine argsv args res rest binding qterm barrier
        (branch :: branches) (clause :: clauses) counter
        (resolutionAlt argsv args res rest binding qterm barrier counter
          clause :: alts)
        finalCounter

/-- The synchronized spine projects to the independent conservative decision
scan without changing any occurrence order or decision. -/
theorem CursorAlternativeSpine.conservative
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst} {qterm : Atom}
    {barrier : Nat} {branches : List ClauseBranch}
    {clauses : List PLeaTTa.Clause} {counter finalCounter : Nat}
    {alts : List Alt}
    (spine :
      CursorAlternativeSpine argsv args res rest binding qterm barrier
        branches clauses counter alts finalCounter) :
    ConservativeResolutionScan argsv (PLeaTTa.subst binding res)
      branches clauses := by
  induction spine with
  | nil counter =>
      exact .nil
  | skipped branch clause branches clauses counter finalCounter alts
      agreement rejected clash tail inductionHypothesis =>
      exact .skipped branch clause branches clauses agreement rejected clash
        inductionHypothesis
  | retained branch clause branches clauses counter finalCounter alts
      agreement kept tail inductionHypothesis =>
      exact .retained branch clause branches clauses agreement kept
        inductionHypothesis

/-- The same synchronized spine projects to the exact executable scan,
including every concrete `resolutionAlt` and seed. -/
theorem CursorAlternativeSpine.executable
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst} {qterm : Atom}
    {barrier : Nat} {branches : List ClauseBranch}
    {clauses : List PLeaTTa.Clause} {counter finalCounter : Nat}
    {alts : List Alt}
    (spine :
      CursorAlternativeSpine argsv args res rest binding qterm barrier
        branches clauses counter alts finalCounter) :
    ResolutionScan argsv args res rest binding qterm barrier clauses counter
      alts finalCounter := by
  induction spine with
  | nil counter =>
      exact .nil counter
  | skipped branch clause branches clauses counter finalCounter alts
      agreement rejected clash tail inductionHypothesis =>
      exact .skipped clause clauses counter finalCounter alts rejected
        inductionHypothesis
  | retained branch clause branches clauses counter finalCounter alts
      agreement kept tail inductionHypothesis =>
      exact .retained clause clauses counter finalCounter alts kept
        inductionHypothesis

/-- One normalized occurrence spine and the actual executable scan construct
the synchronized relation.  No decision is re-run: constructor choice follows
the supplied `ResolutionScan`, while skipped-head impossibility is transported
from the independent normalized-head agreement. -/
theorem cursorAlternativeSpine_of_forall₂
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst} {qterm : Atom}
    {barrier : Nat} {branches : List ClauseBranch}
    {clauses : List PLeaTTa.Clause} {counter finalCounter : Nat}
    {alts : List Alt}
    (heads :
      List.Forall₂
        (fun branch clause =>
          NormalizedHeadAgrees branch argsv
            (PLeaTTa.subst binding res) clause)
        branches clauses)
    (scan :
      ResolutionScan argsv args res rest binding qterm barrier clauses counter
        alts finalCounter) :
    CursorAlternativeSpine argsv args res rest binding qterm barrier
      branches clauses counter alts finalCounter := by
  induction scan generalizing branches with
  | nil counter =>
      cases heads
      exact .nil counter
  | skipped clause clauses counter finalCounter alts rejected tail
      inductionHypothesis =>
      cases heads with
      | cons agreement remainingHeads =>
          exact .skipped _ _ _ _ _ _ _ agreement rejected
            (agreement.no_headResolution_of_rejected rejected)
            (inductionHypothesis remainingHeads)
  | retained clause clauses counter finalCounter alts kept tail
      inductionHypothesis =>
      cases heads with
      | cons agreement remainingHeads =>
          exact .retained _ _ _ _ _ _ _ agreement kept
            (inductionHypothesis remainingHeads)

/-- The already-audited prefilter-bank certificate contains exactly the
synchronized cursor/alternative ownership spine. -/
theorem PreparedPrefilterBankRelates.cursorAlternativeSpine
    {cursor : PreparedCursor}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst}
    {qterm : Atom} {barrier : Nat}
    {candidates : List PLeaTTa.Clause} {counter finalCounter : Nat}
    {alts : List Alt}
    (agreement :
      PreparedPrefilterBankRelates cursor argsv args res rest binding qterm
        barrier candidates counter alts finalCounter) :
    CursorAlternativeSpine argsv args res rest binding qterm barrier
      cursor.remaining candidates counter alts finalCounter :=
  cursorAlternativeSpine_of_forall₂
    agreement.normalizedHeads agreement.bank.scan

/-- The actual post-call-entry relation therefore exposes the synchronized
spine without recomputing `resolveAlts`. -/
theorem CallEntryPrefilterRelates.cursorAlternativeSpine
    {opened : OpenedCall} {before : DemandDrivenStep.OpenConf}
    {pending : DemandDrivenCallStep.PendingCall}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst}
    {qterm : Atom} {barrier startCounter : Nat}
    (agreement :
      CallEntryPrefilterRelates opened before pending argsv args res rest
        binding qterm barrier startCounter) :
    CursorAlternativeSpine argsv args res rest binding qterm barrier
      opened.cursor.remaining
      (pending.persistent.world.resolutionCandidates
        opened.cursor.predicate args.length)
      startCounter pending.branches pending.persistent.counter :=
  PLeaTTa.PrologCursorAlternativeBridge.PreparedPrefilterBankRelates.cursorAlternativeSpine
    agreement.prefilter

/-- The executable alternative bank never contains more occurrences than the
independent cursor.  A skipped occurrence is the precise reason equality can
fail. -/
theorem CursorAlternativeSpine.alts_length_le
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst} {qterm : Atom}
    {barrier : Nat} {branches : List ClauseBranch}
    {clauses : List PLeaTTa.Clause} {counter finalCounter : Nat}
    {alts : List Alt}
    (spine :
      CursorAlternativeSpine argsv args res rest binding qterm barrier
        branches clauses counter alts finalCounter) :
    alts.length ≤ branches.length := by
  induction spine with
  | nil counter =>
      exact Nat.le_refl 0
  | skipped branch clause branches clauses counter finalCounter alts
      agreement rejected clash tail inductionHypothesis =>
      exact Nat.le_succ_of_le inductionHypothesis
  | retained branch clause branches clauses counter finalCounter alts
      agreement kept tail inductionHypothesis =>
      simpa using Nat.succ_le_succ inductionHypothesis

/-- A skipped head makes cursor/alternative list equality impossible by
length alone.  This is the structural anti-vacuity guard against replacing
the synchronized spine with literal list equality. -/
theorem CursorAlternativeSpine.skipped_head_length_lt
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst} {qterm : Atom}
    {barrier : Nat} {branch : ClauseBranch} {branches : List ClauseBranch}
    {clauses : List PLeaTTa.Clause}
    {counter finalCounter : Nat} {alts : List Alt}
    (spine :
      CursorAlternativeSpine argsv args res rest binding qterm barrier
        branches clauses counter alts finalCounter) :
    alts.length < (branch :: branches).length := by
  simpa using Nat.lt_succ_of_le spine.alts_length_le

/-- A suffix is ready when no source-only conservative rejection remains at
its head.  The retained constructor exposes the exact executable head
alternative and the synchronized tail that remains after either success or
failure of its complete head equality. -/
inductive CursorAlternativeReady
    (argsv args : List Atom) (res : Atom)
    (rest : List PLeaTTa.Goal) (binding : Subst) (qterm : Atom)
    (barrier : Nat) :
    List ClauseBranch → List PLeaTTa.Clause →
      Nat → List Alt → Nat → Prop where
  | exhausted (counter : Nat) :
      CursorAlternativeReady argsv args res rest binding qterm barrier
        [] [] counter [] counter
  | retained (branch : ClauseBranch) (clause : PLeaTTa.Clause)
      (branches : List ClauseBranch) (clauses : List PLeaTTa.Clause)
      (counter finalCounter : Nat) (alts : List Alt)
      (agreement :
        NormalizedHeadAgrees branch argsv (PLeaTTa.subst binding res) clause)
      (kept :
        resolutionClauseRetained argsv (PLeaTTa.subst binding res) clause =
          true)
      (tail :
        CursorAlternativeSpine argsv args res rest binding qterm barrier
          branches clauses (counter + 1) alts finalCounter) :
      CursorAlternativeReady argsv args res rest binding qterm barrier
        (branch :: branches) (clause :: clauses) counter
        (resolutionAlt argsv args res rest binding qterm barrier counter
          clause :: alts)
        finalCounter

/-- Every synchronized ownership spine factors into an exactly counted
source-only rejected prefix and one ready suffix.

The skipped source and executable occurrence lists are returned explicitly.
The executable counter and alternative bank do not change across the prefix;
that fact is enforced by the indices of `CursorAlternativeReady`. -/
theorem CursorAlternativeSpine.decomposeRejectedPrefix
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst} {qterm : Atom}
    {barrier : Nat} {branches : List ClauseBranch}
    {clauses : List PLeaTTa.Clause} {counter finalCounter : Nat}
    {alts : List Alt}
    (spine :
      CursorAlternativeSpine argsv args res rest binding qterm barrier
        branches clauses counter alts finalCounter)
    (cursor : PreparedCursor) (remaining : cursor.remaining = branches) :
    ∃ count skippedBranches skippedClauses finish
        readyBranches readyClauses,
      branches = skippedBranches ++ readyBranches ∧
      clauses = skippedClauses ++ readyClauses ∧
      skippedBranches.length = count ∧
      skippedClauses.length = count ∧
      RejectedPullsN count cursor finish ∧
      finish.remaining = readyBranches ∧
      CursorAlternativeReady argsv args res rest binding qterm barrier
        readyBranches readyClauses counter alts finalCounter := by
  induction spine generalizing cursor with
  | nil counter =>
      exact
        ⟨0, [], [], cursor, [], [], rfl, rfl, rfl, rfl, .zero cursor,
          remaining, .exhausted counter⟩
  | skipped branch clause branches clauses counter finalCounter alts
      agreement rejected clash tail inductionHypothesis =>
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
      · exact
          .succ count cursor branch branches finish remaining clash pulls
  | retained branch clause branches clauses counter finalCounter alts
      agreement kept tail inductionHypothesis =>
      exact
        ⟨0, [], [], cursor, branch :: branches, clause :: clauses,
          rfl, rfl, rfl, rfl, .zero cursor, remaining,
          .retained branch clause branches clauses counter finalCounter alts
            agreement kept tail⟩

/-- The maximal rejected prefix is a genuine finite source execution with
exactly empty observations; the ready suffix retains the exact executable
alternative bank and counter. -/
theorem CursorAlternativeSpine.rejectedPrefixSteps
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst} {qterm : Atom}
    {barrier : Nat} {branches : List ClauseBranch}
    {clauses : List PLeaTTa.Clause} {counter finalCounter : Nat}
    {alts : List Alt}
    (spine :
      CursorAlternativeSpine argsv args res rest binding qterm barrier
        branches clauses counter alts finalCounter)
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
      CursorAlternativeReady argsv args res rest binding qterm barrier
        readyBranches readyClauses counter alts finalCounter := by
  obtain
    ⟨count, skippedBranches, skippedClauses, finish,
      readyBranches, readyClauses, branchesEq, clausesEq,
      branchCount, clauseCount, pulls, finishRemaining, ready⟩ :=
    spine.decomposeRejectedPrefix cursor remaining
  exact
    ⟨count, skippedBranches, skippedClauses, finish,
      readyBranches, readyClauses, branchesEq, clausesEq,
      branchCount, clauseCount, pulls.stepsN scope session,
      finishRemaining, ready⟩

/-- The actual paired call-entry states advance to one shared ready frontier.

The independent side pays exactly the maximal conservatively rejected prefix
as source-only silent steps.  The executable side performs its one real
`callPull` fine step.  The returned `CursorAlternativeReady` relates the
resulting independent cursor suffix to the exact bank that `pending.pulled`
has just inspected; no answer or head-MGU claim is hidden in this phase. -/
theorem CallEntryPrefilterRelates.callPull_ready_correspondence
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {opened : OpenedCall} {before : DemandDrivenStep.OpenConf}
    {pending : DemandDrivenCallStep.PendingCall}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst}
    {qterm : Atom} {barrier startCounter : Nat}
    (agreement :
      CallEntryPrefilterRelates opened before pending argsv args res rest
        binding qterm barrier startCounter) :
    ∃ count skippedBranches skippedClauses finish
        readyBranches readyClauses,
      opened.cursor.remaining = skippedBranches ++ readyBranches ∧
      (pending.persistent.world.resolutionCandidates
          opened.cursor.predicate args.length) =
        skippedClauses ++ readyClauses ∧
      skippedBranches.length = count ∧
      skippedClauses.length = count ∧
      StepsN count
        (.running opened.session (.clauses opened.scope opened.cursor)) []
        (.running opened.session (.clauses opened.scope finish)) ∧
      finish.remaining = readyBranches ∧
      CursorAlternativeReady argsv args res rest binding qterm barrier
        readyBranches readyClauses startCounter pending.branches
        pending.persistent.counter ∧
      DemandDrivenCallStep.Step prog gt (.callPending pending)
        (.ready pending.pulled) := by
  have spine :=
    PLeaTTa.PrologCursorAlternativeBridge.CallEntryPrefilterRelates.cursorAlternativeSpine
      agreement
  obtain
    ⟨count, skippedBranches, skippedClauses, finish,
      readyBranches, readyClauses, branchesEq, clausesEq,
      branchCount, clauseCount, steps, finishRemaining, ready⟩ :=
    spine.rejectedPrefixSteps opened.cursor rfl opened.scope opened.session
  exact
    ⟨count, skippedBranches, skippedClauses, finish,
      readyBranches, readyClauses, branchesEq, clausesEq,
      branchCount, clauseCount, steps, finishRemaining, ready,
      .callPull pending⟩

/-- A ready retained suffix exposes exactly one executable branch before its
tail bank, at the current seed.  This eliminator is the handoff used by the
later head-success/head-failure simulation. -/
theorem CursorAlternativeReady.retained_shape
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst} {qterm : Atom}
    {barrier : Nat} {branches : List ClauseBranch}
    {clauses : List PLeaTTa.Clause} {counter finalCounter : Nat}
    {alts : List Alt}
    (ready :
      CursorAlternativeReady argsv args res rest binding qterm barrier
        branches clauses counter alts finalCounter)
    (nonempty : branches ≠ []) :
    ∃ branch clause branchTail clauseTail altTail,
      branches = branch :: branchTail ∧
      clauses = clause :: clauseTail ∧
      alts =
        resolutionAlt argsv args res rest binding qterm barrier counter
          clause :: altTail ∧
      NormalizedHeadAgrees branch argsv
        (PLeaTTa.subst binding res) clause ∧
      resolutionClauseRetained argsv (PLeaTTa.subst binding res) clause =
        true ∧
      CursorAlternativeSpine argsv args res rest binding qterm barrier
        branchTail clauseTail (counter + 1) altTail finalCounter := by
  cases ready with
  | exhausted counter =>
      exact False.elim (nonempty rfl)
  | retained branch clause branches clauses counter finalCounter alts
      agreement kept tail =>
      exact
        ⟨branch, clause, branches, clauses, alts, rfl, rfl, rfl,
          agreement, kept, tail⟩

/-- Pulling a ready retained bank installs exactly its current seeded
full-head equality and leaves exactly the synchronized tail ahead of the
call's barrier and outer alternatives.

The conclusion is equality of complete executable configurations.  Hence the
pull cannot alter the persistent world/counter, answer accumulator, query,
barrier cache, or any other control field beyond the shared `pull` update. -/
theorem CursorAlternativeReady.pending_pulled_retained
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst} {qterm : Atom}
    {barrier : Nat} {branches : List ClauseBranch}
    {clauses : List PLeaTTa.Clause} {counter finalCounter : Nat}
    {pending : DemandDrivenCallStep.PendingCall}
    (ready :
      CursorAlternativeReady argsv args res rest binding qterm barrier
        branches clauses counter pending.branches finalCounter)
    (nonempty : branches ≠ []) :
    ∃ branch clause branchTail clauseTail altTail copied,
      branches = branch :: branchTail ∧
      clauses = clause :: clauseTail ∧
      copied =
        PLeaTTa.freshenResolutionClause argsv args res rest binding qterm
          counter barrier clause ∧
      pending.pulled.toConf =
        { pending.installed.toConf with
          cur :=
            some
              (PLeaTTa.Goal.eq (.expr (args ++ [res]))
                  (.expr (copied.params ++ [copied.result])) ::
                copied.body ++ rest,
                binding)
          alts := altTail ++ Alt.barrier :: pending.outer.alts } ∧
      NormalizedHeadAgrees branch argsv
        (PLeaTTa.subst binding res) clause ∧
      resolutionClauseRetained argsv (PLeaTTa.subst binding res) clause =
        true ∧
      CursorAlternativeSpine argsv args res rest binding qterm barrier
        branchTail clauseTail (counter + 1) altTail finalCounter := by
  obtain
    ⟨branch, clause, branchTail, clauseTail, altTail,
      branchesEq, clausesEq, altsEq, agreement, kept, tail⟩ :=
    ready.retained_shape nonempty
  let copied :=
    PLeaTTa.freshenResolutionClause argsv args res rest binding qterm
      counter barrier clause
  have installedAlts :
      pending.installed.toConf.alts =
        resolutionAlt argsv args res rest binding qterm barrier counter
            clause ::
          (altTail ++ Alt.barrier :: pending.outer.alts) := by
    simp [DemandDrivenCallStep.PendingCall.installed,
      DemandDrivenStep.OpenConf.toConf, DemandDrivenStep.Control.toConf,
      altsEq]
  have pulled :
      PLeaTTa.pull pending.installed.toConf =
        { pending.installed.toConf with
          cur :=
            some
              (PLeaTTa.Goal.eq (.expr (args ++ [res]))
                  (.expr (copied.params ++ [copied.result])) ::
                copied.body ++ rest,
                binding)
          alts := altTail ++ Alt.barrier :: pending.outer.alts } := by
    simpa [resolutionAlt, copied] using
      (PLeaTTa.pull_of_alts_branch pending.installed.toConf
        (PLeaTTa.Goal.eq (.expr (args ++ [res]))
            (.expr (copied.params ++ [copied.result])) ::
          copied.body ++ rest)
        binding (altTail ++ Alt.barrier :: pending.outer.alts)
        installedAlts)
  have pulledToConf :
      pending.pulled.toConf =
        { pending.installed.toConf with
          cur :=
            some
              (PLeaTTa.Goal.eq (.expr (args ++ [res]))
                  (.expr (copied.params ++ [copied.result])) ::
                copied.body ++ rest,
                binding)
          alts := altTail ++ Alt.barrier :: pending.outer.alts } := by
    simpa [DemandDrivenCallStep.PendingCall.pulled] using pulled
  exact
    ⟨branch, clause, branchTail, clauseTail, altTail, copied,
      branchesEq, clausesEq, rfl, pulledToConf, agreement, kept, tail⟩

/-- Pulling an exhausted ready bank skips exactly the freshly installed call
barrier and resumes the outer executable alternatives.  The final persistent
state is retained, while the exhausted local call contributes no branch. -/
theorem CursorAlternativeReady.pending_pulled_exhausted
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst} {qterm : Atom}
    {barrier counter finalCounter : Nat}
    {pending : DemandDrivenCallStep.PendingCall}
    (ready :
      CursorAlternativeReady argsv args res rest binding qterm barrier
        [] [] counter pending.branches finalCounter) :
    pending.pulled.toConf =
      PLeaTTa.pull
        { pending.outer.toConf pending.persistent with cur := none } := by
  generalize bankEq : pending.branches = bank at ready
  have bankEmpty : bank = [] := by
    cases ready with
    | exhausted counter =>
        rfl
  have pendingEmpty : pending.branches = [] :=
    bankEq.trans bankEmpty
  let outer := pending.outer.toConf pending.persistent
  have installedEq :
      pending.installed.toConf =
        { outer with
          cur := none
          alts := Alt.barrier :: pending.outer.alts
          barriers := PLeaTTa.pushBarrierCache pending.outer.barriers } := by
    apply PLeaTTa.Conf.ext <;>
      simp [DemandDrivenCallStep.PendingCall.installed,
        DemandDrivenStep.OpenConf.toConf, DemandDrivenStep.Control.toConf,
        pendingEmpty, outer]
  have pulledEq :
      pending.pulled.toConf = PLeaTTa.pull pending.installed.toConf := by
    simp [DemandDrivenCallStep.PendingCall.pulled]
  rw [pulledEq, installedEq]
  change
    PLeaTTa.pull
        { outer with
          cur := none
          alts := Alt.barrier :: outer.alts
          barriers := PLeaTTa.pushBarrierCache outer.barriers } =
      PLeaTTa.pull { outer with cur := none, alts := outer.alts }
  exact PLeaTTa.pull_barrier outer outer.alts

end PLeaTTa.PrologCursorAlternativeBridge
