-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologSupportedCallFrontierBridge
Purpose: Compose the compiler-supported retained cursor frontier with the
  actual executable callPull state.
Trusted boundary: none
Main exports: SupportedRetainedCallFrontier,
  SupportedCallEntryPrefilterRelates.callPull_supported_retained_frontier
-/
import PLeaTTa.Proofs.PrologSupportedCursorAlternativeBridge
import PLeaTTa.Proofs.ResolutionCounter

namespace PLeaTTa.PrologSupportedCallFrontierBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open PeTTaSpec.PrologCore.GoalSemantics
open PrologActivationMacro
open PrologCallPayloadBridge
open PrologPrefilterBridge
open PrologPrefilterCallBridge
open PrologPrefilterScanBridge
open PrologSupportedCursorAlternativeBridge

/-!
The supported cursor/alternative bridge stops at a ready suffix.  Activation
needs one stronger, shared frontier: the exact supported source occurrence,
the exact executable copied clause installed by `callPull`, the finishing
cursor invariant, and the occupied-variable high-water derived from the
reachable sealed configuration.

Nothing in this module chooses or assumes a head MGU.  It packages the state
immediately before the independent `LocalPull.matched` and executable
`Step.eq_ok`/`Step.eq_fail` split.
-/

/-- Exactly counted rejected pulls preserve the complete prepared-cursor
reservation and logical-update invariant. -/
theorem RejectedPullsN.preserves_wellFormed
    {count : Nat} {before after : PreparedCursor}
    (pulls : RejectedPullsN count before after)
    (wellFormed : before.WellFormed) :
    after.WellFormed := by
  induction pulls with
  | zero cursor =>
      exact wellFormed
  | succ count cursor branch branches finish remaining clash tail
      inductionHypothesis =>
      exact inductionHypothesis
        (cursor.advance_wellFormed wellFormed remaining)

/-- A ready suffix with a nonempty executable bank cannot be exhausted on
the source side. -/
theorem SupportedCursorAlternativeReady.branches_nonempty_of_alts_nonempty
    {callGeneration : Generation} {predicate : String}
    {referenceArguments : List Term} {referenceBindings : Substitution}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst} {qterm : Atom}
    {barrier : Nat} {branches : List ClauseBranch}
    {clauses : List PLeaTTa.Clause} {counter finalCounter : Nat}
    {alts : List Alt}
    (ready :
      SupportedCursorAlternativeReady callGeneration predicate
        referenceArguments referenceBindings argsv args res rest binding
        qterm barrier branches clauses counter alts finalCounter)
    (nonempty : alts ≠ []) :
    branches ≠ [] := by
  cases ready <;> simp_all

/-- Strong retained-bank eliminator.  It mirrors the audited weak pull
equation while retaining the exact compiler-supported occurrence and strong
tail spine. -/
theorem SupportedCursorAlternativeReady.pending_pulled_retained
    {callGeneration : Generation} {predicate : String}
    {referenceArguments : List Term} {referenceBindings : Substitution}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst} {qterm : Atom}
    {barrier : Nat} {branches : List ClauseBranch}
    {clauses : List PLeaTTa.Clause} {counter finalCounter : Nat}
    {pending : DemandDrivenCallStep.PendingCall}
    (ready :
      SupportedCursorAlternativeReady callGeneration predicate
        referenceArguments referenceBindings argsv args res rest binding
        qterm barrier branches clauses counter pending.branches finalCounter)
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
      SupportedPreparedCandidateAgrees callGeneration predicate
        referenceArguments referenceBindings branch clause ∧
      NormalizedHeadAgrees branch argsv
        (PLeaTTa.subst binding res) clause ∧
      resolutionClauseRetained argsv (PLeaTTa.subst binding res) clause =
        true ∧
      SupportedCursorAlternativeSpine callGeneration predicate
        referenceArguments referenceBindings argsv args res rest binding
        qterm barrier branchTail clauseTail (counter + 1) altTail
        finalCounter := by
  obtain
    ⟨branch, clause, branchTail, clauseTail, altTail,
      branchesEq, clausesEq, altsEq, supported, agreement, kept, tail⟩ :=
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
      branchesEq, clausesEq, rfl, pulledToConf, supported, agreement, kept,
      tail⟩

/-- The exact shared state immediately before head unification.

All activation-side premises which follow solely from call entry and
reachability are fields here: the finishing cursor is well formed; the query
alpha relation and compiler support are preserved at that cursor; the
retained clause has the executable input arity; `callPull` installed the
precise copied head/body; and the executable seed dominates every live caller
name, including the query term. -/
structure SupportedRetainedCallFrontier
    (queryAlpha : List (LogicVar × String))
    (opened : OpenedCall) (before : DemandDrivenStep.OpenConf)
    (pending : DemandDrivenCallStep.PendingCall)
    (finish : PreparedCursor)
    (branch : ClauseBranch) (clause : PLeaTTa.Clause)
    (branchTail : List ClauseBranch) (clauseTail : List PLeaTTa.Clause)
    (altTail : List Alt) (copied : PLeaTTa.Clause)
    (argsv args : List Atom) (res : Atom)
    (rest : List PLeaTTa.Goal) (binding : Subst)
    (qterm : Atom) (barrier startCounter : Nat) : Prop where
  finishRemaining : finish.remaining = branch :: branchTail
  finishWellFormed : finish.WellFormed
  finishContext :
    CursorCallContext finish opened.cursor.callGeneration
      opened.cursor.predicate opened.cursor.arguments opened.cursor.bindings
  query :
    NormalizedCallAgrees queryAlpha finish argsv
      (PLeaTTa.subst binding res)
  supported :
    SupportedPreparedCandidateAgrees finish.callGeneration finish.predicate
      finish.arguments finish.bindings branch clause
  normalized :
    NormalizedHeadAgrees branch argsv (PLeaTTa.subst binding res) clause
  arity : clause.params.length = args.length
  retained :
    resolutionClauseRetained argsv (PLeaTTa.subst binding res) clause = true
  tail :
    SupportedCursorAlternativeSpine opened.cursor.callGeneration
      opened.cursor.predicate opened.cursor.arguments opened.cursor.bindings
      argsv args res rest binding qterm barrier branchTail clauseTail
      (startCounter + 1) altTail pending.persistent.counter
  substitutedArgs : argsv = args.map (PLeaTTa.subst binding)
  queryTerm : qterm = before.toConf.qterm
  startCounterExact : startCounter = before.toConf.counter
  copiedExact :
    copied =
      PLeaTTa.freshenResolutionClause argsv args res rest binding qterm
        startCounter barrier clause
  pulledExact :
    pending.pulled.toConf =
      { pending.installed.toConf with
        cur :=
          some
            (PLeaTTa.Goal.eq (.expr (args ++ [res]))
                (.expr (copied.params ++ [copied.result])) ::
              copied.body ++ rest,
              binding)
        alts := altTail ++ Alt.barrier :: pending.outer.alts }
  highWater :
    resolutionSeedHighWaterNames
        (resolutionOccupiedVars argsv res rest binding qterm) ≤
      startCounter

/-- A supported call-entry state with a nonempty retained bank reaches one
exact shared activation frontier.

The rejected source-only prefix is paid one silent transition per occurrence;
the executable `callPull` is a real fine step; and every support, freshness,
query, arity, and configuration fact in the final package is derived from
the concrete opener plus the reachable sealed counter invariant. -/
theorem
    SupportedCallEntryPrefilterRelates.callPull_supported_retained_frontier
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {queryAlpha : List (LogicVar × String)}
    {opened : OpenedCall} {before : DemandDrivenStep.OpenConf}
    {pending : DemandDrivenCallStep.PendingCall}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst}
    {qterm : Atom} {barrier startCounter : Nat}
    (agreement :
      SupportedCallEntryPrefilterRelates queryAlpha opened before pending
        argsv args res rest binding qterm barrier startCounter)
    (below : ConfBelowResolutionCounter before.toConf)
    (nonempty : pending.branches ≠ []) :
    ∃ count skippedBranches skippedClauses finish
        branch clause branchTail clauseTail altTail copied,
      opened.cursor.remaining =
        skippedBranches ++ (branch :: branchTail) ∧
      (pending.persistent.world.resolutionCandidates
          opened.cursor.predicate args.length) =
        skippedClauses ++ (clause :: clauseTail) ∧
      skippedBranches.length = count ∧
      skippedClauses.length = count ∧
      StepsN count
        (.running opened.session (.clauses opened.scope opened.cursor)) []
        (.running opened.session (.clauses opened.scope finish)) ∧
      DemandDrivenCallStep.Step prog gt (.callPending pending)
        (.ready pending.pulled) ∧
      SupportedRetainedCallFrontier queryAlpha opened before pending finish
        branch clause branchTail clauseTail altTail copied argsv args res rest
        binding qterm barrier startCounter := by
  have spine :=
    PLeaTTa.PrologSupportedCursorAlternativeBridge.SupportedPreparedPrefilterBankRelates.supportedCursorAlternativeSpine
      agreement.prefilter
  obtain
    ⟨count, skippedBranches, skippedClauses, finish,
      readyBranches, readyClauses, branchesEq, clausesEq,
      branchCount, clauseCount, pulls, finishRemaining,
      finishContext, ready⟩ :=
    spine.decomposeRejectedPrefix opened.cursor (.refl opened.cursor) rfl
  have readyNonempty : readyBranches ≠ [] :=
    PLeaTTa.PrologSupportedCallFrontierBridge.SupportedCursorAlternativeReady.branches_nonempty_of_alts_nonempty
      ready nonempty
  obtain
    ⟨branch, clause, branchTail, clauseTail, altTail, copied,
      readyBranchesEq, readyClausesEq, copiedExact, pulledExact,
      supported, normalized, retained, tail⟩ :=
    PLeaTTa.PrologSupportedCallFrontierBridge.SupportedCursorAlternativeReady.pending_pulled_retained
      ready readyNonempty
  have finishWellFormed :
      finish.WellFormed :=
    PLeaTTa.PrologSupportedCallFrontierBridge.RejectedPullsN.preserves_wellFormed
      pulls agreement.cursorWellFormed
  have query :
      NormalizedCallAgrees queryAlpha finish argsv
        (PLeaTTa.subst binding res) :=
    finishContext.normalizedCallAgrees (.refl opened.cursor) agreement.query
  have supportedAtFinish :
      SupportedPreparedCandidateAgrees finish.callGeneration finish.predicate
        finish.arguments finish.bindings branch clause :=
    finishContext.supportedPreparedCandidate supported
  have arity : clause.params.length = args.length := by
    calc
      clause.params.length = argsv.length := normalized.arity
      _ = (args.map (PLeaTTa.subst binding)).length :=
        congrArg List.length agreement.entry.substitutedArgs
      _ = args.length := List.length_map ..
  have highWater :
      resolutionSeedHighWaterNames
          (resolutionOccupiedVars argsv res rest binding qterm) ≤
        startCounter := by
    have occupied :=
      below.resolutionOccupied_of_call opened.cursor.predicate args res rest
        binding agreement.entry.callHead
    simpa [agreement.entry.substitutedArgs, agreement.entry.queryTerm,
      agreement.entry.startCounterExact] using occupied
  refine
    ⟨count, skippedBranches, skippedClauses, finish,
      branch, clause, branchTail, clauseTail, altTail, copied, ?_, ?_,
      branchCount, clauseCount, pulls.stepsN opened.scope opened.session,
      .callPull pending, ?_⟩
  · calc
      opened.cursor.remaining =
          skippedBranches ++ readyBranches := branchesEq
      _ = skippedBranches ++ (branch :: branchTail) := by
        rw [readyBranchesEq]
  · calc
      (pending.persistent.world.resolutionCandidates
          opened.cursor.predicate args.length) =
          skippedClauses ++ readyClauses := clausesEq
      _ = skippedClauses ++ (clause :: clauseTail) := by
        rw [readyClausesEq]
  · exact
      ⟨by simpa [readyBranchesEq] using finishRemaining,
        finishWellFormed, finishContext, query, supportedAtFinish,
        normalized, arity, retained, tail,
        agreement.entry.substitutedArgs, agreement.entry.queryTerm,
        agreement.entry.startCounterExact, copiedExact, pulledExact,
        highWater⟩

end PLeaTTa.PrologSupportedCallFrontierBridge
