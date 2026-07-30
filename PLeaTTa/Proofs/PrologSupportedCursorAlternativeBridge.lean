-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologSupportedCursorAlternativeBridge
Purpose: Preserve compiler-supported prepared candidates through the exact
  source/executable cursor-alternative spine and rejected-prefix expansion.
Trusted boundary: none
Main exports: CursorCallContext, SupportedCursorAlternativeSpine,
  SupportedCursorAlternativeReady,
  SupportedCallEntryPrefilterRelates.callPull_supported_ready_correspondence
-/
import PLeaTTa.Proofs.PrologCursorAlternativeBridge

namespace PLeaTTa.PrologSupportedCursorAlternativeBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open PeTTaSpec.PrologCore.GoalSemantics
open PrologActivationMacro
open PrologCallPayloadBridge
open PrologCursorAlternativeBridge
open PrologPrefilterBridge
open PrologPrefilterCallBridge
open PrologPrefilterScanBridge

/-!
The earlier cursor/alternative spine intentionally retained only normalized
head agreement: that is sufficient to justify conservative rejection, but
not to execute a retained clause body.  Body activation also needs the exact
`SupportedPreparedCandidateAgrees` occurrence supplied by the compiler
support proof.

This module is additive.  Its strong spine projects to the already-audited
weak spine, while carrying the supported occurrence at every source/executable
pair.  Rejected source-only prefixes advance the cursor without dropping that
evidence for the first retained occurrence.
-/

/-- The call identity fields which remain fixed while a prepared cursor
advances through its frozen occurrence list. -/
structure CursorCallContext
    (cursor : PreparedCursor)
    (callGeneration : Generation) (predicate : String)
    (arguments : List Term) (bindings : Substitution) : Prop where
  generation : cursor.callGeneration = callGeneration
  predicate_eq : cursor.predicate = predicate
  arguments_eq : cursor.arguments = arguments
  bindings_eq : cursor.bindings = bindings

/-- A cursor agrees with its own call context. -/
theorem CursorCallContext.refl (cursor : PreparedCursor) :
    CursorCallContext cursor cursor.callGeneration cursor.predicate
      cursor.arguments cursor.bindings :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Pulling one frozen occurrence changes only the remaining branch list and
fresh seed; the call identity and carried query stay fixed. -/
theorem CursorCallContext.advance
    {cursor : PreparedCursor}
    {callGeneration : Generation} {predicate : String}
    {arguments : List Term} {bindings : Substitution}
    (context :
      CursorCallContext cursor callGeneration predicate arguments bindings)
    (entered : ClauseBranch) (remaining : List ClauseBranch) :
    CursorCallContext (cursor.advance entered remaining)
      callGeneration predicate arguments bindings := by
  exact
    ⟨context.generation, context.predicate_eq,
      context.arguments_eq, context.bindings_eq⟩

/-- Compiler support indexed by the frozen call identity can be transported
to any cursor reached by conservative prefix pulls.  No candidate decision
or source/executable pairing is recomputed. -/
theorem CursorCallContext.supportedPreparedCandidate
    {cursor : PreparedCursor}
    {callGeneration : Generation} {predicate : String}
    {arguments : List Term} {bindings : Substitution}
    (context :
      CursorCallContext cursor callGeneration predicate arguments bindings)
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    (supported :
      SupportedPreparedCandidateAgrees callGeneration predicate arguments
        bindings branch clause) :
    SupportedPreparedCandidateAgrees cursor.callGeneration cursor.predicate
      cursor.arguments cursor.bindings branch clause := by
  rw [context.generation, context.predicate_eq, context.arguments_eq,
    context.bindings_eq]
  exact supported

/-- The normalized caller payload depends only on the call identity fields,
so it transports unchanged through every conservative cursor advance. -/
theorem CursorCallContext.normalizedCallAgrees
    {queryAlpha : List (LogicVar × String)}
    {source target : PreparedCursor}
    {callGeneration : Generation} {predicate : String}
    {arguments : List Term} {bindings : Substitution}
    (targetContext :
      CursorCallContext target callGeneration predicate arguments bindings)
    (sourceContext :
      CursorCallContext source callGeneration predicate arguments bindings)
    {argsv : List Atom} {resv : Atom}
    (query : NormalizedCallAgrees queryAlpha source argsv resv) :
    NormalizedCallAgrees queryAlpha target argsv resv := by
  constructor
  simpa [sourceContext.arguments_eq, sourceContext.bindings_eq,
    targetContext.arguments_eq, targetContext.bindings_eq] using
    query.arguments

/-- Occurrence-preserving cursor/alternative ownership with the exact
compiler-supported prepared candidate retained at every position. -/
inductive SupportedCursorAlternativeSpine
    (callGeneration : Generation) (predicate : String)
    (referenceArguments : List Term) (referenceBindings : Substitution)
    (argsv args : List Atom) (res : Atom)
    (rest : List PLeaTTa.Goal) (binding : Subst) (qterm : Atom)
    (barrier : Nat) :
    List ClauseBranch → List PLeaTTa.Clause →
      Nat → List Alt → Nat → Prop where
  | nil (counter : Nat) :
      SupportedCursorAlternativeSpine callGeneration predicate
        referenceArguments referenceBindings argsv args res rest binding
        qterm barrier [] [] counter [] counter
  | skipped (branch : ClauseBranch) (clause : PLeaTTa.Clause)
      (branches : List ClauseBranch) (clauses : List PLeaTTa.Clause)
      (counter finalCounter : Nat) (alts : List Alt)
      (supported :
        SupportedPreparedCandidateAgrees callGeneration predicate
          referenceArguments referenceBindings branch clause)
      (agreement :
        NormalizedHeadAgrees branch argsv (PLeaTTa.subst binding res) clause)
      (rejected :
        resolutionClauseRetained argsv (PLeaTTa.subst binding res) clause =
          false)
      (clash : ¬ ∃ result, HeadResolution branch result)
      (tail :
        SupportedCursorAlternativeSpine callGeneration predicate
          referenceArguments referenceBindings argsv args res rest binding
          qterm barrier branches clauses counter alts finalCounter) :
      SupportedCursorAlternativeSpine callGeneration predicate
        referenceArguments referenceBindings argsv args res rest binding
        qterm barrier (branch :: branches) (clause :: clauses)
        counter alts finalCounter
  | retained (branch : ClauseBranch) (clause : PLeaTTa.Clause)
      (branches : List ClauseBranch) (clauses : List PLeaTTa.Clause)
      (counter finalCounter : Nat) (alts : List Alt)
      (supported :
        SupportedPreparedCandidateAgrees callGeneration predicate
          referenceArguments referenceBindings branch clause)
      (agreement :
        NormalizedHeadAgrees branch argsv (PLeaTTa.subst binding res) clause)
      (kept :
        resolutionClauseRetained argsv (PLeaTTa.subst binding res) clause =
          true)
      (tail :
        SupportedCursorAlternativeSpine callGeneration predicate
          referenceArguments referenceBindings argsv args res rest binding
          qterm barrier branches clauses (counter + 1) alts finalCounter) :
      SupportedCursorAlternativeSpine callGeneration predicate
        referenceArguments referenceBindings argsv args res rest binding
        qterm barrier (branch :: branches) (clause :: clauses) counter
        (resolutionAlt argsv args res rest binding qterm barrier counter
          clause :: alts)
        finalCounter

/-- Erasing compiler support recovers the previously audited ownership spine
with the same occurrence order, decisions, alternatives, and counters. -/
theorem SupportedCursorAlternativeSpine.weak
    {callGeneration : Generation} {predicate : String}
    {referenceArguments : List Term} {referenceBindings : Substitution}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst} {qterm : Atom}
    {barrier : Nat} {branches : List ClauseBranch}
    {clauses : List PLeaTTa.Clause} {counter finalCounter : Nat}
    {alts : List Alt}
    (spine :
      SupportedCursorAlternativeSpine callGeneration predicate
        referenceArguments referenceBindings argsv args res rest binding
        qterm barrier branches clauses counter alts finalCounter) :
    CursorAlternativeSpine argsv args res rest binding qterm barrier
      branches clauses counter alts finalCounter := by
  induction spine with
  | nil counter =>
      exact .nil counter
  | skipped branch clause branches clauses counter finalCounter alts
      supported agreement rejected clash tail inductionHypothesis =>
      exact .skipped branch clause branches clauses counter finalCounter alts
        agreement rejected clash inductionHypothesis
  | retained branch clause branches clauses counter finalCounter alts
      supported agreement kept tail inductionHypothesis =>
      exact .retained branch clause branches clauses counter finalCounter alts
        agreement kept inductionHypothesis

/-- A weak ownership spine and the exact supported candidate `Forall₂` spine
construct the strong relation without re-running the executable scan. -/
theorem supportedCursorAlternativeSpine_of_weak
    {callGeneration : Generation} {predicate : String}
    {referenceArguments : List Term} {referenceBindings : Substitution}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst} {qterm : Atom}
    {barrier : Nat} {branches : List ClauseBranch}
    {clauses : List PLeaTTa.Clause} {counter finalCounter : Nat}
    {alts : List Alt}
    (spine :
      CursorAlternativeSpine argsv args res rest binding qterm barrier
        branches clauses counter alts finalCounter)
    (supported :
      List.Forall₂
        (SupportedPreparedCandidateAgrees callGeneration predicate
          referenceArguments referenceBindings)
        branches clauses) :
    SupportedCursorAlternativeSpine callGeneration predicate
      referenceArguments referenceBindings argsv args res rest binding qterm
      barrier branches clauses counter alts finalCounter := by
  induction spine with
  | nil counter =>
      cases supported
      exact .nil counter
  | skipped branch clause branches clauses counter finalCounter alts
      agreement rejected clash tail inductionHypothesis =>
      cases supported with
      | cons head rest =>
          exact .skipped branch clause branches clauses counter finalCounter
            alts head agreement rejected clash (inductionHypothesis rest)
  | retained branch clause branches clauses counter finalCounter alts
      agreement kept tail inductionHypothesis =>
      cases supported with
      | cons head rest =>
          exact .retained branch clause branches clauses counter finalCounter
            alts head agreement kept (inductionHypothesis rest)

/-- The strengthened prepared bank contains the supported synchronized
ownership spine directly. -/
theorem
    SupportedPreparedPrefilterBankRelates.supportedCursorAlternativeSpine
    {cursor : PreparedCursor}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst} {qterm : Atom}
    {barrier : Nat} {candidates : List PLeaTTa.Clause}
    {counter finalCounter : Nat} {alts : List Alt}
    (agreement :
      SupportedPreparedPrefilterBankRelates cursor argsv args res rest
        binding qterm barrier candidates counter alts finalCounter) :
    SupportedCursorAlternativeSpine cursor.callGeneration cursor.predicate
      cursor.arguments cursor.bindings argsv args res rest binding qterm
      barrier cursor.remaining candidates counter alts finalCounter :=
  supportedCursorAlternativeSpine_of_weak
    (PLeaTTa.PrologCursorAlternativeBridge.PreparedPrefilterBankRelates.cursorAlternativeSpine
      agreement.prefilter)
    agreement.supportedCandidates

/-- Ready suffix with the supported retained occurrence still attached. -/
inductive SupportedCursorAlternativeReady
    (callGeneration : Generation) (predicate : String)
    (referenceArguments : List Term) (referenceBindings : Substitution)
    (argsv args : List Atom) (res : Atom)
    (rest : List PLeaTTa.Goal) (binding : Subst) (qterm : Atom)
    (barrier : Nat) :
    List ClauseBranch → List PLeaTTa.Clause →
      Nat → List Alt → Nat → Prop where
  | exhausted (counter : Nat) :
      SupportedCursorAlternativeReady callGeneration predicate
        referenceArguments referenceBindings argsv args res rest binding
        qterm barrier [] [] counter [] counter
  | retained (branch : ClauseBranch) (clause : PLeaTTa.Clause)
      (branches : List ClauseBranch) (clauses : List PLeaTTa.Clause)
      (counter finalCounter : Nat) (alts : List Alt)
      (supported :
        SupportedPreparedCandidateAgrees callGeneration predicate
          referenceArguments referenceBindings branch clause)
      (agreement :
        NormalizedHeadAgrees branch argsv (PLeaTTa.subst binding res) clause)
      (kept :
        resolutionClauseRetained argsv (PLeaTTa.subst binding res) clause =
          true)
      (tail :
        SupportedCursorAlternativeSpine callGeneration predicate
          referenceArguments referenceBindings argsv args res rest binding
          qterm barrier branches clauses (counter + 1) alts finalCounter) :
      SupportedCursorAlternativeReady callGeneration predicate
        referenceArguments referenceBindings argsv args res rest binding
        qterm barrier (branch :: branches) (clause :: clauses) counter
        (resolutionAlt argsv args res rest binding qterm barrier counter
          clause :: alts)
        finalCounter

/-- Erasing support from a ready suffix recovers the weak ready relation. -/
theorem SupportedCursorAlternativeReady.weak
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
        qterm barrier branches clauses counter alts finalCounter) :
    CursorAlternativeReady argsv args res rest binding qterm barrier
      branches clauses counter alts finalCounter := by
  cases ready with
  | exhausted counter =>
      exact .exhausted counter
  | retained branch clause branches clauses counter finalCounter alts
      supported agreement kept tail =>
      exact .retained branch clause branches clauses counter finalCounter alts
        agreement kept tail.weak

/-- A nonempty supported ready suffix exposes the exact retained
source/executable occurrence, its current seeded alternative, and the
supported tail.  This is the strong handoff to clause-body activation; unlike
the weak projection, it cannot substitute an arbitrary agreeing branch. -/
theorem SupportedCursorAlternativeReady.retained_shape
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
    (nonempty : branches ≠ []) :
    ∃ branch clause branchTail clauseTail altTail,
      branches = branch :: branchTail ∧
      clauses = clause :: clauseTail ∧
      alts =
        resolutionAlt argsv args res rest binding qterm barrier counter
          clause :: altTail ∧
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
  cases ready with
  | exhausted counter =>
      exact False.elim (nonempty rfl)
  | retained branch clause branches clauses counter finalCounter alts
      supported agreement kept tail =>
      exact
        ⟨branch, clause, branches, clauses, alts, rfl, rfl, rfl,
          supported, agreement, kept, tail⟩

/-- A supported ownership spine factors through an exactly counted rejected
prefix while preserving both the call context and the first retained
compiler-supported occurrence. -/
theorem SupportedCursorAlternativeSpine.decomposeRejectedPrefix
    {callGeneration : Generation} {predicate : String}
    {referenceArguments : List Term} {referenceBindings : Substitution}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst} {qterm : Atom}
    {barrier : Nat} {branches : List ClauseBranch}
    {clauses : List PLeaTTa.Clause} {counter finalCounter : Nat}
    {alts : List Alt}
    (spine :
      SupportedCursorAlternativeSpine callGeneration predicate
        referenceArguments referenceBindings argsv args res rest binding
        qterm barrier branches clauses counter alts finalCounter)
    (cursor : PreparedCursor)
    (context :
      CursorCallContext cursor callGeneration predicate referenceArguments
        referenceBindings)
    (remaining : cursor.remaining = branches) :
    ∃ count skippedBranches skippedClauses finish
        readyBranches readyClauses,
      branches = skippedBranches ++ readyBranches ∧
      clauses = skippedClauses ++ readyClauses ∧
      skippedBranches.length = count ∧
      skippedClauses.length = count ∧
      RejectedPullsN count cursor finish ∧
      finish.remaining = readyBranches ∧
      CursorCallContext finish callGeneration predicate referenceArguments
        referenceBindings ∧
      SupportedCursorAlternativeReady callGeneration predicate
        referenceArguments referenceBindings argsv args res rest binding
        qterm barrier readyBranches readyClauses counter alts finalCounter := by
  induction spine generalizing cursor with
  | nil counter =>
      exact
        ⟨0, [], [], cursor, [], [], rfl, rfl, rfl, rfl, .zero cursor,
          remaining, context, .exhausted counter⟩
  | skipped branch clause branches clauses counter finalCounter alts
      supported agreement rejected clash tail inductionHypothesis =>
      let next := cursor.advance branch branches
      have nextRemaining : next.remaining = branches := by
        simp [next, PreparedCursor.advance]
      have nextContext :
          CursorCallContext next callGeneration predicate
            referenceArguments referenceBindings :=
        context.advance branch branches
      obtain
        ⟨count, skippedBranches, skippedClauses, finish,
          readyBranches, readyClauses, branchesEq, clausesEq,
          branchCount, clauseCount, pulls, finishRemaining,
          finishContext, ready⟩ :=
        inductionHypothesis next nextContext nextRemaining
      refine
        ⟨count + 1, branch :: skippedBranches, clause :: skippedClauses,
          finish, readyBranches, readyClauses, ?_, ?_, ?_, ?_, ?_,
          finishRemaining, finishContext, ready⟩
      · simp [branchesEq]
      · simp [clausesEq]
      · simp [branchCount]
      · simp [clauseCount]
      · exact
          .succ count cursor branch branches finish remaining clash pulls
  | retained branch clause branches clauses counter finalCounter alts
      supported agreement kept tail inductionHypothesis =>
      exact
        ⟨0, [], [], cursor, branch :: branches, clause :: clauses,
          rfl, rfl, rfl, rfl, .zero cursor, remaining, context,
          .retained branch clause branches clauses counter finalCounter alts
            supported agreement kept tail⟩

/-- Execution form of the strong factorization: source-only rejected
occurrences are paid as exact silent transitions and the supported retained
candidate survives at the shared ready frontier. -/
theorem SupportedCursorAlternativeSpine.rejectedPrefixSteps
    {callGeneration : Generation} {predicate : String}
    {referenceArguments : List Term} {referenceBindings : Substitution}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst} {qterm : Atom}
    {barrier : Nat} {branches : List ClauseBranch}
    {clauses : List PLeaTTa.Clause} {counter finalCounter : Nat}
    {alts : List Alt}
    (spine :
      SupportedCursorAlternativeSpine callGeneration predicate
        referenceArguments referenceBindings argsv args res rest binding
        qterm barrier branches clauses counter alts finalCounter)
    (cursor : PreparedCursor)
    (context :
      CursorCallContext cursor callGeneration predicate referenceArguments
        referenceBindings)
    (remaining : cursor.remaining = branches)
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
      CursorCallContext finish callGeneration predicate referenceArguments
        referenceBindings ∧
      SupportedCursorAlternativeReady callGeneration predicate
        referenceArguments referenceBindings argsv args res rest binding
        qterm barrier readyBranches readyClauses counter alts finalCounter := by
  obtain
    ⟨count, skippedBranches, skippedClauses, finish,
      readyBranches, readyClauses, branchesEq, clausesEq,
      branchCount, clauseCount, pulls, finishRemaining,
      finishContext, ready⟩ :=
    spine.decomposeRejectedPrefix cursor context remaining
  exact
    ⟨count, skippedBranches, skippedClauses, finish,
      readyBranches, readyClauses, branchesEq, clausesEq,
      branchCount, clauseCount, pulls.stepsN scope session,
      finishRemaining, finishContext, ready⟩

/-- The concrete supported post-entry relation advances to one shared ready
frontier without dropping the compiler support needed by the retained
clause-body activation theorem. -/
theorem
    SupportedCallEntryPrefilterRelates.callPull_supported_ready_correspondence
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {queryAlpha : List (LogicVar × String)}
    {opened : OpenedCall} {before : DemandDrivenStep.OpenConf}
    {pending : DemandDrivenCallStep.PendingCall}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst}
    {qterm : Atom} {barrier startCounter : Nat}
    (agreement :
      SupportedCallEntryPrefilterRelates queryAlpha opened before pending
        argsv args res rest binding qterm barrier startCounter) :
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
      CursorCallContext finish opened.cursor.callGeneration
        opened.cursor.predicate opened.cursor.arguments
        opened.cursor.bindings ∧
      SupportedCursorAlternativeReady opened.cursor.callGeneration
        opened.cursor.predicate opened.cursor.arguments opened.cursor.bindings
        argsv args res rest binding qterm barrier readyBranches readyClauses
        startCounter pending.branches pending.persistent.counter ∧
      DemandDrivenCallStep.Step prog gt (.callPending pending)
        (.ready pending.pulled) := by
  have spine :=
    PLeaTTa.PrologSupportedCursorAlternativeBridge.SupportedPreparedPrefilterBankRelates.supportedCursorAlternativeSpine
      agreement.prefilter
  obtain
    ⟨count, skippedBranches, skippedClauses, finish,
      readyBranches, readyClauses, branchesEq, clausesEq,
      branchCount, clauseCount, steps, finishRemaining,
      finishContext, ready⟩ :=
    spine.rejectedPrefixSteps opened.cursor (.refl opened.cursor) rfl
      opened.scope opened.session
  exact
    ⟨count, skippedBranches, skippedClauses, finish,
      readyBranches, readyClauses, branchesEq, clausesEq,
      branchCount, clauseCount, steps, finishRemaining,
      finishContext, ready, .callPull pending⟩

end PLeaTTa.PrologSupportedCursorAlternativeBridge
