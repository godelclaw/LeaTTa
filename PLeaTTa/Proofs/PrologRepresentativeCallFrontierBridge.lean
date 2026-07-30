-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologRepresentativeCallFrontierBridge
Purpose: Carry representation-independent recursive-call agreement through
  the exact ranked candidate scan to one retained local-clause frontier.
Trusted boundary: none
Main exports:
  RepresentativeSupportedCallEntryRelates,
  ResolutionScan.decomposeRepresentativeRejectedPrefix,
  RepresentativeRetainedCallFrontier,
  RepresentativeSupportedCallEntryRelates.callPull_retained_frontier
-/
import PLeaTTa.Proofs.PrologRepresentativeCallPrefilterBridge
import PLeaTTa.Proofs.PrologSupportedCallFrontierBridge

namespace PLeaTTa.PrologRepresentativeCallFrontierBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open PeTTaSpec.PrologCore.GoalSemantics
open PrologActivationMacro
open PrologCallEntryBridge
open PrologCallPayloadBridge
open PrologCallStepBridge
open PrologPrefilterCallBridge
open PrologPrefilterScanBridge
open PrologRecursiveCallPayloadBridge
open PrologRepresentativeCallPrefilterBridge
open PrologOrdinaryStepBridge
open PrologStateBridge
open PrologSupportedCursorAlternativeBridge
open PrologSupportedCallFrontierBridge

/-!
The older retained-frontier theorem stores `NormalizedCallAgrees` and
`NormalizedHeadAgrees`.  Those syntactic relations deliberately fail when
the independent and executable ordered MGUs orient a residual variable alias
in opposite directions.

This module does not weaken or rewrite that theorem.  It combines the actual
`ResolutionScan` with the exact supported candidate `Forall₂` spine and uses
one `RepresentativeNormalizedCallAgrees` witness only to certify skipped
decisions.  The retained suffix carries the untouched tail scan and untouched
occurrence spine, so order, multiplicity, alternative spelling, and counter
increments remain properties of the executable scan rather than of a second
model.
-/

/-- The semantic normalized-call relation depends only on the immutable call
arguments and binding.  It therefore transports through every source-only
cursor advance without choosing a new representative. -/
theorem CursorCallContext.representativeNormalizedCallAgrees
    {queryAlpha : List (LogicVar × String)}
    {source target : PreparedCursor}
    {callGeneration : Generation} {predicate : String}
    {arguments : List Term} {bindings : Substitution}
    (targetContext :
      CursorCallContext target callGeneration predicate arguments bindings)
    (sourceContext :
      CursorCallContext source callGeneration predicate arguments bindings)
    {argsv : List Atom} {resv : Atom}
    (query :
      RepresentativeNormalizedCallAgrees queryAlpha source argsv resv) :
    RepresentativeNormalizedCallAgrees queryAlpha target argsv resv := by
  rcases query with ⟨representative, variants, agreement⟩
  refine ⟨representative, ?_, ?_⟩
  · simpa [sourceContext.bindings_eq, targetContext.bindings_eq] using
      variants
  · simpa [sourceContext.arguments_eq, targetContext.arguments_eq] using
      agreement

/-- Concrete post-entry state for a semantically represented recursive call.

The executable bank and source occurrence bank are the exact objects already
related by `CallEntryBankRelates`.  Compiler support is carried separately
from the scan so no syntactic normalized-head relation is manufactured. -/
structure RepresentativeSupportedCallEntryRelates
    (queryAlpha : List (LogicVar × String))
    (opened : OpenedCall) (before : DemandDrivenStep.OpenConf)
    (pending : DemandDrivenCallStep.PendingCall)
    (argsv args : List Atom) (res : Atom)
    (rest : List PLeaTTa.Goal) (binding : Subst)
    (qterm : Atom) (barrier startCounter : Nat) : Prop where
  entry :
    CallEntryBankRelates opened before pending argsv args res rest binding
      qterm barrier startCounter
  cursorWellFormed : opened.cursor.WellFormed
  query :
    RepresentativeNormalizedCallAgrees queryAlpha opened.cursor argsv
      (PLeaTTa.subst binding res)
  indexReady : pending.persistent.world.clauseIndexReady = true
  supportedCandidates :
    List.Forall₂
      (SupportedPreparedCandidateAgrees opened.cursor.callGeneration
        opened.cursor.predicate opened.cursor.arguments
        opened.cursor.bindings)
      opened.cursor.remaining
      (pending.persistent.world.resolutionCandidates
        opened.cursor.predicate args.length)

/-- The actual opener and pending package construct the semantic call-entry
relation without re-running the executable scan. -/
theorem openedFor_pendingCallOf_representative_supported_relates
    {session : Session} {state : DemandDrivenStep.OpenConf}
    (database :
      DatabaseRelatesWorld session.resolver.database state.persistent.world)
    (ready : state.persistent.world.clauseIndexReady = true)
    (predicate : String)
    (referenceArguments : List Term)
    (referenceBindings : Substitution)
    (queryAlpha : List (LogicVar × String))
    (args : List Atom) (res : Atom)
    (rest : List PLeaTTa.Goal) (binding : Subst)
    (branches : List Alt) (finalCounter : Nat)
    (arity : referenceArguments.length = args.length + 1)
    (head :
      state.toConf.cur =
        some (PLeaTTa.Goal.call predicate args res :: rest, binding))
    (scanned :
      resolveAlts
        (state.persistent.world.resolutionCandidates predicate args.length)
        (args.map (PLeaTTa.subst binding)) args res rest binding
          state.control.qterm (barrierDepth state.toConf + 1)
          state.toConf.counter =
        (branches, finalCounter))
    (query :
      RepresentativeNormalizedCallAgrees queryAlpha
        (openedFor session predicate referenceArguments
          referenceBindings).cursor
        (args.map (PLeaTTa.subst binding))
        (PLeaTTa.subst binding res))
    (supported :
      SupportedCandidateBank predicate
        (session.resolver.database.visibleClausesAt
          session.resolver.database.generation predicate
          referenceArguments.length)
        (state.persistent.world.resolutionCandidates predicate args.length)) :
    RepresentativeSupportedCallEntryRelates queryAlpha
      (openedFor session predicate referenceArguments referenceBindings)
      state (DemandDrivenCallStep.pendingCallOf state branches finalCounter)
      (args.map (PLeaTTa.subst binding)) args res rest binding
      state.control.qterm (barrierDepth state.toConf + 1)
      state.toConf.counter := by
  have entryAgreement :=
    openedFor_pendingCallOf_relates database ready predicate
      referenceArguments referenceBindings args res rest binding branches
      finalCounter arity head scanned
  have supportedSpine :=
    reserveVisible_supported_candidates
      session.resolver.database.generation predicate referenceArguments
      referenceBindings
      (max session.resolver.nextFresh
        (requestFor predicate referenceArguments
          referenceBindings).generatedCeiling)
      supported
  have preparedSpine :
      List.Forall₂
        (SupportedPreparedCandidateAgrees
          (openedFor session predicate referenceArguments
            referenceBindings).cursor.callGeneration
          (openedFor session predicate referenceArguments
            referenceBindings).cursor.predicate
          (openedFor session predicate referenceArguments
            referenceBindings).cursor.arguments
          (openedFor session predicate referenceArguments
            referenceBindings).cursor.bindings)
        (openedFor session predicate referenceArguments
          referenceBindings).cursor.remaining
        (state.persistent.world.resolutionCandidates predicate args.length) := by
    simpa [openedFor, openLocalCall, requestFor, prepareCall, arity] using
      supportedSpine
  refine ⟨entryAgreement, ?_, query, ?_, ?_⟩
  · simpa [openedFor, openLocalCall] using
      (prepareCall_wellFormed session.resolver
        (requestFor predicate referenceArguments referenceBindings))
  · simpa [DemandDrivenCallStep.pendingCallOf] using ready
  · simpa [DemandDrivenCallStep.pendingCallOf, openedFor, openLocalCall,
      requestFor, prepareCall] using preparedSpine

/-- An actual recursive call at the head of an active task constructs the
semantic call-entry relation.

The cumulative payload supplies the single hidden representative used by
every input and output leaf.  The opened cursor contributes only its
definitionally exact source argument list and current binding; no syntactic
residual orientation is assumed. -/
theorem openedFor_pendingCallOf_recursive_supported_relates
    {alpha support : List (LogicVar × String)} {controlBarrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {session : Session} {state : DemandDrivenStep.OpenConf}
    (database :
      DatabaseRelatesWorld session.resolver.database state.persistent.world)
    (ready : state.persistent.world.clauseIndexReady = true)
    (predicate : String)
    (referencePayload : List Term)
    (referenceRest : List PeTTaSpec.PrologCore.Goal)
    (referenceBindings : Substitution)
    (args : List Atom) (res : Atom)
    (rest : List PLeaTTa.Goal) (binding : Subst)
    (branches : List Alt) (finalCounter : Nat)
    (arity : referencePayload.length = args.length + 1)
    (head :
      state.toConf.cur =
        some (PLeaTTa.Goal.call predicate args res :: rest, binding))
    (scanned :
      resolveAlts
        (state.persistent.world.resolutionCandidates predicate args.length)
        (args.map (PLeaTTa.subst binding)) args res rest binding
          state.control.qterm (barrierDepth state.toConf + 1)
          state.toConf.counter =
        (branches, finalCounter))
    (payload :
      TaskPayloadAgrees alpha support controlBarrier canonical referenceBase
        referenceBindings binding
        (.call predicate referencePayload :: referenceRest)
        (.call predicate args res :: rest))
    (payloadSupported :
      AlphaTermsSupported alpha support referencePayload)
    (candidateSupported :
      SupportedCandidateBank predicate
        (session.resolver.database.visibleClausesAt
          session.resolver.database.generation predicate
          referencePayload.length)
        (state.persistent.world.resolutionCandidates predicate args.length)) :
    RepresentativeSupportedCallEntryRelates alpha
      (openedFor session predicate referencePayload referenceBindings)
      state (DemandDrivenCallStep.pendingCallOf state branches finalCounter)
      (args.map (PLeaTTa.subst binding)) args res rest binding
      state.control.qterm (barrierDepth state.toConf + 1)
      state.toConf.counter := by
  have query :
      RepresentativeNormalizedCallAgrees alpha
        (openedFor session predicate referencePayload
          referenceBindings).cursor
        (args.map (PLeaTTa.subst binding))
        (PLeaTTa.subst binding res) :=
    PLeaTTa.PrologRecursiveCallPayloadBridge.TaskPayloadAgrees.representativeNormalizedCallAgrees
      payload payloadSupported
      (openedFor session predicate referencePayload referenceBindings).cursor
      (by simp [openedFor, openLocalCall, requestFor, prepareCall])
      (by simp [openedFor, openLocalCall, requestFor, prepareCall])
  exact
    openedFor_pendingCallOf_representative_supported_relates database ready
      predicate referencePayload referenceBindings alpha args res rest binding
      branches finalCounter arity head scanned query candidateSupported

/-- A semantic scan is ready either because both exact occurrence banks are
empty or because their first occurrence was retained.  The retained case
keeps the original supported tail and the original executable tail scan. -/
inductive RepresentativeSupportedReady
    (callGeneration : Generation) (predicate : String)
    (referenceArguments : List Term) (referenceBindings : Substitution)
    (argsv args : List Atom) (res : Atom)
    (rest : List PLeaTTa.Goal) (binding : Subst) (qterm : Atom)
    (barrier : Nat) :
    List ClauseBranch → List PLeaTTa.Clause →
      Nat → List Alt → Nat → Prop where
  | exhausted (counter : Nat) :
      RepresentativeSupportedReady callGeneration predicate
        referenceArguments referenceBindings argsv args res rest binding
        qterm barrier [] [] counter [] counter
  | retained (branch : ClauseBranch) (clause : PLeaTTa.Clause)
      (branches : List ClauseBranch) (clauses : List PLeaTTa.Clause)
      (counter finalCounter : Nat) (alts : List Alt)
      (supported :
        SupportedPreparedCandidateAgrees callGeneration predicate
          referenceArguments referenceBindings branch clause)
      (arity : clause.params.length = argsv.length)
      (kept :
        resolutionClauseRetained argsv (PLeaTTa.subst binding res) clause =
          true)
      (tailSupported :
        List.Forall₂
          (SupportedPreparedCandidateAgrees callGeneration predicate
            referenceArguments referenceBindings)
          branches clauses)
      (tailScan :
        ResolutionScan argsv args res rest binding qterm barrier clauses
          (counter + 1) alts finalCounter) :
      RepresentativeSupportedReady callGeneration predicate
        referenceArguments referenceBindings argsv args res rest binding
        qterm barrier (branch :: branches) (clause :: clauses) counter
        (resolutionAlt argsv args res rest binding qterm barrier counter
          clause :: alts)
        finalCounter

/-- A real executable scan and its exact supported occurrence spine factor
through a maximal, exactly counted source-only rejected prefix.

Every skipped occurrence is justified by semantic prefilter conservativity
against the original cursor.  Retained false positives are not removed. -/
theorem ResolutionScan.decomposeRepresentativeRejectedPrefix
    {queryAlpha : List (LogicVar × String)}
    {original current : PreparedCursor}
    {callGeneration : Generation} {predicate : String}
    {referenceArguments : List Term} {referenceBindings : Substitution}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst} {qterm : Atom}
    {barrier : Nat} {branches : List ClauseBranch}
    {clauses : List PLeaTTa.Clause} {counter finalCounter : Nat}
    {alts : List Alt}
    (scan :
      ResolutionScan argsv args res rest binding qterm barrier clauses
        counter alts finalCounter)
    (supported :
      List.Forall₂
        (SupportedPreparedCandidateAgrees callGeneration predicate
          referenceArguments referenceBindings)
        branches clauses)
    (query :
      RepresentativeNormalizedCallAgrees queryAlpha original argsv
        (PLeaTTa.subst binding res))
    (wellFormed : original.WellFormed)
    (originalContext :
      CursorCallContext original callGeneration predicate referenceArguments
        referenceBindings)
    (currentContext :
      CursorCallContext current callGeneration predicate referenceArguments
        referenceBindings)
    (remaining : current.remaining = branches)
    (subset :
      ∀ branch, branch ∈ branches → branch ∈ original.remaining)
    (arities :
      ∀ clause, clause ∈ clauses →
        clause.params.length = argsv.length) :
    ∃ count skippedBranches skippedClauses finish
        readyBranches readyClauses,
      branches = skippedBranches ++ readyBranches ∧
      clauses = skippedClauses ++ readyClauses ∧
      skippedBranches.length = count ∧
      skippedClauses.length = count ∧
      RejectedPullsN count current finish ∧
      finish.remaining = readyBranches ∧
      CursorCallContext finish callGeneration predicate referenceArguments
        referenceBindings ∧
      RepresentativeSupportedReady callGeneration predicate
        referenceArguments referenceBindings argsv args res rest binding
        qterm barrier readyBranches readyClauses counter alts finalCounter := by
  induction scan generalizing branches current with
  | nil counter =>
      cases supported
      exact
        ⟨0, [], [], current, [], [], rfl, rfl, rfl, rfl, .zero current,
          remaining, currentContext, .exhausted counter⟩
  | skipped clause clauses counter finalCounter alts rejected tail
      inductionHypothesis =>
      cases supported with
      | @cons branch clause' branches clauses' head tailSupported =>
          have branchMember : branch ∈ original.remaining :=
            subset branch (by simp)
          have clauseArity : clause.params.length = argsv.length :=
            arities clause (by simp)
          have supportedAtOriginal :
              SupportedPreparedCandidateAgrees original.callGeneration
                original.predicate original.arguments original.bindings
                branch clause :=
            originalContext.supportedPreparedCandidate head
          have clash : ¬ ∃ result, HeadResolution branch result :=
            PLeaTTa.PrologRepresentativeCallPrefilterBridge.RepresentativeNormalizedCallAgrees.no_headResolution_of_rejected
              query wellFormed branchMember supportedAtOriginal clauseArity
                rejected
          let next := current.advance branch branches
          have nextContext :
              CursorCallContext next callGeneration predicate
                referenceArguments referenceBindings :=
            currentContext.advance branch branches
          have nextRemaining : next.remaining = branches := by
            simp [next, PreparedCursor.advance]
          have tailSubset :
              ∀ later, later ∈ branches →
                later ∈ original.remaining := by
            intro later member
            exact subset later (by simp [member])
          have tailArities :
              ∀ candidate, candidate ∈ clauses →
                candidate.params.length = argsv.length := by
            intro candidate member
            exact arities candidate (by simp [member])
          obtain
            ⟨count, skippedBranches, skippedClauses, finish,
              readyBranches, readyClauses, branchesEq, clausesEq,
              branchCount, clauseCount, pulls, finishRemaining,
              finishContext, ready⟩ :=
            inductionHypothesis tailSupported nextContext nextRemaining
              tailSubset tailArities
          refine
            ⟨count + 1, branch :: skippedBranches,
              clause :: skippedClauses, finish, readyBranches, readyClauses,
              ?_, ?_, ?_, ?_, ?_, finishRemaining, finishContext, ready⟩
          · simp [branchesEq]
          · simp [clausesEq]
          · simp [branchCount]
          · simp [clauseCount]
          · exact
              .succ count current branch branches finish
                remaining clash pulls
  | retained clause clauses counter finalCounter alts kept tail
      inductionHypothesis =>
      cases supported with
      | @cons branch clause' branches clauses' head tailSupported =>
          exact
            ⟨0, [], [], current, branch :: branches,
              clause :: clauses, rfl, rfl, rfl, rfl, .zero current,
              remaining, currentContext,
              .retained branch clause branches clauses counter
                finalCounter alts head (arities clause (by simp)) kept
                tailSupported tail⟩

/-- A nonempty executable bank rules out the exhausted semantic ready case. -/
theorem RepresentativeSupportedReady.branches_nonempty_of_alts_nonempty
    {callGeneration : Generation} {predicate : String}
    {referenceArguments : List Term} {referenceBindings : Substitution}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst} {qterm : Atom}
    {barrier : Nat} {branches : List ClauseBranch}
    {clauses : List PLeaTTa.Clause} {counter finalCounter : Nat}
    {alts : List Alt}
    (ready :
      RepresentativeSupportedReady callGeneration predicate
        referenceArguments referenceBindings argsv args res rest binding
        qterm barrier branches clauses counter alts finalCounter)
    (nonempty : alts ≠ []) :
    branches ≠ [] := by
  cases ready <;> simp_all

/-- Eliminate a nonempty semantic ready suffix while retaining the exact
supported occurrence and untouched tail certificates. -/
theorem RepresentativeSupportedReady.retained_shape
    {callGeneration : Generation} {predicate : String}
    {referenceArguments : List Term} {referenceBindings : Substitution}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst} {qterm : Atom}
    {barrier : Nat} {branches : List ClauseBranch}
    {clauses : List PLeaTTa.Clause} {counter finalCounter : Nat}
    {alts : List Alt}
    (ready :
      RepresentativeSupportedReady callGeneration predicate
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
      clause.params.length = argsv.length ∧
      resolutionClauseRetained argsv (PLeaTTa.subst binding res) clause =
        true ∧
      List.Forall₂
        (SupportedPreparedCandidateAgrees callGeneration predicate
          referenceArguments referenceBindings)
        branchTail clauseTail ∧
      ResolutionScan argsv args res rest binding qterm barrier clauseTail
        (counter + 1) altTail finalCounter := by
  cases ready with
  | exhausted counter =>
      exact False.elim (nonempty rfl)
  | retained branch clause branches clauses counter finalCounter alts
      supported arity kept tailSupported tailScan =>
      exact
        ⟨branch, clause, branches, clauses, alts, rfl, rfl, rfl,
          supported, arity, kept, tailSupported, tailScan⟩

/-- Exact semantic activation frontier after the maximal rejected prefix and
the real executable `callPull`.

No head MGU is chosen here.  The tail scan and support spine pin every later
occurrence, while the semantic query remains hidden behind one representative
at the finishing cursor. -/
structure RepresentativeRetainedCallFrontier
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
    RepresentativeNormalizedCallAgrees queryAlpha finish argsv
      (PLeaTTa.subst binding res)
  supported :
    SupportedPreparedCandidateAgrees finish.callGeneration finish.predicate
      finish.arguments finish.bindings branch clause
  arity : clause.params.length = args.length
  retained :
    resolutionClauseRetained argsv (PLeaTTa.subst binding res) clause = true
  tailSupported :
    List.Forall₂
      (SupportedPreparedCandidateAgrees opened.cursor.callGeneration
        opened.cursor.predicate opened.cursor.arguments
        opened.cursor.bindings)
      branchTail clauseTail
  tailScan :
    ResolutionScan argsv args res rest binding qterm barrier clauseTail
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

/-- The semantic call-entry state reaches the exact first retained
occurrence, paying one source transition for every executable prefilter skip
and one real executable `callPull`. -/
theorem
    RepresentativeSupportedCallEntryRelates.callPull_retained_frontier
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {queryAlpha : List (LogicVar × String)}
    {opened : OpenedCall} {before : DemandDrivenStep.OpenConf}
    {pending : DemandDrivenCallStep.PendingCall}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst}
    {qterm : Atom} {barrier startCounter : Nat}
    (agreement :
      RepresentativeSupportedCallEntryRelates queryAlpha opened before
        pending argsv args res rest binding qterm barrier startCounter)
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
      RepresentativeRetainedCallFrontier queryAlpha opened before pending
        finish branch clause branchTail clauseTail altTail copied argsv args
        res rest binding qterm barrier startCounter := by
  let executableCandidates :=
    pending.persistent.world.resolutionCandidates
      opened.cursor.predicate args.length
  have arities :
      ∀ clause, clause ∈ executableCandidates →
        clause.params.length = argsv.length := by
    intro clause member
    have candidateMember :
        clause ∈
          pending.persistent.world.resolutionCandidates
            opened.cursor.predicate args.length := by
      simpa [executableCandidates] using member
    have exactArity :=
      resolutionCandidates_member_arity pending.persistent.world
        opened.cursor.predicate args.length agreement.entry.database.clauseIndex
        agreement.indexReady candidateMember
    simpa [agreement.entry.substitutedArgs] using exactArity
  obtain
    ⟨count, skippedBranches, skippedClauses, finish,
      readyBranches, readyClauses, branchesEq, clausesEq,
      branchCount, clauseCount, pulls, finishRemaining,
      finishContext, ready⟩ :=
    PLeaTTa.PrologRepresentativeCallFrontierBridge.ResolutionScan.decomposeRepresentativeRejectedPrefix
      agreement.entry.bank.scan
      agreement.supportedCandidates agreement.query
      agreement.cursorWellFormed (.refl opened.cursor)
      (.refl opened.cursor) rfl (fun _ member => member) arities
  have readyNonempty : readyBranches ≠ [] :=
    ready.branches_nonempty_of_alts_nonempty nonempty
  obtain
    ⟨branch, clause, branchTail, clauseTail, altTail,
      readyBranchesEq, readyClausesEq, altsEq, supported, clauseArity,
      retained, tailSupported, tailScan⟩ :=
    ready.retained_shape readyNonempty
  let copied :=
    PLeaTTa.freshenResolutionClause argsv args res rest binding qterm
      startCounter barrier clause
  have installedAlts :
      pending.installed.toConf.alts =
        resolutionAlt argsv args res rest binding qterm barrier startCounter
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
  have pulledExact :
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
  have finishWellFormed : finish.WellFormed :=
    PLeaTTa.PrologSupportedCallFrontierBridge.RejectedPullsN.preserves_wellFormed
      pulls agreement.cursorWellFormed
  have queryAtFinish :
      RepresentativeNormalizedCallAgrees queryAlpha finish argsv
        (PLeaTTa.subst binding res) :=
    PLeaTTa.PrologRepresentativeCallFrontierBridge.CursorCallContext.representativeNormalizedCallAgrees
      finishContext (.refl opened.cursor) agreement.query
  have supportedAtFinish :
      SupportedPreparedCandidateAgrees finish.callGeneration finish.predicate
        finish.arguments finish.bindings branch clause :=
    finishContext.supportedPreparedCandidate supported
  have executableArity : clause.params.length = args.length := by
    calc
      clause.params.length = argsv.length := clauseArity
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
    ⟨count, skippedBranches, skippedClauses, finish, branch, clause,
      branchTail, clauseTail, altTail, copied, ?_, ?_, branchCount,
      clauseCount, pulls.stepsN opened.scope opened.session, .callPull pending,
      ?_⟩
  · calc
      opened.cursor.remaining =
          skippedBranches ++ readyBranches := branchesEq
      _ = skippedBranches ++ (branch :: branchTail) := by
        rw [readyBranchesEq]
  · calc
      executableCandidates =
          skippedClauses ++ readyClauses := clausesEq
      _ = skippedClauses ++ (clause :: clauseTail) := by
        rw [readyClausesEq]
  · exact
      ⟨by simpa [readyBranchesEq] using finishRemaining,
        finishWellFormed, finishContext, queryAtFinish, supportedAtFinish,
        executableArity, retained, tailSupported, tailScan,
        agreement.entry.substitutedArgs, agreement.entry.queryTerm,
        agreement.entry.startCounterExact, rfl, pulledExact, highWater⟩

end PLeaTTa.PrologRepresentativeCallFrontierBridge
