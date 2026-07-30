-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologHeadFailureContinuationBridge
Purpose: Carry one jointly rejected retained clause head to the exact next
  source/executable local-call frontier.
Trusted boundary: none
Main exports:
  RepresentativeRetainedCallFrontier.afterHeadFailure
-/
import PLeaTTa.Proofs.PrologActivationFailureBridge
import PLeaTTa.Proofs.PrologRepresentativeCallFrontierBridge
import PLeaTTa.Proofs.PrologRepresentativeProductActivationBridge
import PLeaTTa.Proofs.PrologOrdinaryStepBridge

namespace PLeaTTa.PrologHeadFailureContinuationBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologActivationFailureBridge
open PrologActivationMacro
open PrologCallPayloadBridge
open PrologOrdinaryStepBridge
open PrologPrefilterScanBridge
open PrologRepresentativeCallFrontierBridge
open PrologRepresentativeProductActivationBridge
open PrologStateBridge
open PrologSupportedCursorAlternativeBridge

/-!
A conservatively retained local clause can still fail when its complete
input-plus-output head equality is executed.  The independent cursor rejects
that occurrence explicitly and may then pay a finite source-only prefix of
later conservative rejections.  The executable bank already omitted that
later prefix, so `Step.eq_fail` reaches the same ready suffix with one eager
`pull`.

The theorem below records this bounded granularity mismatch rather than
quotienting silent transitions.  Exact source/executable suffix equations and
`RepresentativeSupportedReady` keep clause order, multiplicity, allocation
seeds, and local-call exhaustion visible.
-/

/-- Exactly counted cursor rejections lift through the real predicate
cut-boundary and caller-product wrappers without changing their count or
publishing an observation.

This is the reusable control half of failed-clause backtracking: the caller
tail stays outside the predicate boundary, and every source-only rejection
remains a present transition rather than an observation-list stutter. -/
theorem RejectedPullsN.sourceProductStepsN
    {count : Nat} {before after : PreparedCursor}
    (pulls : RejectedPullsN count before after)
    (callerScope : CutScopeId) (opened : OpenedCall)
    (referenceRest : List PeTTaSpec.PrologCore.Goal) :
    StepsN count
      (.running opened.session
        (sourceProductFrontier callerScope opened before referenceRest))
      []
      (.running opened.session
        (sourceProductFrontier callerScope opened after referenceRest)) := by
  induction pulls with
  | zero cursor =>
      exact .zero _
  | succ count cursor branch branches finish remaining clash tail
      inductionHypothesis =>
      have pulled :
          LocalPull cursor (.silent (cursor.advance branch branches)) :=
        .rejected cursor branch branches remaining clash
      have leaf :
          RawStep opened.session (.clauses opened.scope cursor) [] .none
            opened.session
            (.running
              (.clauses opened.scope (cursor.advance branch branches))) := by
        simpa [localPullEvents, localPullTarget] using
          (RawStep.clausesPull opened.scope cursor
            (.silent (cursor.advance branch branches)) opened.session pulled)
      have boundary :
          RawStep opened.session
            (.cutBoundary opened.scope (.clauses opened.scope cursor))
            [] .none opened.session
            (.running
              (.cutBoundary opened.scope
                (.clauses opened.scope
                  (cursor.advance branch branches)))) :=
        .cutBoundaryProgress opened.scope _ _ [] opened.session
          opened.session leaf
      have wrapped :
          RawStep opened.session
            (sourceProductFrontier callerScope opened cursor referenceRest)
            [] .none opened.session
            (.running
              (sourceProductFrontier callerScope opened
                (cursor.advance branch branches) referenceRest)) := by
        exact
          .productProgress callerScope _ _ referenceRest [] .none
            opened.session opened.session boundary
            (by simp [Trace.AnswerFree])
      have first :
          Transition
            (.running opened.session
              (sourceProductFrontier callerScope opened cursor referenceRest))
            []
            (.running opened.session
              (sourceProductFrontier callerScope opened
                (cursor.advance branch branches) referenceRest)) :=
        .ordinary _ _ _ _ _ wrapped
      simpa using
        (StepsN.succ count
          (.running opened.session
            (sourceProductFrontier callerScope opened cursor referenceRest))
          (.running opened.session
            (sourceProductFrontier callerScope opened
              (cursor.advance branch branches) referenceRest))
          (.running opened.session
            (sourceProductFrontier callerScope opened finish referenceRest))
          [] [] first inductionHypothesis)

/-- A representative ready suffix indexed by an empty source occurrence
list is genuinely exhausted on both representations, with no hidden
executable alternative and no counter discrepancy. -/
theorem RepresentativeSupportedReady.exhausted_shape
    {callGeneration : Generation} {predicate : String}
    {referenceArguments : List Term} {referenceBindings : Substitution}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst} {qterm : Atom}
    {barrier counter finalCounter : Nat}
    {clauses : List PLeaTTa.Clause} {alts : List PLeaTTa.Alt}
    (ready :
      RepresentativeSupportedReady callGeneration predicate
        referenceArguments referenceBindings argsv args res rest binding
        qterm barrier [] clauses counter alts finalCounter) :
    clauses = [] ∧ alts = [] ∧ finalCounter = counter := by
  cases ready
  exact ⟨rfl, rfl, rfl⟩

/-- If a failed equality has a retained executable branch at the front of
its alternative bank, the fine successor installs that exact branch and
leaves the exact tail.  This is the `OpenConf` projection of the shared
machine's `pull_branch` theorem. -/
theorem unifyFailureSuccessor_toConf_of_alts_branch
    (state : OpenConf) (goals : List PLeaTTa.Goal)
    (runtime : Subst) (rest : List PLeaTTa.Alt)
    (alts : state.control.alts = .br goals runtime :: rest) :
    (unifyFailureSuccessor state).toConf =
      { state.toConf with cur := some (goals, runtime), alts := rest } := by
  unfold unifyFailureSuccessor
  rw [OpenConf.ofConf_toConf]
  apply PLeaTTa.pull_of_alts_branch
  change state.control.alts = .br goals runtime :: rest
  exact alts

/-- One jointly rejected retained clause reaches the exact next synchronized
frontier.

The independent side takes `count + 1` transitions: one for the current
complete-head rejection and `count` for the maximal later source-only
prefilter prefix.  The executable side takes exactly one real
`eq_fail → pull` transition.  Persistent world and global fresh state are
unchanged, while the returned ready relation distinguishes a next retained
clause from local-call exhaustion. -/
theorem
    PrologRepresentativeCallFrontierBridge.RepresentativeRetainedCallFrontier.afterHeadFailure
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {queryAlpha : List (LogicVar × String)}
    {opened : OpenedCall} {before : OpenConf}
    {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    {branchTail : List ClauseBranch} {clauseTail : List PLeaTTa.Clause}
    {altTail : List PLeaTTa.Alt} {copied : PLeaTTa.Clause}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst}
    {qterm : Atom} {barrier startCounter : Nat}
    {callerScope : CutScopeId}
    {referenceRest : List PeTTaSpec.PrologCore.Goal}
    (frontier :
      RepresentativeRetainedCallFrontier queryAlpha opened before pending
        finish branch clause branchTail clauseTail altTail copied argsv args
        res rest binding qterm barrier startCounter)
    (failure :
      RetainedHeadFailureAgrees branch args res rest binding qterm
        startCounter barrier clause) :
    ∃ count skippedBranches skippedClauses next
        readyBranches readyClauses,
      branchTail = skippedBranches ++ readyBranches ∧
      clauseTail = skippedClauses ++ readyClauses ∧
      skippedBranches.length = count ∧
      skippedClauses.length = count ∧
      StepsN (count + 1)
        (.running opened.session (.clauses opened.scope finish)) []
        (.running opened.session (.clauses opened.scope next)) ∧
      StepsN (count + 1)
        (.running opened.session
          (sourceProductFrontier callerScope opened finish referenceRest))
        []
        (.running opened.session
          (sourceProductFrontier callerScope opened next referenceRest)) ∧
      DemandDrivenCallStep.Step prog gt (.ready pending.pulled)
        (.ready (unifyFailureSuccessor pending.pulled)) ∧
      (unifyFailureSuccessor pending.pulled).persistent =
        pending.pulled.persistent ∧
      next.remaining = readyBranches ∧
      CursorCallContext next opened.cursor.callGeneration
        opened.cursor.predicate opened.cursor.arguments
        opened.cursor.bindings ∧
      RepresentativeSupportedReady opened.cursor.callGeneration
        opened.cursor.predicate opened.cursor.arguments
        opened.cursor.bindings argsv args res rest binding qterm barrier
        readyBranches readyClauses (startCounter + 1) altTail
        pending.persistent.counter := by
  let advanced := finish.advance branch branchTail
  have advancedRemaining : advanced.remaining = branchTail := by
    simp [advanced, PreparedCursor.advance]
  have advancedContext :
      CursorCallContext advanced opened.cursor.callGeneration
        opened.cursor.predicate opened.cursor.arguments
        opened.cursor.bindings :=
    frontier.finishContext.advance branch branchTail
  have tailSubset :
      ∀ later, later ∈ branchTail → later ∈ finish.remaining := by
    intro later member
    rw [frontier.finishRemaining]
    simp [member]
  obtain
    ⟨count, skippedBranches, skippedClauses, next,
      readyBranches, readyClauses, branchesEq, clausesEq,
      branchCount, clauseCount, pulls, nextRemaining, nextContext, ready⟩ :=
    PLeaTTa.PrologRepresentativeCallFrontierBridge.ResolutionScan.decomposeRepresentativeRejectedPrefix
      frontier.tailScan frontier.tailSupported frontier.query
      frontier.finishWellFormed frontier.finishContext advancedContext
      advancedRemaining tailSubset frontier.tailArities
  have executableCurrent :
      pending.pulled.toConf.cur =
        some
          (PLeaTTa.Goal.eq (.expr (args ++ [res]))
              (.expr
                ((PLeaTTa.freshenResolutionClause argsv args res rest binding
                    qterm startCounter barrier clause).params ++
                  [(PLeaTTa.freshenResolutionClause argsv args res rest
                    binding qterm startCounter barrier clause).result])) ::
            (PLeaTTa.freshenResolutionClause argsv args res rest binding qterm
              startCounter barrier clause).body ++ rest,
            binding) := by
    have exactCur :=
      congrArg (fun conf : PLeaTTa.Conf => conf.cur) frontier.pulledExact
    simpa [frontier.copiedExact] using exactCur
  have paired :=
    failure.step_correspondence
      (prog := prog) (gt := gt) (session := opened.session)
      (scope := opened.scope) (cursor := finish) (branches := branchTail)
      (conf := pending.pulled.toConf) frontier.finishRemaining
      executableCurrent
  have firstTransition :
      Transition
        (.running opened.session (.clauses opened.scope finish)) []
        (.running opened.session (.clauses opened.scope advanced)) := by
    exact .ordinary _ _ _ _ _ (by simpa [advanced] using paired.1)
  have firstSteps :
      StepsN 1
        (.running opened.session (.clauses opened.scope finish)) []
        (.running opened.session (.clauses opened.scope advanced)) := by
    simpa using
      (StepsN.succ 0
        (.running opened.session (.clauses opened.scope finish))
        (.running opened.session (.clauses opened.scope advanced))
        (.running opened.session (.clauses opened.scope advanced))
        [] [] firstTransition (.zero _))
  have tailSteps :
      StepsN count
        (.running opened.session (.clauses opened.scope advanced)) []
        (.running opened.session (.clauses opened.scope next)) :=
    pulls.stepsN opened.scope opened.session
  have sourceSteps :
      StepsN (count + 1)
        (.running opened.session (.clauses opened.scope finish)) []
        (.running opened.session (.clauses opened.scope next)) := by
    simpa [Nat.add_comm] using StepsN.trans firstSteps tailSteps
  have combinedPulls :
      RejectedPullsN (count + 1) finish next :=
    .succ count finish branch branchTail next frontier.finishRemaining
      failure.independentRejected pulls
  have wrappedSourceSteps :
      StepsN (count + 1)
        (.running opened.session
          (sourceProductFrontier callerScope opened finish referenceRest))
        []
        (.running opened.session
          (sourceProductFrontier callerScope opened next referenceRest)) :=
    PLeaTTa.PrologHeadFailureContinuationBridge.RejectedPullsN.sourceProductStepsN
      combinedPulls callerScope opened referenceRest
  have executableControl :
      pending.pulled.control.cur =
        some
          (PLeaTTa.Goal.eq (.expr (args ++ [res]))
              (.expr
                ((PLeaTTa.freshenResolutionClause argsv args res rest binding
                    qterm startCounter barrier clause).params ++
                  [(PLeaTTa.freshenResolutionClause argsv args res rest
                    binding qterm startCounter barrier clause).result])) ::
            (PLeaTTa.freshenResolutionClause argsv args res rest binding qterm
              startCounter barrier clause).body ++ rest,
            binding) := by
    change pending.pulled.toConf.cur = _
    exact executableCurrent
  have executableStep :
      DemandDrivenCallStep.Step prog gt (.ready pending.pulled)
        (.ready (unifyFailureSuccessor pending.pulled)) :=
    executable_unify_failure_step pending.pulled
      .equality
      (.expr (args ++ [res]))
      (.expr
        ((PLeaTTa.freshenResolutionClause argsv args res rest binding qterm
            startCounter barrier clause).params ++
          [(PLeaTTa.freshenResolutionClause argsv args res rest binding qterm
            startCounter barrier clause).result]))
      ((PLeaTTa.freshenResolutionClause argsv args res rest binding qterm
        startCounter barrier clause).body ++ rest)
      binding executableControl failure.executableRejected
  exact
    ⟨count, skippedBranches, skippedClauses, next,
      readyBranches, readyClauses, branchesEq, clausesEq,
      branchCount, clauseCount, sourceSteps, wrappedSourceSteps,
      executableStep,
      unifyFailureSuccessor_persistent pending.pulled,
      nextRemaining, nextContext, ready⟩

/-- A nonempty ready suffix after head failure installs the exact next
source-ordered executable clause.

The complete configuration equation is derived from the frontier's live
alternative stack and the ready relation's exact `resolutionAlt` head.  No
freshening, ordering, or pull decision is recomputed. -/
theorem
    PrologRepresentativeCallFrontierBridge.RepresentativeRetainedCallFrontier.unifyFailureSuccessor_pulls_ready
    {queryAlpha : List (LogicVar × String)}
    {opened : OpenedCall} {before : OpenConf}
    {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    {branchTail : List ClauseBranch} {clauseTail : List PLeaTTa.Clause}
    {altTail : List PLeaTTa.Alt} {copied : PLeaTTa.Clause}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst}
    {qterm : Atom} {barrier startCounter : Nat}
    (frontier :
      RepresentativeRetainedCallFrontier queryAlpha opened before pending
        finish branch clause branchTail clauseTail altTail copied argsv args
        res rest binding qterm barrier startCounter)
    {readyBranches : List ClauseBranch}
    {readyClauses : List PLeaTTa.Clause}
    (ready :
      RepresentativeSupportedReady opened.cursor.callGeneration
        opened.cursor.predicate opened.cursor.arguments
        opened.cursor.bindings argsv args res rest binding qterm barrier
        readyBranches readyClauses (startCounter + 1) altTail
        pending.persistent.counter)
    (nonempty : readyBranches ≠ []) :
    ∃ nextBranch nextClause nextBranchTail nextClauseTail nextAltTail
        nextCopied,
      readyBranches = nextBranch :: nextBranchTail ∧
      readyClauses = nextClause :: nextClauseTail ∧
      nextCopied =
        PLeaTTa.freshenResolutionClause argsv args res rest binding qterm
          (startCounter + 1) barrier nextClause ∧
      (unifyFailureSuccessor pending.pulled).toConf =
        { pending.pulled.toConf with
          cur :=
            some
              (PLeaTTa.Goal.eq (.expr (args ++ [res]))
                  (.expr (nextCopied.params ++ [nextCopied.result])) ::
                nextCopied.body ++ rest,
                binding)
          alts := nextAltTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts } ∧
      SupportedPreparedCandidateAgrees opened.cursor.callGeneration
        opened.cursor.predicate opened.cursor.arguments
        opened.cursor.bindings nextBranch nextClause ∧
      nextClause.params.length = argsv.length ∧
      resolutionClauseRetained argsv (PLeaTTa.subst binding res)
        nextClause = true ∧
      List.Forall₂
        (SupportedPreparedCandidateAgrees opened.cursor.callGeneration
          opened.cursor.predicate opened.cursor.arguments
          opened.cursor.bindings)
        nextBranchTail nextClauseTail ∧
      ResolutionScan argsv args res rest binding qterm barrier nextClauseTail
        (startCounter + 1 + 1) nextAltTail pending.persistent.counter := by
  obtain
    ⟨nextBranch, nextClause, nextBranchTail, nextClauseTail, nextAltTail,
      branchesEq, clausesEq, altsEq, supported, arity, retained,
      tailSupported, tailScan⟩ :=
    ready.retained_shape nonempty
  let nextCopied :=
    PLeaTTa.freshenResolutionClause argsv args res rest binding qterm
      (startCounter + 1) barrier nextClause
  have activeAlts :
      pending.pulled.control.alts =
        .br
            (PLeaTTa.Goal.eq (.expr (args ++ [res]))
                (.expr (nextCopied.params ++ [nextCopied.result])) ::
              nextCopied.body ++ rest)
            binding ::
          (nextAltTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts) := by
    change pending.pulled.toConf.alts = _
    have exactAlts :=
      congrArg (fun conf : PLeaTTa.Conf => conf.alts) frontier.pulledExact
    simpa [altsEq, resolutionAlt, nextCopied] using exactAlts
  have successor :=
    unifyFailureSuccessor_toConf_of_alts_branch pending.pulled
      (PLeaTTa.Goal.eq (.expr (args ++ [res]))
          (.expr (nextCopied.params ++ [nextCopied.result])) ::
        nextCopied.body ++ rest)
      binding
      (nextAltTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts)
      activeAlts
  exact
    ⟨nextBranch, nextClause, nextBranchTail, nextClauseTail, nextAltTail,
      nextCopied, branchesEq, clausesEq, rfl, successor,
      supported, arity, retained, tailSupported, tailScan⟩

/-- An exhausted ready suffix after head failure skips the local predicate's
own barrier and resumes exactly the outer executable alternative stack.

The ready inversion also exposes the empty source clause suffix and exact
counter equality, so local-call exhaustion cannot hide a dropped occurrence
or a fresh-allocation discrepancy. -/
theorem
    PrologRepresentativeCallFrontierBridge.RepresentativeRetainedCallFrontier.unifyFailureSuccessor_exhausted
    {queryAlpha : List (LogicVar × String)}
    {opened : OpenedCall} {before : OpenConf}
    {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    {branchTail : List ClauseBranch} {clauseTail : List PLeaTTa.Clause}
    {altTail : List PLeaTTa.Alt} {copied : PLeaTTa.Clause}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst}
    {qterm : Atom} {barrier startCounter : Nat}
    (frontier :
      RepresentativeRetainedCallFrontier queryAlpha opened before pending
        finish branch clause branchTail clauseTail altTail copied argsv args
        res rest binding qterm barrier startCounter)
    {readyClauses : List PLeaTTa.Clause}
    (ready :
      RepresentativeSupportedReady opened.cursor.callGeneration
        opened.cursor.predicate opened.cursor.arguments
        opened.cursor.bindings argsv args res rest binding qterm barrier
        [] readyClauses (startCounter + 1) altTail
        pending.persistent.counter) :
    readyClauses = [] ∧
      altTail = [] ∧
      pending.persistent.counter = startCounter + 1 ∧
      (unifyFailureSuccessor pending.pulled).toConf =
        PLeaTTa.pull
          { pending.outer.toConf pending.persistent with cur := none } := by
  rcases
      PLeaTTa.PrologHeadFailureContinuationBridge.RepresentativeSupportedReady.exhausted_shape
        ready with
    ⟨clausesEmpty, altsEmpty, counterExact⟩
  have successor :
      (unifyFailureSuccessor pending.pulled).toConf =
        PLeaTTa.pull
          { pending.outer.toConf pending.persistent with cur := none } := by
    calc
      (unifyFailureSuccessor pending.pulled).toConf =
          PLeaTTa.pull { pending.pulled.toConf with cur := none } := by
            rfl
      _ =
          PLeaTTa.pull
            { pending.installed.toConf with
              cur := none
              alts := PLeaTTa.Alt.barrier :: pending.outer.alts } := by
            rw [frontier.pulledExact, altsEmpty]
            simp
      _ =
          PLeaTTa.pull
            { pending.outer.toConf pending.persistent with
              cur := none
              alts := PLeaTTa.Alt.barrier :: pending.outer.alts
              barriers :=
                PLeaTTa.pushBarrierCache pending.outer.barriers } := by
            rfl
      _ =
          PLeaTTa.pull
            { pending.outer.toConf pending.persistent with
              cur := none
              alts := pending.outer.alts } := by
            exact
              PLeaTTa.pull_barrier
                (pending.outer.toConf pending.persistent) pending.outer.alts
      _ =
          PLeaTTa.pull
            { pending.outer.toConf pending.persistent with cur := none } := by
            rfl
  exact
    ⟨clausesEmpty, altsEmpty, counterExact, successor⟩

end PLeaTTa.PrologHeadFailureContinuationBridge
