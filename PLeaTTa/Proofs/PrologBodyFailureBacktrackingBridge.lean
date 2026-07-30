-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologBodyFailureBacktrackingBridge
Purpose: Relate primitive failure inside an entered local clause body to the
  exact next source/executable retained-alternative frontier.
Trusted boundary: none
Main exports:
  activeSourceProduct_unifyFailure,
  SegmentedActiveProductRelates.afterUnifyFailure,
  SegmentedActiveProductRelates.unifyFailureSuccessor_retained,
  SegmentedActiveProductRelates.unifyFailureSuccessor_exhausted,
  changed_persistent_state_rejects_stale_restore
-/
import PLeaTTa.Proofs.PrologHeadFailureContinuationBridge
import PLeaTTa.Proofs.PrologProductSchedulingBridge

namespace PLeaTTa.PrologBodyFailureBacktrackingBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PLeaTTa.PrologBooleanAliasSafety
open PrologActivationMacro
open PrologActivatedProductStepBridge
open PrologAlphaFreshFrontierBridge
open PrologCallPayloadBridge
open PrologHeadFailureContinuationBridge
open PrologOrdinaryStepBridge
open PrologProductSchedulingBridge
open PrologRepresentativeCallFrontierBridge
open PrologRepresentativeProductActivationBridge
open PrologStateBridge
open PrologSupportedCursorAlternativeBridge

/-!
Failure after entering a clause body is a different control seam from
failure of the compiler-inserted complete-head equality.  On the independent
side the body leaf becomes complete, the predicate-scoped choice consumes
that completion, and the caller product remains suspended while the retained
cursor becomes active.  On the executable side the failing equality calls
`pull` eagerly in the same sealed transition.

The bridge below keeps the granularity mismatch explicit.  It first proves
the real wrapped source step, then reconstructs the supported occurrence
spine which activation had established for the immutable tail.  Later
theorems can factor that spine through the exact source-only rejected prefix
which the executable prefilter omitted.
-/

/-! ## Exact wrapped source failure -/

/-- A failed primitive unification inside an entered clause body switches to
the immutable retained cursor in one top-level source transition.

The leaf's completion observation is consumed by `choiceComplete`; the
predicate cut boundary and caller product publish no observation.  The body
tail and caller tail are discarded exactly as Prolog backtracking requires. -/
theorem activeSourceProduct_unifyFailure
    (callerScope : CutScopeId) (opened : OpenedCall)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (current : Substitution)
    (left right : Term)
    (bodyRest referenceRest : List PeTTaSpec.PrologCore.Goal)
    (clash : ¬ ∃ result, UnifyResolution current left right result) :
    RawStep opened.session
      (activeSourceProduct callerScope opened finish branch branchTail current
        (.unify left right :: bodyRest) referenceRest)
      [] .none opened.session
      (.running
        (sourceProductFrontier callerScope opened
          (finish.advance branch branchTail) referenceRest)) := by
  have leaf :
      RawStep opened.session
        (.task opened.scope (.unify left right :: bodyRest) current)
        [.completed] .none opened.session (.terminal .completed) :=
    .taskUnifyFailure opened.scope left right bodyRest current opened.session
      clash
  have choice :
      RawStep opened.session
        (.choice opened.scope
          (.task opened.scope (.unify left right :: bodyRest) current)
          (.clauses opened.scope (finish.advance branch branchTail)))
        [] .none opened.session
        (.running
          (.clauses opened.scope (finish.advance branch branchTail))) :=
    .choiceComplete opened.scope _ _ opened.session opened.session leaf
  have boundary :
      RawStep opened.session
        (.cutBoundary opened.scope
          (.choice opened.scope
            (.task opened.scope (.unify left right :: bodyRest) current)
            (.clauses opened.scope (finish.advance branch branchTail))))
        [] .none opened.session
        (.running
          (.cutBoundary opened.scope
            (.clauses opened.scope (finish.advance branch branchTail)))) :=
    .cutBoundaryProgress opened.scope _ _ [] opened.session opened.session
      choice
  exact
    .productProgress callerScope _ _ referenceRest [] .none
      opened.session opened.session boundary (by simp [Trace.AnswerFree])

/-! ## Paired primitive body failure -/

/-- A failed primitive unification in the selected clause body reaches one
exact shared ready suffix.

The independent side takes one wrapped branch-failure transition followed by
the exactly counted conservative rejections which the executable prefilter
had omitted.  The executable side takes one real `eq_fail -> pull` step.
Strict operand reflection is derived only from the body segment; the caller
tail remains related at its distinct cut barrier and is discarded by failure
without ever being retagged.

The original representative frontier is supplied alongside the active-state
relation because its tail scan is immutable call-start evidence.  No query
orientation is reconstructed after activation. -/
theorem SegmentedActiveProductRelates.afterUnifyFailure
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {bodyBarrier callerBarrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {queryAlpha : List (LogicVar × String)}
    {opened : OpenedCall} {before : OpenConf}
    {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    {branchTail : List ClauseBranch} {clauseTail : List PLeaTTa.Clause}
    {altTail : List PLeaTTa.Alt} {copied : PLeaTTa.Clause}
    {argsv args : List Atom} {res : Atom}
    {executableRest : List PLeaTTa.Goal} {binding : Subst}
    {qterm : Atom} {startCounter : Nat}
    {referenceRest bodyRest : List PeTTaSpec.PrologCore.Goal}
    {callerScope : CutScopeId}
    {current : Substitution} {state : OpenConf}
    {left right : Term}
    (frontier :
      RepresentativeRetainedCallFrontier queryAlpha opened before pending
        finish branch clause branchTail clauseTail altTail copied argsv args
        res executableRest binding qterm bodyBarrier startCounter)
    (agreement :
      SegmentedActiveProductRelates freshFrontier alpha support
        bodyBarrier callerBarrier canonical referenceBase opened pending
        finish branch branchTail altTail referenceRest current
        (.unify left right :: bodyRest) state)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote right))
    (currentSafe : Substitution.BooleanAliasSafe current)
    (leftAliasSafe : TermBooleanAliasSafe left)
    (rightAliasSafe : TermBooleanAliasSafe right)
    (clash : ¬ ∃ result, UnifyResolution current left right result) :
    ∃ (spelling :
          NormalizedAlphaGoalsAgree.ExecutableUnifySpelling)
        (executableLeft executableRight : Atom)
        (bodyExecutableTail callerExecutables : List PLeaTTa.Goal)
        (runtime : Subst)
        (count : Nat) (skippedBranches : List ClauseBranch)
        (skippedClauses : List PLeaTTa.Clause)
        (next : PreparedCursor)
        (readyBranches : List ClauseBranch)
        (readyClauses : List PLeaTTa.Clause),
      state.control.cur =
          some
            (spelling.goal executableLeft executableRight ::
              (bodyExecutableTail ++ callerExecutables),
              runtime) ∧
      branchTail = skippedBranches ++ readyBranches ∧
      clauseTail = skippedClauses ++ readyClauses ∧
      skippedBranches.length = count ∧
      skippedClauses.length = count ∧
      StepsN (count + 1)
        (.running opened.session
          (activeSourceProduct callerScope opened finish branch branchTail
            current (.unify left right :: bodyRest) referenceRest))
        []
        (.running opened.session
          (sourceProductFrontier callerScope opened next referenceRest)) ∧
      DemandDrivenCallStep.Step prog gt (.ready state)
        (.ready (unifyFailureSuccessor state)) ∧
      (unifyFailureSuccessor state).persistent = state.persistent ∧
      next.remaining = readyBranches ∧
      CursorCallContext next opened.cursor.callGeneration
        opened.cursor.predicate opened.cursor.arguments
        opened.cursor.bindings ∧
      RepresentativeSupportedReady opened.cursor.callGeneration
        opened.cursor.predicate opened.cursor.arguments
        opened.cursor.bindings argsv args res executableRest binding qterm
        bodyBarrier readyBranches readyClauses (startCounter + 1) altTail
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
  have firstRaw :
      RawStep opened.session
        (activeSourceProduct callerScope opened finish branch branchTail
          current (.unify left right :: bodyRest) referenceRest)
        [] .none opened.session
        (.running
          (sourceProductFrontier callerScope opened advanced referenceRest)) :=
    activeSourceProduct_unifyFailure callerScope opened finish branch
      branchTail current left right bodyRest referenceRest clash
  have firstTransition :
      Transition
        (.running opened.session
          (activeSourceProduct callerScope opened finish branch branchTail
            current (.unify left right :: bodyRest) referenceRest))
        []
        (.running opened.session
          (sourceProductFrontier callerScope opened advanced referenceRest)) :=
    .ordinary _ _ _ _ _ firstRaw
  have firstSteps :
      StepsN 1
        (.running opened.session
          (activeSourceProduct callerScope opened finish branch branchTail
            current (.unify left right :: bodyRest) referenceRest))
        []
        (.running opened.session
          (sourceProductFrontier callerScope opened advanced referenceRest)) := by
    simpa using
      (StepsN.succ 0
        (.running opened.session
          (activeSourceProduct callerScope opened finish branch branchTail
            current (.unify left right :: bodyRest) referenceRest))
        (.running opened.session
          (sourceProductFrontier callerScope opened advanced referenceRest))
        (.running opened.session
          (sourceProductFrontier callerScope opened advanced referenceRest))
        [] [] firstTransition (.zero _))
  have tailSteps :
      StepsN count
        (.running opened.session
          (sourceProductFrontier callerScope opened advanced referenceRest))
        []
        (.running opened.session
          (sourceProductFrontier callerScope opened next referenceRest)) :=
    PLeaTTa.PrologHeadFailureContinuationBridge.RejectedPullsN.sourceProductStepsN
      pulls callerScope opened referenceRest
  have sourceSteps :
      StepsN (count + 1)
        (.running opened.session
          (activeSourceProduct callerScope opened finish branch branchTail
            current (.unify left right :: bodyRest) referenceRest))
        []
        (.running opened.session
          (sourceProductFrontier callerScope opened next referenceRest)) := by
    simpa [Nat.add_comm] using StepsN.trans firstSteps tailSteps
  rcases agreement.ready with
    ⟨bodyExecutables, callerExecutables, runtime, _persistent,
      currentControl, payload⟩
  rcases payload.body.control.unifyHead with
    ⟨spelling, executableLeft, executableRight, bodyExecutableTail,
      bodyShape, leftAgreement, rightAgreement, _tailControl⟩
  have executableHead :
      state.control.cur =
        some
          (spelling.goal executableLeft executableRight ::
            (bodyExecutableTail ++ callerExecutables),
            runtime) := by
    calc
      state.control.cur =
          some (bodyExecutables ++ callerExecutables, runtime) :=
        currentControl
      _ =
          some
            ((spelling.goal executableLeft executableRight ::
                bodyExecutableTail) ++ callerExecutables,
              runtime) := by rw [bodyShape]
      _ =
          some
            (spelling.goal executableLeft executableRight ::
              (bodyExecutableTail ++ callerExecutables),
              runtime) := by rfl
  have aliasSafe :
      CurrentUnifyOperandsAliasSafe current left right :=
    CurrentUnifyOperandsAliasSafe.of_booleanAliasSafe
      currentSafe leftAliasSafe rightAliasSafe
  have strict :=
    payload.body.strictUnifyOperands_of_currentAliasSafe
      leftAgreement rightAgreement leftSupported rightSupported aliasSafe
  have failed :
      PLeaTTa.unifyB runtime executableLeft executableRight = none :=
    payload.body.unifyB_eq_none_of_no_resolution strict clash
  have executableStep :
      DemandDrivenCallStep.Step prog gt (.ready state)
        (.ready (unifyFailureSuccessor state)) :=
    executable_unify_failure_step state spelling executableLeft
      executableRight (bodyExecutableTail ++ callerExecutables) runtime
      executableHead failed
  exact
    ⟨spelling, executableLeft, executableRight, bodyExecutableTail,
      callerExecutables, runtime, count, skippedBranches, skippedClauses,
      next, readyBranches, readyClauses, executableHead, branchesEq,
      clausesEq, branchCount, clauseCount, sourceSteps, executableStep,
      unifyFailureSuccessor_persistent state, nextRemaining, nextContext,
      ready⟩

/-! ## Exact executable endpoints -/

/-- A nonempty ready suffix after primitive body failure installs the exact
next retained clause occurrence.

Unlike the head-failure theorem, this statement starts from an arbitrary
active body state.  Its target is therefore expressed over the current
configuration: body effects and the current persistent high-water are not
silently restored from the call-entry snapshot. -/
theorem SegmentedActiveProductRelates.unifyFailureSuccessor_retained
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {bodyBarrier callerBarrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {selected : ClauseBranch}
    {selectedTail : List ClauseBranch}
    {altTail : List PLeaTTa.Alt}
    {referenceRest body : List PeTTaSpec.PrologCore.Goal}
    {current : Substitution} {state : OpenConf}
    {argsv args : List Atom} {res : Atom}
    {executableRest : List PLeaTTa.Goal} {binding : Subst}
    {qterm : Atom} {startCounter : Nat}
    {readyBranches : List ClauseBranch}
    {readyClauses : List PLeaTTa.Clause}
    (agreement :
      SegmentedActiveProductRelates freshFrontier alpha support
        bodyBarrier callerBarrier canonical referenceBase opened pending
        finish selected selectedTail altTail referenceRest current body state)
    (ready :
      RepresentativeSupportedReady opened.cursor.callGeneration
        opened.cursor.predicate opened.cursor.arguments
        opened.cursor.bindings argsv args res executableRest binding qterm
        bodyBarrier readyBranches readyClauses (startCounter + 1) altTail
        pending.persistent.counter)
    (nonempty : readyBranches ≠ []) :
    ∃ nextBranch nextClause nextBranchTail nextClauseTail nextAltTail
        nextCopied,
      readyBranches = nextBranch :: nextBranchTail ∧
      readyClauses = nextClause :: nextClauseTail ∧
      nextCopied =
        PLeaTTa.freshenResolutionClause argsv args res executableRest binding
          qterm (startCounter + 1) bodyBarrier nextClause ∧
      (unifyFailureSuccessor state).toConf =
        { state.toConf with
          cur :=
            some
              (PLeaTTa.Goal.eq (.expr (args ++ [res]))
                  (.expr (nextCopied.params ++ [nextCopied.result])) ::
                nextCopied.body ++ executableRest,
                binding)
          alts :=
            nextAltTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts } ∧
      (unifyFailureSuccessor state).persistent = state.persistent ∧
      (unifyFailureSuccessor state).frames = pending.frames ∧
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
      ResolutionScan argsv args res executableRest binding qterm bodyBarrier
        nextClauseTail (startCounter + 1 + 1) nextAltTail
        pending.persistent.counter := by
  obtain
    ⟨nextBranch, nextClause, nextBranchTail, nextClauseTail, nextAltTail,
      branchesEq, clausesEq, altsEq, supported, arity, retained,
      tailSupported, tailScan⟩ :=
    ready.retained_shape nonempty
  let nextCopied :=
    PLeaTTa.freshenResolutionClause argsv args res executableRest binding
      qterm (startCounter + 1) bodyBarrier nextClause
  have activeAlts :
      state.control.alts =
        .br
            (PLeaTTa.Goal.eq (.expr (args ++ [res]))
                (.expr (nextCopied.params ++ [nextCopied.result])) ::
              nextCopied.body ++ executableRest)
            binding ::
          (nextAltTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts) := by
    simpa [altsEq, resolutionAlt, nextCopied] using agreement.retainedAlts
  have successor :=
    unifyFailureSuccessor_toConf_of_alts_branch state
      (PLeaTTa.Goal.eq (.expr (args ++ [res]))
          (.expr (nextCopied.params ++ [nextCopied.result])) ::
        nextCopied.body ++ executableRest)
      binding
      (nextAltTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts)
      activeAlts
  refine
    ⟨nextBranch, nextClause, nextBranchTail, nextClauseTail, nextAltTail,
      nextCopied, branchesEq, clausesEq, rfl, successor,
      unifyFailureSuccessor_persistent state, ?_, supported, arity, retained,
      tailSupported, tailScan⟩
  simp [unifyFailureSuccessor, agreement.frames]

/-- Exhausting the ready suffix after primitive body failure pops exactly
the local predicate barrier.

The resumed configuration is based on `state.toConf`, not on the saved
entry configuration.  Thus any world mutation or fresh allocation performed
by the selected body remains current across the failed branch, while only
the predicate-owned alternative marker and cache increment are removed. -/
theorem SegmentedActiveProductRelates.unifyFailureSuccessor_exhausted
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {bodyBarrier callerBarrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {selected : ClauseBranch}
    {selectedTail : List ClauseBranch}
    {altTail : List PLeaTTa.Alt}
    {referenceRest body : List PeTTaSpec.PrologCore.Goal}
    {current : Substitution} {state : OpenConf}
    {argsv args : List Atom} {res : Atom}
    {executableRest : List PLeaTTa.Goal} {binding : Subst}
    {qterm : Atom} {startCounter : Nat}
    {readyClauses : List PLeaTTa.Clause}
    (agreement :
      SegmentedActiveProductRelates freshFrontier alpha support
        bodyBarrier callerBarrier canonical referenceBase opened pending
        finish selected selectedTail altTail referenceRest current body state)
    (ready :
      RepresentativeSupportedReady opened.cursor.callGeneration
        opened.cursor.predicate opened.cursor.arguments
        opened.cursor.bindings argsv args res executableRest binding qterm
        bodyBarrier [] readyClauses (startCounter + 1) altTail
        pending.persistent.counter) :
    readyClauses = [] ∧
      altTail = [] ∧
      pending.persistent.counter = startCounter + 1 ∧
      (unifyFailureSuccessor state).toConf =
        PLeaTTa.pull
          { state.toConf with
            cur := none
            alts := pending.outer.alts
            barriers := pending.outer.barriers } ∧
      (unifyFailureSuccessor state).persistent = state.persistent ∧
      (unifyFailureSuccessor state).frames = pending.frames := by
  rcases
      PLeaTTa.PrologHeadFailureContinuationBridge.RepresentativeSupportedReady.exhausted_shape
        ready with
    ⟨clausesEmpty, altsEmpty, counterExact⟩
  have activeAlts :
      state.toConf.alts =
        PLeaTTa.Alt.barrier :: pending.outer.alts := by
    change state.control.alts =
      PLeaTTa.Alt.barrier :: pending.outer.alts
    simpa [altsEmpty] using agreement.retainedAlts
  have activeBarriers :
      state.toConf.barriers =
        PLeaTTa.pushBarrierCache pending.outer.barriers := by
    change state.control.barriers =
      PLeaTTa.pushBarrierCache pending.outer.barriers
    exact agreement.retainedBarriers
  let resumedBase : PLeaTTa.Conf :=
    { state.toConf with barriers := pending.outer.barriers }
  have activeConf :
      { state.toConf with cur := none } =
        { resumedBase with
          cur := none
          alts := PLeaTTa.Alt.barrier :: pending.outer.alts
          barriers := PLeaTTa.pushBarrierCache resumedBase.barriers } := by
    apply PLeaTTa.Conf.ext <;>
      simp [resumedBase, activeAlts, activeBarriers]
  have successor :
      (unifyFailureSuccessor state).toConf =
        PLeaTTa.pull
          { state.toConf with
            cur := none
            alts := pending.outer.alts
            barriers := pending.outer.barriers } := by
    calc
      (unifyFailureSuccessor state).toConf =
          PLeaTTa.pull { state.toConf with cur := none } := by
            rfl
      _ =
          PLeaTTa.pull
            { resumedBase with
              cur := none
              alts := PLeaTTa.Alt.barrier :: pending.outer.alts
              barriers := PLeaTTa.pushBarrierCache resumedBase.barriers } := by
            rw [activeConf]
      _ =
          PLeaTTa.pull
            { resumedBase with
              cur := none
              alts := pending.outer.alts } := by
            exact PLeaTTa.pull_barrier resumedBase pending.outer.alts
      _ =
          PLeaTTa.pull
            { state.toConf with
              cur := none
              alts := pending.outer.alts
              barriers := pending.outer.barriers } := by
            rfl
  refine
    ⟨clausesEmpty, altsEmpty, counterExact, successor,
      unifyFailureSuccessor_persistent state, ?_⟩
  simp [unifyFailureSuccessor, agreement.frames]

/-- Persistent change makes the stale-entry restoration model observably
different from the real failure successor.

This is the negative guard for the exhausted endpoint: its use of the current
persistent component is not cosmetic record spelling. -/
theorem changed_persistent_state_rejects_stale_restore
    (state : OpenConf) (entryPersistent : Persistent)
    (changed : state.persistent ≠ entryPersistent) :
    unifyFailureSuccessor state ≠
      { unifyFailureSuccessor state with
        persistent := entryPersistent } := by
  intro same
  apply changed
  calc
    state.persistent = (unifyFailureSuccessor state).persistent := by
      simp
    _ = entryPersistent := by
      simpa using congrArg OpenConf.persistent same

end PLeaTTa.PrologBodyFailureBacktrackingBridge
