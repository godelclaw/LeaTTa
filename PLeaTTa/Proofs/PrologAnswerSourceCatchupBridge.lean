-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologAnswerSourceCatchupBridge
Purpose: Realize classified answer-origin pull landings as exact source steps
Trusted boundary: none
Main exports: SilentStepsN, CompletesN
-/
import PLeaTTa.Proofs.PrologAnswerPullClassificationBridge
import PLeaTTa.Proofs.PrologRepresentativeCallFrontierBridge

namespace PLeaTTa.PrologAnswerSourceCatchupBridge

open Metta (Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.Resolver
open PLeaTTa.PrologAnswerPullClassificationBridge
open PLeaTTa.PrologAnswerOriginBridge
open PLeaTTa.PrologAnswerResourceBridge
open PLeaTTa.PrologActivationMacro
open PLeaTTa.PrologCallPayloadBridge
open PLeaTTa.PrologPrefilterScanBridge
open PLeaTTa.PrologProductResourceContextBridge
open PLeaTTa.PrologRepresentativeCallFrontierBridge
open PLeaTTa.PrologSupportedCursorAlternativeBridge

/-!
# Counted source-control prefixes

The executable answer successor performs one eager `pull`.  The independent
source reaches the same conservative occurrence through a finite sequence of
administrative backtracking steps.  Those steps are silent but must not be
quotiented away: their exact count is part of divergence-sensitive adequacy.

`SilentStepsN` retains the raw, non-committing transition at every position.
`CompletesN` separately retains the unique final `[.completed]` step.  This
distinction lets an enclosing choice consume exactly that completion while a
cut boundary or product propagates it. -/

/-- Exactly counted, session-preserving, observation-free source steps which
remain in the running state. -/
inductive SilentStepsN (session : Session) : Nat -> Search -> Search -> Prop where
  | zero (search : Search) : SilentStepsN session 0 search search
  | succ (count : Nat) (start middle finish : Search)
      (head : RawStep session start [] .none session (.running middle))
      (tail : SilentStepsN session count middle finish) :
      SilentStepsN session (count + 1) start finish

namespace SilentStepsN

/-- Forget only the raw-step spelling; transition count, empty observation
trace, session, and source endpoints remain exact. -/
theorem toStepsN {session : Session} {count : Nat} {start finish : Search}
    (execution : SilentStepsN session count start finish) :
    StepsN count (.running session start) [] (.running session finish) := by
  induction execution with
  | zero search => exact .zero _
  | succ count start middle finish head tail inductionHypothesis =>
      have transition :
          Transition (.running session start) [] (.running session middle) :=
        .ordinary start [] session session (.running middle) head
      simpa using
        (StepsN.succ count (.running session start) (.running session middle)
          (.running session finish) [] [] transition inductionHypothesis)

/-- Silent raw prefixes compose without hiding either count. -/
theorem trans {session : Session} {firstCount secondCount : Nat}
    {start middle finish : Search}
    (first : SilentStepsN session firstCount start middle)
    (second : SilentStepsN session secondCount middle finish) :
    SilentStepsN session (firstCount + secondCount) start finish := by
  induction first with
  | zero search => simpa using second
  | succ count start next middle head tail inductionHypothesis =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        SilentStepsN.succ (count + secondCount) start next finish head
          (inductionHypothesis second)

/-- Silent progress in the active left branch preserves an inactive choice
literally; the right branch is neither inspected nor reordered. -/
theorem underChoice {session : Session} {count : Nat}
    {start finish right : Search} (scope : CutScopeId)
    (execution : SilentStepsN session count start finish) :
    SilentStepsN session count (.choice scope start right)
      (.choice scope finish right) := by
  induction execution with
  | zero search => exact .zero _
  | succ count start middle finish head tail inductionHypothesis =>
      exact .succ count _ _ _
        (.choiceProgress scope start right middle [] session session head)
        inductionHypothesis

/-- Silent progress crosses a cut boundary without changing its identity. -/
theorem underCutBoundary {session : Session} {count : Nat}
    {start finish : Search} (scope : CutScopeId)
    (execution : SilentStepsN session count start finish) :
    SilentStepsN session count (.cutBoundary scope start)
      (.cutBoundary scope finish) := by
  induction execution with
  | zero search => exact .zero _
  | succ count start middle finish head tail inductionHypothesis =>
      exact .succ count _ _ _
        (.cutBoundaryProgress scope start middle [] session session head)
        inductionHypothesis

/-- Silent progress crosses an exception boundary without selecting a handler.
The protected goal remains running, so no catcher matching occurs. -/
theorem underCatchBoundary {session : Session} {count : Nat}
    {start finish : Search} (handlerScope : ExceptionScopeId)
    (scope : CutScopeId) (catcher : Term)
    (handler : PeTTaSpec.PrologCore.Goal)
    (entryBindings : OpenSubstitution.Substitution)
    (execution : SilentStepsN session count start finish) :
    SilentStepsN session count
      (.catchBoundary handlerScope scope start catcher handler entryBindings)
      (.catchBoundary handlerScope scope finish catcher handler
        entryBindings) := by
  induction execution with
  | zero search => exact .zero _
  | succ count start middle finish head tail inductionHypothesis =>
      exact .succ count _ _ _
        (.catchProgress handlerScope scope start middle catcher handler
          entryBindings [] .none session session head)
        inductionHypothesis

/-- Silent, answer-free progress inside a collector preserves its private
accumulator and caller continuation literally. -/
theorem underCollectionBoundary {session : Session} {count : Nat}
    {start finish : Search} (collectionScope : CollectionScopeId)
    (callerScope : CutScopeId) (template output : Term)
    (entryBindings : OpenSubstitution.Substitution)
    (tail : List PeTTaSpec.PrologCore.Goal) (reversed : List Term)
    (execution : SilentStepsN session count start finish) :
    SilentStepsN session count
      (.collectionBoundary collectionScope callerScope start template output
        entryBindings tail reversed)
      (.collectionBoundary collectionScope callerScope finish template output
        entryBindings tail reversed) := by
  induction execution with
  | zero search => exact .zero _
  | succ count start middle finish head rest inductionHypothesis =>
      exact .succ count _ _ _
        (.collectionProgress collectionScope callerScope start middle template
          output entryBindings tail reversed [] .none session session head
          (by simp [Trace.AnswerFree]))
        inductionHypothesis

/-- Silent, answer-free progress in a product head preserves its caller tail;
the tail is carried but never executed by this lift. -/
theorem underProduct {session : Session} {count : Nat}
    {start finish : Search} (scope : CutScopeId)
    (tail : List PeTTaSpec.PrologCore.Goal)
    (execution : SilentStepsN session count start finish) :
    SilentStepsN session count (.product scope start tail)
      (.product scope finish tail) := by
  induction execution with
  | zero search => exact .zero _
  | succ count start middle finish head rest inductionHypothesis =>
      exact .succ count _ _ _
        (.productProgress scope start middle tail [] .none session session head
          (by simp [Trace.AnswerFree]))
        inductionHypothesis

end SilentStepsN

/-- Exactly counted source execution whose sole public observation is the
final completion.  Earlier steps are raw, silent, and remain running. -/
inductive CompletesN (session : Session) : Nat -> Search -> Prop where
  | now (search : Search)
      (step : RawStep session search [.completed] .none session
        (.terminal .completed)) :
      CompletesN session 1 search
  | step (count : Nat) (start middle : Search)
      (head : RawStep session start [] .none session (.running middle))
      (tail : CompletesN session count middle) :
      CompletesN session (count + 1) start

namespace CompletesN

/-- The raw completion discipline realizes the exact public singleton trace. -/
theorem toStepsN {session : Session} {count : Nat} {search : Search}
    (execution : CompletesN session count search) :
    StepsN count (.running session search) [.completed]
      (.terminal session .completed) := by
  induction execution with
  | now search step =>
      have transition :
          Transition (.running session search) [.completed]
            (.terminal session .completed) :=
        .ordinary search [.completed] session session (.terminal .completed)
          step
      simpa using
        (StepsN.succ 0 (.running session search)
          (.terminal session .completed) (.terminal session .completed)
          [.completed] [] transition (.zero _))
  | step count start middle head tail inductionHypothesis =>
      have transition :
          Transition (.running session start) [] (.running session middle) :=
        .ordinary start [] session session (.running middle) head
      simpa using
        (StepsN.succ count (.running session start) (.running session middle)
          (.terminal session .completed) [] [.completed] transition
          inductionHypothesis)

/-- A silent running prefix may precede an exact completion without changing
the unique public event. -/
theorem prepend {session : Session} {silentCount completeCount : Nat}
    {start middle : Search}
    (leading : SilentStepsN session silentCount start middle)
    (completion : CompletesN session completeCount middle) :
    CompletesN session (silentCount + completeCount) start := by
  induction leading with
  | zero search => simpa using completion
  | succ count start next middle head tail inductionHypothesis =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        CompletesN.step (count + completeCount) start next head
          (inductionHypothesis completion)

/-- An enclosing choice consumes exactly the child's final completion and
switches to its right branch without publishing that completion. -/
theorem choiceToRight {session : Session} {count : Nat}
    {left right : Search} (scope : CutScopeId)
    (completion : CompletesN session count left) :
    SilentStepsN session count (.choice scope left right) right := by
  induction completion with
  | now search step =>
      exact .succ 0 _ _ _
        (.choiceComplete scope search right session session step) (.zero _)
  | step count start middle head tail inductionHypothesis =>
      exact .succ count _ _ _
        (.choiceProgress scope start right middle [] session session head)
        inductionHypothesis

/-- A cut boundary propagates the child's exact completion rather than
consuming it. -/
theorem underCutBoundary {session : Session} {count : Nat}
    {search : Search} (scope : CutScopeId)
    (completion : CompletesN session count search) :
    CompletesN session count (.cutBoundary scope search) := by
  induction completion with
  | now search step =>
      exact .now _
        (.cutBoundaryComplete scope search session session step)
  | step count start middle head tail inductionHypothesis =>
      exact .step count _ _
        (.cutBoundaryProgress scope start middle [] session session head)
        inductionHypothesis

/-- Product completion propagates the head's singleton completion and
discards, rather than executes, the caller tail. -/
theorem underProduct {session : Session} {count : Nat}
    {search : Search} (scope : CutScopeId)
    (tail : List PeTTaSpec.PrologCore.Goal)
    (completion : CompletesN session count search) :
    CompletesN session count (.product scope search tail) := by
  induction completion with
  | now search step =>
      exact .now _
        (.productComplete scope search tail [.completed] session session step
          (by simp [Trace.AnswerFree]))
  | step count start middle head rest inductionHypothesis =>
      exact .step count _ _
        (.productProgress scope start middle tail [] .none session session head
          (by simp [Trace.AnswerFree]))
        inductionHypothesis

end CompletesN

/-! ## Exact conservative cursor landing -/

/-- Rejected prepared occurrences form exactly the silent source prefix used
by answer backtracking.  The final cursor is not guessed from the executable
bank; it is the indexed endpoint of `RejectedPullsN`. -/
theorem RejectedPullsN.toSilentStepsN
    {count : Nat} {before after : PreparedCursor}
    (pulls : RejectedPullsN count before after)
    (scope : CutScopeId) (session : Session) :
    SilentStepsN session count (.clauses scope before)
      (.clauses scope after) := by
  induction pulls with
  | zero cursor => exact .zero _
  | succ count cursor branch branches finish remaining clash tail
      inductionHypothesis =>
      have pulled :
          LocalPull cursor (.silent (cursor.advance branch branches)) :=
        .rejected cursor branch branches remaining clash
      have head :
          RawStep session (.clauses scope cursor) [] .none session
            (.running
              (.clauses scope (cursor.advance branch branches))) := by
        simpa [localPullEvents, localPullTarget] using
          (RawStep.clausesPull scope cursor
            (.silent (cursor.advance branch branches)) session pulled)
      exact .succ count _ _ _ head inductionHypothesis

/-- The strongest honest source endpoint before full head unification.

The executable head selected by `pullAux` and the supported first occurrence
of the source ready suffix are tied through one literal alternative bank.
This fixes occurrence identity, order, continuation, seed, and body support,
but deliberately says nothing about `HeadResolution`: a conservatively
retained occurrence can still be a false positive. -/
structure SelectedReadyFrontier
    (alpha : List (LogicVar × String))
    (resource : RetainedAlternativeSegment)
    (selectedGoals : List PLeaTTa.Goal) (selectedBinding : Subst)
    (selectedTail : List PLeaTTa.Alt)
    (callStart original finish : PreparedCursor) (startPosition : Nat)
    (candidates : List PLeaTTa.Clause) : Type where
  ownership : resource.Owns alpha callStart original startPosition
  /-- The exact executable candidate bank owned at this cursor before the
  rejected source prefix is consumed.  Naming it here prevents the ready
  suffix below from being supplied independently of the scan which produced
  `resource.alts`. -/
  originalCandidates : List PLeaTTa.Clause
  skippedCandidates : List PLeaTTa.Clause
  originalSupported :
    List.Forall₂
      (SupportedPreparedCandidateAgrees original.callGeneration
        original.predicate original.arguments original.bindings)
      original.remaining originalCandidates
  originalArities :
    ∀ clause, clause ∈ originalCandidates →
      clause.params.length = resource.argsv.length
  originalScan :
    ResolutionScan resource.argsv resource.args resource.res resource.rest
      resource.binding resource.qterm resource.barrier originalCandidates
      resource.counter resource.alts resource.finalCounter
  rejectedCount : Nat
  rejectedPulls : RejectedPullsN rejectedCount original finish
  originalCandidatesExact :
    originalCandidates = skippedCandidates ++ candidates
  positioned :
    CallScopedCursorPosition callStart finish
      (startPosition + rejectedCount)
  selected :
    resource.alts = .br selectedGoals selectedBinding :: selectedTail
  context :
    CursorCallContext finish original.callGeneration original.predicate
      original.arguments original.bindings
  ready :
    RepresentativeSupportedReady original.callGeneration original.predicate
      original.arguments original.bindings resource.argsv resource.args
      resource.res resource.rest resource.binding resource.qterm
      resource.barrier finish.remaining candidates resource.counter
      resource.alts resource.finalCounter
  readyArities :
    ∀ clause, clause ∈ candidates →
      clause.params.length = resource.argsv.length

namespace SelectedReadyFrontier

/-- The executable prefix removed by the shared scan has exactly the same
length as the independently executed source rejection prefix.  The equality
is derived from the two positional spines rather than stored as a second
potentially drifting assertion. -/
theorem skippedCandidates_count
    {alpha : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
    {selectedTail : List PLeaTTa.Alt}
    {callStart original finish : PreparedCursor} {startPosition : Nat}
    {candidates : List PLeaTTa.Clause}
    (frontier :
      SelectedReadyFrontier alpha resource selectedGoals selectedBinding
        selectedTail callStart original finish startPosition candidates) :
    frontier.skippedCandidates.length = frontier.rejectedCount := by
  have sourceLength :
      original.remaining.length = frontier.originalCandidates.length :=
    frontier.originalSupported.length_eq
  have finishRemaining := frontier.rejectedPulls.remaining_eq_drop
  have readyLength : finish.remaining.length = candidates.length :=
    frontier.ready.length_eq
  have splitLength := congrArg List.length frontier.originalCandidatesExact
  simp only [List.length_append] at splitLength
  have countBound := frontier.rejectedPulls.count_le_remaining_length
  rw [finishRemaining, List.length_drop] at readyLength
  omega

/-- Every executable occurrence in the removed positional prefix was truly
skipped by the conservative scan.  This maximality fact is derived by
comparing the full scan and ready-suffix scan at the same counter and output;
a retained prefix occurrence would necessarily advance the counter. -/
theorem skippedCandidates_retainedCount_zero
    {alpha : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
    {selectedTail : List PLeaTTa.Alt}
    {callStart original finish : PreparedCursor} {startPosition : Nat}
    {candidates : List PLeaTTa.Clause}
    (frontier :
      SelectedReadyFrontier alpha resource selectedGoals selectedBinding
        selectedTail callStart original finish startPosition candidates) :
    retainedClauseCount resource.argsv
        (PLeaTTa.subst resource.binding resource.res)
        frontier.skippedCandidates = 0 := by
  have fullCounter := frontier.originalScan.counter_exact
  have suffixCounter := frontier.ready.scan.counter_exact
  rw [frontier.originalCandidatesExact] at fullCounter
  simp only [retainedClauseCount, List.filter_append,
    List.length_append] at fullCounter
  simp only [retainedClauseCount] at suffixCounter
  change
    (frontier.skippedCandidates.filter
      (resolutionClauseRetained resource.argsv
        (PLeaTTa.subst resource.binding resource.res))).length = 0
  omega

/-- Pointwise form of `skippedCandidates_retainedCount_zero`: membership in
the removed executable prefix carries the literal Boolean rejection used by
the scan. -/
theorem skippedCandidate_rejected
    {alpha : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
    {selectedTail : List PLeaTTa.Alt}
    {callStart original finish : PreparedCursor} {startPosition : Nat}
    {candidates : List PLeaTTa.Clause}
    (frontier :
      SelectedReadyFrontier alpha resource selectedGoals selectedBinding
        selectedTail callStart original finish startPosition candidates)
    {clause : PLeaTTa.Clause}
    (member : clause ∈ frontier.skippedCandidates) :
    resolutionClauseRetained resource.argsv
        (PLeaTTa.subst resource.binding resource.res) clause = false := by
  cases retained : resolutionClauseRetained resource.argsv
      (PLeaTTa.subst resource.binding resource.res) clause with
  | false => rfl
  | true =>
      have inFilter :
          clause ∈ frontier.skippedCandidates.filter
            (resolutionClauseRetained resource.argsv
              (PLeaTTa.subst resource.binding resource.res)) := by
        exact List.mem_filter.mpr ⟨member, by simp [retained]⟩
      have positive :
          0 <
            (frontier.skippedCandidates.filter
              (resolutionClauseRetained resource.argsv
                (PLeaTTa.subst resource.binding resource.res))).length :=
        List.length_pos_of_mem inFilter
      exact False.elim
        (by
          have zero :
              (frontier.skippedCandidates.filter
                (resolutionClauseRetained resource.argsv
                  (PLeaTTa.subst resource.binding resource.res))).length = 0 := by
            simpa [retainedClauseCount] using
              frontier.skippedCandidates_retainedCount_zero
          omega)

/-- The source cursor and executable candidate bank advance by the same
occurrence count.  This is an equality of literal suffixes, so duplicate
candidate values remain distinguished by their position in the frozen bank.
-/
theorem candidate_remaining_eq_drop
    {alpha : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
    {selectedTail : List PLeaTTa.Alt}
    {callStart original finish : PreparedCursor} {startPosition : Nat}
    {candidates : List PLeaTTa.Clause}
    (frontier :
      SelectedReadyFrontier alpha resource selectedGoals selectedBinding
        selectedTail callStart original finish startPosition candidates) :
    candidates =
      frontier.originalCandidates.drop frontier.rejectedCount := by
  rw [frontier.originalCandidatesExact,
    ← frontier.skippedCandidates_count]
  simp

/-- A selected bank rules out the exhausted ready constructor and exposes the
exact source branch/executable clause occurrence at the frontier. -/
theorem head_exact
    {alpha : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
    {selectedTail : List PLeaTTa.Alt}
    {callStart original finish : PreparedCursor} {startPosition : Nat}
    {candidates : List PLeaTTa.Clause}
    (frontier :
      SelectedReadyFrontier alpha resource selectedGoals selectedBinding
        selectedTail callStart original finish startPosition candidates) :
    exists branch clause branchTail clauseTail altTail,
      finish.remaining = branch :: branchTail /\
      candidates = clause :: clauseTail /\
      resource.alts =
        resolutionAlt resource.argsv resource.args resource.res resource.rest
          resource.binding resource.qterm resource.barrier resource.counter
          clause :: altTail /\
      resource.alts = .br selectedGoals selectedBinding :: selectedTail /\
      SupportedPreparedCandidateAgrees original.callGeneration
        original.predicate original.arguments original.bindings branch clause /\
      clause.params.length = resource.argsv.length /\
      resolutionClauseRetained resource.argsv
        (PLeaTTa.subst resource.binding resource.res) clause = true /\
      List.Forall₂
        (SupportedPreparedCandidateAgrees original.callGeneration
          original.predicate original.arguments original.bindings)
        branchTail clauseTail /\
      ResolutionScan resource.argsv resource.args resource.res resource.rest
        resource.binding resource.qterm resource.barrier clauseTail
        (resource.counter + 1) altTail resource.finalCounter := by
  have altsNonempty : resource.alts ≠ [] := by
    rw [frontier.selected]
    simp
  have branchesNonempty : finish.remaining ≠ [] :=
    frontier.ready.branches_nonempty_of_alts_nonempty altsNonempty
  obtain
    ⟨branch, clause, branchTail, clauseTail, altTail,
      remaining, candidatesEq, altsEq, supported, arity, kept,
      tailSupported, tailScan⟩ :=
    frontier.ready.retained_shape branchesNonempty
  exact
    ⟨branch, clause, branchTail, clauseTail, altTail, remaining,
      candidatesEq, altsEq, frontier.selected, supported, arity, kept,
      tailSupported, tailScan⟩

/-- A positioned ready frontier identifies the exact supported source clause
occurrence at the absolute index in the immutable call-start bank.  This is
stronger than identifying the clause payload: duplicate payloads remain
distinguished by their consumed-prefix lengths. -/
theorem source_occurrence_at
    {alpha : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
    {selectedTail : List PLeaTTa.Alt}
    {callStart original finish : PreparedCursor}
    {startPosition finishPosition : Nat}
    {candidates : List PLeaTTa.Clause}
    (positioned :
      CallScopedCursorPosition callStart finish finishPosition)
    (frontier :
      SelectedReadyFrontier alpha resource selectedGoals selectedBinding
        selectedTail callStart original finish startPosition candidates) :
    exists consumed branch clause branchTail clauseTail,
      callStart.remaining = consumed ++ (branch :: branchTail) /\
      consumed.length = finishPosition /\
      finish.remaining = branch :: branchTail /\
      candidates = clause :: clauseTail /\
      SupportedPreparedCandidateAgrees original.callGeneration
        original.predicate original.arguments original.bindings branch clause := by
  obtain
    ⟨branch, clause, branchTail, clauseTail, _altTail, remaining,
      candidatesEq, _altsEq, _selected, supported, _arity, _kept,
      _tailSupported, _tailScan⟩ := frontier.head_exact
  obtain ⟨consumed, callStartEq, positionEq⟩ :=
    positioned.selectedOccurrence remaining
  exact
    ⟨consumed, branch, clause, branchTail, clauseTail, callStartEq,
      positionEq, remaining, candidatesEq, supported⟩

end SelectedReadyFrontier

namespace RetainedAlternativeSegment

/-- A selected marker-free resource advances the source cursor through its
maximal definitely rejected prefix and lands at the exact supported
occurrence selected by the executable bank.  The returned call-scoped
coordinate counts every rejected source occurrence, even though those
occurrences contributed no executable alternative and did not advance the
resolution counter. -/
theorem catchupSelectedAt
    {alpha : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {callStart cursor : PreparedCursor} {position : Nat}
    {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
    {selectedTail : List PLeaTTa.Alt}
    (ownership : resource.Owns alpha callStart cursor position)
  (selected :
      resource.alts = .br selectedGoals selectedBinding :: selectedTail)
    (scope : CutScopeId) (session : Session) :
    exists finish readyClauses,
      exists frontier :
          SelectedReadyFrontier alpha resource selectedGoals selectedBinding
            selectedTail callStart cursor finish position readyClauses,
        SilentStepsN session frontier.rejectedCount (.clauses scope cursor)
          (.clauses scope finish) /\
        CallScopedCursorPosition callStart finish
          (position + frontier.rejectedCount) := by
  rcases ownership.scan with
    ⟨candidates, wellFormed, query, substitutedArgs, supported, arities,
      scan⟩
  obtain
    ⟨count, skippedBranches, skippedClauses, finish,
      readyBranches, readyClauses, branchesEq, clausesEq,
      branchCount, clauseCount, pulls, finishRemaining, finishContext,
      ready⟩ :=
    ResolutionScan.decomposeRepresentativeRejectedPrefix scan supported query
      wellFormed (.refl cursor) (.refl cursor) rfl
      (fun _ member => member) arities
  have readyAtFinish :
      RepresentativeSupportedReady cursor.callGeneration cursor.predicate
        cursor.arguments cursor.bindings resource.argsv resource.args
        resource.res resource.rest resource.binding resource.qterm
        resource.barrier finish.remaining readyClauses resource.counter
        resource.alts resource.finalCounter := by
    simpa only [finishRemaining] using ready
  exact
    ⟨finish, readyClauses,
      { ownership := ownership
        originalCandidates := candidates
        skippedCandidates := skippedClauses
        originalSupported := supported
        originalArities := arities
        originalScan := scan
        rejectedCount := count
        rejectedPulls := pulls
        originalCandidatesExact := clausesEq
        positioned :=
          CallScopedCursorPosition.afterRejected pulls ownership.positioned
        selected := selected
        context := finishContext
        ready := readyAtFinish
        readyArities := by
          intro clause member
          apply arities clause
          rw [clausesEq]
          simp [member] },
      PLeaTTa.PrologAnswerSourceCatchupBridge.RejectedPullsN.toSilentStepsN
        pulls scope session,
      CallScopedCursorPosition.afterRejected pulls ownership.positioned⟩

/-- An owned marker-free resource with no executable branch consumes every
prepared occurrence silently and then performs one genuine exhausted-cursor
completion. -/
theorem catchupEmpty
    {alpha : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {callStart cursor : PreparedCursor} {position : Nat}
    (ownership : resource.Owns alpha callStart cursor position)
    (empty : resource.alts = [])
    (scope : CutScopeId) (session : Session) :
    exists count,
      CompletesN session count (.clauses scope cursor) := by
  rcases ownership.scan with
    ⟨candidates, wellFormed, query, substitutedArgs, supported, arities,
      scan⟩
  obtain
    ⟨count, skippedBranches, skippedClauses, finish,
      readyBranches, readyClauses, branchesEq, clausesEq,
      branchCount, clauseCount, pulls, finishRemaining, finishContext,
      ready⟩ :=
    ResolutionScan.decomposeRepresentativeRejectedPrefix scan supported query
      wellFormed (.refl cursor) (.refl cursor) rfl
      (fun _ member => member) arities
  have readyBranchesEmpty : readyBranches = [] := by
    by_contra nonempty
    obtain
      ⟨branch, clause, branchTail, clauseTail, altTail,
        remaining, candidatesEq, altsEq, supported, arity, kept,
        tailSupported, tailScan⟩ :=
      ready.retained_shape nonempty
    rw [empty] at altsEq
    simp at altsEq
  have finishEmpty : finish.remaining = [] :=
    finishRemaining.trans readyBranchesEmpty
  have exhausted :
      RawStep session (.clauses scope finish) [.completed] .none session
        (.terminal .completed) := by
    simpa [localPullEvents, localPullTarget] using
      (RawStep.clausesPull scope finish .exhausted session
        (.exhausted finish finishEmpty))
  exact
    ⟨count + 1,
      CompletesN.prepend
        (PLeaTTa.PrologAnswerSourceCatchupBridge.RejectedPullsN.toSilentStepsN
          pulls scope session)
        (.now _ exhausted)⟩

end RetainedAlternativeSegment

/-! ## Mutual realization of classified answer origins -/

/-- A source search focused at the exact conservative occurrence selected by
the executable pull.  Wrapper constructors retain every source-control node
which remains active at the landing; a consumed choice is intentionally
absent.  The local constructor carries the branch-indexed supported frontier
and its absolute call-start position, so later head success/failure can attach
without rediscovering or conflating a duplicate occurrence. -/
inductive ConservativeReadyTarget
    (alpha : List (LogicVar × String))
    (selectedGoals : List PLeaTTa.Goal) (selectedBinding : Subst) :
    List PLeaTTa.Alt -> Search -> Prop where
  | clauses (scope : CutScopeId)
      (callStart original finish : PreparedCursor)
      (startPosition finishPosition : Nat)
      (positioned :
        CallScopedCursorPosition callStart finish finishPosition)
      (resource : RetainedAlternativeSegment)
      (selectedTail : List PLeaTTa.Alt)
      (candidates : List PLeaTTa.Clause)
      (frontier :
        SelectedReadyFrontier alpha resource selectedGoals selectedBinding
          selectedTail callStart original finish startPosition candidates) :
      ConservativeReadyTarget alpha selectedGoals selectedBinding selectedTail
        (.clauses scope finish)
  | taskChoices (support : List (LogicVar × String))
      (scope : CutScopeId) (barrier : Nat)
      (canonical : Canonical.TreeSubstitution)
      (referenceBase current : OpenSubstitution.Substitution)
      (right : Search) (selectedTail : List PLeaTTa.Alt)
      (choices :
        TaskChoiceAlternativeRegionAgrees alpha support scope barrier canonical
          referenceBase current selectedBinding right
          (.br selectedGoals selectedBinding :: selectedTail)) :
      ConservativeReadyTarget alpha selectedGoals selectedBinding selectedTail
        right
  | underChoice (scope : CutScopeId) (inside right : Search)
      {selectedTail : List PLeaTTa.Alt}
      (target : ConservativeReadyTarget alpha selectedGoals selectedBinding
        selectedTail inside) :
      ConservativeReadyTarget alpha selectedGoals selectedBinding selectedTail
        (.choice scope inside right)
  | underCutBoundary (scope : CutScopeId) (inside : Search)
      {selectedTail : List PLeaTTa.Alt}
      (target : ConservativeReadyTarget alpha selectedGoals selectedBinding
        selectedTail inside) :
      ConservativeReadyTarget alpha selectedGoals selectedBinding selectedTail
        (.cutBoundary scope inside)
  | underCatchBoundary (handlerScope : ExceptionScopeId) (scope : CutScopeId)
      (inside : Search) (catcher : Term)
      (handler : PeTTaSpec.PrologCore.Goal)
      (entryBindings : OpenSubstitution.Substitution)
      {selectedTail : List PLeaTTa.Alt}
      (target : ConservativeReadyTarget alpha selectedGoals selectedBinding
        selectedTail inside) :
      ConservativeReadyTarget alpha selectedGoals selectedBinding selectedTail
        (.catchBoundary handlerScope scope inside catcher handler
          entryBindings)
  | underCollectionBoundary (collectionScope : CollectionScopeId)
      (callerScope : CutScopeId) (inside : Search) (template output : Term)
      (entryBindings : OpenSubstitution.Substitution)
      (tail : List PeTTaSpec.PrologCore.Goal) (reversed : List Term)
      {selectedTail : List PLeaTTa.Alt}
      (target : ConservativeReadyTarget alpha selectedGoals selectedBinding
        selectedTail inside) :
      ConservativeReadyTarget alpha selectedGoals selectedBinding selectedTail
        (.collectionBoundary collectionScope callerScope inside template output
          entryBindings tail reversed)
  | underProduct (scope : CutScopeId) (inside : Search)
      (tail : List PeTTaSpec.PrologCore.Goal)
      {selectedTail : List PLeaTTa.Alt}
      (target : ConservativeReadyTarget alpha selectedGoals selectedBinding
        selectedTail inside) :
      ConservativeReadyTarget alpha selectedGoals selectedBinding selectedTail
        (.product scope inside tail)

/-- A source-ready frontier together with the literal older executable suffix
which remains behind that frontier's locally owned alternatives.

`fullTail` is exactly the tail returned by the fine machine's eager pull.
The source target owns only `localTail`; `suffix` records the older bank which
is still suspended outside that source frontier. -/
inductive ConservativeReadyPullTarget
    (alpha : List (LogicVar × String))
    (selectedGoals : List PLeaTTa.Goal) (selectedBinding : Subst)
    (fullTail : List PLeaTTa.Alt) (target : Search) : Prop where
  | mk (localTail suffix : List PLeaTTa.Alt)
      (tail_eq : fullTail = localTail ++ suffix)
      (ready :
        ConservativeReadyTarget alpha selectedGoals selectedBinding localTail
          target) :
      ConservativeReadyPullTarget alpha selectedGoals selectedBinding fullTail
        target

namespace ConservativeReadyPullTarget

/-- A ready frontier with no older executable suffix. -/
theorem exact
    {alpha : List (LogicVar × String)}
    {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
    {tail : List PLeaTTa.Alt} {target : Search}
    (ready :
      ConservativeReadyTarget alpha selectedGoals selectedBinding tail target) :
    ConservativeReadyPullTarget alpha selectedGoals selectedBinding tail
      target :=
  ⟨tail, [], by simp, ready⟩

/-- Append a literal older bank without changing the selected source
occurrence or its locally owned tail. -/
theorem appendSuffix
    {alpha : List (LogicVar × String)}
    {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
    {tail : List PLeaTTa.Alt} {target : Search}
    (agreement :
      ConservativeReadyPullTarget alpha selectedGoals selectedBinding tail
        target)
    (older : List PLeaTTa.Alt) :
    ConservativeReadyPullTarget alpha selectedGoals selectedBinding
      (tail ++ older) target := by
  cases agreement with
  | mk localTail suffix tailEq ready =>
      refine .mk localTail (suffix ++ older) ?_ ready
      rw [tailEq, List.append_assoc]

/-- Preserve the exact tail decomposition under an inactive choice. -/
theorem underChoice
    {alpha : List (LogicVar × String)}
    {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
    {tail : List PLeaTTa.Alt} {target right : Search}
    (scope : CutScopeId)
    (agreement :
      ConservativeReadyPullTarget alpha selectedGoals selectedBinding tail
        target) :
    ConservativeReadyPullTarget alpha selectedGoals selectedBinding tail
      (.choice scope target right) := by
  cases agreement with
  | mk localTail suffix tailEq ready =>
      exact .mk localTail suffix tailEq
        (.underChoice scope target right ready)

/-- Preserve the exact tail decomposition across a cut boundary. -/
theorem underCutBoundary
    {alpha : List (LogicVar × String)}
    {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
    {tail : List PLeaTTa.Alt} {target : Search}
    (scope : CutScopeId)
    (agreement :
      ConservativeReadyPullTarget alpha selectedGoals selectedBinding tail
        target) :
    ConservativeReadyPullTarget alpha selectedGoals selectedBinding tail
      (.cutBoundary scope target) := by
  cases agreement with
  | mk localTail suffix tailEq ready =>
      exact .mk localTail suffix tailEq
        (.underCutBoundary scope target ready)

/-- Preserve the exact tail decomposition across an exception boundary. -/
theorem underCatchBoundary
    {alpha : List (LogicVar × String)}
    {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
    {tail : List PLeaTTa.Alt} {target : Search}
    (handlerScope : ExceptionScopeId) (scope : CutScopeId)
    (catcher : Term) (handler : PeTTaSpec.PrologCore.Goal)
    (entryBindings : OpenSubstitution.Substitution)
    (agreement :
      ConservativeReadyPullTarget alpha selectedGoals selectedBinding tail
        target) :
    ConservativeReadyPullTarget alpha selectedGoals selectedBinding tail
      (.catchBoundary handlerScope scope target catcher handler
        entryBindings) := by
  cases agreement with
  | mk localTail suffix tailEq ready =>
      exact .mk localTail suffix tailEq
        (.underCatchBoundary handlerScope scope target catcher handler
          entryBindings ready)

/-- Preserve the exact tail decomposition inside an active collector. -/
theorem underCollectionBoundary
    {alpha : List (LogicVar × String)}
    {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
    {tail : List PLeaTTa.Alt} {target : Search}
    (collectionScope : CollectionScopeId) (callerScope : CutScopeId)
    (template output : Term) (entryBindings : OpenSubstitution.Substitution)
    (callerTail : List PeTTaSpec.PrologCore.Goal) (reversed : List Term)
    (agreement :
      ConservativeReadyPullTarget alpha selectedGoals selectedBinding tail
        target) :
    ConservativeReadyPullTarget alpha selectedGoals selectedBinding tail
      (.collectionBoundary collectionScope callerScope target template output
        entryBindings callerTail reversed) := by
  cases agreement with
  | mk localTail suffix tailEq ready =>
      exact .mk localTail suffix tailEq
        (.underCollectionBoundary collectionScope callerScope target template
          output entryBindings callerTail reversed ready)

/-- Preserve the exact tail decomposition in a product head. -/
theorem underProduct
    {alpha : List (LogicVar × String)}
    {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
    {tail : List PLeaTTa.Alt} {target : Search}
    (scope : CutScopeId) (callerTail : List PeTTaSpec.PrologCore.Goal)
    (agreement :
      ConservativeReadyPullTarget alpha selectedGoals selectedBinding tail
        target) :
    ConservativeReadyPullTarget alpha selectedGoals selectedBinding tail
      (.product scope target callerTail) := by
  cases agreement with
  | mk localTail suffix tailEq ready =>
      exact .mk localTail suffix tailEq
        (.underProduct scope target callerTail ready)

end ConservativeReadyPullTarget

private def RightLandingRealizes
    (session : Session) {alpha : List (LogicVar × String)}
    {right : Search} {resources : List RetainedAlternativeSegment}
    {segment : List PLeaTTa.Alt}
    {agreement : RightAlternativeRegionAgrees alpha right resources segment}
    {goals : List PLeaTTa.Goal} {binding : Subst}
    {tail : List PLeaTTa.Alt}
    (_landing : RightRegionLanding alpha agreement goals binding tail) : Prop :=
  exists count target,
    SilentStepsN session count right target /\
    ConservativeReadyPullTarget alpha goals binding tail target

private def RightEmptyRealizes
    (session : Session) {alpha : List (LogicVar × String)}
    {right : Search} {resources : List RetainedAlternativeSegment}
    {segment : List PLeaTTa.Alt}
    {agreement : RightAlternativeRegionAgrees alpha right resources segment}
    (_empty : RightRegionEmpty alpha agreement) : Prop :=
  exists count, CompletesN session count right

private def OriginLandingRealizes
    (session : Session) {alpha : List (LogicVar × String)}
    {leafScope : CutScopeId} {bindings : OpenSubstitution.Substitution}
    {source next : Search}
    {origin : AnswerOrigin leafScope bindings source next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    {agreement :
      AnswerOriginResourceAgrees alpha origin beforeResources afterResources
        beforeAlts afterAlts}
    {goals : List PLeaTTa.Goal} {binding : Subst}
    {tail : List PLeaTTa.Alt}
    (_landing : OriginPrefixLanding alpha agreement goals binding tail) : Prop :=
  exists count target,
    SilentStepsN session count next target /\
    ConservativeReadyPullTarget alpha goals binding tail target

private def OriginFallsRealizes
    (session : Session) {alpha : List (LogicVar × String)}
    {leafScope : CutScopeId} {bindings : OpenSubstitution.Substitution}
    {source next : Search}
    {origin : AnswerOrigin leafScope bindings source next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    {agreement :
      AnswerOriginResourceAgrees alpha origin beforeResources afterResources
        beforeAlts afterAlts}
    (_falls : OriginPrefixFallsThrough alpha agreement) : Prop :=
  exists count, CompletesN session count next

private theorem realizeRightClauses
    {alpha : List (LogicVar × String)} (session : Session)
    (scope : CutScopeId) (callStart cursor : PreparedCursor)
    (position : Nat)
    (resource : RetainedAlternativeSegment)
    (ownership : resource.Owns alpha callStart cursor position)
    (goals : List PLeaTTa.Goal) (binding : Subst)
    (tail : List PLeaTTa.Alt)
    (head : resource.alts = .br goals binding :: tail)
    (pullExact :
      PLeaTTa.pullAux resource.alts =
        some (.branch goals binding, tail)) :
    RightLandingRealizes session
      (.clauses scope callStart cursor position resource ownership
        goals binding tail head pullExact) := by
  obtain ⟨finish, candidates, frontier, steps, finishPosition⟩ :=
    PLeaTTa.PrologAnswerSourceCatchupBridge.RetainedAlternativeSegment.catchupSelectedAt
      ownership head scope session
  exact
    ⟨frontier.rejectedCount, .clauses scope finish, steps,
      ConservativeReadyPullTarget.exact
        (.clauses scope callStart cursor finish position
          (position + frontier.rejectedCount)
          finishPosition resource tail candidates frontier)⟩

private theorem realizeRightScheduled
    {alpha : List (LogicVar × String)} (session : Session)
    (callerScope : CutScopeId)
    (callerTail : List PeTTaSpec.PrologCore.Goal)
    {leafScope : CutScopeId} {bindings : OpenSubstitution.Substitution}
    {head next : Search}
    (origin : AnswerOrigin leafScope bindings head next)
    (resources : List RetainedAlternativeSegment) (nonempty : resources ≠ [])
    (history :
      AnswerOriginResourceAgrees alpha origin resources []
        (flattenOwnedAlts resources []) [])
    (goals : List PLeaTTa.Goal) (binding : Subst)
    (tail : List PLeaTTa.Alt)
    (inside : OriginPrefixLanding alpha history goals binding tail)
    (pullExact :
      PLeaTTa.pullAux (flattenOwnedAlts resources []) =
        some (.branch goals binding, tail))
    (insideIH : OriginLandingRealizes session inside) :
    RightLandingRealizes session
      (.scheduled callerScope callerTail origin resources nonempty history
        goals binding tail inside pullExact) := by
  obtain ⟨count, target, steps, ready⟩ := insideIH
  exact
    ⟨count, .product callerScope target callerTail,
      steps.underProduct callerScope callerTail,
      ready.underProduct callerScope callerTail⟩

private theorem realizeRightTaskChoices
    {alpha : List (LogicVar × String)} (session : Session)
    (support : List (LogicVar × String))
    (scope : CutScopeId) (barrier : Nat)
    (canonical : Canonical.TreeSubstitution)
    (referenceBase current : OpenSubstitution.Substitution)
    (runtime : Subst) (right : Search)
    (goals : List PLeaTTa.Goal) (tail : List PLeaTTa.Alt)
    (choices :
      TaskChoiceAlternativeRegionAgrees alpha support scope barrier canonical
        referenceBase current runtime right (.br goals runtime :: tail))
    (pullExact :
      PLeaTTa.pullAux (.br goals runtime :: tail) =
        some (.branch goals runtime, tail)) :
    RightLandingRealizes session
      (.taskChoices support scope barrier canonical referenceBase current
        runtime right goals tail choices pullExact) := by
  exact
    ⟨0, right, .zero right,
      ConservativeReadyPullTarget.exact
        (.taskChoices support scope barrier canonical referenceBase current
          right tail choices)⟩

private theorem realizeRightEmptyClauses
    {alpha : List (LogicVar × String)} (session : Session)
    (scope : CutScopeId) (callStart cursor : PreparedCursor)
    (position : Nat)
    (resource : RetainedAlternativeSegment)
    (ownership : resource.Owns alpha callStart cursor position)
    (empty : resource.alts = [])
    (pullNone : PLeaTTa.pullAux resource.alts = none) :
    RightEmptyRealizes session
      (.clauses scope callStart cursor position resource ownership
        empty pullNone) := by
  exact
    PLeaTTa.PrologAnswerSourceCatchupBridge.RetainedAlternativeSegment.catchupEmpty
      ownership empty scope session

private theorem realizeRightEmptyScheduled
    {alpha : List (LogicVar × String)} (session : Session)
    (callerScope : CutScopeId)
    (callerTail : List PeTTaSpec.PrologCore.Goal)
    {leafScope : CutScopeId} {bindings : OpenSubstitution.Substitution}
    {head next : Search}
    (origin : AnswerOrigin leafScope bindings head next)
    (resources : List RetainedAlternativeSegment) (nonempty : resources ≠ [])
    (history :
      AnswerOriginResourceAgrees alpha origin resources []
        (flattenOwnedAlts resources []) [])
    (inside : OriginPrefixFallsThrough alpha history)
    (pullNone : PLeaTTa.pullAux (flattenOwnedAlts resources []) = none)
    (insideIH : OriginFallsRealizes session inside) :
    RightEmptyRealizes session
      (.scheduled callerScope callerTail origin resources nonempty history
        inside pullNone) := by
  obtain ⟨count, completion⟩ := insideIH
  exact ⟨count, completion.underProduct callerScope callerTail⟩

private theorem realizeOriginChoiceInside
    {alpha : List (LogicVar × String)} (session : Session)
    (scope : CutScopeId) (right : Search)
    {leafScope : CutScopeId} {bindings : OpenSubstitution.Substitution}
    {left next : Search}
    (insideOrigin : AnswerOrigin leafScope bindings left next)
    {beforeResources afterResources regionResources :
      List RetainedAlternativeSegment}
    {beforeAlts afterAlts regionAlts : List PLeaTTa.Alt}
    (insideAgreement :
      AnswerOriginResourceAgrees alpha insideOrigin beforeResources
        (regionResources ++ afterResources) beforeAlts
        (regionAlts ++ afterAlts))
    (regionAgreement :
      RightAlternativeRegionAgrees alpha right regionResources regionAlts)
    (goals : List PLeaTTa.Goal) (binding : Subst)
    (rest : List PLeaTTa.Alt)
    (inside : OriginPrefixLanding alpha insideAgreement goals binding rest)
    (pullExact :
      PLeaTTa.pullAux beforeAlts = some (.branch goals binding, rest))
    (insideIH : OriginLandingRealizes session inside) :
    OriginLandingRealizes session
      (.choiceInside scope right insideOrigin insideAgreement regionAgreement
        goals binding rest inside pullExact) := by
  obtain ⟨count, target, steps, ready⟩ := insideIH
  exact
    ⟨count, .choice scope target right, steps.underChoice scope,
      ready.underChoice scope⟩

private theorem realizeOriginChoiceRegion
    {alpha : List (LogicVar × String)} (session : Session)
    (scope : CutScopeId) (right : Search)
    {leafScope : CutScopeId} {bindings : OpenSubstitution.Substitution}
    {left next : Search}
    (insideOrigin : AnswerOrigin leafScope bindings left next)
    {beforeResources afterResources regionResources :
      List RetainedAlternativeSegment}
    {beforeAlts afterAlts regionAlts : List PLeaTTa.Alt}
    (insideAgreement :
      AnswerOriginResourceAgrees alpha insideOrigin beforeResources
        (regionResources ++ afterResources) beforeAlts
        (regionAlts ++ afterAlts))
    (regionAgreement :
      RightAlternativeRegionAgrees alpha right regionResources regionAlts)
    (goals : List PLeaTTa.Goal) (binding : Subst)
    (regionTail : List PLeaTTa.Alt)
    (insideEmpty : OriginPrefixFallsThrough alpha insideAgreement)
    (regionLive :
      RightRegionLanding alpha regionAgreement goals binding regionTail)
    (pullExact :
      PLeaTTa.pullAux beforeAlts =
        some (.branch goals binding, regionTail ++ afterAlts))
    (insideIH : OriginFallsRealizes session insideEmpty)
    (regionIH : RightLandingRealizes session regionLive) :
    OriginLandingRealizes session
      (.choiceRegion scope right insideOrigin insideAgreement regionAgreement
        goals binding regionTail insideEmpty regionLive pullExact) := by
  obtain ⟨insideCount, insideCompletion⟩ := insideIH
  obtain ⟨regionCount, target, regionSteps, ready⟩ := regionIH
  have enterRight :
      SilentStepsN session insideCount (.choice scope next right) right :=
    insideCompletion.choiceToRight scope
  exact
    ⟨insideCount + regionCount, target,
      enterRight.trans regionSteps, ready.appendSuffix afterAlts⟩

private theorem realizeOriginCut
    {alpha : List (LogicVar × String)} (session : Session)
    (scope : CutScopeId)
    {leafScope : CutScopeId} {bindings : OpenSubstitution.Substitution}
    {body next : Search}
    (insideOrigin : AnswerOrigin leafScope bindings body next)
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (insideAgreement :
      AnswerOriginResourceAgrees alpha insideOrigin beforeResources
        afterResources beforeAlts (.barrier :: afterAlts))
    (goals : List PLeaTTa.Goal) (binding : Subst)
    (rest : List PLeaTTa.Alt)
    (inside : OriginPrefixLanding alpha insideAgreement goals binding rest)
    (pullExact :
      PLeaTTa.pullAux beforeAlts = some (.branch goals binding, rest))
    (insideIH : OriginLandingRealizes session inside) :
    OriginLandingRealizes session
      (.cutBoundary scope insideOrigin insideAgreement goals binding rest inside
        pullExact) := by
  obtain ⟨count, target, steps, ready⟩ := insideIH
  exact
    ⟨count, .cutBoundary scope target, steps.underCutBoundary scope,
      ready.underCutBoundary scope⟩

private theorem realizeOriginTask
    {alpha : List (LogicVar × String)} (session : Session)
    (leafScope : CutScopeId) (bindings : OpenSubstitution.Substitution)
    (resources : List RetainedAlternativeSegment)
    (alts : List PLeaTTa.Alt)
    (pullEq : PLeaTTa.pullAux alts = PLeaTTa.pullAux alts) :
    OriginFallsRealizes (alpha := alpha) session
      (.task (alpha := alpha) leafScope bindings resources alts pullEq) := by
  exact ⟨1, .now .done (.done session)⟩

private theorem realizeOriginChoiceFalls
    {alpha : List (LogicVar × String)} (session : Session)
    (scope : CutScopeId) (right : Search)
    {leafScope : CutScopeId} {bindings : OpenSubstitution.Substitution}
    {left next : Search}
    (insideOrigin : AnswerOrigin leafScope bindings left next)
    {beforeResources afterResources regionResources :
      List RetainedAlternativeSegment}
    {beforeAlts afterAlts regionAlts : List PLeaTTa.Alt}
    (insideAgreement :
      AnswerOriginResourceAgrees alpha insideOrigin beforeResources
        (regionResources ++ afterResources) beforeAlts
        (regionAlts ++ afterAlts))
    (regionAgreement :
      RightAlternativeRegionAgrees alpha right regionResources regionAlts)
    (insideEmpty : OriginPrefixFallsThrough alpha insideAgreement)
    (regionEmpty : RightRegionEmpty alpha regionAgreement)
    (pullEq : PLeaTTa.pullAux beforeAlts = PLeaTTa.pullAux afterAlts)
    (insideIH : OriginFallsRealizes session insideEmpty)
    (regionIH : RightEmptyRealizes session regionEmpty) :
    OriginFallsRealizes session
      (.choice scope right insideOrigin insideAgreement regionAgreement
        insideEmpty regionEmpty pullEq) := by
  obtain ⟨insideCount, insideCompletion⟩ := insideIH
  obtain ⟨regionCount, regionCompletion⟩ := regionIH
  have enterRight :
      SilentStepsN session insideCount (.choice scope next right) right :=
    insideCompletion.choiceToRight scope
  exact
    ⟨insideCount + regionCount,
      CompletesN.prepend enterRight regionCompletion⟩

private theorem realizeOriginCutFalls
    {alpha : List (LogicVar × String)} (session : Session)
    (scope : CutScopeId)
    {leafScope : CutScopeId} {bindings : OpenSubstitution.Substitution}
    {body next : Search}
    (insideOrigin : AnswerOrigin leafScope bindings body next)
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (insideAgreement :
      AnswerOriginResourceAgrees alpha insideOrigin beforeResources
        afterResources beforeAlts (.barrier :: afterAlts))
    (insideEmpty : OriginPrefixFallsThrough alpha insideAgreement)
    (pullEq : PLeaTTa.pullAux beforeAlts = PLeaTTa.pullAux afterAlts)
    (insideIH : OriginFallsRealizes session insideEmpty) :
    OriginFallsRealizes session
      (.cutBoundary scope insideOrigin insideAgreement insideEmpty pullEq) := by
  obtain ⟨count, completion⟩ := insideIH
  exact ⟨count, completion.underCutBoundary scope⟩

private theorem realizeRightLanding
    {alpha : List (LogicVar × String)} (session : Session)
    {right : Search} {resources : List RetainedAlternativeSegment}
    {segment : List PLeaTTa.Alt}
    {agreement : RightAlternativeRegionAgrees alpha right resources segment}
    {goals : List PLeaTTa.Goal} {binding : Subst}
    {tail : List PLeaTTa.Alt}
    (landing : RightRegionLanding alpha agreement goals binding tail) :
    RightLandingRealizes session landing := by
  exact RightRegionLanding.rec
    (motive_1 := fun _ goals binding _ landing =>
      RightLandingRealizes session landing)
    (motive_2 := fun _ empty => RightEmptyRealizes session empty)
    (motive_3 := fun _ goals binding _ landing =>
      OriginLandingRealizes session landing)
    (motive_4 := fun _ falls => OriginFallsRealizes session falls)
    (realizeRightClauses session) (realizeRightScheduled session)
    (realizeRightTaskChoices session)
    (realizeRightEmptyClauses session) (realizeRightEmptyScheduled session)
    (realizeOriginChoiceInside session) (realizeOriginChoiceRegion session)
    (realizeOriginCut session) (realizeOriginTask session)
    (realizeOriginChoiceFalls session) (realizeOriginCutFalls session) landing

private theorem realizeRightEmpty
    {alpha : List (LogicVar × String)} (session : Session)
    {right : Search} {resources : List RetainedAlternativeSegment}
    {segment : List PLeaTTa.Alt}
    {agreement : RightAlternativeRegionAgrees alpha right resources segment}
    (empty : RightRegionEmpty alpha agreement) :
    RightEmptyRealizes session empty := by
  exact RightRegionEmpty.rec
    (motive_1 := fun _ goals binding _ landing =>
      RightLandingRealizes session landing)
    (motive_2 := fun _ empty => RightEmptyRealizes session empty)
    (motive_3 := fun _ goals binding _ landing =>
      OriginLandingRealizes session landing)
    (motive_4 := fun _ falls => OriginFallsRealizes session falls)
    (realizeRightClauses session) (realizeRightScheduled session)
    (realizeRightTaskChoices session)
    (realizeRightEmptyClauses session) (realizeRightEmptyScheduled session)
    (realizeOriginChoiceInside session) (realizeOriginChoiceRegion session)
    (realizeOriginCut session) (realizeOriginTask session)
    (realizeOriginChoiceFalls session) (realizeOriginCutFalls session) empty

private theorem realizeOriginLanding
    {alpha : List (LogicVar × String)} (session : Session)
    {leafScope : CutScopeId} {bindings : OpenSubstitution.Substitution}
    {source next : Search}
    {origin : AnswerOrigin leafScope bindings source next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    {agreement :
      AnswerOriginResourceAgrees alpha origin beforeResources afterResources
        beforeAlts afterAlts}
    {goals : List PLeaTTa.Goal} {binding : Subst}
    {tail : List PLeaTTa.Alt}
    (landing : OriginPrefixLanding alpha agreement goals binding tail) :
    OriginLandingRealizes session landing := by
  exact OriginPrefixLanding.rec
    (motive_1 := fun _ goals binding _ landing =>
      RightLandingRealizes session landing)
    (motive_2 := fun _ empty => RightEmptyRealizes session empty)
    (motive_3 := fun _ goals binding _ landing =>
      OriginLandingRealizes session landing)
    (motive_4 := fun _ falls => OriginFallsRealizes session falls)
    (realizeRightClauses session) (realizeRightScheduled session)
    (realizeRightTaskChoices session)
    (realizeRightEmptyClauses session) (realizeRightEmptyScheduled session)
    (realizeOriginChoiceInside session) (realizeOriginChoiceRegion session)
    (realizeOriginCut session) (realizeOriginTask session)
    (realizeOriginChoiceFalls session) (realizeOriginCutFalls session) landing

private theorem realizeOriginFalls
    {alpha : List (LogicVar × String)} (session : Session)
    {leafScope : CutScopeId} {bindings : OpenSubstitution.Substitution}
    {source next : Search}
    {origin : AnswerOrigin leafScope bindings source next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    {agreement :
      AnswerOriginResourceAgrees alpha origin beforeResources afterResources
        beforeAlts afterAlts}
    (falls : OriginPrefixFallsThrough alpha agreement) :
    OriginFallsRealizes session falls := by
  exact OriginPrefixFallsThrough.rec
    (motive_1 := fun _ goals binding _ landing =>
      RightLandingRealizes session landing)
    (motive_2 := fun _ empty => RightEmptyRealizes session empty)
    (motive_3 := fun _ goals binding _ landing =>
      OriginLandingRealizes session landing)
    (motive_4 := fun _ falls => OriginFallsRealizes session falls)
    (realizeRightClauses session) (realizeRightScheduled session)
    (realizeRightTaskChoices session)
    (realizeRightEmptyClauses session) (realizeRightEmptyScheduled session)
    (realizeOriginChoiceInside session) (realizeOriginChoiceRegion session)
    (realizeOriginCut session) (realizeOriginTask session)
    (realizeOriginChoiceFalls session) (realizeOriginCutFalls session) falls

/-- A live right-region classification performs exact silent source steps to
the branch-indexed conservative occurrence selected by `pullAux`. -/
theorem RightRegionLanding.sourceCatchup
    {alpha : List (LogicVar × String)}
    {right : Search} {resources : List RetainedAlternativeSegment}
    {segment : List PLeaTTa.Alt}
    {agreement : RightAlternativeRegionAgrees alpha right resources segment}
    {goals : List PLeaTTa.Goal} {binding : Subst}
    {tail : List PLeaTTa.Alt}
    (landing : RightRegionLanding alpha agreement goals binding tail)
    (session : Session) :
    exists count target,
      SilentStepsN session count right target /\
      ConservativeReadyPullTarget alpha goals binding tail target :=
  realizeRightLanding session landing

/-- An empty right region genuinely completes; a scheduled product discards
its caller tail through `productComplete` rather than executing it. -/
theorem RightRegionEmpty.sourceCompletes
    {alpha : List (LogicVar × String)}
    {right : Search} {resources : List RetainedAlternativeSegment}
    {segment : List PLeaTTa.Alt}
    {agreement : RightAlternativeRegionAgrees alpha right resources segment}
    (empty : RightRegionEmpty alpha agreement) (session : Session) :
    exists count, CompletesN session count right :=
  realizeRightEmpty session empty

/-- A classified origin-local landing is realized from the actual
post-answer successor indexed by that origin. -/
theorem OriginPrefixLanding.sourceCatchup
    {alpha : List (LogicVar × String)}
    {leafScope : CutScopeId} {bindings : OpenSubstitution.Substitution}
    {source next : Search}
    {origin : AnswerOrigin leafScope bindings source next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    {agreement :
      AnswerOriginResourceAgrees alpha origin beforeResources afterResources
        beforeAlts afterAlts}
    {goals : List PLeaTTa.Goal} {binding : Subst}
    {tail : List PLeaTTa.Alt}
    (landing : OriginPrefixLanding alpha agreement goals binding tail)
    (session : Session) :
    exists count target,
      SilentStepsN session count next target /\
      ConservativeReadyPullTarget alpha goals binding tail target :=
  realizeOriginLanding session landing

/-- Complete fall-through emits exactly one completion after a finite silent
prefix; choices consume child completion and cut boundaries preserve it. -/
theorem OriginPrefixFallsThrough.sourceCompletes
    {alpha : List (LogicVar × String)}
    {leafScope : CutScopeId} {bindings : OpenSubstitution.Substitution}
    {source next : Search}
    {origin : AnswerOrigin leafScope bindings source next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    {agreement :
      AnswerOriginResourceAgrees alpha origin beforeResources afterResources
        beforeAlts afterAlts}
    (falls : OriginPrefixFallsThrough alpha agreement) (session : Session) :
    exists count, CompletesN session count next :=
  realizeOriginFalls session falls

/-- Public exact-step form of an origin-local landing. -/
theorem OriginPrefixLanding.sourceStepsN
    {alpha : List (LogicVar × String)}
    {leafScope : CutScopeId} {bindings : OpenSubstitution.Substitution}
    {source next : Search}
    {origin : AnswerOrigin leafScope bindings source next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    {agreement :
      AnswerOriginResourceAgrees alpha origin beforeResources afterResources
        beforeAlts afterAlts}
    {goals : List PLeaTTa.Goal} {binding : Subst}
    {tail : List PLeaTTa.Alt}
    (landing : OriginPrefixLanding alpha agreement goals binding tail)
    (session : Session) :
    exists count target,
      StepsN count (.running session next) [] (.running session target) /\
      ConservativeReadyPullTarget alpha goals binding tail target := by
  obtain ⟨count, target, steps, ready⟩ :=
    PLeaTTa.PrologAnswerSourceCatchupBridge.OriginPrefixLanding.sourceCatchup
      landing session
  exact ⟨count, target, steps.toStepsN, ready⟩

/-- Public exact-step form of complete origin fall-through. -/
theorem OriginPrefixFallsThrough.sourceStepsN
    {alpha : List (LogicVar × String)}
    {leafScope : CutScopeId} {bindings : OpenSubstitution.Substitution}
    {source next : Search}
    {origin : AnswerOrigin leafScope bindings source next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    {agreement :
      AnswerOriginResourceAgrees alpha origin beforeResources afterResources
        beforeAlts afterAlts}
    (falls : OriginPrefixFallsThrough alpha agreement) (session : Session) :
    exists count,
      StepsN count (.running session next) [.completed]
        (.terminal session .completed) := by
  obtain ⟨count, completion⟩ :=
    PLeaTTa.PrologAnswerSourceCatchupBridge.OriginPrefixFallsThrough.sourceCompletes
      falls session
  exact ⟨count, completion.toStepsN⟩

namespace OriginPullOutcome

/-- Exact independent-source phase corresponding to one classified
executable pull outcome.  The middle branch deliberately records child
completion with no classified terminal observation: an enclosing source
context still has to consume that completion before the older executable
base answer is reached. -/
def SourcePhase
    (alpha : List (LogicVar × String)) (next : Search)
    (afterAlts : List PLeaTTa.Alt)
    (events : List Observation) (session : Session) : Prop :=
  (exists count target goals binding rest,
      events = [] /\
      StepsN count (.running session next) [] (.running session target) /\
      ConservativeReadyPullTarget alpha goals binding rest target) \/
    (events = [] /\
      exists count goals binding rest,
        PLeaTTa.pullAux afterAlts =
            some (.branch goals binding, rest) /\
        StepsN count (.running session next) [.completed]
          (.terminal session .completed)) \/
    (events = [] /\
      exists count,
        ∃ frame : PLeaTTa.CatchFrame,
          ∃ protectedAlts rest : List PLeaTTa.Alt,
            PLeaTTa.pullAux afterAlts =
                some (.catchResume frame protectedAlts, rest) /\
            StepsN count (.running session next) [.completed]
              (.terminal session .completed)) \/
    (events = [] /\
      exists count,
        ∃ frame : PLeaTTa.SoftcutFrame,
          ∃ rest : List PLeaTTa.Alt,
            PLeaTTa.pullAux afterAlts =
                some (.softcutExhausted frame false, rest) /\
            StepsN count (.running session next) [.completed]
              (.terminal session .completed)) \/
    (events = [] /\
      exists count,
        ∃ frame : PLeaTTa.SoftcutFrame,
          ∃ rest : List PLeaTTa.Alt,
            PLeaTTa.pullAux afterAlts =
                some (.softcutExhausted frame true, rest) /\
            StepsN count (.running session next) [.completed]
              (.terminal session .completed)) \/
    (events = [] /\
      exists count,
        ∃ frame : PLeaTTa.SoftcutFrame,
          ∃ protectedAlts rest : List PLeaTTa.Alt,
            PLeaTTa.pullAux afterAlts =
                some (.softcutResume frame protectedAlts, rest) /\
            StepsN count (.running session next) [.completed]
              (.terminal session .completed)) \/
    (events = [.completed] /\
      exists count,
        PLeaTTa.pullAux afterAlts = none /\
        StepsN count (.running session next) [.completed]
          (.terminal session .completed))

/-- Exact first source phase corresponding to the executable pull
classification.

* a local branch reaches its branch-indexed conservative cursor silently;
* a live older base first completes the child origin, after which an outer
  source context must consume that completion before selecting the base;
* an older dormant catch likewise completes the child origin before its
  protected continuation is resumed by the enclosing executable context;
* the three soft-cut delimiter transitions likewise remain distinct while
  the child-origin phase records the same exact completion;
* total exhaustion completes the child origin and that completion is the
  classified terminal observation.

The context-pending disjuncts are intentionally distinct from the terminal
one even though every child phase ends in `.completed`: only the executable
older-bank equation distinguishes ordinary selection, delimiter transitions,
and total exhaustion. -/
theorem sourcePhase
    {alpha : List (LogicVar × String)}
    {leafScope : CutScopeId} {bindings : OpenSubstitution.Substitution}
    {source next : Search}
    {origin : AnswerOrigin leafScope bindings source next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    {agreement :
      AnswerOriginResourceAgrees alpha origin beforeResources afterResources
        beforeAlts afterAlts}
    {events : List Observation}
    (outcome : OriginPullOutcome alpha agreement events)
    (session : Session) :
    SourcePhase alpha next afterAlts events session := by
  cases outcome with
  | localLive goals binding rest landing =>
      obtain ⟨count, target, steps, ready⟩ :=
        PLeaTTa.PrologAnswerSourceCatchupBridge.OriginPrefixLanding.sourceStepsN
          landing session
      exact .inl ⟨count, target, goals, binding, rest, rfl, steps, ready⟩
  | baseLive falls goals binding rest basePull =>
      obtain ⟨count, steps⟩ :=
        PLeaTTa.PrologAnswerSourceCatchupBridge.OriginPrefixFallsThrough.sourceStepsN
          falls session
      exact .inr (.inl ⟨rfl, count, goals, binding, rest, basePull, steps⟩)
  | baseCatchResume falls frame protectedAlts rest basePull =>
      obtain ⟨count, steps⟩ :=
        PLeaTTa.PrologAnswerSourceCatchupBridge.OriginPrefixFallsThrough.sourceStepsN
          falls session
      exact .inr (.inr (.inl
        ⟨rfl, count, frame, protectedAlts, rest, basePull, steps⟩))
  | baseSoftcutElse falls frame rest basePull =>
      obtain ⟨count, steps⟩ :=
        PLeaTTa.PrologAnswerSourceCatchupBridge.OriginPrefixFallsThrough.sourceStepsN
          falls session
      exact .inr (.inr (.inr (.inl
        ⟨rfl, count, frame, rest, basePull, steps⟩)))
  | baseSoftcutDone falls frame rest basePull =>
      obtain ⟨count, steps⟩ :=
        PLeaTTa.PrologAnswerSourceCatchupBridge.OriginPrefixFallsThrough.sourceStepsN
          falls session
      exact .inr (.inr (.inr (.inr (.inl
        ⟨rfl, count, frame, rest, basePull, steps⟩))))
  | baseSoftcutResume falls frame protectedAlts rest basePull =>
      obtain ⟨count, steps⟩ :=
        PLeaTTa.PrologAnswerSourceCatchupBridge.OriginPrefixFallsThrough.sourceStepsN
          falls session
      exact .inr (.inr (.inr (.inr (.inr (.inl
        ⟨rfl, count, frame, protectedAlts, rest, basePull, steps⟩)))))
  | terminal falls basePull =>
      obtain ⟨count, steps⟩ :=
        PLeaTTa.PrologAnswerSourceCatchupBridge.OriginPrefixFallsThrough.sourceStepsN
          falls session
      exact .inr (.inr (.inr (.inr (.inr (.inr
        ⟨rfl, count, basePull, steps⟩)))))

end OriginPullOutcome

/-! ## Granularity and semantic-boundary discriminators -/

/-- One immediate child completion becomes exactly one silent
`choiceComplete`; it is neither erased nor followed by a second scheduling
step. -/
theorem one_choice_completion_is_exactly_one
    (session : Session) (scope : CutScopeId) (right : Search) :
    SilentStepsN session 1 (.choice scope .done right) right := by
  exact (CompletesN.now .done (.done session)).choiceToRight scope

/-- The same product grammar distinguishes progress from completion:
ordinary head progress preserves the caller tail, while exhausted-head
completion terminates the product and therefore never executes that tail. -/
theorem product_progress_and_completion_are_distinct
    (session : Session) (scope : CutScopeId)
    (tail : List PeTTaSpec.PrologCore.Goal)
    (bindings : OpenSubstitution.Substitution) :
    SilentStepsN session 1
        (.product scope (.task scope [.truth] bindings) tail)
        (.product scope (.task scope [] bindings) tail) /\
      CompletesN session 1 (.product scope .done tail) := by
  have childProgress :
      SilentStepsN session 1 (.task scope [.truth] bindings)
        (.task scope [] bindings) :=
    .succ 0 _ _ _ (.taskTruth scope [] bindings session) (.zero _)
  have childCompletion : CompletesN session 1 .done :=
    .now .done (.done session)
  exact
    ⟨childProgress.underProduct scope tail,
      childCompletion.underProduct scope tail⟩

private theorem nested_done_choices_are_not_ready
    {alpha : List (LogicVar × String)}
    {goals : List PLeaTTa.Goal} {binding : Subst}
    {selectedTail : List PLeaTTa.Alt}
    (innerScope outerScope : CutScopeId) (emptyRight liveRight : Search) :
    ¬ ConservativeReadyTarget alpha goals binding selectedTail
        (.choice outerScope (.choice innerScope .done emptyRight) liveRight) := by
  intro ready
  cases ready with
  | taskChoices _ _ _ _ _ _ _ _ choices => cases choices
  | underChoice _ _ _ innerReady =>
      cases innerReady with
      | taskChoices _ _ _ _ _ _ _ _ choices => cases choices
      | underChoice _ _ _ doneReady =>
          cases doneReady with
          | taskChoices _ _ _ _ _ _ _ _ choices => cases choices

/-- A genuine empty owned region is crossed before a second live owned
region is reached.  The positive source-step count rules out a reflexive or
zero-step realization of the classification. -/
theorem second_local_region_after_empty_source_catchup_is_inhabited
    (session : Session) :
    exists (emptyCursor liveCursor : PreparedCursor)
        (emptyResource liveResource : RetainedAlternativeSegment)
        (goals : List PLeaTTa.Goal) (binding : Subst)
        (selectedTail : List PLeaTTa.Alt)
        (count : Nat) (target : Search),
      emptyResource.alts = [] /\
      liveResource.alts ≠ [] /\
      0 < count /\
      StepsN count
          (.running session
            (.choice 2
              (.choice 1 .done (.clauses 1 emptyCursor))
              (.clauses 2 liveCursor)))
          [] (.running session target) /\
      ConservativeReadyPullTarget [] goals binding selectedTail target := by
  obtain
      ⟨emptyCursor, liveCursor, emptyResource, liveResource, origin,
        agreement, emptyHead, liveNonempty, goals, binding, rest, landing,
        _outcome⟩ :=
    PLeaTTa.PrologAnswerPullClassificationBridge.second_local_region_after_empty_is_inhabited
  obtain ⟨count, target, steps, ready⟩ :=
    PLeaTTa.PrologAnswerSourceCatchupBridge.OriginPrefixLanding.sourceCatchup
      landing session
  have countPositive : 0 < count := by
    apply Nat.pos_of_ne_zero
    intro countZero
    subst count
    cases steps
    rcases ready with ⟨localTail, suffix, tailEq, localReady⟩
    exact
      nested_done_choices_are_not_ready
        (selectedTail := localTail) 1 2 (.clauses 1 emptyCursor)
        (.clauses 2 liveCursor) localReady
  exact
    ⟨emptyCursor, liveCursor, emptyResource, liveResource, goals, binding,
      rest, count, target, emptyHead, liveNonempty, countPositive,
      steps.toStepsN, ready⟩

/-- The recursive scheduled case is inhabited with two independently owned
regions and two predicate barriers.  Its classified result has an exact
source phase, so scheduled recursion is not a singleton shortcut. -/
theorem depth_two_scheduled_source_phase_is_inhabited
    (session : Session) :
    exists (next : Search) (resources : List RetainedAlternativeSegment)
        (segment : List PLeaTTa.Alt),
      (exists _region :
          RightAlternativeRegionAgrees
            ([] : List (LogicVar × String)) (.product 4 next []) resources
              segment,
        resources.length = 2 /\
        PLeaTTa.barrierCount segment = 2 /\
        exists events,
          OriginPullOutcome.SourcePhase []
            (.choice 5 .done (.product 4 next [])) [] events session) := by
  obtain
      ⟨next, resources, segment, region, resourceCount, markerCount, origin,
        agreement, events, outcome⟩ :=
    PLeaTTa.PrologAnswerPullClassificationBridge.depth_two_scheduled_classification_is_inhabited
  exact
    ⟨next, resources, segment, region, resourceCount, markerCount, events,
      PLeaTTa.PrologAnswerSourceCatchupBridge.OriginPullOutcome.sourcePhase
        outcome session⟩

/-- A live older base and a terminal marker-only base both complete the
source child in one step, but only the latter publishes `.completed` as the
classified observation.  The former remains context-pending. -/
theorem base_live_and_terminal_source_phases_are_distinct
    (session : Session) :
    let liveBase : List PLeaTTa.Alt := [.br [] []]
    let exhaustedBase : List PLeaTTa.Alt := [.barrier, .barrier]
    OriginPullOutcome.SourcePhase [] .done liveBase [] session /\
      PLeaTTa.pullAux liveBase = some (.branch [] [], []) /\
      OriginPullOutcome.SourcePhase [] .done exhaustedBase [.completed]
        session /\
      PLeaTTa.pullAux exhaustedBase = none /\
      StepsN 1 (.running session .done) [.completed]
        (.terminal session .completed) := by
  dsimp only
  have liveOutcome :=
    PLeaTTa.PrologAnswerPullClassificationBridge.base_live_is_inhabited
  have terminalOutcome :=
    PLeaTTa.PrologAnswerPullClassificationBridge.marker_only_terminal_is_inhabited
  have completion : CompletesN session 1 .done :=
    .now .done (.done session)
  exact
    ⟨PLeaTTa.PrologAnswerSourceCatchupBridge.OriginPullOutcome.sourcePhase
        liveOutcome session,
      rfl,
      PLeaTTa.PrologAnswerSourceCatchupBridge.OriginPullOutcome.sourcePhase
        terminalOutcome session,
      rfl, completion.toStepsN⟩

/-- A source `disjoin` region that was previously opaque to the resource
zipper now composes through one actual answer successor.  The source consumes
the completed answer leaf in exactly one silent `choiceComplete` step and is
then already focused at the selected task-choice tree.  The executable pull
retains both duplicate local alternatives followed by the literal older base
branch, in that order. -/
theorem three_branch_task_choice_source_catchup_preserves_older_suffix
    (session : Session) :
    let referenceBranches : List PeTTaSpec.PrologCore.Goal :=
      [.truth, .unify (.integer 1) (.integer 1),
        .unify (.integer 1) (.integer 1)]
    let equality : PLeaTTa.Goal :=
      .eq (.gnd (.int 1)) (.gnd (.int 1))
    let right : Search := Search.disjoin 7 referenceBranches [] []
    let regionTail : List PLeaTTa.Alt :=
      [.br [equality] [], .br [equality] []]
    let base : List PLeaTTa.Alt := [.br [.cut] []]
    exists origin :
        AnswerOrigin 7 ([] : OpenSubstitution.Substitution)
          (.choice 7 (.task 7 [] []) right) (.choice 7 .done right),
      exists agreement :
          AnswerOriginResourceAgrees [] origin [] []
            ((.br [] [] :: regionTail) ++ base) base,
        OriginPrefixLanding [] agreement [] [] (regionTail ++ base) /\
          SilentStepsN session 1 (.choice 7 .done right) right /\
          ConservativeReadyPullTarget [] [] [] (regionTail ++ base) right /\
          PLeaTTa.pullAux ((.br [] [] :: regionTail) ++ base) =
            some (.branch [] [], regionTail ++ base) := by
  dsimp only
  obtain ⟨region, _length, _markers⟩ :=
    PLeaTTa.PrologAnswerResourceBridge.AnswerOriginResourceAgrees.three_branch_task_choice_region_is_inhabited
  cases region with
  | taskChoices support scope barrier canonical referenceBase current runtime
      right goals tail choices =>
      let leafOrigin :
          AnswerOrigin 7 ([] : OpenSubstitution.Substitution)
            (.task 7 [] []) .done := .task
      let origin :
          AnswerOrigin 7 ([] : OpenSubstitution.Substitution)
            (.choice 7 (.task 7 [] [])
              (Search.disjoin 7
                [.truth, .unify (.integer 1) (.integer 1),
                  .unify (.integer 1) (.integer 1)] [] []))
            (.choice 7 .done
              (Search.disjoin 7
                [.truth, .unify (.integer 1) (.integer 1),
                  .unify (.integer 1) (.integer 1)] [] [])) :=
        .choice 7 _ leafOrigin
      let regionAgreement :
          RightAlternativeRegionAgrees []
            (Search.disjoin 7
              [.truth, .unify (.integer 1) (.integer 1),
                .unify (.integer 1) (.integer 1)] [] []) []
            [.br [] [],
              .br [.eq (.gnd (.int 1)) (.gnd (.int 1))] [],
              .br [.eq (.gnd (.int 1)) (.gnd (.int 1))] []] :=
        .taskChoices support scope barrier canonical referenceBase current [] _ [] _
          choices
      let leafAgreement :
          AnswerOriginResourceAgrees [] leafOrigin [] []
            ((.br [] [] ::
              [.br [.eq (.gnd (.int 1)) (.gnd (.int 1))] [],
                .br [.eq (.gnd (.int 1)) (.gnd (.int 1))] []]) ++
              [.br [.cut] []])
            ((.br [] [] ::
              [.br [.eq (.gnd (.int 1)) (.gnd (.int 1))] [],
                .br [.eq (.gnd (.int 1)) (.gnd (.int 1))] []]) ++
              [.br [.cut] []]) :=
        .task 7 [] [] _
      let agreement :
          AnswerOriginResourceAgrees [] origin [] []
            ((.br [] [] ::
              [.br [.eq (.gnd (.int 1)) (.gnd (.int 1))] [],
                .br [.eq (.gnd (.int 1)) (.gnd (.int 1))] []]) ++
              [.br [.cut] []])
            [.br [.cut] []] :=
        by
          apply AnswerOriginResourceAgrees.choice
            (regionResources := [])
            (regionAlts :=
              [.br [] [],
                .br [.eq (.gnd (.int 1)) (.gnd (.int 1))] [],
                .br [.eq (.gnd (.int 1)) (.gnd (.int 1))] []])
          · exact leafAgreement
          · exact regionAgreement
      have leafFalls : OriginPrefixFallsThrough [] leafAgreement :=
        .task 7 [] [] _ rfl
      have regionLive : RightRegionLanding [] regionAgreement [] []
          [.br [.eq (.gnd (.int 1)) (.gnd (.int 1))] [],
            .br [.eq (.gnd (.int 1)) (.gnd (.int 1))] []] :=
        .taskChoices support scope barrier canonical referenceBase current [] _ [] _
          choices rfl
      have landing : OriginPrefixLanding [] agreement [] []
          ( [.br [.eq (.gnd (.int 1)) (.gnd (.int 1))] [],
              .br [.eq (.gnd (.int 1)) (.gnd (.int 1))] []] ++
            [.br [.cut] []]) :=
        .choiceRegion 7 _ leafOrigin leafAgreement regionAgreement [] [] _
          leafFalls regionLive rfl
      have completion : CompletesN session 1 .done :=
        .now .done (.done session)
      have steps : SilentStepsN session 1
          (.choice 7 .done
            (Search.disjoin 7
              [.truth, .unify (.integer 1) (.integer 1),
                .unify (.integer 1) (.integer 1)] [] []))
          (Search.disjoin 7
            [.truth, .unify (.integer 1) (.integer 1),
              .unify (.integer 1) (.integer 1)] [] []) :=
        completion.choiceToRight 7
      have localReady : ConservativeReadyTarget [] [] []
          [.br [.eq (.gnd (.int 1)) (.gnd (.int 1))] [],
            .br [.eq (.gnd (.int 1)) (.gnd (.int 1))] []]
          (Search.disjoin 7
            [.truth, .unify (.integer 1) (.integer 1),
              .unify (.integer 1) (.integer 1)] [] []) :=
        .taskChoices support scope barrier canonical referenceBase current _ _
          choices
      have ready : ConservativeReadyPullTarget [] [] []
          ([.br [.eq (.gnd (.int 1)) (.gnd (.int 1))] [],
              .br [.eq (.gnd (.int 1)) (.gnd (.int 1))] []] ++
            [.br [.cut] []])
          (Search.disjoin 7
            [.truth, .unify (.integer 1) (.integer 1),
              .unify (.integer 1) (.integer 1)] [] []) :=
        (ConservativeReadyPullTarget.exact localReady).appendSuffix
          [.br [.cut] []]
      exact ⟨origin, agreement, landing, steps, ready, rfl⟩

/-- Conservative retention does not imply clause entry.  A supported
two-input occurrence exists whose per-slot prefilter retains it but whose
shared head variable makes full source head resolution impossible. -/
theorem retained_false_positive_blocks_clause_entry :
    exists (branch : ClauseBranch) (args : List Metta.Atom)
        (result : Metta.Atom) (binding : Subst)
        (clause : PLeaTTa.Clause),
      PLeaTTa.PrologPrefilterBridge.NormalizedHeadAgrees branch
          (args.map (PLeaTTa.subst binding))
          (PLeaTTa.subst binding result) clause /\
      resolutionClauseRetained (args.map (PLeaTTa.subst binding))
          (PLeaTTa.subst binding result) clause = true /\
      ¬ exists independentResult, HeadResolution branch independentResult := by
  obtain ⟨branch, args, result, rest, binding, qterm, seed, barrier, clause,
      witness⟩ :=
    PLeaTTa.PrologActivationFailureBridge.exists_retained_head_false_positive
  exact
    ⟨branch, args, result, binding, clause, witness.normalized,
      witness.retained,
      witness.independentRejected⟩

end PLeaTTa.PrologAnswerSourceCatchupBridge
