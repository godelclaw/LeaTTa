-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologSourceProductContextBridge
Purpose: Lift one answer-free, non-committing local source transition through
  an arbitrary ordered stack of already-entered predicate product/cut/choice
  regions.
Trusted boundary: none
Main exports:
  ActiveProductFrame,
  ActiveProductContext,
  ActiveProductContext.liftProgress,
  ActiveProductContext.plug_wellScoped,
  two_retained_cursor_scopes_exact,
  wrong_reversed_cursor_order_is_rejected,
  wrong_reversed_context_is_not_wellScoped
-/
import PLeaTTa.Proofs.PrologActivatedProductStepBridge

namespace PLeaTTa.PrologSourceProductContextBridge

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.Resolver
open PrologActivatedProductStepBridge

/-- One already-entered source predicate surrounding a currently executing
inner search.

The focus runs as the left branch at `predicateScope`; `retained` owns the
remaining clauses on the right.  The predicate cut boundary encloses both,
while `callerRest` remains outside that boundary at `callerScope`. -/
structure ActiveProductFrame where
  callerScope : CutScopeId
  predicateScope : CutScopeId
  retained : Search
  callerRest : List PeTTaSpec.PrologCore.Goal
deriving Repr, Inhabited

namespace ActiveProductFrame

/-- Install an inner search into one older predicate activation. -/
def wrap (frame : ActiveProductFrame) (focus : Search) : Search :=
  .product frame.callerScope
    (.cutBoundary frame.predicateScope
      (.choice frame.predicateScope focus frame.retained))
    frame.callerRest

@[simp] theorem wrap_liveCursors
    (frame : ActiveProductFrame) (focus : Search) :
    (frame.wrap focus).liveCursors =
      focus.liveCursors ++ frame.retained.liveCursors := by
  rfl

@[simp] theorem wrap_liveCursorScopes
    (frame : ActiveProductFrame) (focus : Search) :
    (frame.wrap focus).liveCursorScopes =
      focus.liveCursorScopes ++ frame.retained.liveCursorScopes := by
  rfl

/-- One answer-free, non-committing child transition crosses one older
predicate frame without changing events, session state, or the cut signal. -/
theorem liftProgress
    (frame : ActiveProductFrame)
    {before after : Session} {focus next : Search}
    {events : List Observation}
    (child :
      RawStep before focus events .none after (.running next))
    (answerFree : Trace.AnswerFree events) :
    RawStep before (frame.wrap focus) events .none after
      (.running (frame.wrap next)) := by
  have choiceStep :
      RawStep before
        (.choice frame.predicateScope focus frame.retained)
        events .none after
        (.running
          (.choice frame.predicateScope next frame.retained)) :=
    .choiceProgress frame.predicateScope _ _ _ events before after child
  have boundaryStep :
      RawStep before
        (.cutBoundary frame.predicateScope
          (.choice frame.predicateScope focus frame.retained))
        events .none after
        (.running
          (.cutBoundary frame.predicateScope
            (.choice frame.predicateScope next frame.retained))) :=
    .cutBoundaryProgress frame.predicateScope _ _ events before after
      choiceStep
  exact
    .productProgress frame.callerScope _ _ frame.callerRest events .none
      before after boundaryStep answerFree

/-- A frame built from the exact retained-cursor shape used by
`activeSourceProduct`. -/
def ofActiveProduct
    (callerScope : CutScopeId) (opened : OpenedCall)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch)
    (referenceRest : List PeTTaSpec.PrologCore.Goal) :
    ActiveProductFrame :=
  { callerScope := callerScope
    predicateScope := opened.scope
    retained :=
      .clauses opened.scope (finish.advance branch branchTail)
    callerRest := referenceRest }

/-- The generic frame is definitionally the source control shape already
used by the one-level representative activation proof. -/
@[simp] theorem ofActiveProduct_wrap_task
    (callerScope : CutScopeId) (opened : OpenedCall)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch)
    (current : PeTTaSpec.PrologCore.OpenSubstitution.Substitution)
    (body referenceRest : List PeTTaSpec.PrologCore.Goal) :
    (ofActiveProduct callerScope opened finish branch branchTail
      referenceRest).wrap (.task opened.scope body current) =
      activeSourceProduct callerScope opened finish branch branchTail current
        body referenceRest :=
  rfl

/-- A well-scoped focus and retained alternative form a well-scoped enclosing
predicate activation at the caller's scope. -/
theorem wrap_wellScoped
    {frame : ActiveProductFrame} {focus : Search}
    (focusScoped : focus.WellScoped frame.predicateScope)
    (retainedScoped : frame.retained.WellScoped frame.predicateScope) :
    (frame.wrap focus).WellScoped frame.callerScope := by
  exact
    .product frame.callerScope _ frame.callerRest
      (.cutBoundary frame.callerScope frame.predicateScope _
        (.choice frame.predicateScope focus frame.retained focusScoped
          retainedScoped))

end ActiveProductFrame

/-- An inner-to-outer stack of active predicate regions. -/
abbrev ActiveProductContext := List ActiveProductFrame

namespace ActiveProductContext

/-- Plug a focus through its active predicate regions, nearest caller first. -/
def plug : ActiveProductContext → Search → Search
  | [], focus => focus
  | frame :: outer, focus => plug outer (frame.wrap focus)

/-- Retained cursor resources in exact inner-to-outer structural order. -/
def retainedCursors (context : ActiveProductContext) : List CursorToken :=
  context.flatMap (fun frame => frame.retained.liveCursors)

/-- Retained cursor scopes in exact inner-to-outer structural order. -/
def retainedCursorScopes
    (context : ActiveProductContext) : List CutScopeId :=
  context.flatMap (fun frame => frame.retained.liveCursorScopes)

@[simp] theorem plug_nil (focus : Search) :
    plug [] focus = focus := rfl

@[simp] theorem plug_cons
    (frame : ActiveProductFrame) (outer : ActiveProductContext)
    (focus : Search) :
    plug (frame :: outer) focus = plug outer (frame.wrap focus) := rfl

/-- Appending an older context is literal nesting: the inner context wraps
the focus first, then the appended outer context wraps that result.

The equation fixes the inner-to-outer orientation used by every payload and
history zipper; reversing either side would change clause order and cut
scope. -/
theorem plug_append
    (inner outer : ActiveProductContext) (focus : Search) :
    plug (inner ++ outer) focus = plug outer (plug inner focus) := by
  induction inner generalizing focus with
  | nil =>
      rfl
  | cons frame inner inductionHypothesis =>
      simpa only [List.cons_append, plug_cons] using
        inductionHypothesis (frame.wrap focus)

/-- Plugging neither loses nor duplicates a cursor: the active focus comes
first, followed by each retained region from inner to outer. -/
theorem plug_liveCursors
    (context : ActiveProductContext) (focus : Search) :
    (plug context focus).liveCursors =
      focus.liveCursors ++ context.retainedCursors := by
  induction context generalizing focus with
  | nil =>
      simp [retainedCursors]
  | cons frame outer inductionHypothesis =>
      rw [plug_cons, inductionHypothesis, ActiveProductFrame.wrap_liveCursors]
      simp only [retainedCursors, List.flatMap_cons, List.append_assoc]

/-- Scope identities obey the same exact inner-to-outer ownership equation. -/
theorem plug_liveCursorScopes
    (context : ActiveProductContext) (focus : Search) :
    (plug context focus).liveCursorScopes =
      focus.liveCursorScopes ++ context.retainedCursorScopes := by
  induction context generalizing focus with
  | nil =>
      simp [retainedCursorScopes]
  | cons frame outer inductionHypothesis =>
      rw [plug_cons, inductionHypothesis,
        ActiveProductFrame.wrap_liveCursorScopes]
      simp only [retainedCursorScopes, List.flatMap_cons, List.append_assoc]

/-- The stored scopes of adjacent frames must form a typed source-control
chain.  Each retained right branch is certified at its predicate scope. -/
inductive WellScoped :
    CutScopeId → ActiveProductContext → CutScopeId → Prop where
  | nil (scope : CutScopeId) : WellScoped scope [] scope
  | cons (frame : ActiveProductFrame) (outer : ActiveProductContext)
      (active : CutScopeId)
      (retainedScoped :
        frame.retained.WellScoped frame.predicateScope)
      (outerScoped : WellScoped frame.callerScope outer active) :
      WellScoped frame.predicateScope (frame :: outer) active

/-- Scope-only projection of a context, independent of retained-search
contents. -/
def ScopeChain :
    CutScopeId → ActiveProductContext → CutScopeId → Prop
  | inner, [], outer => inner = outer
  | inner, frame :: context, outer =>
      inner = frame.predicateScope ∧
        ScopeChain frame.callerScope context outer

/-- Every typed context carries the exact adjacent-scope chain. -/
theorem WellScoped.scopeChain
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (agreement : WellScoped inner context outer) :
    ScopeChain inner context outer := by
  induction agreement with
  | nil scope =>
      rfl
  | cons frame context active retainedScoped outerScoped
      inductionHypothesis =>
      exact ⟨rfl, inductionHypothesis⟩

/-- A typed context chain turns a focus well-scoped at the innermost
predicate into a search well-scoped at the outermost caller. -/
theorem plug_wellScoped
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {focus : Search}
    (contextScoped : WellScoped inner context outer)
    (focusScoped : focus.WellScoped inner) :
    (plug context focus).WellScoped outer := by
  induction contextScoped generalizing focus with
  | nil scope =>
      exact focusScoped
  | cons frame context active retainedScoped outerScoped
      inductionHypothesis =>
      exact inductionHypothesis
        (ActiveProductFrame.wrap_wellScoped focusScoped retainedScoped)

/-- Every answer-free, non-committing local transition lifts through an
arbitrary number of already-entered source predicate regions.  The exact
event list and session endpoints are unchanged. -/
theorem liftProgress
    (context : ActiveProductContext)
    {before after : Session} {focus next : Search}
    {events : List Observation}
    (child :
      RawStep before focus events .none after (.running next))
    (answerFree : Trace.AnswerFree events) :
    RawStep before (plug context focus) events .none after
      (.running (plug context next)) := by
  induction context generalizing focus next with
  | nil =>
      exact child
  | cons frame outer inductionHypothesis =>
      exact inductionHypothesis
        (frame.liftProgress child answerFree)

end ActiveProductContext

/-- Two retained clause cursors remain in inner-to-outer order after plugging.
The focus itself owns no cursor in this witness. -/
theorem two_retained_cursor_scopes_exact
    (inner middle outer : CutScopeId)
    (innerCursor middleCursor : PreparedCursor) :
    (ActiveProductContext.plug
      [{ callerScope := middle
         predicateScope := inner
         retained := .clauses inner innerCursor
         callerRest := [] },
       { callerScope := outer
         predicateScope := middle
         retained := .clauses middle middleCursor
         callerRest := [] }]
      .done).liveCursorScopes =
      [inner, middle] :=
  rfl

/-- Reversing two distinct retained cursor regions is rejected.  This is the
anti-vacuity guard distinguishing the zipper from an unordered bag of
independently valid frames. -/
theorem wrong_reversed_cursor_order_is_rejected
    {inner middle outer : CutScopeId}
    (innerCursor middleCursor : PreparedCursor)
    (different : inner ≠ middle) :
    (ActiveProductContext.plug
      [{ callerScope := middle
         predicateScope := inner
         retained := .clauses inner innerCursor
         callerRest := [] },
       { callerScope := outer
         predicateScope := middle
         retained := .clauses middle middleCursor
         callerRest := [] }]
      .done).liveCursorScopes ≠
      [middle, inner] := by
  rw [two_retained_cursor_scopes_exact]
  intro reversed
  exact different (List.cons.inj reversed).1

/-- Reversing two adjacent frames whose scope chain is genuinely distinct is
not merely observationally different: no `WellScoped` derivation exists for
the reversed context at any outer scope. -/
theorem wrong_reversed_context_is_not_wellScoped
    {inner middle outer : CutScopeId}
    (different : outer ≠ inner)
    (firstRetained secondRetained : Search)
    (firstRest secondRest : List PeTTaSpec.PrologCore.Goal)
    (finalScope : CutScopeId) :
    (¬ ActiveProductContext.WellScoped middle
      [{ callerScope := outer
         predicateScope := middle
         retained := secondRetained
         callerRest := secondRest },
       { callerScope := middle
         predicateScope := inner
         retained := firstRetained
         callerRest := firstRest }]
      finalScope) := by
  intro agreement
  have chain := ActiveProductContext.WellScoped.scopeChain agreement
  exact different chain.2.1

end PLeaTTa.PrologSourceProductContextBridge
