/-
Module: PLeaTTa.PeTTaSpec.PrologGoalSemantics
Purpose: Independent finite small-step execution of locally owned Prolog goals.
Trusted boundary: none for the local core developed here
Main exports: Session, Search, RawStep, Transition, StepsN
-/
import PLeaTTa.PeTTaSpec.PrologResolver

namespace PLeaTTa.PeTTaSpec.PrologCore.GoalSemantics

open OpenSubstitution
open Resolver
open Canonical

/-!
`Trace.Process` deliberately contains no Prolog terms or substitutions.  That
generic layer is therefore not itself a recursive Prolog interpreter.  Trying
to compile an arbitrary recursive clause body into one finite `Process` would
require partiality, treating fuel exhaustion as completion, or placing
recursive scheduling inside a call oracle.

This module instead gives the independent local language a finite explicit
search state.  The tree shape follows the standard leaf/sum/product account of
SLD search, but the scheduler below is strictly leftmost depth-first: it does
not inherit miniKanren's fair interleaving.  Raw goals and their cumulative
substitution live here; provider-independent trace control remains free of
first-order syntax.

The retained clause cursor is an explicit right alternative at the
predicate's cut scope.  Consequently a cut in clause `N` can prune clauses
`N+1...`; the cursor is never hidden inside an oracle that returns answers.
Recursive calls allocate another finite activation and another cut boundary,
so left recursion is represented by an unbounded transition sequence rather
than an infinite inductive value.

[SPEC metta.pl:251-256, left-to-right `call_goals/1`]
[SPEC SWI-Prolog manual 4.14.1.1, logical update view]
-/

abbrev CutScopeId := Trace.CutScopeId

/-- Identity-bearing handle for one live local predicate cursor.

The prepared snapshot alone is not an identity: two independent calls can
prepare extensionally equal snapshots.  The fresh predicate cut scope is the
activation identifier allocated by the certified layer, while `cursor` keeps
the exact frozen clauses that would be discarded. -/
structure CursorToken where
  scope : CutScopeId
  cursor : PreparedCursor
deriving Repr, Inhabited

/-- Ordered observations of the certified local lane.  `Empty` in the effect
slot is intentional for this first core: world actions receive a distinct
typed extension rather than being smuggled through a clause reply. -/
abbrev Observation :=
  Trace.Observation CallRequest CursorToken Substitution Empty Term

/-- Activation identities explicitly reported as pruned by an event batch. -/
def prunedScopes : List Observation → List CutScopeId
  | [] => []
  | .pruned cursor :: rest => cursor.scope :: prunedScopes rest
  | _ :: rest => prunedScopes rest

@[simp] theorem prunedScopes_append (left right : List Observation) :
    prunedScopes (left ++ right) = prunedScopes left ++ prunedScopes right := by
  induction left with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      cases event <;> simp [prunedScopes, inductionHypothesis]

@[simp] theorem prunedScopes_pruned_map (cursors : List CursorToken) :
    prunedScopes (cursors.map Trace.Observation.pruned) =
      cursors.map CursorToken.scope := by
  induction cursors with
  | nil => rfl
  | cons cursor rest inductionHypothesis =>
      simp [prunedScopes, inductionHypothesis]

/-- Non-backtrackable state.  The local database and fresh-name high-water
remain outside the search tree; cut-scope identities use a separate monotone
allocator.  Exception and collection delimiters will use distinct types and
allocators when those constructs are added. -/
structure Session where
  resolver : LocalSession := {}
  nextCutScope : Nat := 1
deriving Repr, Inhabited

/-- The complete result of opening one locally owned call. -/
structure OpenedCall where
  scope : CutScopeId
  cursor : PreparedCursor
  session : Session
deriving Repr, Inhabited

/-- Allocate a fresh predicate cut scope and prepare the call-start clause
snapshot.  Both monotone allocators advance before any clause body runs. -/
def openLocalCall (session : Session) (request : CallRequest) : OpenedCall :=
  let prepared := prepareCall session.resolver request
  { scope := session.nextCutScope
    cursor := prepared.1
    session :=
      { resolver := prepared.2
        nextCutScope := session.nextCutScope + 1 } }

@[simp] theorem openLocalCall_scope (session : Session)
    (request : CallRequest) :
    (openLocalCall session request).scope = session.nextCutScope := rfl

@[simp] theorem openLocalCall_database (session : Session)
    (request : CallRequest) :
    (openLocalCall session request).session.resolver.database =
      session.resolver.database := by
  exact prepareCall_database session.resolver request

theorem openLocalCall_nextFresh_mono (session : Session)
    (request : CallRequest) :
    session.resolver.nextFresh ≤
      (openLocalCall session request).session.resolver.nextFresh := by
  exact prepareCall_nextFresh_mono session.resolver request

@[simp] theorem openLocalCall_nextCutScope (session : Session)
    (request : CallRequest) :
    (openLocalCall session request).session.nextCutScope =
      session.nextCutScope + 1 := rfl

/-- A finite local search state.

`task` carries raw residual goals and their cumulative substitution.
`clauses` owns a frozen prepared cursor for one predicate activation.
`product head tail` feeds every answer substitution of `head` into the raw
caller continuation `tail`; this is conjunction without precomputing an
answer bag. -/
inductive Search where
  | done
  | task (scope : CutScopeId) (goals : List Goal)
      (bindings : Substitution)
  | clauses (scope : CutScopeId) (cursor : PreparedCursor)
  | raise (exception : Term)
  | choice (scope : CutScopeId) (left right : Search)
  | cutBoundary (scope : CutScopeId) (body : Search)
  | product (scope : CutScopeId) (head : Search) (tail : List Goal)
deriving Repr, Inhabited

namespace Search

/-- Live local cursors in the exact left-to-right structural order in which a
cut or exception would discard them.  A latent product tail owns no cursor
until it is entered.  Pairing the snapshot with its activation scope makes
two equal snapshots from distinct calls distinguishable resources. -/
def liveCursors : Search → List CursorToken
  | .done => []
  | .task _ _ _ => []
  | .clauses scope cursor => [{ scope := scope, cursor := cursor }]
  | .raise _ => []
  | .choice _ left right => left.liveCursors ++ right.liveCursors
  | .cutBoundary _ body => body.liveCursors
  | .product _ head _ => head.liveCursors

/-- Activation identities of all live cursors, preserving structural order. -/
def liveCursorScopes : Search → List CutScopeId
  | .done => []
  | .task _ _ _ => []
  | .clauses scope _ => [scope]
  | .raise _ => []
  | .choice _ left right => left.liveCursorScopes ++ right.liveCursorScopes
  | .cutBoundary _ body => body.liveCursorScopes
  | .product _ head _ => head.liveCursorScopes

theorem liveCursorScopes_eq_map (search : Search) :
    search.liveCursorScopes = search.liveCursors.map CursorToken.scope := by
  induction search <;>
    simp_all [liveCursorScopes, liveCursors]

@[simp] theorem prunedScopes_liveCursors (search : Search) :
    prunedScopes (search.liveCursors.map Trace.Observation.pruned) =
      search.liveCursorScopes := by
  rw [prunedScopes_pruned_map, liveCursorScopes_eq_map]

/-- Linear ownership invariant for local cursors.

`Nodup` forbids copying one activation cursor into two search positions.  The
high-water bound rules out inventing a future activation identity.  Starting
from `initialState`, preservation below strengthens the latter into an
issuance guarantee: the only transition that can introduce a previously
absent scope is `taskCall`, at the current high-water. -/
def CursorOwnership (nextCutScope : Nat) (search : Search) : Prop :=
  search.liveCursorScopes.Nodup ∧
    ∀ scope ∈ search.liveCursorScopes, scope < nextCutScope

/-- Source-order disjunction.  Every alternative contains the same residual
tail, so a later cut in that tail can prune the not-yet-entered disjuncts at
the current predicate scope. -/
def disjoin (scope : CutScopeId) (branches : List Goal) (tail : List Goal)
    (bindings : Substitution) : Search :=
  match branches with
  | [] => .done
  | branch :: rest =>
      match rest with
      | [] => .task scope (branch :: tail) bindings
      | _ =>
          .choice scope (.task scope (branch :: tail) bindings)
            (disjoin scope rest tail bindings)

@[simp] theorem disjoin_liveCursors (scope : CutScopeId)
    (branches tail : List Goal) (bindings : Substitution) :
    (disjoin scope branches tail bindings).liveCursors = [] := by
  induction branches with
  | nil => rfl
  | cons branch rest inductionHypothesis =>
      cases rest with
      | nil => rfl
      | cons next remaining =>
          change [] ++
            (disjoin scope (next :: remaining) tail bindings).liveCursors = []
          simpa using inductionHypothesis

@[simp] theorem disjoin_liveCursorScopes (scope : CutScopeId)
    (branches tail : List Goal) (bindings : Substitution) :
    (disjoin scope branches tail bindings).liveCursorScopes = [] := by
  rw [liveCursorScopes_eq_map, disjoin_liveCursors]
  rfl

/-- Structural cut-scope discipline for finite local search states. -/
inductive WellScoped : CutScopeId → Search → Prop where
  | done (active : CutScopeId) : WellScoped active .done
  | task (scope : CutScopeId) (goals : List Goal)
      (bindings : Substitution) : WellScoped scope (.task scope goals bindings)
  | clauses (scope : CutScopeId) (cursor : PreparedCursor) :
      WellScoped scope (.clauses scope cursor)
  | raise (active : CutScopeId) (exception : Term) :
      WellScoped active (.raise exception)
  | choice (scope : CutScopeId) (left right : Search)
      (leftScoped : WellScoped scope left)
      (rightScoped : WellScoped scope right) :
      WellScoped scope (.choice scope left right)
  | cutBoundary (active scope : CutScopeId) (body : Search)
      (bodyScoped : WellScoped scope body) :
      WellScoped active (.cutBoundary scope body)
  | product (scope : CutScopeId) (head : Search) (tail : List Goal)
      (headScoped : WellScoped scope head) :
      WellScoped scope (.product scope head tail)

theorem disjoin_wellScoped (scope : CutScopeId) (branches tail : List Goal)
    (bindings : Substitution) :
    WellScoped scope (disjoin scope branches tail bindings) := by
  induction branches with
  | nil => exact .done scope
  | cons branch rest inductionHypothesis =>
      cases rest with
      | nil => exact .task scope (branch :: tail) bindings
      | cons next remaining =>
          exact .choice scope _ _
            (.task scope (branch :: tail) bindings)
            inductionHypothesis

end Search

/-- The local call request produced by a raw call goal under the cumulative
substitution carried by its task. -/
def requestFor (predicate : String) (arguments : List Term)
    (bindings : Substitution) : CallRequest :=
  { predicate := predicate, arguments := arguments, bindings := bindings }

/-- Deterministic call-opening package for one call goal. -/
def openedFor (session : Session) (predicate : String)
    (arguments : List Term) (bindings : Substitution) : OpenedCall :=
  openLocalCall session (requestFor predicate arguments bindings)

/-- One deterministic ordered-MGU extension of a primitive equality. -/
def UnifyResolution (bindings : Substitution) (left right : Term)
    (result : Substitution) : Prop :=
  ∃ extension,
    ComputesDenotationalMgu
      [(bindings.applyTerm left, bindings.applyTerm right)] extension ∧
    result = extension ++ bindings

theorem UnifyResolution.deterministic {bindings : Substitution}
    {left right : Term} {first second : Substitution}
    (one : UnifyResolution bindings left right first)
    (two : UnifyResolution bindings left right second) : first = second := by
  rcases one with ⟨firstExtension, firstMgu, rfl⟩
  rcases two with ⟨secondExtension, secondMgu, rfl⟩
  exact congrArg (fun extension => extension ++ bindings)
    (firstMgu.unique secondMgu)

/-- One raw transition target.  Successful search exhaustion and an exception
remain distinct terminal tags. -/
inductive RawTarget where
  | terminal (tag : Trace.Terminal Term)
  | running (search : Search)
deriving Inhabited

namespace RawTarget

/-- Cursor activations retained by a raw successor. -/
def liveCursorScopes : RawTarget → List CutScopeId
  | .terminal _ => []
  | .running search => search.liveCursorScopes

/-- A terminal successor owns no cursor; a running successor must satisfy the
same linear ownership invariant as a search state. -/
def CursorOwnership (nextCutScope : Nat) : RawTarget → Prop
  | .terminal _ => True
  | .running search => search.CursorOwnership nextCutScope

end RawTarget

/-- Terminal targets need no scope proof; running successors must preserve the
active predicate cut scope. -/
def TargetWellScoped (active : CutScopeId) : RawTarget → Prop
  | .terminal _ => True
  | .running search => search.WellScoped active

abbrev LocalOutcome :=
  Trace.PullResult PreparedCursor EnteredClause Empty Empty

/-- Internal clause-provider replies are unobservable.  Only exhaustion of
the local call becomes completion of that predicate search. -/
def localPullEvents : LocalOutcome → List Observation
  | .silent _ => []
  | .reply _ _ => []
  | .effect effect _ => nomatch effect
  | .exhausted => [.completed]
  | .raised exception => nomatch exception

/-- Certified interpretation of one clause-provider reply.  The provider can
name a clause occurrence, but only this function may install its body as the
left DFS branch or retain the cursor as the right alternative. -/
def localPullTarget (scope : CutScopeId) : LocalOutcome → RawTarget
  | .silent next => .running (.clauses scope next)
  | .reply entered next =>
      .running
        (.choice scope
          (.task scope entered.rawBody entered.bindings)
          (.clauses scope next))
  | .effect effect _ => nomatch effect
  | .exhausted => .terminal .completed
  | .raised exception => nomatch exception

/-- One certified local search transition.

Each rule demands only the left child of a choice or product.  There is no
right-progress rule: switching to the right is licensed only by observed
completion of the left.  This is the structural point at which Prolog's
incomplete leftmost DFS differs from fair miniKanren scheduling. -/
inductive RawStep : Session → Search → List Observation → Trace.CutSignal →
    Session → RawTarget → Prop where
  | done (session : Session) :
      RawStep session .done [.completed] .none session
        (.terminal .completed)
  | taskAnswer (scope : CutScopeId) (bindings : Substitution)
      (session : Session) :
      RawStep session (.task scope [] bindings) [.answer bindings] .none
        session (.running .done)
  | taskTruth (scope : CutScopeId) (rest : List Goal)
      (bindings : Substitution) (session : Session) :
      RawStep session (.task scope (.truth :: rest) bindings) [] .none
        session (.running (.task scope rest bindings))
  | taskFail (scope : CutScopeId) (rest : List Goal)
      (bindings : Substitution) (session : Session) :
      RawStep session (.task scope (.fail :: rest) bindings) [.completed]
        .none session (.terminal .completed)
  | taskUnifySuccess (scope : CutScopeId) (left right : Term)
      (rest : List Goal) (bindings result : Substitution) (session : Session)
      (resolved : UnifyResolution bindings left right result) :
      RawStep session (.task scope (.unify left right :: rest) bindings) []
        .none session (.running (.task scope rest result))
  | taskUnifyFailure (scope : CutScopeId) (left right : Term)
      (rest : List Goal) (bindings : Substitution) (session : Session)
      (clash : ¬ ∃ result, UnifyResolution bindings left right result) :
      RawStep session (.task scope (.unify left right :: rest) bindings)
        [.completed] .none session (.terminal .completed)
  | taskIdentical (scope : CutScopeId) (left right : Term)
      (rest : List Goal) (bindings : Substitution) (session : Session)
      (same : bindings.applyTerm left = bindings.applyTerm right) :
      RawStep session (.task scope (.identical left right :: rest) bindings) []
        .none session (.running (.task scope rest bindings))
  | taskNotIdentical (scope : CutScopeId) (left right : Term)
      (rest : List Goal) (bindings : Substitution) (session : Session)
      (different : bindings.applyTerm left ≠ bindings.applyTerm right) :
      RawStep session (.task scope (.identical left right :: rest) bindings)
        [.completed] .none session (.terminal .completed)
  | taskConjunction (scope : CutScopeId) (nested rest : List Goal)
      (bindings : Substitution) (session : Session) :
      RawStep session (.task scope (.conjunction nested :: rest) bindings) []
        .none session (.running (.task scope (nested ++ rest) bindings))
  | taskDisjunction (scope : CutScopeId) (branches rest : List Goal)
      (bindings : Substitution) (session : Session) :
      RawStep session (.task scope (.disjunction branches :: rest) bindings) []
        .none session
        (.running (Search.disjoin scope branches rest bindings))
  | taskCut (scope : CutScopeId) (rest : List Goal)
      (bindings : Substitution) (session : Session) :
      RawStep session (.task scope (.cut :: rest) bindings) [] (.commit scope)
        session (.running (.task scope rest bindings))
  | taskCall (scope : CutScopeId) (predicate : String)
      (arguments : List Term) (rest : List Goal) (bindings : Substitution)
      (session : Session) :
      RawStep session (.task scope (.call predicate arguments :: rest) bindings)
        [.opened (requestFor predicate arguments bindings)] .none
        (openedFor session predicate arguments bindings).session
        (.running
          (.product scope
            (.cutBoundary
              (openedFor session predicate arguments bindings).scope
              (.clauses
                (openedFor session predicate arguments bindings).scope
                (openedFor session predicate arguments bindings).cursor))
            rest))
  | clausesPull (scope : CutScopeId) (cursor : PreparedCursor)
      (outcome : LocalOutcome) (session : Session)
      (pulled : LocalPull cursor outcome) :
      RawStep session (.clauses scope cursor) (localPullEvents outcome) .none
        session (localPullTarget scope outcome)
  | raise (exception : Term) (session : Session) :
      RawStep session (.raise exception) [.raised exception] .none session
        (.terminal (.raised exception))
  | choiceProgress (scope : CutScopeId) (left right next : Search)
      (events : List Observation) (before after : Session)
      (step : RawStep before left events .none after (.running next)) :
      RawStep before (.choice scope left right) events .none after
        (.running (.choice scope next right))
  | choiceComplete (scope : CutScopeId) (left right : Search)
      (before after : Session)
      (step : RawStep before left [.completed] .none after
        (.terminal .completed)) :
      RawStep before (.choice scope left right) [] .none after
        (.running right)
  | choiceRaised (scope : CutScopeId) (left right : Search)
      (exception : Term) (events : List Observation)
      (before after : Session)
      (step : RawStep before left events .none after
        (.terminal (.raised exception))) :
      RawStep before (.choice scope left right)
        (events ++ right.liveCursors.map Trace.Observation.pruned) .none after
        (.terminal (.raised exception))
  | choiceCommitHere (scope : CutScopeId) (left right next : Search)
      (events : List Observation) (before after : Session)
      (step : RawStep before left events (.commit scope) after
        (.running next)) :
      RawStep before (.choice scope left right)
        (events ++ right.liveCursors.map Trace.Observation.pruned)
        (.commit scope)
        after (.running next)
  | choiceCommitOutside (scope other : CutScopeId)
      (different : other ≠ scope) (left right next : Search)
      (events : List Observation) (before after : Session)
      (step : RawStep before left events (.commit other) after
        (.running next)) :
      RawStep before (.choice scope left right) events (.commit other) after
        (.running (.choice scope next right))
  | cutBoundaryProgress (scope : CutScopeId) (body next : Search)
      (events : List Observation) (before after : Session)
      (step : RawStep before body events .none after (.running next)) :
      RawStep before (.cutBoundary scope body) events .none after
        (.running (.cutBoundary scope next))
  | cutBoundaryComplete (scope : CutScopeId) (body : Search)
      (before after : Session)
      (step : RawStep before body [.completed] .none after
        (.terminal .completed)) :
      RawStep before (.cutBoundary scope body) [.completed] .none after
        (.terminal .completed)
  | cutBoundaryRaised (scope : CutScopeId) (body : Search)
      (exception : Term) (events : List Observation)
      (before after : Session)
      (step : RawStep before body events .none after
        (.terminal (.raised exception))) :
      RawStep before (.cutBoundary scope body) events .none after
        (.terminal (.raised exception))
  | cutBoundaryCatch (scope : CutScopeId) (body next : Search)
      (events : List Observation) (before after : Session)
      (step : RawStep before body events (.commit scope) after
        (.running next)) :
      RawStep before (.cutBoundary scope body) events .none after
        (.running (.cutBoundary scope next))
  | cutBoundaryPass (scope other : CutScopeId)
      (different : other ≠ scope) (body next : Search)
      (events : List Observation) (before after : Session)
      (step : RawStep before body events (.commit other) after
        (.running next)) :
      RawStep before (.cutBoundary scope body) events (.commit other) after
        (.running (.cutBoundary scope next))
  | productAnswer (scope : CutScopeId) (head next : Search)
      (tail : List Goal) (bindings : Substitution)
      (before after : Session)
      (step : RawStep before head [.answer bindings] .none after
        (.running next)) :
      RawStep before (.product scope head tail) [] .none after
        (.running
          (.choice scope (.task scope tail bindings)
            (.product scope next tail)))
  | productProgress (scope : CutScopeId) (head next : Search)
      (tail : List Goal) (events : List Observation)
      (signal : Trace.CutSignal) (before after : Session)
      (step : RawStep before head events signal after (.running next))
      (answerFree : Trace.AnswerFree events) :
      RawStep before (.product scope head tail) events signal after
        (.running (.product scope next tail))
  | productComplete (scope : CutScopeId) (head : Search)
      (tail : List Goal) (events : List Observation)
      (before after : Session)
      (step : RawStep before head events .none after (.terminal .completed))
      (answerFree : Trace.AnswerFree events) :
      RawStep before (.product scope head tail) events .none after
        (.terminal .completed)
  | productRaised (scope : CutScopeId) (head : Search)
      (tail : List Goal) (exception : Term) (events : List Observation)
      (before after : Session)
      (step : RawStep before head events .none after
        (.terminal (.raised exception)))
      (answerFree : Trace.AnswerFree events) :
      RawStep before (.product scope head tail) events .none after
        (.terminal (.raised exception))

namespace RawStep

/-- A raw step can retain an old cursor activation or introduce one at/above
the incoming scope high-water.  This is the frame lemma used to show that a
nested call cannot collide with a cursor parked in a right alternative. -/
theorem cursor_scope_old_or_fresh {before after : Session} {search : Search}
    {events : List Observation} {signal : Trace.CutSignal}
    {target : RawTarget}
    (step : RawStep before search events signal after target) :
    ∀ scope ∈ target.liveCursorScopes,
      scope ∈ search.liveCursorScopes ∨ before.nextCutScope ≤ scope := by
  induction step with
  | clausesPull scope cursor outcome session pulled =>
      cases outcome with
      | silent next =>
          simp [RawTarget.liveCursorScopes, Search.liveCursorScopes,
            localPullTarget]
      | reply entered next =>
          simp [RawTarget.liveCursorScopes, Search.liveCursorScopes,
            localPullTarget]
      | effect effect next => exact Empty.elim effect
      | exhausted =>
          simp [RawTarget.liveCursorScopes, localPullTarget]
      | raised exception => exact Empty.elim exception
  | choiceProgress scope left right next events before after child
      inductionHypothesis =>
    intro scope member
    simp only [RawTarget.liveCursorScopes, Search.liveCursorScopes,
      List.mem_append] at member ⊢
    rcases member with member | member
    · rcases inductionHypothesis scope member with old | fresh
      · exact Or.inl (Or.inl old)
      · exact Or.inr fresh
    · exact Or.inl (Or.inr member)
  | choiceCommitHere scope left right next events before after child
      inductionHypothesis =>
    intro scope member
    simp only [RawTarget.liveCursorScopes, Search.liveCursorScopes,
      List.mem_append] at member ⊢
    rcases inductionHypothesis scope member with old | fresh
    · exact Or.inl (Or.inl old)
    · exact Or.inr fresh
  | choiceCommitOutside scope other different left right next events before
      after child inductionHypothesis =>
    intro scope member
    simp only [RawTarget.liveCursorScopes, Search.liveCursorScopes,
      List.mem_append] at member ⊢
    rcases member with member | member
    · rcases inductionHypothesis scope member with old | fresh
      · exact Or.inl (Or.inl old)
      · exact Or.inr fresh
    · exact Or.inl (Or.inr member)
  | taskDisjunction scope branches rest bindings session =>
      simp [RawTarget.liveCursorScopes, Search.liveCursorScopes]
  | taskCall scope predicate arguments rest bindings session =>
      simp [RawTarget.liveCursorScopes, Search.liveCursorScopes,
        openedFor, openLocalCall]
  | _ =>
      simp_all (config := { failIfUnchanged := false })
        [RawTarget.liveCursorScopes, Search.liveCursorScopes]

/-- Once an identity below the incoming high-water is absent, no step can
reintroduce it.  A new call can use only the high-water or a later identity. -/
theorem old_absence_preserved {before after : Session} {search : Search}
    {events : List Observation} {signal : Trace.CutSignal}
    {target : RawTarget} (step : RawStep before search events signal after target)
    (scope : CutScopeId) (old : scope < before.nextCutScope)
    (absent : scope ∉ search.liveCursorScopes) :
    scope ∉ target.liveCursorScopes := by
  intro member
  rcases cursor_scope_old_or_fresh step scope member with retained | fresh
  · exact absent retained
  · exact (Nat.not_le_of_gt old) fresh

/-- Every reported prune names a cursor activation that was live in the
source search state.  Prune observations therefore cannot be fabricated by a
primitive task or by a continuation that never owned the cursor. -/
theorem pruned_scope_origin {before after : Session} {search : Search}
    {events : List Observation} {signal : Trace.CutSignal}
    {target : RawTarget}
    (step : RawStep before search events signal after target) :
    ∀ scope ∈ prunedScopes events, scope ∈ search.liveCursorScopes := by
  induction step with
  | clausesPull scope cursor outcome session pulled =>
      cases outcome with
      | silent next => simp [localPullEvents, prunedScopes]
      | reply entered next => simp [localPullEvents, prunedScopes]
      | effect effect next => exact Empty.elim effect
      | exhausted => simp [localPullEvents, prunedScopes]
      | raised exception => exact Empty.elim exception
  | choiceRaised scope left right exception events before after child
      inductionHypothesis =>
      intro cursor member
      simp only [prunedScopes_append, prunedScopes_pruned_map,
        List.mem_append] at member
      simp only [Search.liveCursorScopes, List.mem_append]
      rcases member with childPrune | rightPrune
      · exact Or.inl (inductionHypothesis cursor childPrune)
      · exact Or.inr (by
          rw [Search.liveCursorScopes_eq_map]
          exact rightPrune)
  | choiceCommitHere scope left right next events before after child
      inductionHypothesis =>
      intro cursor member
      simp only [prunedScopes_append, prunedScopes_pruned_map,
        List.mem_append] at member
      simp only [Search.liveCursorScopes, List.mem_append]
      rcases member with childPrune | rightPrune
      · exact Or.inl (inductionHypothesis cursor childPrune)
      · exact Or.inr (by
          rw [Search.liveCursorScopes_eq_map]
          exact rightPrune)
  | _ =>
      simp_all (config := { failIfUnchanged := false })
        [prunedScopes, Search.liveCursorScopes]

/-- Every cursor reported as pruned is absent from the successor.  The
nontrivial cases are nested pruning under a retained sibling: source `Nodup`
separates old branches, and the allocator high-water separates newly opened
calls from every old sibling. -/
theorem pruned_scope_removed {before after : Session} {search : Search}
    {events : List Observation} {signal : Trace.CutSignal}
    {target : RawTarget} (step : RawStep before search events signal after target)
    (owned : search.CursorOwnership before.nextCutScope) :
    ∀ scope ∈ prunedScopes events, scope ∉ target.liveCursorScopes := by
  induction step with
  | clausesPull scope cursor outcome session pulled =>
      cases outcome with
      | silent next => simp [localPullEvents, prunedScopes]
      | reply entered next => simp [localPullEvents, prunedScopes]
      | effect effect next => exact Empty.elim effect
      | exhausted => simp [localPullEvents, prunedScopes]
      | raised exception => exact Empty.elim exception
  | choiceProgress scope left right next events before after child
      inductionHypothesis =>
      rw [Search.CursorOwnership] at owned
      simp only [Search.liveCursorScopes, List.nodup_append,
        List.mem_append] at owned
      rcases owned with
        ⟨⟨leftNodup, rightNodup, separated⟩, oldBound⟩
      have leftOwned : left.CursorOwnership before.nextCutScope :=
        ⟨leftNodup, fun cursor member => oldBound cursor (Or.inl member)⟩
      intro cursor pruned
      simp only [RawTarget.liveCursorScopes, Search.liveCursorScopes,
        List.mem_append]
      intro retained
      rcases retained with retainedInNext | retainedInRight
      · exact inductionHypothesis leftOwned cursor pruned retainedInNext
      · have origin := pruned_scope_origin child cursor pruned
        exact separated cursor origin cursor retainedInRight rfl
  | choiceRaised scope left right exception events before after child
      inductionHypothesis =>
      simp [RawTarget.liveCursorScopes]
  | choiceCommitHere scope left right next events before after child
      inductionHypothesis =>
      rw [Search.CursorOwnership] at owned
      simp only [Search.liveCursorScopes, List.nodup_append,
        List.mem_append] at owned
      rcases owned with
        ⟨⟨leftNodup, rightNodup, separated⟩, oldBound⟩
      have leftOwned : left.CursorOwnership before.nextCutScope :=
        ⟨leftNodup, fun cursor member => oldBound cursor (Or.inl member)⟩
      intro cursor pruned retained
      simp only [prunedScopes_append, Search.prunedScopes_liveCursors,
        List.mem_append] at pruned
      simp only [RawTarget.liveCursorScopes] at retained
      rcases pruned with childPrune | rightPrune
      · exact inductionHypothesis leftOwned cursor childPrune retained
      · rcases cursor_scope_old_or_fresh child cursor retained with
          retainedOld | retainedFresh
        · exact separated cursor retainedOld cursor rightPrune rfl
        · exact (Nat.not_le_of_gt (oldBound cursor (Or.inr rightPrune)))
            retainedFresh
  | choiceCommitOutside scope other different left right next events before
      after child inductionHypothesis =>
      rw [Search.CursorOwnership] at owned
      simp only [Search.liveCursorScopes, List.nodup_append,
        List.mem_append] at owned
      rcases owned with
        ⟨⟨leftNodup, rightNodup, separated⟩, oldBound⟩
      have leftOwned : left.CursorOwnership before.nextCutScope :=
        ⟨leftNodup, fun cursor member => oldBound cursor (Or.inl member)⟩
      intro cursor pruned
      simp only [RawTarget.liveCursorScopes, Search.liveCursorScopes,
        List.mem_append]
      intro retained
      rcases retained with retainedInNext | retainedInRight
      · exact inductionHypothesis leftOwned cursor pruned retainedInNext
      · have origin := pruned_scope_origin child cursor pruned
        exact separated cursor origin cursor retainedInRight rfl
  | _ =>
      simp_all (config := { failIfUnchanged := false })
        [prunedScopes, RawTarget.liveCursorScopes, Search.CursorOwnership,
          Search.liveCursorScopes, List.nodup_append]

/-- One well-owned transition cannot report the same activation as pruned
twice.  Nested child prunes and a discarded right branch are disjoint because
the source search owns their cursor scopes linearly. -/
theorem prunedScopes_nodup {before after : Session} {search : Search}
    {events : List Observation} {signal : Trace.CutSignal}
    {target : RawTarget} (step : RawStep before search events signal after target)
    (owned : search.CursorOwnership before.nextCutScope) :
    (prunedScopes events).Nodup := by
  induction step with
  | clausesPull scope cursor outcome session pulled =>
      cases outcome with
      | silent next => simp [localPullEvents, prunedScopes]
      | reply entered next => simp [localPullEvents, prunedScopes]
      | effect effect next => exact Empty.elim effect
      | exhausted => simp [localPullEvents, prunedScopes]
      | raised exception => exact Empty.elim exception
  | choiceRaised scope left right exception events before after child
      inductionHypothesis =>
      rw [Search.CursorOwnership] at owned
      simp only [Search.liveCursorScopes, List.nodup_append,
        List.mem_append] at owned
      rcases owned with
        ⟨⟨leftNodup, rightNodup, separated⟩, oldBound⟩
      have leftOwned : left.CursorOwnership before.nextCutScope :=
        ⟨leftNodup, fun cursor member => oldBound cursor (Or.inl member)⟩
      simp only [prunedScopes_append, Search.prunedScopes_liveCursors,
        List.nodup_append]
      refine ⟨inductionHypothesis leftOwned, rightNodup, ?_⟩
      intro cursor childPrune sibling siblingInRight equal
      have origin := pruned_scope_origin child cursor childPrune
      exact separated cursor origin sibling siblingInRight equal
  | choiceCommitHere scope left right next events before after child
      inductionHypothesis =>
      rw [Search.CursorOwnership] at owned
      simp only [Search.liveCursorScopes, List.nodup_append,
        List.mem_append] at owned
      rcases owned with
        ⟨⟨leftNodup, rightNodup, separated⟩, oldBound⟩
      have leftOwned : left.CursorOwnership before.nextCutScope :=
        ⟨leftNodup, fun cursor member => oldBound cursor (Or.inl member)⟩
      simp only [prunedScopes_append, Search.prunedScopes_liveCursors,
        List.nodup_append]
      refine ⟨inductionHypothesis leftOwned, rightNodup, ?_⟩
      intro cursor childPrune sibling siblingInRight equal
      have origin := pruned_scope_origin child cursor childPrune
      exact separated cursor origin sibling siblingInRight equal
  | _ =>
      simp_all (config := { failIfUnchanged := false })
        [prunedScopes, Search.CursorOwnership, Search.liveCursorScopes,
          List.nodup_append]

/-- Primitive task reduction is deterministic.  In particular, the only
relational computation here is the canonical ordered MGU, whose exact
substitution spelling is already unique. -/
theorem task_deterministic {before : Session} {scope : CutScopeId}
    {goals : List Goal} {bindings : Substitution}
    {firstEvents secondEvents : List Observation}
    {firstSignal secondSignal : Trace.CutSignal}
    {firstAfter secondAfter : Session}
    {firstTarget secondTarget : RawTarget}
    (first : RawStep before (.task scope goals bindings) firstEvents
      firstSignal firstAfter firstTarget)
    (second : RawStep before (.task scope goals bindings) secondEvents
      secondSignal secondAfter secondTarget) :
    firstEvents = secondEvents ∧ firstSignal = secondSignal ∧
      firstAfter = secondAfter ∧ firstTarget = secondTarget := by
  cases first <;> cases second
  all_goals try exact ⟨rfl, rfl, rfl, rfl⟩
  case taskUnifySuccess.taskUnifySuccess =>
    rename_i resultOne resolvedOne resultTwo resolvedTwo
    have result := UnifyResolution.deterministic resolvedOne resolvedTwo
    subst resultTwo
    exact ⟨rfl, rfl, rfl, rfl⟩
  case taskUnifySuccess.taskUnifyFailure =>
    rename_i result resolved clash
    exact False.elim (clash ⟨result, resolved⟩)
  case taskUnifyFailure.taskUnifySuccess =>
    rename_i clash result resolved
    exact False.elim (clash ⟨result, resolved⟩)
  case taskIdentical.taskNotIdentical =>
    rename_i same different
    exact False.elim (different same)
  case taskNotIdentical.taskIdentical =>
    rename_i different same
    exact False.elim (different same)

/-- Pulling the same frozen local cursor has one exact small-step outcome.
This lifts canonical head-MGU and `LocalPull` determinism through the search
state without quotienting answer order or clause multiplicity. -/
theorem clauses_deterministic {before : Session} {scope : CutScopeId}
    {cursor : PreparedCursor}
    {firstEvents secondEvents : List Observation}
    {firstSignal secondSignal : Trace.CutSignal}
    {firstAfter secondAfter : Session}
    {firstTarget secondTarget : RawTarget}
    (first : RawStep before (.clauses scope cursor) firstEvents firstSignal
      firstAfter firstTarget)
    (second : RawStep before (.clauses scope cursor) secondEvents secondSignal
      secondAfter secondTarget) :
    firstEvents = secondEvents ∧ firstSignal = secondSignal ∧
      firstAfter = secondAfter ∧ firstTarget = secondTarget := by
  cases first <;> cases second
  case clausesPull.clausesPull =>
    rename_i outcomeOne pulledOne outcomeTwo pulledTwo
    have outcome := LocalPull.deterministic pulledOne pulledTwo
    subst outcomeTwo
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- Every certified interpretation of a local clause reply is well-scoped at
the predicate activation that owns the frozen cursor.  In particular, an
entered clause body and the retained later-clause cursor become the two
children of one choice at that same predicate scope. -/
theorem localPullTarget_wellScoped (scope : CutScopeId)
    (outcome : LocalOutcome) :
    TargetWellScoped scope (localPullTarget scope outcome) := by
  cases outcome with
  | silent next => exact .clauses scope next
  | reply entered next =>
      exact .choice scope _ _
        (.task scope entered.rawBody entered.bindings)
        (.clauses scope next)
  | effect effect next => exact Empty.elim effect
  | exhausted => exact True.intro
  | raised exception => exact Empty.elim exception

/-- Target-indexed subject reduction for the local search machine's cut-scope
discipline.  This includes the load-bearing clause splice: entering a clause
installs its body on the left and the remaining frozen cursor on the right at
the predicate's scope. -/
theorem preserves_wellScoped_target {active : CutScopeId}
    {search : Search} {events : List Observation}
    {signal : Trace.CutSignal} {before after : Session}
    {target : RawTarget}
    (step : RawStep before search events signal after target)
    (wellFormed : search.WellScoped active) :
    TargetWellScoped active target := by
  induction step generalizing active with
  | done session => exact True.intro
  | taskAnswer scope bindings session =>
      cases wellFormed
      exact .done scope
  | taskTruth scope rest bindings session =>
      cases wellFormed
      exact .task scope rest bindings
  | taskFail scope rest bindings session => exact True.intro
  | taskUnifySuccess scope left right rest bindings result session resolved =>
      cases wellFormed
      exact .task scope rest result
  | taskUnifyFailure scope left right rest bindings session clash =>
      exact True.intro
  | taskIdentical scope left right rest bindings session same =>
      cases wellFormed
      exact .task scope rest bindings
  | taskNotIdentical scope left right rest bindings session different =>
      exact True.intro
  | taskConjunction scope nested rest bindings session =>
      cases wellFormed
      exact .task scope (nested ++ rest) bindings
  | taskDisjunction scope branches rest bindings session =>
      cases wellFormed
      exact Search.disjoin_wellScoped scope branches rest bindings
  | taskCut scope rest bindings session =>
      cases wellFormed
      exact .task scope rest bindings
  | taskCall scope predicate arguments rest bindings session =>
      cases wellFormed
      exact .product scope _ rest
        (.cutBoundary scope
          (openedFor session predicate arguments bindings).scope _
          (.clauses
            (openedFor session predicate arguments bindings).scope
            (openedFor session predicate arguments bindings).cursor))
  | clausesPull scope cursor outcome session pulled =>
      cases wellFormed
      exact localPullTarget_wellScoped scope outcome
  | raise exception session => exact True.intro
  | choiceProgress scope left right next events before after step
      inductionHypothesis =>
      cases wellFormed with
      | choice _ _ _ leftScoped rightScoped =>
          exact .choice scope next right
            (inductionHypothesis leftScoped) rightScoped
  | choiceComplete scope left right before after step inductionHypothesis =>
      cases wellFormed with
      | choice _ _ _ leftScoped rightScoped => exact rightScoped
  | choiceRaised scope left right exception events before after step
      inductionHypothesis =>
      exact True.intro
  | choiceCommitHere scope left right next events before after step
      inductionHypothesis =>
      cases wellFormed with
      | choice _ _ _ leftScoped rightScoped =>
          exact inductionHypothesis leftScoped
  | choiceCommitOutside scope other different left right next events before
      after step inductionHypothesis =>
      cases wellFormed with
      | choice _ _ _ leftScoped rightScoped =>
          exact .choice scope next right
            (inductionHypothesis leftScoped) rightScoped
  | cutBoundaryProgress scope body next events before after step
      inductionHypothesis =>
      cases wellFormed with
      | cutBoundary active _ _ bodyScoped =>
          exact .cutBoundary active scope next
            (inductionHypothesis bodyScoped)
  | cutBoundaryComplete scope body before after step inductionHypothesis =>
      exact True.intro
  | cutBoundaryRaised scope body exception events before after step
      inductionHypothesis =>
      exact True.intro
  | cutBoundaryCatch scope body next events before after step
      inductionHypothesis =>
      cases wellFormed with
      | cutBoundary active _ _ bodyScoped =>
          exact .cutBoundary active scope next
            (inductionHypothesis bodyScoped)
  | cutBoundaryPass scope other different body next events before after step
      inductionHypothesis =>
      cases wellFormed with
      | cutBoundary active _ _ bodyScoped =>
          exact .cutBoundary active scope next
            (inductionHypothesis bodyScoped)
  | productAnswer scope head next tail bindings before after step
      inductionHypothesis =>
      cases wellFormed with
      | product _ _ _ headScoped =>
          exact .choice scope _ _
            (.task scope tail bindings)
            (.product scope next tail (inductionHypothesis headScoped))
  | productProgress scope head next tail events signal before after step
      answerFree inductionHypothesis =>
      cases wellFormed with
      | product _ _ _ headScoped =>
          exact .product scope next tail (inductionHypothesis headScoped)
  | productComplete scope head tail events before after step answerFree
      inductionHypothesis =>
      exact True.intro
  | productRaised scope head tail exception events before after step answerFree
      inductionHypothesis =>
      exact True.intro

/-- Any running successor of a well-scoped local search remains well-scoped at
the same enclosing predicate scope. -/
theorem preserves_wellScoped {active : CutScopeId}
    {search next : Search} {events : List Observation}
    {signal : Trace.CutSignal} {before after : Session}
    (step : RawStep before search events signal after (.running next))
    (wellFormed : search.WellScoped active) :
    next.WellScoped active :=
  preserves_wellScoped_target step wellFormed

/-- A well-scoped local search can emit only a cut for its active predicate
scope.  Raw foreign-scope propagation rules remain useful for diagnostic
states, but are unreachable from a well-scoped entry. -/
theorem signal_matches_active {active : CutScopeId}
    {search : Search} {events : List Observation}
    {signal : Trace.CutSignal} {before after : Session}
    {target : RawTarget}
    (step : RawStep before search events signal after target)
    (wellFormed : search.WellScoped active) :
    Trace.SignalMatches active signal := by
  induction step generalizing active <;> cases wellFormed <;>
    simp_all (config := { failIfUnchanged := false }) [Trace.SignalMatches]
  case choiceCommitOutside.choice => solve_by_elim
  case cutBoundaryPass.cutBoundary =>
    exfalso
    solve_by_elim

/-- Convenient negative form of `signal_matches_active`. -/
theorem no_foreign_commit {active other : CutScopeId}
    {search : Search} {events : List Observation}
    {before after : Session} {target : RawTarget}
    (step : RawStep before search events (.commit other) after target)
    (wellFormed : search.WellScoped active)
    (different : other ≠ active) : False :=
  different (signal_matches_active step wellFormed)

/-- In the pure local lane, exceptional choice unwinding removes the entire
right search structurally and records every discarded prepared cursor in its
left-to-right order.  Unlike the generic imported-provider protocol, no
external cursor resource remains to close: a `PreparedCursor` is an immutable
finite snapshot value. -/
theorem choice_raised_prunes_right_cursors {scope : CutScopeId}
    {left right : Search} {exception : Term}
    {events : List Observation} {before after : Session}
    (step : RawStep before (.choice scope left right) events .none after
      (.terminal (.raised exception))) :
    ∃ leftEvents,
      events = leftEvents ++
        right.liveCursors.map Trace.Observation.pruned ∧
      RawStep before left leftEvents .none after
        (.terminal (.raised exception)) := by
  cases step with
  | choiceRaised _ _ _ _ leftEvents _ _ child =>
      exact ⟨leftEvents, rfl, child⟩

/-- No structural search step can restore a stale fresh-name high-water.
The only allocating rule is local-call opening; every wrapper inherits its
child's monotonicity. -/
theorem nextFresh_mono {before after : Session} {search : Search}
    {events : List Observation} {signal : Trace.CutSignal}
    {target : RawTarget}
    (step : RawStep before search events signal after target) :
    before.resolver.nextFresh ≤ after.resolver.nextFresh := by
  induction step <;> try exact Nat.le_refl _
  case taskCall scope predicate arguments rest bindings session =>
    simpa only [openedFor] using
      (openLocalCall_nextFresh_mono session
        (requestFor predicate arguments bindings))
  all_goals assumption

/-- Cut-scope allocation is globally monotone and therefore cannot alias an
outer activation after backtracking. -/
theorem nextCutScope_mono {before after : Session} {search : Search}
    {events : List Observation} {signal : Trace.CutSignal}
    {target : RawTarget}
    (step : RawStep before search events signal after target) :
    before.nextCutScope ≤ after.nextCutScope := by
  induction step <;> try exact Nat.le_refl _
  case taskCall scope predicate arguments rest bindings session =>
    simp only [openedFor, openLocalCall_nextCutScope]
    omega
  all_goals assumption

/-- Cursor ownership is subject-reduction invariant.  No transition can
duplicate a live activation, manufacture a future identifier, or collide a
nested call with a retained right alternative.  The proof uses both halves of
the invariant: old branch identities are disjoint by `Nodup`, while a newly
opened call is at/above the old high-water and every retained sibling is
strictly below it. -/
theorem preserves_cursorOwnership_target {before after : Session}
    {search : Search} {events : List Observation}
    {signal : Trace.CutSignal} {target : RawTarget}
    (step : RawStep before search events signal after target)
    (owned : search.CursorOwnership before.nextCutScope) :
    target.CursorOwnership after.nextCutScope := by
  induction step with
  | clausesPull scope cursor outcome session pulled =>
      cases outcome with
      | silent next =>
          simpa [RawTarget.CursorOwnership, Search.CursorOwnership,
            Search.liveCursorScopes, localPullTarget] using owned
      | reply entered next =>
          simpa [RawTarget.CursorOwnership, Search.CursorOwnership,
            Search.liveCursorScopes, localPullTarget] using owned
      | effect effect next => exact Empty.elim effect
      | exhausted => exact True.intro
      | raised exception => exact Empty.elim exception
  | choiceProgress scope left right next events before after child
      inductionHypothesis =>
      rw [Search.CursorOwnership] at owned
      simp only [Search.liveCursorScopes, List.nodup_append,
        List.mem_append] at owned
      rcases owned with
        ⟨⟨leftNodup, rightNodup, separated⟩, oldBound⟩
      have leftOwned : left.CursorOwnership before.nextCutScope :=
        ⟨leftNodup, fun cursor member => oldBound cursor (Or.inl member)⟩
      rcases inductionHypothesis leftOwned with
        ⟨nextNodup, nextBound⟩
      rw [RawTarget.CursorOwnership, Search.CursorOwnership]
      simp only [Search.liveCursorScopes, List.nodup_append,
        List.mem_append]
      refine ⟨⟨nextNodup, rightNodup, ?_⟩, ?_⟩
      · intro cursor cursorInNext sibling siblingInRight equal
        rcases cursor_scope_old_or_fresh child cursor cursorInNext with
          old | fresh
        · exact separated cursor old sibling siblingInRight equal
        · have siblingBound := oldBound sibling (Or.inr siblingInRight)
          subst sibling
          exact (Nat.not_le_of_gt siblingBound) fresh
      · intro cursor member
        rcases member with inNext | inRight
        · exact nextBound cursor inNext
        · exact Nat.lt_of_lt_of_le (oldBound cursor (Or.inr inRight))
            (nextCutScope_mono child)
  | choiceComplete scope left right before after child inductionHypothesis =>
      rw [Search.CursorOwnership] at owned
      simp only [Search.liveCursorScopes, List.nodup_append,
        List.mem_append] at owned
      rcases owned with
        ⟨⟨leftNodup, rightNodup, separated⟩, oldBound⟩
      rw [RawTarget.CursorOwnership, Search.CursorOwnership]
      exact ⟨rightNodup, fun cursor member =>
        Nat.lt_of_lt_of_le (oldBound cursor (Or.inr member))
          (nextCutScope_mono child)⟩
  | choiceCommitOutside scope other different left right next events before
      after child inductionHypothesis =>
      rw [Search.CursorOwnership] at owned
      simp only [Search.liveCursorScopes, List.nodup_append,
        List.mem_append] at owned
      rcases owned with
        ⟨⟨leftNodup, rightNodup, separated⟩, oldBound⟩
      have leftOwned : left.CursorOwnership before.nextCutScope :=
        ⟨leftNodup, fun cursor member => oldBound cursor (Or.inl member)⟩
      rcases inductionHypothesis leftOwned with
        ⟨nextNodup, nextBound⟩
      rw [RawTarget.CursorOwnership, Search.CursorOwnership]
      simp only [Search.liveCursorScopes, List.nodup_append,
        List.mem_append]
      refine ⟨⟨nextNodup, rightNodup, ?_⟩, ?_⟩
      · intro cursor cursorInNext sibling siblingInRight equal
        rcases cursor_scope_old_or_fresh child cursor cursorInNext with
          old | fresh
        · exact separated cursor old sibling siblingInRight equal
        · have siblingBound := oldBound sibling (Or.inr siblingInRight)
          subst sibling
          exact (Nat.not_le_of_gt siblingBound) fresh
      · intro cursor member
        rcases member with inNext | inRight
        · exact nextBound cursor inNext
        · exact Nat.lt_of_lt_of_le (oldBound cursor (Or.inr inRight))
            (nextCutScope_mono child)
  | _ =>
      simp_all (config := { failIfUnchanged := false })
        [RawTarget.CursorOwnership, Search.CursorOwnership,
          Search.liveCursorScopes, openedFor, openLocalCall,
          List.nodup_append] <;>
        try omega

/-- Running successors inherit the linear cursor-ownership invariant. -/
theorem preserves_cursorOwnership {before after : Session}
    {search next : Search} {events : List Observation}
    {signal : Trace.CutSignal}
    (step : RawStep before search events signal after (.running next))
    (owned : search.CursorOwnership before.nextCutScope) :
    next.CursorOwnership after.nextCutScope :=
  preserves_cursorOwnership_target step owned

/-- The present pure local core never rewinds or mutates the database.  When
dynamic world-action rules are added this equality will be replaced by a
generation-monotone extension relation; the database will remain in this
same non-backtrackable session channel. -/
theorem database_eq {before after : Session} {search : Search}
    {events : List Observation} {signal : Trace.CutSignal}
    {target : RawTarget}
    (step : RawStep before search events signal after target) :
    after.resolver.database = before.resolver.database := by
  induction step <;> try rfl
  all_goals assumption

set_option maxHeartbeats 2000000 in
/-- The whole local scheduler is functional: one state has one exact event
batch, cut signal, successor session, and target.  This is stronger than
answer-set determinism; it fixes silence, answer order, pruning, and terminal
tags one transition at a time. -/
theorem deterministic {before : Session} {search : Search}
    {firstEvents secondEvents : List Observation}
    {firstSignal secondSignal : Trace.CutSignal}
    {firstAfter secondAfter : Session}
    {firstTarget secondTarget : RawTarget}
    (first : RawStep before search firstEvents firstSignal firstAfter
      firstTarget)
    (second : RawStep before search secondEvents secondSignal secondAfter
      secondTarget) :
    firstEvents = secondEvents ∧ firstSignal = secondSignal ∧
      firstAfter = secondAfter ∧ firstTarget = secondTarget := by
  induction search generalizing firstEvents secondEvents firstSignal
      secondSignal firstAfter secondAfter firstTarget secondTarget with
  | done =>
      cases first
      cases second
      exact ⟨rfl, rfl, rfl, rfl⟩
  | task scope goals bindings =>
      exact task_deterministic first second
  | clauses scope cursor =>
      exact clauses_deterministic first second
  | raise exception =>
      cases first
      cases second
      exact ⟨rfl, rfl, rfl, rfl⟩
  | choice scope left right leftInduction rightInduction =>
      have compareStep :
          ∀ {firstEvents : List Observation}
            {firstSignal : Trace.CutSignal} {firstAfter : Session}
            {firstTarget : RawTarget},
            RawStep before left firstEvents firstSignal firstAfter
              firstTarget →
            ∀ {secondEvents : List Observation}
              {secondSignal : Trace.CutSignal} {secondAfter : Session}
              {secondTarget : RawTarget},
              RawStep before left secondEvents secondSignal secondAfter
                secondTarget →
              firstEvents = secondEvents ∧ firstSignal = secondSignal ∧
                firstAfter = secondAfter ∧ firstTarget = secondTarget := by
        intro firstEvents firstSignal firstAfter firstTarget firstStep
          secondEvents secondSignal secondAfter secondTarget secondStep
        exact leftInduction firstStep secondStep
      cases first with
      | choiceProgress _ _ _ _ _ _ _ firstStep =>
          have compare := @compareStep _ _ _ _ firstStep
          clear firstStep
          cases second <;>
            have inner := compare (by assumption) <;>
            clear compare compareStep leftInduction rightInduction <;>
            rcases inner with ⟨eventsEq, signalEq, afterEq, targetEq⟩ <;>
            cases eventsEq <;> cases signalEq <;> cases afterEq <;>
            cases targetEq <;>
            simp_all
      | choiceComplete _ _ _ _ _ firstStep =>
          have compare := @compareStep _ _ _ _ firstStep
          clear firstStep
          cases second <;>
            have inner := compare (by assumption) <;>
            clear compare compareStep leftInduction rightInduction <;>
            rcases inner with ⟨eventsEq, signalEq, afterEq, targetEq⟩ <;>
            cases eventsEq <;> cases signalEq <;> cases afterEq <;>
            cases targetEq <;>
            simp_all
      | choiceRaised _ _ _ _ _ _ _ firstStep =>
          have compare := @compareStep _ _ _ _ firstStep
          clear firstStep
          cases second <;>
            have inner := compare (by assumption) <;>
            clear compare compareStep leftInduction rightInduction <;>
            rcases inner with ⟨eventsEq, signalEq, afterEq, targetEq⟩ <;>
            cases eventsEq <;> cases signalEq <;> cases afterEq <;>
            cases targetEq <;>
            simp_all
      | choiceCommitHere _ _ _ _ _ _ _ firstStep =>
          have compare := @compareStep _ _ _ _ firstStep
          clear firstStep
          cases second <;>
            have inner := compare (by assumption) <;>
            clear compare compareStep leftInduction rightInduction <;>
            rcases inner with ⟨eventsEq, signalEq, afterEq, targetEq⟩ <;>
            cases eventsEq <;> cases signalEq <;> cases afterEq <;>
            cases targetEq <;>
            simp_all
      | choiceCommitOutside _ _ _ _ _ _ _ _ _ firstStep =>
          have compare := @compareStep _ _ _ _ firstStep
          clear firstStep
          cases second <;>
            have inner := compare (by assumption) <;>
            clear compare compareStep leftInduction rightInduction <;>
            rcases inner with ⟨eventsEq, signalEq, afterEq, targetEq⟩ <;>
            cases eventsEq <;> cases signalEq <;> cases afterEq <;>
            cases targetEq <;>
            simp_all
  | cutBoundary scope body inductionHypothesis =>
      have compareStep :
          ∀ {firstEvents : List Observation}
            {firstSignal : Trace.CutSignal} {firstAfter : Session}
            {firstTarget : RawTarget},
            RawStep before body firstEvents firstSignal firstAfter
              firstTarget →
            ∀ {secondEvents : List Observation}
              {secondSignal : Trace.CutSignal} {secondAfter : Session}
              {secondTarget : RawTarget},
              RawStep before body secondEvents secondSignal secondAfter
                secondTarget →
              firstEvents = secondEvents ∧ firstSignal = secondSignal ∧
                firstAfter = secondAfter ∧ firstTarget = secondTarget := by
        intro firstEvents firstSignal firstAfter firstTarget firstStep
          secondEvents secondSignal secondAfter secondTarget secondStep
        exact inductionHypothesis firstStep secondStep
      cases first with
      | cutBoundaryProgress _ _ _ _ _ _ firstStep =>
          have compare := @compareStep _ _ _ _ firstStep
          clear firstStep
          cases second <;>
            have inner := compare (by assumption) <;>
            clear compare compareStep inductionHypothesis <;>
            rcases inner with ⟨eventsEq, signalEq, afterEq, targetEq⟩ <;>
            cases eventsEq <;> cases signalEq <;> cases afterEq <;>
            cases targetEq <;>
            simp_all
      | cutBoundaryComplete _ _ _ _ firstStep =>
          have compare := @compareStep _ _ _ _ firstStep
          clear firstStep
          cases second <;>
            have inner := compare (by assumption) <;>
            clear compare compareStep inductionHypothesis <;>
            rcases inner with ⟨eventsEq, signalEq, afterEq, targetEq⟩ <;>
            cases eventsEq <;> cases signalEq <;> cases afterEq <;>
            cases targetEq <;>
            simp_all
      | cutBoundaryRaised _ _ _ _ _ _ firstStep =>
          have compare := @compareStep _ _ _ _ firstStep
          clear firstStep
          cases second <;>
            have inner := compare (by assumption) <;>
            clear compare compareStep inductionHypothesis <;>
            rcases inner with ⟨eventsEq, signalEq, afterEq, targetEq⟩ <;>
            cases eventsEq <;> cases signalEq <;> cases afterEq <;>
            cases targetEq <;>
            simp_all
      | cutBoundaryCatch _ _ _ _ _ _ firstStep =>
          have compare := @compareStep _ _ _ _ firstStep
          clear firstStep
          cases second <;>
            have inner := compare (by assumption) <;>
            clear compare compareStep inductionHypothesis <;>
            rcases inner with ⟨eventsEq, signalEq, afterEq, targetEq⟩ <;>
            cases eventsEq <;> cases signalEq <;> cases afterEq <;>
            cases targetEq <;>
            simp_all
      | cutBoundaryPass _ _ _ _ _ _ _ _ firstStep =>
          have compare := @compareStep _ _ _ _ firstStep
          clear firstStep
          cases second <;>
            have inner := compare (by assumption) <;>
            clear compare compareStep inductionHypothesis <;>
            rcases inner with ⟨eventsEq, signalEq, afterEq, targetEq⟩ <;>
            cases eventsEq <;> cases signalEq <;> cases afterEq <;>
            cases targetEq <;>
            simp_all
  | product scope head tail inductionHypothesis =>
      have compareStep :
          ∀ {firstEvents : List Observation}
            {firstSignal : Trace.CutSignal} {firstAfter : Session}
            {firstTarget : RawTarget},
            RawStep before head firstEvents firstSignal firstAfter
              firstTarget →
            ∀ {secondEvents : List Observation}
              {secondSignal : Trace.CutSignal} {secondAfter : Session}
              {secondTarget : RawTarget},
              RawStep before head secondEvents secondSignal secondAfter
                secondTarget →
              firstEvents = secondEvents ∧ firstSignal = secondSignal ∧
                firstAfter = secondAfter ∧ firstTarget = secondTarget := by
        intro firstEvents firstSignal firstAfter firstTarget firstStep
          secondEvents secondSignal secondAfter secondTarget secondStep
        exact inductionHypothesis firstStep secondStep
      cases first with
      | productAnswer _ _ _ _ _ _ _ firstStep =>
          have compare := @compareStep _ _ _ _ firstStep
          clear firstStep
          cases second <;>
            have inner := compare (by assumption) <;>
            clear compare compareStep inductionHypothesis <;>
            rcases inner with ⟨eventsEq, signalEq, afterEq, targetEq⟩ <;>
            cases eventsEq <;> cases signalEq <;> cases afterEq <;>
            cases targetEq <;>
            simp_all [Trace.AnswerFree]
      | productProgress _ _ _ _ _ _ _ _ firstStep _ =>
          have compare := @compareStep _ _ _ _ firstStep
          clear firstStep
          cases second <;>
            have inner := compare (by assumption) <;>
            clear compare compareStep inductionHypothesis <;>
            rcases inner with ⟨eventsEq, signalEq, afterEq, targetEq⟩ <;>
            cases eventsEq <;> cases signalEq <;> cases afterEq <;>
            cases targetEq <;>
            simp_all [Trace.AnswerFree]
      | productComplete _ _ _ _ _ _ firstStep _ =>
          have compare := @compareStep _ _ _ _ firstStep
          clear firstStep
          cases second <;>
            have inner := compare (by assumption) <;>
            clear compare compareStep inductionHypothesis <;>
            rcases inner with ⟨eventsEq, signalEq, afterEq, targetEq⟩ <;>
            cases eventsEq <;> cases signalEq <;> cases afterEq <;>
            cases targetEq <;>
            simp_all [Trace.AnswerFree]
      | productRaised _ _ _ _ _ _ _ firstStep _ =>
          have compare := @compareStep _ _ _ _ firstStep
          clear firstStep
          cases second <;>
            have inner := compare (by assumption) <;>
            clear compare compareStep inductionHypothesis <;>
            rcases inner with ⟨eventsEq, signalEq, afterEq, targetEq⟩ <;>
            cases eventsEq <;> cases signalEq <;> cases afterEq <;>
            cases targetEq <;>
            simp_all [Trace.AnswerFree]

end RawStep

/-- Public local-goal state.  An escaped cut remains explicit instead of being
silently reinterpreted as failure. -/
inductive State where
  | terminal (session : Session) (tag : Trace.Terminal Term)
  | running (session : Session) (search : Search)
  | uncaughtCut (session : Session) (scope : CutScopeId)
      (continuation : Search)
deriving Inhabited

namespace State

/-- Reachable query states remain inside the distinguished root cut boundary.
The public `uncaughtCut` constructor is retained for diagnosing arbitrary raw
inputs, but a rooted execution can never enter it. -/
inductive Rooted : State → Prop where
  | terminal (session : Session) (tag : Trace.Terminal Term) :
      Rooted (.terminal session tag)
  | running (session : Session) (body : Search)
      (bodyScoped : body.WellScoped 0) :
      Rooted (.running session (.cutBoundary 0 body))

/-- Cursor resources carried by a public state are linearly owned below that
state's allocator high-water. -/
def CursorOwned : State → Prop
  | .terminal _ _ => True
  | .running session search =>
      search.CursorOwnership session.nextCutScope
  | .uncaughtCut session _ continuation =>
      continuation.CursorOwnership session.nextCutScope

/-- Session high-water carried by every public state. -/
def scopeHighWater : State → Nat
  | .terminal session _ => session.nextCutScope
  | .running session _ => session.nextCutScope
  | .uncaughtCut session _ _ => session.nextCutScope

/-- Live cursor activations carried by every public state. -/
def liveCursorScopes : State → List CutScopeId
  | .terminal _ _ => []
  | .running _ search => search.liveCursorScopes
  | .uncaughtCut _ _ continuation => continuation.liveCursorScopes

/-- Complete public structural invariant used by reachability theorems. -/
def WellFormed (state : State) : Prop := state.Rooted ∧ state.CursorOwned

end State

private def RawTarget.toState (session : Session) : RawTarget → State
  | .terminal tag => .terminal session tag
  | .running search => .running session search

/-- One public transition of the local goal machine. -/
inductive Transition : State → List Observation → State → Prop where
  | ordinary (search : Search) (events : List Observation)
      (before after : Session) (target : RawTarget)
      (step : RawStep before search events .none after target) :
      Transition (.running before search) events (target.toState after)
  | uncaught (search next : Search) (events : List Observation)
      (before after : Session) (scope : CutScopeId)
      (step : RawStep before search events (.commit scope) after
        (.running next)) :
      Transition (.running before search) events
        (.uncaughtCut after scope next)

namespace Transition

/-- The public one-step machine inherits exact determinism from `RawStep`.
In particular, an ordinary successor and an escaped-cut successor cannot both
leave the same state. -/
theorem deterministic {start firstFinish secondFinish : State}
    {firstEvents secondEvents : List Observation}
    (first : Transition start firstEvents firstFinish)
    (second : Transition start secondEvents secondFinish) :
    firstEvents = secondEvents ∧ firstFinish = secondFinish := by
  cases first with
  | ordinary search firstEvents before firstAfter firstTarget firstStep =>
      cases second with
      | ordinary _ secondEvents _ secondAfter secondTarget secondStep =>
          rcases RawStep.deterministic firstStep secondStep with
            ⟨eventsEq, signalEq, afterEq, targetEq⟩
          subst secondEvents
          subst secondAfter
          subst secondTarget
          exact ⟨rfl, rfl⟩
      | uncaught _ next secondEvents _ secondAfter scope secondStep =>
          have comparison := RawStep.deterministic firstStep secondStep
          have impossible :
              (Trace.CutSignal.none : Trace.CutSignal) = .commit scope :=
            comparison.2.1
          cases impossible
  | uncaught search firstNext firstEvents before firstAfter firstScope
      firstStep =>
      cases second with
      | ordinary _ secondEvents _ secondAfter secondTarget secondStep =>
          have comparison := RawStep.deterministic firstStep secondStep
          have impossible :
              Trace.CutSignal.commit firstScope = .none := comparison.2.1
          cases impossible
      | uncaught _ secondNext secondEvents _ secondAfter secondScope
          secondStep =>
          rcases RawStep.deterministic firstStep secondStep with
            ⟨eventsEq, signalEq, afterEq, targetEq⟩
          cases signalEq
          subst secondEvents
          subst secondAfter
          cases targetEq
          exact ⟨rfl, rfl⟩

/-- Public subject reduction: a query that starts beneath the root cut
boundary stays rooted, and therefore cannot expose an uncaught cut. -/
theorem preserves_rooted {start finish : State} {events : List Observation}
    (step : Transition start events finish) (rooted : start.Rooted) :
    finish.Rooted := by
  cases step with
  | ordinary search events before after target raw =>
      cases rooted with
      | running _ body bodyScoped =>
          cases raw with
          | cutBoundaryProgress _ _ next _ _ _ child =>
              exact .running _ next (child.preserves_wellScoped bodyScoped)
          | cutBoundaryComplete _ _ _ _ child => exact .terminal _ _
          | cutBoundaryRaised _ _ _ _ _ _ child => exact .terminal _ _
          | cutBoundaryCatch _ _ next _ _ _ child =>
              exact .running _ next (child.preserves_wellScoped bodyScoped)
  | uncaught search next events before after scope raw =>
      cases rooted with
      | running _ body bodyScoped =>
          cases raw with
          | cutBoundaryPass _ other different _ _ _ _ _ child =>
              exact False.elim
                (RawStep.no_foreign_commit child bodyScoped different)

/-- Public transitions preserve linear cursor ownership, including diagnostic
escaped-cut states for arbitrary non-rooted inputs. -/
theorem preserves_cursorOwned {start finish : State}
    {events : List Observation} (step : Transition start events finish)
    (owned : start.CursorOwned) : finish.CursorOwned := by
  cases step with
  | ordinary search events before after target raw =>
      change search.CursorOwnership before.nextCutScope at owned
      have targetOwned := raw.preserves_cursorOwnership_target owned
      cases target <;> exact targetOwned
  | uncaught search next events before after scope raw =>
      change search.CursorOwnership before.nextCutScope at owned
      exact raw.preserves_cursorOwnership owned

/-- Public transitions never rewind the predicate-activation allocator. -/
theorem scopeHighWater_mono {start finish : State}
    {events : List Observation} (step : Transition start events finish) :
    start.scopeHighWater ≤ finish.scopeHighWater := by
  cases step with
  | ordinary search events before after target raw =>
      cases target <;>
        exact raw.nextCutScope_mono
  | uncaught search next events before after scope raw =>
      exact raw.nextCutScope_mono

/-- Every public prune event names a cursor live in the source state. -/
theorem pruned_scope_origin {start finish : State}
    {events : List Observation} (step : Transition start events finish) :
    ∀ scope ∈ prunedScopes events, scope ∈ start.liveCursorScopes := by
  cases step with
  | ordinary search events before after target raw =>
      exact raw.pruned_scope_origin
  | uncaught search next events before after scope raw =>
      exact raw.pruned_scope_origin

/-- Every public prune event removes that activation from the successor. -/
theorem pruned_scope_removed {start finish : State}
    {events : List Observation} (step : Transition start events finish)
    (owned : start.CursorOwned) :
    ∀ scope ∈ prunedScopes events, scope ∉ finish.liveCursorScopes := by
  cases step with
  | ordinary search events before after target raw =>
      change search.CursorOwnership before.nextCutScope at owned
      have removed := raw.pruned_scope_removed owned
      cases target <;> exact removed
  | uncaught search next events before after scope raw =>
      change search.CursorOwnership before.nextCutScope at owned
      exact raw.pruned_scope_removed owned

/-- An already-issued absent activation cannot be resurrected by a public
transition. -/
theorem old_absence_preserved {start finish : State}
    {events : List Observation} (step : Transition start events finish)
    (scope : CutScopeId) (old : scope < start.scopeHighWater)
    (absent : scope ∉ start.liveCursorScopes) :
    scope ∉ finish.liveCursorScopes := by
  cases step with
  | ordinary search events before after target raw =>
      have preserved := raw.old_absence_preserved scope old absent
      cases target <;> exact preserved
  | uncaught search next events before after escaped raw =>
      exact raw.old_absence_preserved scope old absent

/-- One public transition reports pairwise-distinct pruned activations. -/
theorem prunedScopes_nodup {start finish : State}
    {events : List Observation} (step : Transition start events finish)
    (owned : start.CursorOwned) : (prunedScopes events).Nodup := by
  cases step with
  | ordinary search events before after target raw =>
      change search.CursorOwnership before.nextCutScope at owned
      exact raw.prunedScopes_nodup owned
  | uncaught search next events before after scope raw =>
      change search.CursorOwnership before.nextCutScope at owned
      exact raw.prunedScopes_nodup owned

/-- A pruned activation is necessarily older than the source allocator
high-water. -/
theorem pruned_scope_lt_highWater {start finish : State}
    {events : List Observation} (step : Transition start events finish)
    (owned : start.CursorOwned) (scope : CutScopeId)
    (pruned : scope ∈ prunedScopes events) :
    scope < start.scopeHighWater := by
  cases step with
  | ordinary search events before after target raw =>
      change search.CursorOwnership before.nextCutScope at owned
      exact owned.2 scope (raw.pruned_scope_origin scope pruned)
  | uncaught search next events before after escaped raw =>
      change search.CursorOwnership before.nextCutScope at owned
      exact owned.2 scope (raw.pruned_scope_origin scope pruned)

/-- Public subject reduction for the combined scope and cursor invariant. -/
theorem preserves_wellFormed {start finish : State}
    {events : List Observation} (step : Transition start events finish)
    (wellFormed : start.WellFormed) : finish.WellFormed :=
  ⟨step.preserves_rooted wellFormed.1,
    step.preserves_cursorOwned wellFormed.2⟩

end Transition

/-- A finite exact observation prefix. -/
inductive Steps : State → List Observation → State → Prop where
  | refl (state : State) : Steps state [] state
  | cons (start middle finish : State) (first rest : List Observation)
      (head : Transition start first middle)
      (tail : Steps middle rest finish) :
      Steps start (first ++ rest) finish

/-- Exactly `count` transitions.  The count prevents arbitrarily-long-prefix
claims from being witnessed by reflexivity. -/
inductive StepsN : Nat → State → List Observation → State → Prop where
  | zero (state : State) : StepsN 0 state [] state
  | succ (count : Nat) (start middle finish : State)
      (first rest : List Observation)
      (head : Transition start first middle)
      (tail : StepsN count middle rest finish) :
      StepsN (count + 1) start (first ++ rest) finish

namespace StepsN

theorem toSteps {count : Nat} {start finish : State}
    {events : List Observation}
    (execution : StepsN count start events finish) :
    Steps start events finish := by
  induction execution with
  | zero state => exact .refl state
  | succ _ start middle finish first rest head _ inductionHypothesis =>
      exact .cons start middle finish first rest head inductionHypothesis

/-- Exact finite prefixes compose without erasing either transition counts or
the boundary between their ordered observation sequences. -/
theorem trans {firstCount secondCount : Nat} {start middle finish : State}
    {firstEvents secondEvents : List Observation}
    (first : StepsN firstCount start firstEvents middle)
    (second : StepsN secondCount middle secondEvents finish) :
    StepsN (firstCount + secondCount) start
      (firstEvents ++ secondEvents) finish := by
  induction first with
  | zero state => simpa using second
  | succ count start next middle headEvents tailEvents head tail
      inductionHypothesis =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.append_assoc] using
        (StepsN.succ (count + secondCount) start next finish headEvents
          (tailEvents ++ secondEvents) head
          (inductionHypothesis second))

/-- Fixing the number of demands fixes the complete ordered observation
prefix and successor state.  This is trajectory determinism, not merely
equality of final answer sets. -/
theorem deterministic {count : Nat} {start firstFinish secondFinish : State}
    {firstEvents secondEvents : List Observation}
    (first : StepsN count start firstEvents firstFinish)
    (second : StepsN count start secondEvents secondFinish) :
    firstEvents = secondEvents ∧ firstFinish = secondFinish := by
  induction first generalizing secondEvents secondFinish with
  | zero state =>
      cases second
      exact ⟨rfl, rfl⟩
  | succ count start middle firstFinish headEvents tailEvents head tail
      inductionHypothesis =>
      cases second with
      | succ _ _ secondMiddle secondFinish secondHeadEvents secondTailEvents
          secondHead secondTail =>
          rcases head.deterministic secondHead with
            ⟨headEventsEq, middleEq⟩
          subst secondHeadEvents
          subst secondMiddle
          rcases inductionHypothesis secondTail with
            ⟨tailEventsEq, finishEq⟩
          subst secondTailEvents
          subst secondFinish
          exact ⟨rfl, rfl⟩

/-- Every exact finite prefix from a rooted query remains rooted. -/
theorem preserves_rooted {count : Nat} {start finish : State}
    {events : List Observation} (execution : StepsN count start events finish)
    (rooted : start.Rooted) : finish.Rooted := by
  induction execution with
  | zero state => exact rooted
  | succ count start middle finish first rest head tail
      inductionHypothesis =>
      exact inductionHypothesis (head.preserves_rooted rooted)

/-- Every exact finite prefix preserves linear cursor ownership. -/
theorem preserves_cursorOwned {count : Nat} {start finish : State}
    {events : List Observation} (execution : StepsN count start events finish)
    (owned : start.CursorOwned) : finish.CursorOwned := by
  induction execution with
  | zero state => exact owned
  | succ count start middle finish first rest head tail
      inductionHypothesis =>
      exact inductionHypothesis (head.preserves_cursorOwned owned)

/-- Every exact finite prefix preserves the combined public invariant. -/
theorem preserves_wellFormed {count : Nat} {start finish : State}
    {events : List Observation} (execution : StepsN count start events finish)
    (wellFormed : start.WellFormed) : finish.WellFormed :=
  ⟨execution.preserves_rooted wellFormed.1,
    execution.preserves_cursorOwned wellFormed.2⟩

/-- Finite execution never rewinds the predicate-activation allocator. -/
theorem scopeHighWater_mono {count : Nat} {start finish : State}
    {events : List Observation} (execution : StepsN count start events finish) :
    start.scopeHighWater ≤ finish.scopeHighWater := by
  induction execution with
  | zero state => exact Nat.le_refl _
  | succ count start middle finish first rest head tail
      inductionHypothesis =>
      exact Nat.le_trans head.scopeHighWater_mono inductionHypothesis

/-- An absent already-issued activation remains absent through every finite
execution prefix. -/
theorem old_absence_preserved {count : Nat} {start finish : State}
    {events : List Observation} (execution : StepsN count start events finish)
    (scope : CutScopeId) (old : scope < start.scopeHighWater)
    (absent : scope ∉ start.liveCursorScopes) :
    scope ∉ finish.liveCursorScopes := by
  induction execution with
  | zero state => exact absent
  | succ count start middle finish first rest head tail
      inductionHypothesis =>
      have middleAbsent := head.old_absence_preserved scope old absent
      have middleOld := Nat.lt_of_lt_of_le old head.scopeHighWater_mono
      exact inductionHypothesis middleOld middleAbsent

/-- An absent already-issued activation cannot appear in any later prune
observation, because every prune must originate from a live cursor. -/
theorem old_absence_no_prune {count : Nat} {start finish : State}
    {events : List Observation} (execution : StepsN count start events finish)
    (scope : CutScopeId) (old : scope < start.scopeHighWater)
    (absent : scope ∉ start.liveCursorScopes) :
    scope ∉ prunedScopes events := by
  induction execution with
  | zero state => simp [prunedScopes]
  | succ count start middle finish first rest head tail
      inductionHypothesis =>
      rw [prunedScopes_append]
      simp only [List.mem_append]
      intro member
      rcases member with headPrune | tailPrune
      · exact absent (head.pruned_scope_origin scope headPrune)
      · have middleAbsent := head.old_absence_preserved scope old absent
        have middleOld := Nat.lt_of_lt_of_le old head.scopeHighWater_mono
        exact (inductionHypothesis middleOld middleAbsent) tailPrune

/-- Across a whole well-owned finite execution, each activation is reported
as pruned at most once.  This is the trace-level resource-linearity theorem:
one-step pruning removes the cursor, old identities cannot be resurrected,
and later prune events must originate from a live cursor. -/
theorem prunedScopes_nodup {count : Nat} {start finish : State}
    {events : List Observation} (execution : StepsN count start events finish)
    (owned : start.CursorOwned) : (prunedScopes events).Nodup := by
  induction execution with
  | zero state => simp [prunedScopes]
  | succ count start middle finish first rest head tail
      inductionHypothesis =>
      have middleOwned := head.preserves_cursorOwned owned
      have headNodup := head.prunedScopes_nodup owned
      have tailNodup := inductionHypothesis middleOwned
      rw [prunedScopes_append, List.nodup_append]
      refine ⟨headNodup, tailNodup, ?_⟩
      intro cursor headPrune later laterPrune equal
      subst later
      have old := head.pruned_scope_lt_highWater owned cursor headPrune
      have removed := head.pruned_scope_removed owned cursor headPrune
      have middleOld := Nat.lt_of_lt_of_le old head.scopeHighWater_mono
      exact (tail.old_absence_no_prune cursor middleOld removed) laterPrune

end StepsN

/-- Root execution starts inside cut scope zero.  All recursive predicate
activations receive strictly positive fresh scopes from `Session`. -/
def rootSession (resolverSession : LocalSession) : Session :=
  { resolver := resolverSession, nextCutScope := 1 }

def initialState (resolverSession : LocalSession) (goals : List Goal) : State :=
  .running (rootSession resolverSession)
    (.cutBoundary 0 (.task 0 goals []))

/-- Every source query enters through the distinguished root cut boundary. -/
theorem initialState_rooted (resolverSession : LocalSession)
    (goals : List Goal) : (initialState resolverSession goals).Rooted := by
  exact .running _ _ (.task 0 goals [])

/-- An initialized query owns no cursor before its first local call opens. -/
theorem initialState_cursorOwned (resolverSession : LocalSession)
    (goals : List Goal) : (initialState resolverSession goals).CursorOwned := by
  simp [initialState, State.CursorOwned, Search.CursorOwnership,
    Search.liveCursorScopes]

/-- Every initialized query satisfies the complete public structural
invariant. -/
theorem initialState_wellFormed (resolverSession : LocalSession)
    (goals : List Goal) : (initialState resolverSession goals).WellFormed :=
  ⟨initialState_rooted resolverSession goals,
    initialState_cursorOwned resolverSession goals⟩

/-! ## Concrete left-recursive program

The zero-arity clause below is deliberately tiny: `loop :- loop`.  It has no
clause-local variables, so the only unbounded structures in its execution are
the explicit finite search states and the monotone cut-scope allocator.  This
makes it a discriminating witness that recursion is represented by arbitrarily
long finite prefixes rather than by an eager infinite answer bag or fabricated
completion. -/

private def leftRecursivePredicate : String := "$pleatta_left_recursive"

private def leftRecursiveClause : LocalClause :=
  { predicate := leftRecursivePredicate
    arguments := []
    body := [.call leftRecursivePredicate []] }

private def leftRecursiveResolver : LocalSession :=
  { database := Database.empty.assertz leftRecursiveClause
    nextFresh := 0 }

private def leftRecursiveSession (nextCutScope : Nat) : Session :=
  { resolver := leftRecursiveResolver
    nextCutScope := nextCutScope }

private def leftRecursiveRequest : CallRequest :=
  requestFor leftRecursivePredicate [] []

private def leftRecursiveBranch : ClauseBranch :=
  { sourceId := 0
    callGeneration := 1
    freshSubstitution := []
    headEquations := []
    body := [.call leftRecursivePredicate []]
    bindings := []
    firstFresh := 0
    nextFresh := 0 }

private def leftRecursiveCursor : PreparedCursor :=
  { callGeneration := 1
    predicate := leftRecursivePredicate
    arguments := []
    bindings := []
    reservationStart := 0
    remaining := [leftRecursiveBranch]
    reservedUntil := 0 }

private def leftRecursiveTailCursor : PreparedCursor :=
  leftRecursiveCursor.advance leftRecursiveBranch []

private def leftRecursiveEntered : EnteredClause :=
  leftRecursiveBranch.enter []

private theorem prepareCall_leftRecursive :
    prepareCall leftRecursiveResolver leftRecursiveRequest =
      (leftRecursiveCursor, leftRecursiveResolver) := by
  rfl

private theorem openedFor_leftRecursive (nextCutScope : Nat) :
    openedFor (leftRecursiveSession nextCutScope) leftRecursivePredicate [] [] =
      { scope := nextCutScope
        cursor := leftRecursiveCursor
        session := leftRecursiveSession (nextCutScope + 1) } := by
  rfl

private theorem leftRecursiveHeadResolution :
    HeadResolution leftRecursiveBranch [] := by
  refine ⟨[], ?_, rfl⟩
  exact ⟨[], .nil, rfl⟩

private theorem leftRecursivePull :
    LocalPull leftRecursiveCursor
      (.reply leftRecursiveEntered leftRecursiveTailCursor) := by
  exact .matched leftRecursiveCursor leftRecursiveBranch [] [] rfl
    leftRecursiveHeadResolution

/-- A finite spine of already-entered recursive activations.  `depth` counts
the retained clause alternatives outside the currently demanded cursor. -/
private def leftRecursiveChain : Nat → CutScopeId → Search
  | 0, scope => .cutBoundary scope (.clauses scope leftRecursiveCursor)
  | depth + 1, scope =>
      .cutBoundary scope
        (.choice scope
          (.product scope (leftRecursiveChain depth (scope + 1)) [])
          (.clauses scope leftRecursiveTailCursor))

/-- The intermediate state after the innermost clause occurrence has been
pulled but before its recursive body opens the next activation. -/
private def leftRecursivePulled : Nat → CutScopeId → Search
  | 0, scope =>
      .cutBoundary scope
        (.choice scope
          (.task scope [.call leftRecursivePredicate []] [])
          (.clauses scope leftRecursiveTailCursor))
  | depth + 1, scope =>
      .cutBoundary scope
        (.choice scope
          (.product scope (leftRecursivePulled depth (scope + 1)) [])
          (.clauses scope leftRecursiveTailCursor))

private theorem leftRecursiveChain_pull (depth : Nat) (scope : CutScopeId)
    (session : Session) :
    RawStep session (leftRecursiveChain depth scope) [] .none session
      (.running (leftRecursivePulled depth scope)) := by
  induction depth generalizing scope with
  | zero =>
      exact .cutBoundaryProgress scope _ _ [] session session
        (.clausesPull scope leftRecursiveCursor
          (.reply leftRecursiveEntered leftRecursiveTailCursor) session
          leftRecursivePull)
  | succ depth inductionHypothesis =>
      exact .cutBoundaryProgress scope _ _ [] session session
        (.choiceProgress scope _ _ _ [] session session
          (.productProgress scope _ _ [] [] .none session session
            (inductionHypothesis (scope + 1))
            (by simp [Trace.AnswerFree])))

private theorem leftRecursivePulled_open (depth : Nat)
    (scope : CutScopeId) :
    RawStep (leftRecursiveSession (scope + depth + 1))
      (leftRecursivePulled depth scope) [.opened leftRecursiveRequest] .none
      (leftRecursiveSession (scope + depth + 2))
      (.running (leftRecursiveChain (depth + 1) scope)) := by
  induction depth generalizing scope with
  | zero =>
      have opened := RawStep.taskCall scope leftRecursivePredicate [] [] []
        (leftRecursiveSession (scope + 1))
      simpa [leftRecursivePulled, leftRecursiveChain, leftRecursiveRequest,
        openedFor_leftRecursive, Nat.add_assoc] using
        (RawStep.cutBoundaryProgress scope _ _
          [.opened leftRecursiveRequest]
          (leftRecursiveSession (scope + 1))
          (leftRecursiveSession (scope + 2))
          (RawStep.choiceProgress scope _ _ _
            [.opened leftRecursiveRequest]
            (leftRecursiveSession (scope + 1))
            (leftRecursiveSession (scope + 2)) opened))
  | succ depth inductionHypothesis =>
      have inner :
          RawStep (leftRecursiveSession (scope + (depth + 1) + 1))
            (leftRecursivePulled depth (scope + 1))
            [.opened leftRecursiveRequest] .none
            (leftRecursiveSession (scope + (depth + 1) + 2))
            (.running (leftRecursiveChain (depth + 1) (scope + 1))) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (inductionHypothesis (scope + 1))
      have lifted := RawStep.productProgress scope _ _ []
        [.opened leftRecursiveRequest] .none
        (leftRecursiveSession (scope + (depth + 1) + 1))
        (leftRecursiveSession (scope + (depth + 1) + 2)) inner
        (by simp [Trace.AnswerFree])
      simpa [leftRecursivePulled, leftRecursiveChain, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using
        (RawStep.cutBoundaryProgress scope _ _
          [.opened leftRecursiveRequest]
          (leftRecursiveSession (scope + (depth + 1) + 1))
          (leftRecursiveSession (scope + (depth + 1) + 2))
          (RawStep.choiceProgress scope _ _ _
            [.opened leftRecursiveRequest]
            (leftRecursiveSession (scope + (depth + 1) + 1))
            (leftRecursiveSession (scope + (depth + 1) + 2)) lifted))

private def leftRecursiveOpenState (depth : Nat) : State :=
  .running (leftRecursiveSession (depth + 2))
    (.cutBoundary 0
      (.product 0 (leftRecursiveChain depth 1) []))

private def leftRecursivePulledState (depth : Nat) : State :=
  .running (leftRecursiveSession (depth + 2))
    (.cutBoundary 0
      (.product 0 (leftRecursivePulled depth 1) []))

private theorem leftRecursive_pull_transition (depth : Nat) :
    Transition (leftRecursiveOpenState depth) []
      (leftRecursivePulledState depth) := by
  have inner := leftRecursiveChain_pull depth 1
    (leftRecursiveSession (depth + 2))
  exact .ordinary _ _ _ _ _
    (.cutBoundaryProgress 0 _ _ [] _ _
      (.productProgress 0 _ _ [] [] .none _ _ inner
        (by simp [Trace.AnswerFree])))

private theorem leftRecursive_open_transition (depth : Nat) :
    Transition (leftRecursivePulledState depth)
      [.opened leftRecursiveRequest] (leftRecursiveOpenState (depth + 1)) := by
  have inner :
      RawStep (leftRecursiveSession (depth + 2))
        (leftRecursivePulled depth 1) [.opened leftRecursiveRequest] .none
        (leftRecursiveSession (depth + 3))
        (.running (leftRecursiveChain (depth + 1) 1)) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (leftRecursivePulled_open depth 1)
  simpa [leftRecursivePulledState, leftRecursiveOpenState,
    RawTarget.toState, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (Transition.ordinary _ _
      (leftRecursiveSession (depth + 2))
      (leftRecursiveSession (depth + 3)) _
      (RawStep.cutBoundaryProgress 0 _ _
        [.opened leftRecursiveRequest]
        (leftRecursiveSession (depth + 2))
        (leftRecursiveSession (depth + 3))
        (RawStep.productProgress 0 _ _ []
          [.opened leftRecursiveRequest] .none
          (leftRecursiveSession (depth + 2))
          (leftRecursiveSession (depth + 3)) inner
          (by simp [Trace.AnswerFree]))))

private theorem leftRecursive_cycle (depth : Nat) :
    StepsN 2 (leftRecursiveOpenState depth) [.opened leftRecursiveRequest]
      (leftRecursiveOpenState (depth + 1)) := by
  exact StepsN.succ 1 _ _ _ [] [.opened leftRecursiveRequest]
    (leftRecursive_pull_transition depth)
    (StepsN.succ 0 _ _ _ [.opened leftRecursiveRequest] []
      (leftRecursive_open_transition depth)
      (StepsN.zero _))

private def leftRecursiveEvents : Nat → List Observation
  | 0 => []
  | cycles + 1 =>
      leftRecursiveEvents cycles ++ [.opened leftRecursiveRequest]

private theorem leftRecursiveEvents_length (cycles : Nat) :
    (leftRecursiveEvents cycles).length = cycles := by
  induction cycles with
  | zero => rfl
  | succ cycles inductionHypothesis =>
      simp [leftRecursiveEvents, inductionHypothesis]

private theorem leftRecursiveEvents_only_opened (cycles : Nat) :
    ∀ event ∈ leftRecursiveEvents cycles,
      event = .opened leftRecursiveRequest := by
  intro event member
  induction cycles generalizing event with
  | zero => simp [leftRecursiveEvents] at member
  | succ cycles inductionHypothesis =>
      simp only [leftRecursiveEvents, List.mem_append, List.mem_singleton]
        at member
      exact member.elim (inductionHypothesis event) id

private theorem leftRecursive_cycles (cycles : Nat) :
    StepsN (2 * cycles) (leftRecursiveOpenState 0)
      (leftRecursiveEvents cycles) (leftRecursiveOpenState cycles) := by
  induction cycles with
  | zero => exact StepsN.zero _
  | succ cycles inductionHypothesis =>
      simpa [leftRecursiveEvents, Nat.mul_succ] using
        (StepsN.trans inductionHypothesis (leftRecursive_cycle cycles))

private theorem leftRecursive_initial_open :
    Transition
      (initialState leftRecursiveResolver
        [.call leftRecursivePredicate []])
      [.opened leftRecursiveRequest] (leftRecursiveOpenState 0) := by
  exact .ordinary _ _ _ _ _
    (.cutBoundaryProgress 0 _ _ [.opened leftRecursiveRequest]
      (leftRecursiveSession 1) (leftRecursiveSession 2)
      (.taskCall 0 leftRecursivePredicate [] [] []
        (leftRecursiveSession 1)))

/-- The actual local clause `loop :- loop` has exact arbitrarily long finite
prefixes containing only call-open observations.  After every such positive
prefix the machine is still running: no answer, effect, exception, or
completion is fabricated.  The exact transition count prevents a reflexive
`Steps` proof from masquerading as divergence evidence. -/
theorem left_recursive_arbitrarily_long_open_prefix (cycles : Nat) :
    ∃ resolverSession predicate request events session search,
      request = requestFor predicate [] [] ∧
      events.length = cycles + 1 ∧
      (∀ event ∈ events, event = .opened request) ∧
      (Trace.Observation.completed : Observation) ∉ events ∧
      StepsN (2 * cycles + 1)
        (initialState resolverSession [.call predicate []]) events
        (.running session search) := by
  let events := [.opened leftRecursiveRequest] ++ leftRecursiveEvents cycles
  refine ⟨leftRecursiveResolver, leftRecursivePredicate,
    leftRecursiveRequest, events, (leftRecursiveSession (cycles + 2)),
    (.cutBoundary 0 (.product 0 (leftRecursiveChain cycles 1) [])),
    rfl, ?_, ?_, ?_, ?_⟩
  · simp [events, leftRecursiveEvents_length]
  · intro event member
    rcases List.mem_append.mp member with first | rest
    · simpa only [List.mem_singleton] using first
    · exact leftRecursiveEvents_only_opened cycles event rest
  · intro completedMember
    have impossible :
        (Trace.Observation.completed : Observation) =
          .opened leftRecursiveRequest := by
      rcases List.mem_append.mp completedMember with first | rest
      · simpa only [List.mem_singleton] using first
      · exact leftRecursiveEvents_only_opened cycles _ rest
    cases impossible
  · have first : StepsN 1
        (initialState leftRecursiveResolver
          [.call leftRecursivePredicate []])
        [.opened leftRecursiveRequest] (leftRecursiveOpenState 0) :=
      StepsN.succ 0 _ _ _ [.opened leftRecursiveRequest] []
        leftRecursive_initial_open (StepsN.zero _)
    simpa [events, leftRecursiveOpenState, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
      (StepsN.trans first (leftRecursive_cycles cycles))

/-! ## Structural scheduling and clause-cut witnesses -/

/-- A left truth goal advances before an immediately-answering right branch.
This is the positive, one-step form of fixed leftmost scheduling. -/
theorem left_truth_steps_before_right_answer (scope : CutScopeId)
    (leftBindings rightBindings : Substitution) (session : Session) :
    RawStep session
      (.choice scope
        (.task scope [.truth] leftBindings)
        (.task scope [] rightBindings))
      [] .none session
      (.running
        (.choice scope
          (.task scope [] leftBindings)
          (.task scope [] rightBindings))) := by
  exact .choiceProgress scope _ _ _ [] session session
    (.taskTruth scope [] leftBindings session)

/-- A truth task has exactly its silent left-to-right successor. -/
theorem taskTruth_step_exact (scope : CutScopeId) (rest : List Goal)
    (bindings : Substitution) (session after : Session)
    (events : List Observation) (signal : Trace.CutSignal)
    (target : RawTarget)
    (step : RawStep session (.task scope (.truth :: rest) bindings)
      events signal after target) :
    events = [] ∧ signal = .none ∧ after = session ∧
      target = .running (.task scope rest bindings) := by
  cases step
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- While the left truth task is still producing a running state, its
enclosing choice can emit no observation. -/
theorem choice_left_truth_running_events_empty (scope : CutScopeId)
    (leftBindings rightBindings : Substitution) (session after : Session)
    (events : List Observation) (next : Search)
    (step : RawStep session
      (.choice scope
        (.task scope [.truth] leftBindings)
        (.task scope [] rightBindings))
      events .none after (.running next)) : events = [] := by
  cases step with
  | choiceProgress scope left right next events before after child =>
      exact (taskTruth_step_exact scope [] leftBindings session after events
        .none (.running next) child).1
  | choiceComplete scope left right before after child =>
      have exact := taskTruth_step_exact scope [] leftBindings session after
        [.completed] .none (.terminal .completed) child
      simp at exact

/-- The same state cannot expose the right answer in that step.  A scheduler
with a right-progress/fair-interleaving rule would falsify this theorem. -/
theorem left_truth_cannot_emit_right_answer (scope : CutScopeId)
    (leftBindings rightBindings : Substitution) (session : Session) :
    ¬ ∃ after next,
      RawStep session
        (.choice scope
          (.task scope [.truth] leftBindings)
          (.task scope [] rightBindings))
        [.answer rightBindings] .none after (.running next) := by
  rintro ⟨after, next, step⟩
  have empty := choice_left_truth_running_events_empty scope leftBindings
    rightBindings session after [.answer rightBindings] next step
  simp at empty

/-- Deliberately wrong scheduler fragment: it is allowed to step the right
child while the left child remains live.  This relation is only a
countermodel; no execution theorem may use it. -/
inductive WrongRightStep : Session → Search → List Observation →
    Trace.CutSignal → Session → RawTarget → Prop where
  | choiceRight (scope : CutScopeId) (left right next : Search)
      (events : List Observation) (before after : Session)
      (step : RawStep before right events .none after (.running next)) :
      WrongRightStep before (.choice scope left right) events .none after
        (.running (.choice scope left next))

/-- The wrong scheduler can expose the right answer before even reducing the
left truth goal. -/
theorem wrong_right_first_emits_out_of_order (scope : CutScopeId)
    (leftBindings rightBindings : Substitution) (session : Session) :
    WrongRightStep session
      (.choice scope
        (.task scope [.truth] leftBindings)
        (.task scope [] rightBindings))
      [.answer rightBindings] .none session
      (.running
        (.choice scope
          (.task scope [.truth] leftBindings)
          .done)) := by
  exact .choiceRight scope _ _ _ [.answer rightBindings] session session
    (.taskAnswer scope rightBindings session)

/-- Exact-trace equivalence rejects the wrong scheduler on the witness above:
its first observable answer is not a legal reference transition. -/
theorem wrong_right_first_not_reference (scope : CutScopeId)
    (leftBindings rightBindings : Substitution) (session : Session) :
    ¬ RawStep session
      (.choice scope
        (.task scope [.truth] leftBindings)
        (.task scope [] rightBindings))
      [.answer rightBindings] .none session
      (.running
        (.choice scope
          (.task scope [.truth] leftBindings)
          .done)) := by
  intro step
  exact left_truth_cannot_emit_right_answer scope leftBindings rightBindings
    session ⟨session,
      (.choice scope (.task scope [.truth] leftBindings) .done), step⟩

/-- Opening a recursive local call is one finite transition.  No recursive
body is preconstructed and the caller tail remains outside the callee's cut
boundary under `product`. -/
theorem call_opens_finite_activation (scope : CutScopeId)
    (predicate : String) (arguments : List Term) (rest : List Goal)
    (bindings : Substitution) (session : Session) :
    RawStep session
      (.task scope (.call predicate arguments :: rest) bindings)
      [.opened (requestFor predicate arguments bindings)] .none
      (openedFor session predicate arguments bindings).session
      (.running
        (.product scope
          (.cutBoundary
            (openedFor session predicate arguments bindings).scope
            (.clauses
              (openedFor session predicate arguments bindings).scope
              (openedFor session predicate arguments bindings).cursor))
          rest)) := by
  exact .taskCall scope predicate arguments rest bindings session

/-- A successful pull puts the entered raw body on the left and the frozen
remaining clause cursor on the right, both at the predicate cut scope. -/
theorem matched_clause_splices_body_first (scope : CutScopeId)
    {cursor next : PreparedCursor} {entered : EnteredClause}
    (session : Session) (pulled : LocalPull cursor (.reply entered next)) :
    RawStep session (.clauses scope cursor) [] .none session
      (.running
        (.choice scope
          (.task scope entered.rawBody entered.bindings)
          (.clauses scope next))) := by
  exact .clausesPull scope cursor (.reply entered next) session pulled

/-- A cut in the active clause branch discards the retained later-clause
cursor and records that pruning before the predicate boundary catches the
commit. -/
theorem cut_prunes_later_clauses (scope : CutScopeId)
    (cursor : PreparedCursor) (bindings : Substitution) (session : Session) :
    RawStep session
      (.cutBoundary scope
        (.choice scope
          (.task scope [.cut] bindings)
          (.clauses scope cursor)))
      [.pruned { scope := scope, cursor := cursor }] .none session
      (.running
        (.cutBoundary scope (.task scope [] bindings))) := by
  exact .cutBoundaryCatch scope _ _
    [.pruned { scope := scope, cursor := cursor }] session session
    (.choiceCommitHere scope _ _ _ [] session session
      (.taskCut scope [] bindings session))

/-- Anti-vacuity witness: structural scope well-formedness alone would permit
two copies of the same cursor activation, but linear ownership rejects it. -/
theorem duplicated_cursor_activation_rejected (scope highWater : CutScopeId)
    (cursor : PreparedCursor) :
    ¬ (Search.choice scope
        (.clauses scope cursor)
        (.clauses scope cursor)).CursorOwnership highWater := by
  simp [Search.CursorOwnership, Search.liveCursorScopes]

/-- Anti-vacuity witness: a search cannot forge the allocator's next, not-yet
issued activation identity. -/
theorem future_cursor_activation_rejected (highWater : CutScopeId)
    (cursor : PreparedCursor) :
    ¬ (Search.clauses highWater cursor).CursorOwnership highWater := by
  simp [Search.CursorOwnership, Search.liveCursorScopes]

/-- Snapshot equality is deliberately not cursor identity.  Two independent
activations may carry the same prepared value and remain valid resources when
their certified activation scopes are distinct. -/
theorem equal_snapshots_distinct_activations_owned
    (outer first second highWater : CutScopeId) (cursor : PreparedCursor)
    (different : first ≠ second) (firstBound : first < highWater)
    (secondBound : second < highWater) :
    (Search.choice outer
      (.cutBoundary first (.clauses first cursor))
      (.cutBoundary second (.clauses second cursor))).CursorOwnership
        highWater := by
  simp [Search.CursorOwnership, Search.liveCursorScopes, different,
    firstBound, secondBound]

/-- The smallest successful query demonstrates the answer/completion split:
the answer is observed first and whole-search exhaustion is a later event. -/
theorem truth_exact_trace (resolverSession : LocalSession) :
    StepsN 3 (initialState resolverSession [.truth])
      [.answer [], .completed]
      (.terminal (rootSession resolverSession) .completed) := by
  let session := rootSession resolverSession
  let start : State :=
    .running session (.cutBoundary 0 (.task 0 [.truth] []))
  let afterTruth : State :=
    .running session (.cutBoundary 0 (.task 0 [] []))
  let afterAnswer : State :=
    .running session (.cutBoundary 0 .done)
  let finish : State := .terminal session .completed
  have first : Transition start [] afterTruth := by
    exact .ordinary _ _ session session _
      (.cutBoundaryProgress 0 _ _ [] session session
        (.taskTruth 0 [] [] session))
  have second : Transition afterTruth [.answer []] afterAnswer := by
    exact .ordinary _ _ session session _
      (.cutBoundaryProgress 0 _ _ [.answer []] session session
        (.taskAnswer 0 [] session))
  have third : Transition afterAnswer [.completed] finish := by
    exact .ordinary _ _ session session _
      (.cutBoundaryComplete 0 _ session session (.done session))
  change StepsN 3 start [.answer [], .completed] finish
  simpa using
    (StepsN.succ 2 start afterTruth finish [] [.answer [], .completed] first
      (StepsN.succ 1 afterTruth afterAnswer finish [.answer []] [.completed]
        second
        (StepsN.succ 0 afterAnswer finish finish [.completed] [] third
          (StepsN.zero finish))))

end PLeaTTa.PeTTaSpec.PrologCore.GoalSemantics
