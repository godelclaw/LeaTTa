/-
Module: PLeaTTa.PeTTaSpec.PrologGoalSemantics
Purpose: Independent finite small-step execution of locally owned Prolog goals.
Trusted boundary: none for the local core developed here
Main exports: Session, Search, RawStep, Transition, StepsN
-/
import PLeaTTa.PeTTaSpec.PrologCopy
import PLeaTTa.PeTTaSpec.PrologDatabaseActions

namespace PLeaTTa.PeTTaSpec.PrologCore.GoalSemantics

open OpenSubstitution
open Resolver
open Canonical
open Copy
open DatabaseActions

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
abbrev ExceptionScopeId := Trace.ExceptionScopeId
abbrev CollectionScopeId := Trace.CollectionScopeId

/-- Identity-bearing handle for one live local predicate cursor.

The prepared snapshot alone is not an identity: two independent calls can
prepare extensionally equal snapshots.  The fresh predicate cut scope is the
activation identifier allocated by the certified layer, while `cursor` keeps
the exact frozen clauses that would be discarded. -/
structure CursorToken where
  scope : CutScopeId
  cursor : PreparedCursor
deriving Repr, Inhabited

/-- Ordered observations of the certified local lane.  Dynamic database
mutations have their own typed effect vocabulary.  The clause-provider reply
protocol remains `Empty`-effect below, so an oracle still cannot manufacture
one of these effects. -/
abbrev Observation :=
  Trace.Observation CallRequest CursorToken Substitution
    LocalDatabaseEffect Term

/-- Retain only database mutations from one exact ordered observation batch. -/
def databaseEffects : List Observation → List LocalDatabaseEffect
  | [] => []
  | .effect effect :: rest => effect :: databaseEffects rest
  | _ :: rest => databaseEffects rest

@[simp] theorem databaseEffects_append (left right : List Observation) :
    databaseEffects (left ++ right) =
      databaseEffects left ++ databaseEffects right := by
  induction left with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      cases event <;> simp [databaseEffects, inductionHypothesis]

@[simp] theorem databaseEffects_pruned (cursors : List CursorToken) :
    databaseEffects (cursors.map Trace.Observation.pruned) = [] := by
  induction cursors with
  | nil => rfl
  | cons cursor rest inductionHypothesis =>
      simp [databaseEffects, inductionHypothesis]

/-- Internal evidence retained while a finite-tree exception unwinds.

`ball` is the copied exception term visible to catchers and eventual external
observers.  `throwBindings` is the protected goal's substitution at the throw
point.  SWI-Prolog deliberately tests a catcher against that still-bound
environment before unwinding; if selected, recovery is then reconstructed in
the entry environment.  Keeping this evidence internal preserves the public
exception observation as the ball alone.

The future source-level `throw/1` specialization must prove that `ball` is the
correct fresh finite-tree copy.  Rational trees and attributed variables stay
outside this first local fragment. -/
structure RaisedException where
  ball : Term
  throwBindings : Substitution
deriving Repr, Inhabited

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
remain outside the search tree.  Cut, exception, and collection identities
have separate nominal types and separate monotone allocators; none is
backtracked. -/
structure Session where
  resolver : LocalSession := {}
  nextCutScope : Nat := 1
  nextExceptionScope : Nat := 1
  nextCollectionScope : Nat := 1
deriving Repr, Inhabited

/-- Reachability invariant for the persistent logical-update history. -/
def Session.DatabaseClosed (session : Session) : Prop :=
  DatabaseReachable session.resolver.database

/-- Replace the persistent database and fresh frontier together, leaving all
three typed control allocators untouched. -/
def Session.withDatabaseAndFresh (session : Session) (database : Database)
    (nextFresh : Nat) : Session :=
  { session with
    resolver :=
      { session.resolver with
        database := database
        nextFresh := nextFresh } }

/-- Replace only the persistent database. -/
def Session.withDatabase (session : Session) (database : Database) : Session :=
  session.withDatabaseAndFresh database session.resolver.nextFresh

@[simp] theorem Session.withDatabaseAndFresh_database
    (session : Session) (database : Database) (nextFresh : Nat) :
    (session.withDatabaseAndFresh database nextFresh).resolver.database =
      database := rfl

@[simp] theorem Session.withDatabaseAndFresh_nextFresh
    (session : Session) (database : Database) (nextFresh : Nat) :
    (session.withDatabaseAndFresh database nextFresh).resolver.nextFresh =
      nextFresh := rfl

@[simp] theorem Session.withDatabaseAndFresh_nextCutScope
    (session : Session) (database : Database) (nextFresh : Nat) :
    (session.withDatabaseAndFresh database nextFresh).nextCutScope =
      session.nextCutScope := rfl

@[simp] theorem Session.withDatabaseAndFresh_nextExceptionScope
    (session : Session) (database : Database) (nextFresh : Nat) :
    (session.withDatabaseAndFresh database nextFresh).nextExceptionScope =
      session.nextExceptionScope := rfl

@[simp] theorem Session.withDatabaseAndFresh_nextCollectionScope
    (session : Session) (database : Database) (nextFresh : Nat) :
    (session.withDatabaseAndFresh database nextFresh).nextCollectionScope =
      session.nextCollectionScope := rfl

/-- The complete result of opening one locally owned call. -/
structure OpenedCall where
  scope : CutScopeId
  cursor : PreparedCursor
  session : Session
deriving Repr, Inhabited

/-- Fresh, nominally distinct delimiters allocated when entering `catch/3`.
The exception identity cannot be supplied where a cut identity is required;
both high-waters advance before the protected goal starts. -/
structure OpenedCatch where
  cutScope : CutScopeId
  handlerScope : ExceptionScopeId
  session : Session
deriving Repr

/-- Fresh, nominally distinct delimiters allocated when entering `findall/3`.
The generator receives its own cut scope; the collector receives a separate
identity that cannot be confused with either cut or exception handling. -/
structure OpenedFindall where
  cutScope : CutScopeId
  collectionScope : CollectionScopeId
  session : Session
deriving Repr

/-- One finite-tree exception copy and the non-backtrackable allocator state
after reserving its fresh variables. -/
structure OpenedThrow where
  prepared : PreparedTermCopy
  exception : RaisedException
  session : Session
deriving Repr, Inhabited

/-- One copied template instance and the non-backtrackable allocator state
after reserving its fresh variables.  The generator answer is materialized
before copying, preserving sharing while preventing its bindings from escaping
the collection boundary. -/
structure CollectedTemplate where
  prepared : PreparedTermCopy
  session : Session
deriving Repr, Inhabited

/-- Allocate a fresh predicate cut scope and prepare the call-start clause
snapshot.  The fresh-name and cut-scope allocators advance before any clause
body runs; the independent exception allocator is preserved. -/
def openLocalCall (session : Session) (request : CallRequest) : OpenedCall :=
  let prepared := prepareCall session.resolver request
  { scope := session.nextCutScope
    cursor := prepared.1
    session :=
      { session with
        resolver := prepared.2
        nextCutScope := session.nextCutScope + 1 } }

/-- Allocate the independent cut and exception delimiters for one `catch/3`
activation.  The resolver and its fresh-name/database state are unchanged. -/
def openCatch (session : Session) : OpenedCatch :=
  { cutScope := session.nextCutScope
    handlerScope := { index := session.nextExceptionScope }
    session :=
      { session with
        nextCutScope := session.nextCutScope + 1
        nextExceptionScope := session.nextExceptionScope + 1 } }

/-- Allocate independent generator-cut and collection delimiters.  The
resolver, exception allocator, and fresh-name high-water are unchanged until
the generator runs or an answer template is copied. -/
def openFindall (session : Session) : OpenedFindall :=
  { cutScope := session.nextCutScope
    collectionScope := { index := session.nextCollectionScope }
    session :=
      { session with
        nextCutScope := session.nextCutScope + 1
        nextCollectionScope := session.nextCollectionScope + 1 } }

/-- Materialize and injectively alpha-copy one exception term above the
resolver's global fresh high-water.  Only that high-water changes; database,
cut scopes, and exception scopes are preserved. -/
def openThrow (session : Session) (raw : Term)
    (bindings : Substitution) : OpenedThrow :=
  let prepared :=
    prepareTermCopy session.resolver.nextFresh bindings raw
  { prepared := prepared
    exception :=
      { ball := prepared.copied
        throwBindings := bindings }
    session :=
      { session with
        resolver :=
          { session.resolver with nextFresh := prepared.nextFresh } } }

/-- Materialize one successful generator's template and injectively alpha-copy
it above the global fresh high-water.  Only the resolver's allocator advances;
the database and all delimiter allocators are preserved. -/
def collectTemplate (session : Session) (template : Term)
    (answerBindings : Substitution) : CollectedTemplate :=
  let prepared :=
    prepareTermCopy session.resolver.nextFresh answerBindings template
  { prepared := prepared
    session :=
      { session with
        resolver :=
          { session.resolver with nextFresh := prepared.nextFresh } } }

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

/-- A newly opened local call starts its complete eager reservation no lower
than the incoming global fresh high-water.  The request ceiling may move the
start farther forward, but can never roll it back. -/
theorem openLocalCall_reservationStart_ge (session : Session)
    (request : CallRequest) :
    session.resolver.nextFresh ≤
      (openLocalCall session request).cursor.reservationStart := by
  exact Nat.le_max_left _ _

@[simp] theorem openLocalCall_nextCutScope (session : Session)
    (request : CallRequest) :
    (openLocalCall session request).session.nextCutScope =
      session.nextCutScope + 1 := rfl

@[simp] theorem openLocalCall_nextExceptionScope (session : Session)
    (request : CallRequest) :
    (openLocalCall session request).session.nextExceptionScope =
      session.nextExceptionScope := rfl

@[simp] theorem openLocalCall_nextCollectionScope (session : Session)
    (request : CallRequest) :
    (openLocalCall session request).session.nextCollectionScope =
      session.nextCollectionScope := rfl

@[simp] theorem openCatch_cutScope (session : Session) :
    (openCatch session).cutScope = session.nextCutScope := rfl

@[simp] theorem openCatch_handlerScope (session : Session) :
    (openCatch session).handlerScope =
      ({ index := session.nextExceptionScope } : ExceptionScopeId) := rfl

@[simp] theorem openCatch_resolver (session : Session) :
    (openCatch session).session.resolver = session.resolver := rfl

@[simp] theorem openCatch_nextCutScope (session : Session) :
    (openCatch session).session.nextCutScope = session.nextCutScope + 1 := rfl

@[simp] theorem openCatch_nextExceptionScope (session : Session) :
    (openCatch session).session.nextExceptionScope =
      session.nextExceptionScope + 1 := rfl

@[simp] theorem openCatch_nextCollectionScope (session : Session) :
    (openCatch session).session.nextCollectionScope =
      session.nextCollectionScope := rfl

@[simp] theorem openFindall_cutScope (session : Session) :
    (openFindall session).cutScope = session.nextCutScope := rfl

@[simp] theorem openFindall_collectionScope (session : Session) :
    (openFindall session).collectionScope =
      ({ index := session.nextCollectionScope } : CollectionScopeId) := rfl

@[simp] theorem openFindall_resolver (session : Session) :
    (openFindall session).session.resolver = session.resolver := rfl

@[simp] theorem openFindall_nextCutScope (session : Session) :
    (openFindall session).session.nextCutScope =
      session.nextCutScope + 1 := rfl

@[simp] theorem openFindall_nextExceptionScope (session : Session) :
    (openFindall session).session.nextExceptionScope =
      session.nextExceptionScope := rfl

@[simp] theorem openFindall_nextCollectionScope (session : Session) :
    (openFindall session).session.nextCollectionScope =
      session.nextCollectionScope + 1 := rfl

@[simp] theorem openThrow_ball (session : Session) (raw : Term)
    (bindings : Substitution) :
    (openThrow session raw bindings).exception.ball =
      (openThrow session raw bindings).prepared.copied := rfl

@[simp] theorem openThrow_throwBindings (session : Session) (raw : Term)
    (bindings : Substitution) :
    (openThrow session raw bindings).exception.throwBindings = bindings := rfl

@[simp] theorem openThrow_database (session : Session) (raw : Term)
    (bindings : Substitution) :
    (openThrow session raw bindings).session.resolver.database =
      session.resolver.database := rfl

@[simp] theorem openThrow_nextCutScope (session : Session) (raw : Term)
    (bindings : Substitution) :
    (openThrow session raw bindings).session.nextCutScope =
      session.nextCutScope := rfl

@[simp] theorem openThrow_nextExceptionScope (session : Session) (raw : Term)
    (bindings : Substitution) :
    (openThrow session raw bindings).session.nextExceptionScope =
      session.nextExceptionScope := rfl

@[simp] theorem openThrow_nextCollectionScope (session : Session)
    (raw : Term) (bindings : Substitution) :
    (openThrow session raw bindings).session.nextCollectionScope =
      session.nextCollectionScope := rfl

theorem openThrow_nextFresh_mono (session : Session) (raw : Term)
    (bindings : Substitution) :
    session.resolver.nextFresh ≤
      (openThrow session raw bindings).session.resolver.nextFresh := by
  exact prepareTermCopy_next_ge_allocator _ _ _

/-- The exception ball is an injective fresh copy of the term materialized at
the throw point. -/
theorem openThrow_isFreshCopy (session : Session) (raw : Term)
    (bindings : Substitution) :
    Term.IsFreshCopy
      (openThrow session raw bindings).prepared.materialized
      (openThrow session raw bindings).exception.ball
      (openThrow session raw bindings).prepared.firstFresh
      (openThrow session raw bindings).prepared.nextFresh := by
  exact prepareTermCopy_isFreshCopy _ _ _

/-- Throw-time bindings cannot rewrite the freshly copied exception ball. -/
theorem openThrow_ball_stable_raw (session : Session) (raw : Term)
    (bindings : Substitution) :
    bindings.applyTerm (openThrow session raw bindings).exception.ball =
      (openThrow session raw bindings).exception.ball := by
  exact prepareTermCopy_stable _ _ _

@[simp] theorem collectTemplate_copied (session : Session) (template : Term)
    (answerBindings : Substitution) :
    (collectTemplate session template answerBindings).prepared.copied =
      Copy.copyTerm
        (collectTemplate session template answerBindings).prepared.firstFresh
        (answerBindings.applyTerm template) := rfl

@[simp] theorem collectTemplate_database (session : Session) (template : Term)
    (answerBindings : Substitution) :
    (collectTemplate session template answerBindings).session.resolver.database =
      session.resolver.database := rfl

@[simp] theorem collectTemplate_nextCutScope (session : Session)
    (template : Term) (answerBindings : Substitution) :
    (collectTemplate session template answerBindings).session.nextCutScope =
      session.nextCutScope := rfl

@[simp] theorem collectTemplate_nextExceptionScope (session : Session)
    (template : Term) (answerBindings : Substitution) :
    (collectTemplate session template answerBindings).session.nextExceptionScope =
      session.nextExceptionScope := rfl

@[simp] theorem collectTemplate_nextCollectionScope (session : Session)
    (template : Term) (answerBindings : Substitution) :
    (collectTemplate session template answerBindings).session.nextCollectionScope =
      session.nextCollectionScope := rfl

theorem collectTemplate_nextFresh_mono (session : Session) (template : Term)
    (answerBindings : Substitution) :
    session.resolver.nextFresh ≤
      (collectTemplate session template answerBindings).session.resolver.nextFresh := by
  exact prepareTermCopy_next_ge_allocator _ _ _

/-- Each collected element is an injective fresh copy of the successful
generator's materialized template. -/
theorem collectTemplate_isFreshCopy (session : Session) (template : Term)
    (answerBindings : Substitution) :
    Term.IsFreshCopy
      (collectTemplate session template answerBindings).prepared.materialized
      (collectTemplate session template answerBindings).prepared.copied
      (collectTemplate session template answerBindings).prepared.firstFresh
      (collectTemplate session template answerBindings).prepared.nextFresh := by
  exact prepareTermCopy_isFreshCopy _ _ _

/-- Generator bindings cannot rewrite the copied element accumulated by
`findall/3`. -/
theorem collectTemplate_stable (session : Session) (template : Term)
    (answerBindings : Substitution) :
    answerBindings.applyTerm
        (collectTemplate session template answerBindings).prepared.copied =
      (collectTemplate session template answerBindings).prepared.copied := by
  exact prepareTermCopy_stable _ _ _

/-- A finite local search state.

`task` carries raw residual goals and their cumulative substitution.
`clauses` owns a frozen prepared cursor for one predicate activation.
`product head tail` feeds every answer substitution of `head` into the raw
caller continuation `tail`; this is conjunction without precomputing an
answer bag.  `collectionBoundary` instead consumes generator answers, copies
one template instance per answer, and resumes the caller only after generator
exhaustion. -/
inductive Search where
  | done
  | task (scope : CutScopeId) (goals : List Goal)
      (bindings : Substitution)
  | clauses (scope : CutScopeId) (cursor : PreparedCursor)
  | raise (exception : RaisedException)
  | choice (scope : CutScopeId) (left right : Search)
  | cutBoundary (scope : CutScopeId) (body : Search)
  | catchBoundary (handlerScope : ExceptionScopeId)
      (cutScope : CutScopeId) (body : Search) (catcher : Term)
      (handler : Goal) (entryBindings : Substitution)
  | collectionBoundary (collectionScope : CollectionScopeId)
      (scope : CutScopeId) (body : Search) (template output : Term)
      (entryBindings : Substitution) (tail : List Goal)
      (reversed : List Term)
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
  | .catchBoundary _ _ body _ _ _ => body.liveCursors
  | .collectionBoundary _ _ body _ _ _ _ _ => body.liveCursors
  | .product _ head _ => head.liveCursors

/-- Activation identities of all live cursors, preserving structural order. -/
def liveCursorScopes : Search → List CutScopeId
  | .done => []
  | .task _ _ _ => []
  | .clauses scope _ => [scope]
  | .raise _ => []
  | .choice _ left right => left.liveCursorScopes ++ right.liveCursorScopes
  | .cutBoundary _ body => body.liveCursorScopes
  | .catchBoundary _ _ body _ _ _ => body.liveCursorScopes
  | .collectionBoundary _ _ body _ _ _ _ _ => body.liveCursorScopes
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
  | raise (active : CutScopeId) (exception : RaisedException) :
      WellScoped active (.raise exception)
  | choice (scope : CutScopeId) (left right : Search)
      (leftScoped : WellScoped scope left)
      (rightScoped : WellScoped scope right) :
      WellScoped scope (.choice scope left right)
  | cutBoundary (active scope : CutScopeId) (body : Search)
      (bodyScoped : WellScoped scope body) :
      WellScoped active (.cutBoundary scope body)
  | catchBoundary (scope : CutScopeId) (handlerScope : ExceptionScopeId)
      (body : Search) (catcher : Term) (handler : Goal)
      (entryBindings : Substitution) (bodyScoped : WellScoped scope body) :
      WellScoped scope
        (.catchBoundary handlerScope scope body catcher handler entryBindings)
  | collectionBoundary (scope : CutScopeId)
      (collectionScope : CollectionScopeId) (body : Search)
      (template output : Term) (entryBindings : Substitution)
      (tail : List Goal) (reversed : List Term)
      (bodyScoped : WellScoped scope body) :
      WellScoped scope
        (.collectionBoundary collectionScope scope body template output
          entryBindings tail reversed)
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

/-- Exact built-in `throw/1` shape.  Ordinary locally owned predicate calls
exclude this shape, so exception production and clause lookup cannot both
step from the same task. -/
def BuiltinThrowCall (predicate : String) (arguments : List Term) : Prop :=
  ∃ ball, predicate = "throw" ∧ arguments = [ball]

/-- Exact ball witness for the total throw/DB-action/ordinary-call partition.
Keeping the predicate and argument indices generic avoids relying on
dependent elimination between distinct string literals. -/
def BuiltinThrowCall.Witness (predicate : String) (arguments : List Term)
    (ball : Term) : Prop :=
  predicate = "throw" ∧ arguments = [ball]

theorem BuiltinThrowCall.Witness.call
    {predicate : String} {arguments : List Term} {ball : Term}
    (recognized : BuiltinThrowCall.Witness predicate arguments ball) :
    BuiltinThrowCall predicate arguments :=
  ⟨ball, recognized⟩

theorem BuiltinThrowCall.Witness.conflicts
    {predicate : String} {arguments : List Term} {ball : Term}
    (recognized : BuiltinThrowCall.Witness predicate arguments ball)
    (excluded : ¬ BuiltinThrowCall predicate arguments) : False :=
  excluded recognized.call

/-- `throw/1`, recognized database actions, and ordinary clause calls are
pairwise separated by their total recognizers. -/
theorem DatabaseActionCall.Recognized.notThrow
    {predicate : String} {arguments : List Term}
    {action : DatabaseActionCall}
    (recognized : action.Recognized predicate arguments) :
    ¬ BuiltinThrowCall predicate arguments := by
  rintro ⟨ball, predicateEq, argumentsEq⟩
  subst predicate
  subst arguments
  simp [DatabaseActionCall.Recognized, recognizeDatabaseAction] at recognized

/-- Every call has exactly one operational family available: built-in throw,
typed database action, or ordinary local clause lookup. -/
theorem call_family_exhaustive (predicate : String) (arguments : List Term) :
    BuiltinThrowCall predicate arguments ∨
      (∃ action : DatabaseActionCall,
        action.Recognized predicate arguments) ∨
      (¬ BuiltinThrowCall predicate arguments ∧
        recognizeDatabaseAction predicate arguments = none) := by
  by_cases throwCall : BuiltinThrowCall predicate arguments
  · exact Or.inl throwCall
  · cases databaseEq :
      recognizeDatabaseAction predicate arguments with
    | none => exact Or.inr (Or.inr ⟨throwCall, rfl⟩)
    | some action =>
        exact Or.inr (Or.inl
          ⟨action, by
            simpa [DatabaseActionCall.Recognized] using databaseEq⟩)

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

/-- A cumulative substitution descends from an earlier binding state when it
is obtained solely by prepending a finite extension.  This is the exact shape
produced by primitive unification and clause-head resolution; the direction
is deliberately explicit because newer bindings live at the list head. -/
def BindingLineage (entry current : Substitution) : Prop :=
  ∃ extension, current = extension ++ entry

namespace BindingLineage

theorem refl (bindings : Substitution) : BindingLineage bindings bindings := by
  exact ⟨[], rfl⟩

theorem prepend (extension bindings : Substitution) :
    BindingLineage bindings (extension ++ bindings) := by
  exact ⟨extension, rfl⟩

theorem trans {entry middle current : Substitution}
    (first : BindingLineage entry middle)
    (second : BindingLineage middle current) :
    BindingLineage entry current := by
  rcases first with ⟨firstExtension, rfl⟩
  rcases second with ⟨secondExtension, rfl⟩
  exact ⟨secondExtension ++ firstExtension, by simp [List.append_assoc]⟩

end BindingLineage

theorem UnifyResolution.bindingLineage {bindings result : Substitution}
    {left right : Term}
    (resolved : UnifyResolution bindings left right result) :
    BindingLineage bindings result := by
  rcases resolved with ⟨extension, computed, rfl⟩
  exact BindingLineage.prepend extension bindings

namespace RaisedException

/-- The throw-time binding state is a cumulative descendant of the bindings
saved when an enclosing catch was entered. -/
def ExtendsEntry (exception : RaisedException)
    (entryBindings : Substitution) : Prop :=
  BindingLineage entryBindings exception.throwBindings

/-- A copied exception ball is independent of the throw-time substitution.
This is the finite-tree freshness fact needed to transport SWI's pre-unwind
selection back to the catch-entry environment.  A future source-level
`throw/1` specialization must establish it from the copy operation. -/
def BallStable (exception : RaisedException) : Prop :=
  exception.throwBindings.applyTerm exception.ball = exception.ball

end RaisedException

/-- The packet produced by a real local throw starts at the task's cumulative
binding state. -/
theorem openThrow_extends_current (session : Session) (raw : Term)
    (bindings : Substitution) :
    (openThrow session raw bindings).exception.ExtendsEntry bindings := by
  exact BindingLineage.refl bindings

/-- The fresh-copy algorithm discharges the stability premise consumed by
two-phase catch progress. -/
theorem openThrow_ballStable (session : Session) (raw : Term)
    (bindings : Substitution) :
    (openThrow session raw bindings).exception.BallStable := by
  exact openThrow_ball_stable_raw session raw bindings

/-- Binding-lineage obligations carried by a finite search tree relative to
an enclosing entry state.  Every executable task and frozen call cursor must
descend by prepending extensions; every raised packet additionally carries a
copied ball stable under its throw-time state.  Nested catch entries remain
descendants of the same outer state. -/
def Search.BindingLineageFrom (entryBindings : Substitution) : Search → Prop
  | .done => True
  | .task _ _ current => BindingLineage entryBindings current
  | .clauses _ cursor =>
      cursor.BindingsAligned ∧
        BindingLineage entryBindings cursor.bindings
  | .raise exception =>
      exception.ExtendsEntry entryBindings ∧ exception.BallStable
  | .choice _ left right =>
      left.BindingLineageFrom entryBindings ∧
        right.BindingLineageFrom entryBindings
  | .cutBoundary _ body => body.BindingLineageFrom entryBindings
  | .catchBoundary _ _ body _ _ nestedEntry =>
      BindingLineage entryBindings nestedEntry ∧
        body.BindingLineageFrom nestedEntry
  | .collectionBoundary _ _ body _ _ nestedEntry _ _ =>
      BindingLineage entryBindings nestedEntry ∧
        body.BindingLineageFrom nestedEntry
  | .product _ head _ => head.BindingLineageFrom entryBindings

/-- Every branch of a source-order disjunction inherits the same cumulative
substitution lineage as its surrounding task. -/
theorem Search.disjoin_bindingLineageFrom
    {entryBindings bindings : Substitution}
    (lineage : BindingLineage entryBindings bindings)
    (scope : CutScopeId) (branches tail : List Goal) :
    (Search.disjoin scope branches tail bindings).BindingLineageFrom
      entryBindings := by
  induction branches with
  | nil => exact True.intro
  | cons branch rest inductionHypothesis =>
      cases rest with
      | nil => exact lineage
      | cons next remaining =>
          exact ⟨lineage, inductionHypothesis⟩

/-- Per-event binding lineage.  Only answers carry substitutions; internal
replies are unobservable and every other public event is lineage-neutral. -/
def ObservationBindingLineage (entryBindings : Substitution) :
    Observation → Prop
  | .answer bindings => BindingLineage entryBindings bindings
  | .opened _ | .effect _ | .pruned _ | .raised _ | .completed => True

/-- Every observable answer in one emitted batch descends from the enclosing
entry substitution. -/
def EventsBindingLineage (entryBindings : Substitution)
    (events : List Observation) : Prop :=
  ∀ event ∈ events, ObservationBindingLineage entryBindings event

@[simp] theorem EventsBindingLineage.nil (entryBindings : Substitution) :
    EventsBindingLineage entryBindings [] := by
  simp [EventsBindingLineage]

theorem EventsBindingLineage.cons {entryBindings : Substitution}
    {event : Observation} {events : List Observation}
    (head : ObservationBindingLineage entryBindings event)
    (tail : EventsBindingLineage entryBindings events) :
    EventsBindingLineage entryBindings (event :: events) := by
  intro candidate member
  rcases List.mem_cons.mp member with rfl | later
  · exact head
  · exact tail candidate later

theorem EventsBindingLineage.append {entryBindings : Substitution}
    {left right : List Observation}
    (leftLineage : EventsBindingLineage entryBindings left)
    (rightLineage : EventsBindingLineage entryBindings right) :
    EventsBindingLineage entryBindings (left ++ right) := by
  intro event member
  rcases List.mem_append.mp member with leftMember | rightMember
  · exact leftLineage event leftMember
  · exact rightLineage event rightMember

/-- Answer lineage weakens transitively from a nested entry state to any
enclosing ancestor. -/
theorem EventsBindingLineage.mono {outerEntry nestedEntry : Substitution}
    {events : List Observation}
    (nestedLineage : BindingLineage outerEntry nestedEntry)
    (eventLineage : EventsBindingLineage nestedEntry events) :
    EventsBindingLineage outerEntry events := by
  intro event member
  have inner := eventLineage event member
  cases event with
  | answer bindings =>
      exact BindingLineage.trans nestedLineage inner
  | opened request | effect value | pruned cursor | raised exception |
      completed =>
      trivial

@[simp] theorem EventsBindingLineage.pruned
    (entryBindings : Substitution) (cursors : List CursorToken) :
    EventsBindingLineage entryBindings
      (cursors.map Trace.Observation.pruned) := by
  intro event member
  simp only [List.mem_map] at member
  rcases member with ⟨cursor, _, rfl⟩
  trivial

/-- SWI's pre-unwind catcher-selection test for the supported finite-tree
fragment.  Unlike ISO's abstract account, SWI tests the catcher while bindings
made by the protected goal are still present.  The copied ball itself is not
reinterpreted through those bindings.

[SPEC SWI-Prolog manual 4.10, delayed backtracking during exception search] -/
def CatchSelection (raised : RaisedException) (catcher : Term) : Prop :=
  ∃ extension,
    ComputesDenotationalMgu
      [(raised.throwBindings.applyTerm catcher, raised.ball)] extension

/-- Exact recovery matching performed after a selected `catch/3` has unwound.
Only bindings present on entry survive the unwind; the copied ball is unified
again with the catcher by the same canonical ordered MGU used for primitive
equality.  This second match reconstructs precisely the bindings visible to
the recovery goal.

This is the independent local counterpart of SWI's
`catch(Goal, Catcher, Recovery)` recovery step for the supported finite-tree
fragment.  Rational-tree/cyclic matching and attributed variables remain open
adequacy obligations.

[SPEC translator.pl:300-308] -/
def CatchResolution (entryBindings : Substitution) (catcher exception : Term)
    (result : Substitution) : Prop :=
  UnifyResolution entryBindings catcher exception result

theorem CatchResolution.deterministic {entryBindings : Substitution}
    {catcher exception : Term} {first second : Substitution}
    (one : CatchResolution entryBindings catcher exception first)
    (two : CatchResolution entryBindings catcher exception second) :
    first = second :=
  UnifyResolution.deterministic one two

theorem CatchResolution.bindingLineage
    {entryBindings result : Substitution} {catcher exception : Term}
    (resolved : CatchResolution entryBindings catcher exception result) :
    BindingLineage entryBindings result :=
  UnifyResolution.bindingLineage resolved

/-- Successful SWI pre-unwind selection can always be reconstructed after
unwind when the throw state extends the catch-entry state and the copied ball
is stable under that throw state.  The witness is not postulated: the
selection MGU composed with the intervening binding extension is a unifier of
the entry-normalized equation, so completeness of the canonical ordered MGU
algorithm computes the unique recovery extension. -/
theorem CatchSelection.exists_resolution_of_lineage
    {raised : RaisedException} {catcher : Term}
    {entryBindings : Substitution}
    (lineage : raised.ExtendsEntry entryBindings)
    (ballStable : raised.BallStable)
    (selected : CatchSelection raised catcher) :
    ∃ result, CatchResolution entryBindings catcher raised.ball result := by
  rcases lineage with ⟨intervening, throwBindingsEq⟩
  rcases selected with ⟨selection, computed⟩
  have selectedUnifies : DenotationalUnifier selection
      (raised.throwBindings.applyTerm catcher) raised.ball :=
    computed.isMostGeneral.1
      (raised.throwBindings.applyTerm catcher, raised.ball) (by simp)
  have candidateUnifier : DenotationalUnifier (selection ++ intervening)
      (entryBindings.applyTerm catcher)
      (entryBindings.applyTerm raised.ball) := by
    unfold DenotationalUnifier at selectedUnifies ⊢
    calc
      TreeSubstitution.apply
          (Canonical.Substitution.denote (selection ++ intervening))
          (Term.denote (entryBindings.applyTerm catcher)) =
        TreeSubstitution.apply (Canonical.Substitution.denote selection)
          (TreeSubstitution.apply
            (Canonical.Substitution.denote intervening)
            (Term.denote (entryBindings.applyTerm catcher))) := by
              rw [Canonical.Substitution.denote_append,
                TreeSubstitution.apply_append]
      _ = TreeSubstitution.apply (Canonical.Substitution.denote selection)
          (Term.denote (raised.throwBindings.applyTerm catcher)) := by
            rw [throwBindingsEq, Substitution.applyTerm_append]
            simp only [Canonical.Substitution.denote_applyTerm]
      _ = TreeSubstitution.apply (Canonical.Substitution.denote selection)
          (Term.denote raised.ball) := selectedUnifies
      _ = TreeSubstitution.apply (Canonical.Substitution.denote selection)
          (Term.denote (raised.throwBindings.applyTerm raised.ball)) := by
            rw [ballStable]
      _ = TreeSubstitution.apply (Canonical.Substitution.denote selection)
          (TreeSubstitution.apply
            (Canonical.Substitution.denote intervening)
            (Term.denote (entryBindings.applyTerm raised.ball))) := by
            rw [throwBindingsEq, Substitution.applyTerm_append]
            simp only [Canonical.Substitution.denote_applyTerm]
      _ = TreeSubstitution.apply
          (Canonical.Substitution.denote (selection ++ intervening))
          (Term.denote (entryBindings.applyTerm raised.ball)) := by
            rw [Canonical.Substitution.denote_append,
              TreeSubstitution.apply_append]
  have candidateUnifies : DenotationalUnifiesEquations
      (selection ++ intervening)
      [(entryBindings.applyTerm catcher,
        entryBindings.applyTerm raised.ball)] := by
    intro equation member
    simp only [List.mem_singleton] at member
    subst equation
    exact candidateUnifier
  rcases ComputesDenotationalMgu.exists_of_unifier
      (selection ++ intervening) candidateUnifies with
    ⟨extension, recovery⟩
  exact ⟨extension ++ entryBindings, extension, recovery, rfl⟩

/-- Internal terminal state.  The throw-time substitution remains available
to enclosing catchers until the exception escapes the local machine. -/
inductive RawTerminal where
  | completed
  | raised (exception : RaisedException)
deriving Repr, Inhabited

namespace RawTerminal

/-- Erase internal selection evidence only at the public terminal boundary. -/
def toTerminal : RawTerminal → Trace.Terminal Term
  | .completed => .completed
  | .raised exception => .raised exception.ball

/-- Internal terminal packets preserve the same binding-lineage evidence as
the search that produced them. -/
def BindingLineageFrom (entryBindings : Substitution) : RawTerminal → Prop
  | .completed => True
  | .raised exception =>
      exception.ExtendsEntry entryBindings ∧ exception.BallStable

end RawTerminal

/-- One raw transition target.  Successful search exhaustion and an exception
remain distinct terminal tags, while internal exceptions retain the evidence
needed by an enclosing SWI-style catcher. -/
inductive RawTarget where
  | terminal (tag : RawTerminal)
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

/-- A terminal packet or running successor retains the enclosing cumulative
substitution lineage. -/
def BindingLineageFrom (entryBindings : Substitution) : RawTarget → Prop
  | .terminal tag => tag.BindingLineageFrom entryBindings
  | .running search => search.BindingLineageFrom entryBindings

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

/-- The certified clause splice preserves cumulative substitution lineage.
An entered body extends the cursor's call-entry bindings by exactly its head
MGU, while the retained cursor keeps the unchanged entry state and alignment.
-/
theorem localPullTarget_bindingLineageFrom
    {entryBindings : Substitution} (scope : CutScopeId)
    {cursor : PreparedCursor} {outcome : LocalOutcome}
    (aligned : cursor.BindingsAligned)
    (cursorLineage : BindingLineage entryBindings cursor.bindings)
    (pulled : LocalPull cursor outcome) :
    (localPullTarget scope outcome).BindingLineageFrom entryBindings := by
  cases pulled with
  | matched branch rest result remaining resolved =>
      have branchAligned : branch.bindings = cursor.bindings := by
        apply aligned branch
        rw [remaining]
        simp
      have enteredLineage : BindingLineage entryBindings result := by
        apply BindingLineage.trans cursorLineage
        rw [← branchAligned]
        rcases resolved with ⟨extension, computed, resultEq⟩
        exact ⟨extension, resultEq⟩
      have nextAligned :=
        PreparedCursor.advance_bindingsAligned aligned remaining
      exact ⟨enteredLineage, nextAligned, cursorLineage⟩
  | rejected branch rest remaining clash =>
      have nextAligned :=
        PreparedCursor.advance_bindingsAligned aligned remaining
      exact ⟨nextAligned, cursorLineage⟩
  | exhausted done =>
      exact True.intro

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
  | taskThrow (scope : CutScopeId) (ball : Term) (rest : List Goal)
      (bindings : Substitution) (session : Session)
      {predicate : String} {arguments : List Term}
      (recognized : BuiltinThrowCall.Witness predicate arguments ball) :
      RawStep session
        (.task scope (.call predicate arguments :: rest) bindings) [] .none
        (openThrow session ball bindings).session
        (.running (.raise (openThrow session ball bindings).exception))
  | taskAsserta (scope : CutScopeId) (payload result : Term)
      (rest : List Goal) (bindings : Substitution) (session : Session)
      (clause : LocalClause)
      {predicate : String} {arguments : List Term}
      (recognized :
        ({ kind := .asserta, payload := payload, result := result } :
          DatabaseActionCall).Recognized predicate arguments)
      (decoded :
        decodePredicateClause (bindings.applyTerm payload) = some clause) :
      RawStep session
        (.task scope
          (.call predicate arguments :: rest) bindings)
        [.effect
          (.asserta (session.resolver.database.allocate clause))]
        .none
        (session.withDatabase (session.resolver.database.asserta clause))
        (.running
          (.task scope (.unify result (.atom "true") :: rest) bindings))
  | taskAssertz (scope : CutScopeId) (payload result : Term)
      (rest : List Goal) (bindings : Substitution) (session : Session)
      (clause : LocalClause)
      {predicate : String} {arguments : List Term}
      (recognized :
        ({ kind := .assertz, payload := payload, result := result } :
          DatabaseActionCall).Recognized predicate arguments)
      (decoded :
        decodePredicateClause (bindings.applyTerm payload) = some clause) :
      RawStep session
        (.task scope
          (.call predicate arguments :: rest) bindings)
        [.effect
          (.assertz (session.resolver.database.allocate clause))]
        .none
        (session.withDatabase (session.resolver.database.assertz clause))
        (.running
          (.task scope (.unify result (.atom "true") :: rest) bindings))
  | taskRetractMatched (scope : CutScopeId) (payload result : Term)
      (rest : List Goal) (bindings : Substitution) (session : Session)
      (pattern : LocalClause) (entry : VersionedClause)
      (extension : Substitution) (nextFresh : Nat) (afterDatabase : Database)
      {predicate : String} {arguments : List Term}
      (recognized :
        ({ kind := .retract, payload := payload, result := result } :
          DatabaseActionCall).Recognized predicate arguments)
      (decoded :
        decodePredicateClause (bindings.applyTerm payload) = some pattern)
      (scan :
        RetractScan pattern session.resolver.nextFresh
          (currentEntries session.resolver.database)
          (.matched entry extension nextFresh))
      (reachable : DatabaseReachable session.resolver.database)
      (retracted :
        session.resolver.database.retractId entry.id = some afterDatabase) :
      RawStep session
        (.task scope
          (.call predicate arguments :: rest) bindings)
        [.effect (.retract entry)] .none
        (session.withDatabaseAndFresh afterDatabase nextFresh)
        (.running
          (.task scope (.unify result (.atom "true") :: rest)
            (extension ++ bindings)))
  | taskRetractMissing (scope : CutScopeId) (payload result : Term)
      (rest : List Goal) (bindings : Substitution) (session : Session)
      (pattern : LocalClause) (nextFresh : Nat)
      {predicate : String} {arguments : List Term}
      (recognized :
        ({ kind := .retract, payload := payload, result := result } :
          DatabaseActionCall).Recognized predicate arguments)
      (decoded :
        decodePredicateClause (bindings.applyTerm payload) = some pattern)
      (scan :
        RetractScan pattern session.resolver.nextFresh
          (currentEntries session.resolver.database) (.missing nextFresh)) :
      RawStep session
        (.task scope
          (.call predicate arguments :: rest) bindings)
        [] .none
        (session.withDatabaseAndFresh session.resolver.database nextFresh)
        (.running
          (.task scope (.unify result (.atom "false") :: rest) bindings))
  | taskDatabaseDecodeFailure (scope : CutScopeId) (predicate : String)
      (arguments : List Term) (rest : List Goal)
      (bindings : Substitution) (session : Session)
      (action : DatabaseActionCall)
      (recognized : action.Recognized predicate arguments)
      (malformed :
        decodePredicateClause
          (bindings.applyTerm action.payload) = none) :
      RawStep session
        (.task scope (.call predicate arguments :: rest) bindings)
        [.completed] .none session (.terminal .completed)
  | taskCall (scope : CutScopeId) (predicate : String)
      (arguments : List Term) (rest : List Goal) (bindings : Substitution)
      (session : Session)
      (notThrow : ¬ BuiltinThrowCall predicate arguments)
      (notDatabase : recognizeDatabaseAction predicate arguments = none) :
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
  | taskCatch (scope : CutScopeId) (protectedGoal : Goal) (catcher : Term)
      (handler : Goal) (rest : List Goal) (bindings : Substitution)
      (session : Session) :
      RawStep session
        (.task scope (.catch protectedGoal catcher handler :: rest) bindings)
        [] .none (openCatch session).session
        (.running
          (.product scope
            (.cutBoundary (openCatch session).cutScope
              (.catchBoundary (openCatch session).handlerScope
                (openCatch session).cutScope
                (.task (openCatch session).cutScope [protectedGoal] bindings)
                catcher handler bindings))
            rest))
  | taskFindall (scope : CutScopeId) (template : Term) (generator : Goal)
      (output : Term) (rest : List Goal) (bindings : Substitution)
      (session : Session) :
      RawStep session
        (.task scope (.findall template generator output :: rest) bindings)
        [] .none (openFindall session).session
        (.running
          (.collectionBoundary (openFindall session).collectionScope scope
            (.cutBoundary (openFindall session).cutScope
              (.task (openFindall session).cutScope [generator] bindings))
            template output bindings rest []))
  | clausesPull (scope : CutScopeId) (cursor : PreparedCursor)
      (outcome : LocalOutcome) (session : Session)
      (pulled : LocalPull cursor outcome) :
      RawStep session (.clauses scope cursor) (localPullEvents outcome) .none
        session (localPullTarget scope outcome)
  | raise (exception : RaisedException) (session : Session) :
      RawStep session (.raise exception) [.raised exception.ball] .none session
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
      (exception : RaisedException) (events : List Observation)
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
      (exception : RaisedException) (events : List Observation)
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
  | catchProgress (handlerScope : ExceptionScopeId) (scope : CutScopeId)
      (body next : Search) (catcher : Term) (handler : Goal)
      (entryBindings : Substitution) (events : List Observation)
      (signal : Trace.CutSignal) (before after : Session)
      (step : RawStep before body events signal after (.running next)) :
      RawStep before
        (.catchBoundary handlerScope scope body catcher handler entryBindings)
        events signal after
        (.running
          (.catchBoundary handlerScope scope next catcher handler
            entryBindings))
  | catchComplete (handlerScope : ExceptionScopeId) (scope : CutScopeId)
      (body : Search) (catcher : Term) (handler : Goal)
      (entryBindings : Substitution) (before after : Session)
      (step : RawStep before body [.completed] .none after
        (.terminal .completed)) :
      RawStep before
        (.catchBoundary handlerScope scope body catcher handler entryBindings)
        [.completed] .none after (.terminal .completed)
  | catchHandled (handlerScope : ExceptionScopeId) (scope : CutScopeId)
      (body : Search) (catcher : Term) (exception : RaisedException)
      (handler : Goal)
      (entryBindings result : Substitution) (cleanup : List Observation)
      (before after : Session)
      (step : RawStep before body (.raised exception.ball :: cleanup) .none after
        (.terminal (.raised exception)))
      (selected : CatchSelection exception catcher)
      (resolved : CatchResolution entryBindings catcher exception.ball result) :
      RawStep before
        (.catchBoundary handlerScope scope body catcher handler entryBindings)
        cleanup .none after
        (.running (.task scope [handler] result))
  | catchUnmatched (handlerScope : ExceptionScopeId) (scope : CutScopeId)
      (body : Search) (catcher : Term) (exception : RaisedException)
      (handler : Goal)
      (entryBindings : Substitution) (cleanup : List Observation)
      (before after : Session)
      (step : RawStep before body (.raised exception.ball :: cleanup) .none after
        (.terminal (.raised exception)))
      (unmatched : ¬ CatchSelection exception catcher) :
      RawStep before
        (.catchBoundary handlerScope scope body catcher handler entryBindings)
        (.raised exception.ball :: cleanup) .none after
        (.terminal (.raised exception))
  | collectionAnswer (collectionScope : CollectionScopeId)
      (scope : CutScopeId) (body next : Search) (template output : Term)
      (entryBindings : Substitution) (tail : List Goal)
      (reversed : List Term) (answerBindings : Substitution)
      (before after : Session)
      (step : RawStep before body [.answer answerBindings] .none after
        (.running next)) :
      RawStep before
        (.collectionBoundary collectionScope scope body template output
          entryBindings tail reversed)
        [] .none (collectTemplate after template answerBindings).session
        (.running
          (.collectionBoundary collectionScope scope next template output
            entryBindings tail
            ((collectTemplate after template answerBindings).prepared.copied ::
              reversed)))
  | collectionProgress (collectionScope : CollectionScopeId)
      (scope : CutScopeId) (body next : Search) (template output : Term)
      (entryBindings : Substitution) (tail : List Goal)
      (reversed : List Term) (events : List Observation)
      (signal : Trace.CutSignal) (before after : Session)
      (step : RawStep before body events signal after (.running next))
      (answerFree : Trace.AnswerFree events) :
      RawStep before
        (.collectionBoundary collectionScope scope body template output
          entryBindings tail reversed)
        events signal after
        (.running
          (.collectionBoundary collectionScope scope next template output
            entryBindings tail reversed))
  | collectionComplete (collectionScope : CollectionScopeId)
      (scope : CutScopeId) (body : Search) (template output : Term)
      (entryBindings : Substitution) (tail : List Goal)
      (reversed : List Term) (before after : Session)
      (step : RawStep before body [.completed] .none after
        (.terminal .completed)) :
      RawStep before
        (.collectionBoundary collectionScope scope body template output
          entryBindings tail reversed)
        [] .none after
        (.running
          (.task scope
            (.unify output (.list reversed.reverse none) :: tail)
            entryBindings))
  | collectionRaised (collectionScope : CollectionScopeId)
      (scope : CutScopeId) (body : Search) (template output : Term)
      (entryBindings : Substitution) (tail : List Goal)
      (reversed : List Term) (exception : RaisedException)
      (events : List Observation) (before after : Session)
      (step : RawStep before body events .none after
        (.terminal (.raised exception))) :
      RawStep before
        (.collectionBoundary collectionScope scope body template output
          entryBindings tail reversed)
        events .none after (.terminal (.raised exception))
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
      (tail : List Goal) (exception : RaisedException)
      (events : List Observation)
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
  | taskCall scope predicate arguments rest bindings session notThrow
      notDatabase =>
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
  case taskThrow.taskCall =>
    exact False.elim
      (BuiltinThrowCall.Witness.conflicts (by assumption) (by assumption))
  case taskCall.taskThrow =>
    exact False.elim
      (BuiltinThrowCall.Witness.conflicts (by assumption) (by assumption))
  all_goals
    try simp_all [BuiltinThrowCall, BuiltinThrowCall.Witness,
      DatabaseActionCall.Recognized, recognizeDatabaseAction]
  all_goals
    try
      subst_vars
      simp_all
  case taskRetractMatched.taskRetractMatched =>
    rename_i payloadOne resultOne rest patternOne entryOne extensionOne
      nextFreshOne afterDatabaseOne predicate arguments scanOne retractedOne
      payloadTwo resultTwo patternTwo entryTwo extensionTwo nextFreshTwo
      afterDatabaseTwo patternEquality scanTwo reachableTwo retractedTwo
      actionEquality decodedTwo
    have outcomeEquality := RetractScan.deterministic scanOne scanTwo
    cases outcomeEquality
    rw [retractedOne] at retractedTwo
    cases retractedTwo
    exact ⟨rfl, rfl, rfl⟩
  case taskRetractMatched.taskRetractMissing =>
    rename_i payloadOne resultOne rest patternOne entry extension nextFreshOne
      afterDatabase predicate arguments scanOne reachable retracted payloadTwo
      resultTwo patternTwo nextFreshTwo patternEquality scanTwo actionEquality
      decodedTwo
    have outcomeEquality := RetractScan.deterministic scanOne scanTwo
    cases outcomeEquality
  case taskRetractMissing.taskRetractMatched =>
    rename_i payloadOne resultOne rest patternOne nextFreshOne predicate
      arguments scanOne payloadTwo resultTwo patternTwo entry extension
      nextFreshTwo afterDatabase patternEquality scanTwo reachable retracted
      actionEquality decodedTwo
    have outcomeEquality := RetractScan.deterministic scanOne scanTwo
    cases outcomeEquality
  case taskRetractMissing.taskRetractMissing =>
    rename_i payloadOne resultOne rest patternOne nextFreshOne predicate
      arguments scanOne payloadTwo resultTwo patternTwo nextFreshTwo
      patternEquality scanTwo actionEquality decodedTwo
    have outcomeEquality := RetractScan.deterministic scanOne scanTwo
    cases outcomeEquality
    rfl

/-- Every recognized database-action call has one concrete successor on a
reachable database.  Ordered retract scanning is total; a matched current
occurrence is retractable by complete database reachability; missing and
malformed inputs have explicit transitions rather than stuck states. -/
theorem databaseAction_progress
    {scope : CutScopeId} {predicate : String} {arguments : List Term}
    {rest : List Goal} {bindings : Substitution} {session : Session}
    {action : DatabaseActionCall}
    (recognized : action.Recognized predicate arguments)
    (closed : session.DatabaseClosed) :
    ∃ events after target,
      RawStep session
        (.task scope (.call predicate arguments :: rest) bindings)
        events .none after target := by
  cases action with
  | mk kind payload result =>
      cases kind with
      | asserta =>
          cases decoded :
              decodePredicateClause (bindings.applyTerm payload) with
          | none =>
              exact
                ⟨[.completed], session, .terminal .completed,
                  .taskDatabaseDecodeFailure scope predicate arguments rest
                    bindings session
                    { kind := .asserta, payload := payload, result := result }
                    recognized decoded⟩
          | some clause =>
              exact
                ⟨[.effect
                    (.asserta
                      (session.resolver.database.allocate clause))],
                  session.withDatabase
                    (session.resolver.database.asserta clause),
                  .running
                    (.task scope (.unify result (.atom "true") :: rest)
                      bindings),
                  .taskAsserta scope payload result rest bindings session
                    clause recognized decoded⟩
      | assertz =>
          cases decoded :
              decodePredicateClause (bindings.applyTerm payload) with
          | none =>
              exact
                ⟨[.completed], session, .terminal .completed,
                  .taskDatabaseDecodeFailure scope predicate arguments rest
                    bindings session
                    { kind := .assertz, payload := payload, result := result }
                    recognized decoded⟩
          | some clause =>
              exact
                ⟨[.effect
                    (.assertz
                      (session.resolver.database.allocate clause))],
                  session.withDatabase
                    (session.resolver.database.assertz clause),
                  .running
                    (.task scope (.unify result (.atom "true") :: rest)
                      bindings),
                  .taskAssertz scope payload result rest bindings session
                    clause recognized decoded⟩
      | retract =>
          cases decoded :
              decodePredicateClause (bindings.applyTerm payload) with
          | none =>
              exact
                ⟨[.completed], session, .terminal .completed,
                  .taskDatabaseDecodeFailure scope predicate arguments rest
                    bindings session
                    { kind := .retract, payload := payload, result := result }
                    recognized decoded⟩
          | some pattern =>
              obtain ⟨outcome, scan⟩ :=
                RetractScan.exists_scan pattern session.resolver.nextFresh
                  (currentEntries session.resolver.database)
              cases outcome with
              | matched entry extension nextFresh =>
                  have member := RetractScan.matched_mem scan
                  obtain ⟨afterDatabase, retracted⟩ :=
                    exists_retractId_of_mem_currentEntries closed member
                  exact
                    ⟨[.effect (.retract entry)],
                      session.withDatabaseAndFresh afterDatabase nextFresh,
                      .running
                        (.task scope (.unify result (.atom "true") :: rest)
                          (extension ++ bindings)),
                      .taskRetractMatched scope payload result rest bindings
                        session pattern entry extension nextFresh afterDatabase
                        recognized decoded scan closed retracted⟩
              | missing nextFresh =>
                  exact
                    ⟨[],
                      session.withDatabaseAndFresh
                        session.resolver.database nextFresh,
                      .running
                        (.task scope (.unify result (.atom "false") :: rest)
                          bindings),
                      .taskRetractMissing scope payload result rest bindings
                        session pattern nextFresh recognized decoded scan⟩

set_option linter.unnecessarySeqFocus false in
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

/-- Coupled substitution-lineage subject reduction.  Every answer emitted by
one raw step descends from the enclosing entry substitution, and every
running or raised successor retains the same invariant.  This is deliberately
stronger than a theorem about final answers: product splicing and exception
unwind consume the event and terminal components internally. -/
theorem preserves_bindingLineage_target {entryBindings : Substitution}
    {search : Search} {events : List Observation}
    {signal : Trace.CutSignal} {before after : Session}
    {target : RawTarget}
    (step : RawStep before search events signal after target)
    (lineage : search.BindingLineageFrom entryBindings) :
    EventsBindingLineage entryBindings events ∧
      target.BindingLineageFrom entryBindings := by
  induction step generalizing entryBindings <;>
    simp_all (config := { failIfUnchanged := false })
      [EventsBindingLineage, ObservationBindingLineage,
        RawTarget.BindingLineageFrom, RawTerminal.BindingLineageFrom,
        Search.BindingLineageFrom, localPullEvents, localPullTarget]
  case taskUnifySuccess =>
    apply BindingLineage.trans lineage
    exact UnifyResolution.bindingLineage (by assumption)
  case taskDisjunction =>
    exact Search.disjoin_bindingLineageFrom lineage _ _ _
  case taskThrow =>
    constructor
    · exact BindingLineage.trans lineage (openThrow_extends_current _ _ _)
    · exact openThrow_ballStable _ _ _
  case taskRetractMatched =>
    exact BindingLineage.trans lineage (BindingLineage.prepend _ _)
  case taskCall =>
    constructor
    · exact prepareCall_bindingsAligned _ _
    · exact lineage
  case taskCatch =>
    exact BindingLineage.refl _
  case taskFindall =>
    exact BindingLineage.refl _
  case clausesPull scope cursor outcome session pulled =>
    constructor
    · cases outcome with
      | silent next => simp
      | reply entered next => simp
      | effect effect next => exact Empty.elim effect
      | exhausted => simp
      | raised exception => exact Empty.elim exception
    · exact localPullTarget_bindingLineageFrom scope lineage.1 lineage.2 pulled
  case choiceRaised scope left right exception events before after child
      inductionHypothesis =>
    have childLineage := inductionHypothesis lineage.1
    constructor
    · simpa only [EventsBindingLineage, ObservationBindingLineage,
          List.mem_append, List.mem_map, eq_comm] using
        (EventsBindingLineage.append childLineage.1
          (EventsBindingLineage.pruned entryBindings right.liveCursors))
    · exact childLineage.2.2
  case choiceCommitHere scope left right next events before after child
      inductionHypothesis =>
    have childLineage := inductionHypothesis lineage.1
    simpa only [EventsBindingLineage, ObservationBindingLineage,
        List.mem_append, List.mem_map, eq_comm] using
      (EventsBindingLineage.append childLineage.1
        (EventsBindingLineage.pruned entryBindings right.liveCursors))
  case cutBoundaryRaised scope body exception events before after child
      inductionHypothesis =>
    exact (inductionHypothesis lineage).2.2
  case catchProgress handlerScope scope body next catcher handler nestedEntry
      events signal before after child inductionHypothesis =>
    have childLineage := inductionHypothesis lineage.2
    simpa only [EventsBindingLineage, ObservationBindingLineage] using
      (EventsBindingLineage.mono lineage.1 childLineage.1)
  case catchHandled handlerScope scope body catcher exception handler
      nestedEntry result cleanup before after child selected resolved
      inductionHypothesis =>
    have childLineage := inductionHypothesis lineage.2
    constructor
    · simpa only [EventsBindingLineage, ObservationBindingLineage] using
        (EventsBindingLineage.mono lineage.1 childLineage.1)
    · exact BindingLineage.trans lineage.1 resolved.bindingLineage
  case catchUnmatched handlerScope scope body catcher exception handler
      nestedEntry cleanup before after child unmatched inductionHypothesis =>
    have childLineage := inductionHypothesis lineage.2
    constructor
    · simpa only [EventsBindingLineage, ObservationBindingLineage] using
        (EventsBindingLineage.mono lineage.1 childLineage.1)
    · exact ⟨BindingLineage.trans lineage.1 childLineage.2.1,
        childLineage.2.2⟩
  case collectionProgress collectionScope scope body next template output
      nestedEntry tail reversed events signal before after child answerFree
      inductionHypothesis =>
    have childLineage := inductionHypothesis lineage.2
    simpa only [EventsBindingLineage, ObservationBindingLineage] using
      (EventsBindingLineage.mono lineage.1 childLineage.1)
  case collectionRaised collectionScope scope body template output nestedEntry
      tail reversed exception events before after child inductionHypothesis =>
    have childLineage := inductionHypothesis lineage.2
    constructor
    · simpa only [EventsBindingLineage, ObservationBindingLineage] using
        (EventsBindingLineage.mono lineage.1 childLineage.1)
    · exact ⟨BindingLineage.trans lineage.1 childLineage.2.1,
        childLineage.2.2⟩
  case productRaised scope head tail exception events before after child
      answerFree inductionHypothesis =>
    exact (inductionHypothesis lineage).2.2

/-- Running successors and their emitted answer batches preserve cumulative
substitution lineage. -/
theorem preserves_bindingLineage {entryBindings : Substitution}
    {search next : Search} {events : List Observation}
    {signal : Trace.CutSignal} {before after : Session}
    (step : RawStep before search events signal after (.running next))
    (lineage : search.BindingLineageFrom entryBindings) :
    EventsBindingLineage entryBindings events ∧
      next.BindingLineageFrom entryBindings :=
  preserves_bindingLineage_target step lineage

/-- A well-lineaged protected search cannot leave `catch/3` stuck after an
exception.  Canonical selection either fails, in which case the exact packet
escapes, or succeeds, in which case binding lineage plus copied-ball stability
computes a recovery substitution and the handler starts. -/
theorem catch_raised_progress
    {handlerScope : ExceptionScopeId} {scope : CutScopeId}
    {body : Search} {catcher : Term} {exception : RaisedException}
    {handler : Goal} {entryBindings : Substitution}
    {cleanup : List Observation} {before after : Session}
    (bodyLineage : body.BindingLineageFrom entryBindings)
    (child : RawStep before body
      (.raised exception.ball :: cleanup) .none after
      (.terminal (.raised exception))) :
    ∃ emitted target,
      RawStep before
        (.catchBoundary handlerScope scope body catcher handler entryBindings)
        emitted .none after target := by
  have packetLineage :=
    (preserves_bindingLineage_target child bodyLineage).2
  by_cases selected : CatchSelection exception catcher
  · rcases selected.exists_resolution_of_lineage packetLineage.1
      packetLineage.2 with ⟨result, resolved⟩
    exact ⟨cleanup, .running (.task scope [handler] result),
      .catchHandled handlerScope scope body catcher exception handler
        entryBindings result cleanup before after child selected resolved⟩
  · exact ⟨.raised exception.ball :: cleanup,
      .terminal (.raised exception),
      .catchUnmatched handlerScope scope body catcher exception handler
        entryBindings cleanup before after child selected⟩

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
  | taskThrow scope ball rest bindings session =>
      cases wellFormed
      exact .raise scope (openThrow session ball bindings).exception
  | taskAsserta scope payload result rest bindings session clause decoded =>
      cases wellFormed
      exact .task scope (.unify result (.atom "true") :: rest) bindings
  | taskAssertz scope payload result rest bindings session clause decoded =>
      cases wellFormed
      exact .task scope (.unify result (.atom "true") :: rest) bindings
  | taskRetractMatched scope payload result rest bindings session pattern
      entry extension nextFresh afterDatabase decoded scan retracted =>
      cases wellFormed
      exact .task scope (.unify result (.atom "true") :: rest)
        (extension ++ bindings)
  | taskRetractMissing scope payload result rest bindings session pattern
      nextFresh decoded scan =>
      cases wellFormed
      exact .task scope (.unify result (.atom "false") :: rest) bindings
  | taskDatabaseDecodeFailure =>
      exact True.intro
  | taskCall scope predicate arguments rest bindings session notThrow
      notDatabase =>
      cases wellFormed
      exact .product scope _ rest
        (.cutBoundary scope
          (openedFor session predicate arguments bindings).scope _
          (.clauses
            (openedFor session predicate arguments bindings).scope
            (openedFor session predicate arguments bindings).cursor))
  | taskCatch scope protectedGoal catcher handler rest bindings session =>
      cases wellFormed
      exact .product scope _ rest
        (.cutBoundary scope (openCatch session).cutScope _
          (.catchBoundary (openCatch session).cutScope
            (openCatch session).handlerScope _ catcher handler bindings
            (.task (openCatch session).cutScope [protectedGoal] bindings)))
  | taskFindall scope template generator output rest bindings session =>
      cases wellFormed
      exact .collectionBoundary scope
        (openFindall session).collectionScope _ template output bindings rest []
        (.cutBoundary scope (openFindall session).cutScope _
          (.task (openFindall session).cutScope [generator] bindings))
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
  | catchProgress handlerScope scope body next catcher handler entryBindings
      events signal before after step inductionHypothesis =>
      cases wellFormed with
      | catchBoundary _ _ _ _ _ _ bodyScoped =>
          exact .catchBoundary scope handlerScope next catcher handler
            entryBindings (inductionHypothesis bodyScoped)
  | catchComplete handlerScope scope body catcher handler entryBindings before
      after step inductionHypothesis =>
      exact True.intro
  | catchHandled handlerScope scope body catcher exception handler
      entryBindings result cleanup before after step resolved
      inductionHypothesis =>
      cases wellFormed
      exact .task scope [handler] result
  | catchUnmatched handlerScope scope body catcher exception handler
      entryBindings cleanup before after step unmatched inductionHypothesis =>
      exact True.intro
  | collectionAnswer collectionScope scope body next template output
      entryBindings tail reversed answerBindings before after step
      inductionHypothesis =>
      cases wellFormed with
      | collectionBoundary _ _ _ _ _ _ _ _ bodyScoped =>
          exact .collectionBoundary scope collectionScope next template output
            entryBindings tail _ (inductionHypothesis bodyScoped)
  | collectionProgress collectionScope scope body next template output
      entryBindings tail reversed events signal before after step answerFree
      inductionHypothesis =>
      cases wellFormed with
      | collectionBoundary _ _ _ _ _ _ _ _ bodyScoped =>
          exact .collectionBoundary scope collectionScope next template output
            entryBindings tail reversed (inductionHypothesis bodyScoped)
  | collectionComplete collectionScope scope body template output
      entryBindings tail reversed before after step inductionHypothesis =>
      cases wellFormed
      exact .task scope (.unify output (.list reversed.reverse none) :: tail)
        entryBindings
  | collectionRaised collectionScope scope body template output entryBindings
      tail reversed exception events before after step inductionHypothesis =>
      exact True.intro
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
    {left right : Search} {exception : RaisedException}
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
Local-call opening and exception copying are the allocating rules; every
wrapper inherits its child's monotonicity. -/
theorem nextFresh_mono {before after : Session} {search : Search}
    {events : List Observation} {signal : Trace.CutSignal}
    {target : RawTarget}
    (step : RawStep before search events signal after target) :
    before.resolver.nextFresh ≤ after.resolver.nextFresh := by
  induction step <;> try exact Nat.le_refl _
  case taskThrow =>
    exact openThrow_nextFresh_mono _ _ _
  case taskRetractMatched =>
    simpa [RetractOutcome.nextFresh] using
      RetractScan.nextFresh_mono (by assumption)
  case taskRetractMissing =>
    simpa [RetractOutcome.nextFresh] using
      RetractScan.nextFresh_mono (by assumption)
  case taskCall scope predicate arguments rest bindings session notThrow
      notDatabase =>
    simpa only [openedFor] using
      (openLocalCall_nextFresh_mono session
        (requestFor predicate arguments bindings))
  case collectionAnswer collectionScope scope body next template output
      entryBindings tail reversed answerBindings before after child
      inductionHypothesis =>
    exact Nat.le_trans inductionHypothesis
      (collectTemplate_nextFresh_mono after template answerBindings)
  all_goals assumption

/-- Cut-scope allocation is globally monotone and therefore cannot alias an
outer activation after backtracking. -/
theorem nextCutScope_mono {before after : Session} {search : Search}
    {events : List Observation} {signal : Trace.CutSignal}
    {target : RawTarget}
    (step : RawStep before search events signal after target) :
    before.nextCutScope ≤ after.nextCutScope := by
  induction step <;> try exact Nat.le_refl _
  case taskCall scope predicate arguments rest bindings session notThrow
      notDatabase =>
    simp only [openedFor, openLocalCall_nextCutScope]
    omega
  case taskCatch scope protectedGoal catcher handler rest bindings session =>
    simp only [openCatch_nextCutScope]
    omega
  case taskFindall scope template generator output rest bindings session =>
    simp only [openFindall_nextCutScope]
    omega
  case collectionAnswer collectionScope scope body next template output
      entryBindings tail reversed answerBindings before after child
      inductionHypothesis =>
    simpa only [collectTemplate_nextCutScope] using inductionHypothesis
  all_goals assumption

/-- Exception-handler identities use their own non-backtrackable allocator.
Ordinary calls leave it unchanged; entering `catch/3` advances it exactly
once, and every structural wrapper inherits the child's monotonicity. -/
theorem nextExceptionScope_mono {before after : Session} {search : Search}
    {events : List Observation} {signal : Trace.CutSignal}
    {target : RawTarget}
    (step : RawStep before search events signal after target) :
    before.nextExceptionScope ≤ after.nextExceptionScope := by
  induction step <;> try exact Nat.le_refl _
  case taskCatch scope protectedGoal catcher handler rest bindings session =>
    simp only [openCatch_nextExceptionScope]
    omega
  case collectionAnswer collectionScope scope body next template output
      entryBindings tail reversed answerBindings before after child
      inductionHypothesis =>
    simpa only [collectTemplate_nextExceptionScope] using inductionHypothesis
  all_goals assumption

/-- Collection identities use their own non-backtrackable allocator.  Only
entering `findall/3` advances it; copied elements and every other control node
preserve it exactly. -/
theorem nextCollectionScope_mono {before after : Session} {search : Search}
    {events : List Observation} {signal : Trace.CutSignal}
    {target : RawTarget}
    (step : RawStep before search events signal after target) :
    before.nextCollectionScope ≤ after.nextCollectionScope := by
  induction step <;> try exact Nat.le_refl _
  case taskFindall scope template generator output rest bindings session =>
    simp only [openFindall_nextCollectionScope]
    omega
  case collectionAnswer collectionScope scope body next template output
      entryBindings tail reversed answerBindings before after child
      inductionHypothesis =>
    simpa only [collectTemplate_nextCollectionScope] using inductionHypothesis
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
          List.nodup_append]

/-- Running successors inherit the linear cursor-ownership invariant. -/
theorem preserves_cursorOwnership {before after : Session}
    {search next : Search} {events : List Observation}
    {signal : Trace.CutSignal}
    (step : RawStep before search events signal after (.running next))
    (owned : search.CursorOwnership before.nextCutScope) :
    next.CursorOwnership after.nextCutScope :=
  preserves_cursorOwnership_target step owned

/-- Every raw transition carries an exact ordered chronology for its
persistent database mutations.  Search backtracking can restore goals and
substitutions, but it cannot restore this session component: wrappers inherit
their child's chronology and discarded cursors add only prune observations. -/
theorem database_chronology {before after : Session} {search : Search}
    {events : List Observation} {signal : Trace.CutSignal}
    {target : RawTarget}
    (step : RawStep before search events signal after target) :
    DatabaseChronology before.resolver.database
      (databaseEffects events) after.resolver.database := by
  induction step with
  | taskAsserta =>
      exact .step (.asserta _ _) (.refl _)
  | taskAssertz =>
      exact .step (.assertz _ _) (.refl _)
  | taskRetractMatched _ _ _ _ _ _ _ _ _ _ _ _ _ scan reachable retracted =>
      exact .step
        (.retract reachable (RetractScan.matched_mem scan) retracted)
        (.refl _)
  | clausesPull scope cursor outcome session pulled =>
      cases outcome with
      | silent next => exact .refl _
      | reply entered next => exact .refl _
      | effect effect next => exact Empty.elim effect
      | exhausted => exact .refl _
      | raised exception => exact Empty.elim exception
  | collectionAnswer collectionScope scope body next template output
      entryBindings tail reversed answerBindings before after child
      inductionHypothesis =>
      simpa [databaseEffects] using inductionHypothesis
  | _ =>
      first
      | exact .refl _
      | simpa [databaseEffects, databaseEffects_append] using
          (by assumption : DatabaseChronology _ _ _)

/-- A raw step advances the persistent logical-update generation by exactly
the number of ordered database effects that it emits. -/
theorem database_generation_eq_add_effects {before after : Session}
    {search : Search} {events : List Observation}
    {signal : Trace.CutSignal} {target : RawTarget}
    (step : RawStep before search events signal after target) :
    after.resolver.database.generation =
      before.resolver.database.generation +
        (databaseEffects events).length :=
  step.database_chronology.generation_eq_add_length

/-- Persistent logical-update generations cannot regress across a raw step. -/
theorem database_generation_mono {before after : Session}
    {search : Search} {events : List Observation}
    {signal : Trace.CutSignal} {target : RawTarget}
    (step : RawStep before search events signal after target) :
    before.resolver.database.generation ≤
      after.resolver.database.generation :=
  step.database_chronology.generation_mono

/-- Database histories stay completely reachable across every raw transition,
including failure, backtracking, and exception unwinding. -/
theorem preserves_databaseClosed {before after : Session} {search : Search}
    {events : List Observation} {signal : Trace.CutSignal}
    {target : RawTarget}
    (step : RawStep before search events signal after target)
    (closed : before.DatabaseClosed) : after.DatabaseClosed :=
  step.database_chronology.preserves_reachable closed

set_option linter.unnecessarySeqFocus false in
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
  | catchBoundary handlerScope scope body catcher handler entryBindings
      inductionHypothesis =>
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
      | catchProgress _ _ _ _ _ _ _ _ _ _ _ firstStep =>
          have compare := @compareStep _ _ _ _ firstStep
          clear firstStep
          cases second <;>
            have inner := compare (by assumption) <;>
            clear compare compareStep inductionHypothesis <;>
            rcases inner with ⟨eventsEq, signalEq, afterEq, targetEq⟩ <;>
            cases eventsEq <;> cases signalEq <;> cases afterEq <;>
            cases targetEq <;>
            simp_all
      | catchComplete _ _ _ _ _ _ _ _ firstStep =>
          have compare := @compareStep _ _ _ _ firstStep
          clear firstStep
          cases second <;>
            have inner := compare (by assumption) <;>
            clear compare compareStep inductionHypothesis <;>
            rcases inner with ⟨eventsEq, signalEq, afterEq, targetEq⟩ <;>
            cases eventsEq <;> cases signalEq <;> cases afterEq <;>
            cases targetEq <;>
            simp_all
      | catchHandled _ _ _ _ _ _ _ _ _ _ _ firstStep firstSelected
          firstResolved =>
          have compare := @compareStep _ _ _ _ firstStep
          clear firstStep
          cases second <;>
            have inner := compare (by assumption) <;>
            rcases inner with ⟨eventsEq, signalEq, afterEq, targetEq⟩ <;>
            cases targetEq <;> cases eventsEq <;> cases signalEq <;>
            cases afterEq <;>
            simp_all <;>
            exact CatchResolution.deterministic firstResolved (by assumption)
      | catchUnmatched _ _ _ _ _ _ _ _ _ _ firstStep firstUnmatched =>
          have compare := @compareStep _ _ _ _ firstStep
          clear firstStep
          cases second <;>
            have inner := compare (by assumption) <;>
            rcases inner with ⟨eventsEq, signalEq, afterEq, targetEq⟩ <;>
            cases targetEq <;> cases eventsEq <;> cases signalEq <;>
            cases afterEq <;>
            simp_all
  | collectionBoundary collectionScope scope body template output
      entryBindings tail reversed inductionHypothesis =>
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
      | collectionAnswer _ _ _ firstNext _ _ _ _ _ firstAnswer _ firstAfter
          firstStep =>
          cases second with
          | collectionAnswer _ _ _ secondNext _ _ _ _ _ secondAnswer _
              secondAfter secondStep =>
              rcases compareStep firstStep secondStep with
                ⟨eventsEq, _, afterEq, targetEq⟩
              have answerEq : firstAnswer = secondAnswer := by
                exact Trace.Observation.answer.inj
                  (List.cons.inj eventsEq).1
              have nextEq : firstNext = secondNext := by
                exact RawTarget.running.inj targetEq
              subst secondAnswer
              subst secondNext
              subst secondAfter
              exact ⟨rfl, rfl, rfl, rfl⟩
          | collectionProgress _ _ _ secondNext _ _ _ _ _ secondEvents
              secondSignal _ secondAfter secondStep secondAnswerFree =>
              rcases compareStep firstStep secondStep with
                ⟨eventsEq, _, _, _⟩
              exfalso
              apply secondAnswerFree firstAnswer
              rw [← eventsEq]
              simp
          | collectionComplete _ _ _ _ _ _ _ _ _ secondAfter secondStep =>
              have targetEq := (compareStep firstStep secondStep).2.2.2
              exact RawTarget.noConfusion targetEq
          | collectionRaised _ _ _ _ _ _ _ _ _ _ _ secondAfter
              secondStep =>
              have targetEq := (compareStep firstStep secondStep).2.2.2
              exact RawTarget.noConfusion targetEq
      | collectionProgress _ _ _ firstNext _ _ _ _ _ firstEvents firstSignal
          _ firstAfter firstStep firstAnswerFree =>
          cases second with
          | collectionAnswer _ _ _ secondNext _ _ _ _ _ secondAnswer _
              secondAfter secondStep =>
              rcases compareStep firstStep secondStep with
                ⟨eventsEq, _, _, _⟩
              exfalso
              apply firstAnswerFree secondAnswer
              rw [eventsEq]
              simp
          | collectionProgress _ _ _ secondNext _ _ _ _ _ secondEvents
              secondSignal _ secondAfter secondStep secondAnswerFree =>
              rcases compareStep firstStep secondStep with
                ⟨eventsEq, signalEq, afterEq, targetEq⟩
              have nextEq : firstNext = secondNext := by
                exact RawTarget.running.inj targetEq
              subst secondNext
              exact ⟨eventsEq, signalEq, afterEq, rfl⟩
          | collectionComplete _ _ _ _ _ _ _ _ _ secondAfter secondStep =>
              have targetEq := (compareStep firstStep secondStep).2.2.2
              exact RawTarget.noConfusion targetEq
          | collectionRaised _ _ _ _ _ _ _ _ _ _ _ secondAfter
              secondStep =>
              have targetEq := (compareStep firstStep secondStep).2.2.2
              exact RawTarget.noConfusion targetEq
      | collectionComplete _ _ _ _ _ _ _ _ _ firstAfter firstStep =>
          cases second with
          | collectionAnswer _ _ _ secondNext _ _ _ _ _ secondAnswer _
              secondAfter secondStep =>
              have targetEq := (compareStep firstStep secondStep).2.2.2
              exact RawTarget.noConfusion targetEq
          | collectionProgress _ _ _ secondNext _ _ _ _ _ secondEvents
              secondSignal _ secondAfter secondStep secondAnswerFree =>
              have targetEq := (compareStep firstStep secondStep).2.2.2
              exact RawTarget.noConfusion targetEq
          | collectionComplete _ _ _ _ _ _ _ _ _ secondAfter secondStep =>
              have afterEq := (compareStep firstStep secondStep).2.2.1
              subst secondAfter
              exact ⟨rfl, rfl, rfl, rfl⟩
          | collectionRaised _ _ _ _ _ _ _ _ secondException secondEvents _
              secondAfter secondStep =>
              have targetEq := (compareStep firstStep secondStep).2.2.2
              have tagEq := RawTarget.terminal.inj targetEq
              exact RawTerminal.noConfusion tagEq
      | collectionRaised _ _ _ _ _ _ _ _ firstException firstEvents _
          firstAfter firstStep =>
          cases second with
          | collectionAnswer _ _ _ secondNext _ _ _ _ _ secondAnswer _
              secondAfter secondStep =>
              have targetEq := (compareStep firstStep secondStep).2.2.2
              exact RawTarget.noConfusion targetEq
          | collectionProgress _ _ _ secondNext _ _ _ _ _ secondEvents
              secondSignal _ secondAfter secondStep secondAnswerFree =>
              have targetEq := (compareStep firstStep secondStep).2.2.2
              exact RawTarget.noConfusion targetEq
          | collectionComplete _ _ _ _ _ _ _ _ _ secondAfter secondStep =>
              have targetEq := (compareStep firstStep secondStep).2.2.2
              have tagEq := RawTarget.terminal.inj targetEq
              exact RawTerminal.noConfusion tagEq
          | collectionRaised _ _ _ _ _ _ _ _ secondException secondEvents _
              secondAfter secondStep =>
              rcases compareStep firstStep secondStep with
                ⟨eventsEq, _, afterEq, targetEq⟩
              have exceptionEq : firstException = secondException := by
                exact RawTerminal.raised.inj (RawTarget.terminal.inj targetEq)
              subst secondException
              subst secondAfter
              exact ⟨eventsEq, rfl, rfl, rfl⟩
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

/-- Exception-handler high-water carried by every public state.  Exception
identities are allocated independently of cut scopes and are not rewound by
failure, exception recovery, or backtracking. -/
def exceptionHighWater : State → Nat
  | .terminal session _ => session.nextExceptionScope
  | .running session _ => session.nextExceptionScope
  | .uncaughtCut session _ _ => session.nextExceptionScope

/-- Answer-collection high-water carried by every public state.  Collection
identities are nominally separate from cut and exception delimiters. -/
def collectionHighWater : State → Nat
  | .terminal session _ => session.nextCollectionScope
  | .running session _ => session.nextCollectionScope
  | .uncaughtCut session _ _ => session.nextCollectionScope

/-- Persistent logical-update database carried by every public state. -/
def database : State → Database
  | .terminal session _ => session.resolver.database
  | .running session _ => session.resolver.database
  | .uncaughtCut session _ _ => session.resolver.database

/-- Live cursor activations carried by every public state. -/
def liveCursorScopes : State → List CutScopeId
  | .terminal _ _ => []
  | .running _ search => search.liveCursorScopes
  | .uncaughtCut _ _ continuation => continuation.liveCursorScopes

/-- Complete public structural invariant used by reachability theorems. -/
def WellFormed (state : State) : Prop := state.Rooted ∧ state.CursorOwned

/-- Reachability invariant for the persistent database component of a public
state.  It is kept separate from cursor/scope well-formedness so each theorem
states exactly which resource discipline it consumes. -/
def DatabaseClosed (state : State) : Prop :=
  DatabaseReachable state.database

/-- Public running and diagnostic states retain cumulative substitution
lineage.  Public terminals have already erased the internal exception packet,
so this invariant is intentionally about the states from which further local
control can execute. -/
def BindingLineageFrom (entryBindings : Substitution) : State → Prop
  | .terminal _ _ => True
  | .running _ search => search.BindingLineageFrom entryBindings
  | .uncaughtCut _ _ continuation =>
      continuation.BindingLineageFrom entryBindings

end State

private def RawTarget.toState (session : Session) : RawTarget → State
  | .terminal tag => .terminal session tag.toTerminal
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

/-- Public transitions never rewind the independently allocated exception-
handler identities. -/
theorem exceptionHighWater_mono {start finish : State}
    {events : List Observation} (step : Transition start events finish) :
    start.exceptionHighWater ≤ finish.exceptionHighWater := by
  cases step with
  | ordinary search events before after target raw =>
      cases target <;>
        exact raw.nextExceptionScope_mono
  | uncaught search next events before after scope raw =>
      exact raw.nextExceptionScope_mono

/-- Public transitions never rewind the independently allocated collection
identities. -/
theorem collectionHighWater_mono {start finish : State}
    {events : List Observation} (step : Transition start events finish) :
    start.collectionHighWater ≤ finish.collectionHighWater := by
  cases step with
  | ordinary search events before after target raw =>
      cases target <;>
        exact raw.nextCollectionScope_mono
  | uncaught search next events before after scope raw =>
      exact raw.nextCollectionScope_mono

/-- One public transition changes the persistent database exactly according
to its ordered typed mutation observations. -/
theorem database_chronology {start finish : State}
    {events : List Observation} (step : Transition start events finish) :
    DatabaseChronology start.database (databaseEffects events)
      finish.database := by
  cases step with
  | ordinary search events before after target raw =>
      cases target <;> exact raw.database_chronology
  | uncaught search next events before after scope raw =>
      exact raw.database_chronology

/-- Public transitions preserve reachable database histories. -/
theorem preserves_databaseClosed {start finish : State}
    {events : List Observation} (step : Transition start events finish)
    (closed : start.DatabaseClosed) : finish.DatabaseClosed :=
  step.database_chronology.preserves_reachable closed

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

/-- Public one-step subject reduction for cumulative bindings.  The ordered
event batch is covered simultaneously so a product cannot consume an answer
whose substitution escaped the invariant. -/
theorem preserves_bindingLineage {entryBindings : Substitution}
    {start finish : State} {events : List Observation}
    (step : Transition start events finish)
    (lineage : start.BindingLineageFrom entryBindings) :
    EventsBindingLineage entryBindings events ∧
      finish.BindingLineageFrom entryBindings := by
  cases step with
  | ordinary search events before after target raw =>
      have preserved := raw.preserves_bindingLineage_target lineage
      constructor
      · exact preserved.1
      · cases target with
        | terminal tag => exact True.intro
        | running search => exact preserved.2
  | uncaught search next events before after scope raw =>
      exact raw.preserves_bindingLineage_target lineage

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

/-- Cumulative binding lineage and answer lineage hold over every finite
exact execution prefix. -/
theorem preserves_bindingLineage {count : Nat} {start finish : State}
    {events : List Observation} {entryBindings : Substitution}
    (execution : StepsN count start events finish)
    (lineage : start.BindingLineageFrom entryBindings) :
    EventsBindingLineage entryBindings events ∧
      finish.BindingLineageFrom entryBindings := by
  induction execution with
  | zero state => exact ⟨EventsBindingLineage.nil entryBindings, lineage⟩
  | succ count start middle finish first rest head tail
      inductionHypothesis =>
      have firstLineage := head.preserves_bindingLineage lineage
      have restLineage := inductionHypothesis firstLineage.2
      exact ⟨EventsBindingLineage.append firstLineage.1 restLineage.1,
        restLineage.2⟩

/-- Every finite exact prefix preserves the complete ordered database
chronology; no backtracking transition can erase an earlier mutation. -/
theorem database_chronology {count : Nat} {start finish : State}
    {events : List Observation} (execution : StepsN count start events finish) :
    DatabaseChronology start.database (databaseEffects events)
      finish.database := by
  induction execution with
  | zero state => exact .refl _
  | succ count start middle finish first rest head tail
      inductionHypothesis =>
      simpa [databaseEffects_append] using
        DatabaseChronology.trans head.database_chronology inductionHypothesis

/-- Every finite exact execution prefix preserves complete database
reachability, including prefixes that cross failure and backtracking. -/
theorem preserves_databaseClosed {count : Nat} {start finish : State}
    {events : List Observation} (execution : StepsN count start events finish)
    (closed : start.DatabaseClosed) : finish.DatabaseClosed :=
  execution.database_chronology.preserves_reachable closed

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

/-- Finite execution never rewinds the exception-handler allocator. -/
theorem exceptionHighWater_mono {count : Nat} {start finish : State}
    {events : List Observation} (execution : StepsN count start events finish) :
    start.exceptionHighWater ≤ finish.exceptionHighWater := by
  induction execution with
  | zero state => exact Nat.le_refl _
  | succ count start middle finish first rest head tail
      inductionHypothesis =>
      exact Nat.le_trans head.exceptionHighWater_mono inductionHypothesis

/-- Finite execution never rewinds the collection-identity allocator. -/
theorem collectionHighWater_mono {count : Nat} {start finish : State}
    {events : List Observation} (execution : StepsN count start events finish) :
    start.collectionHighWater ≤ finish.collectionHighWater := by
  induction execution with
  | zero state => exact Nat.le_refl _
  | succ count start middle finish first rest head tail
      inductionHypothesis =>
      exact Nat.le_trans head.collectionHighWater_mono inductionHypothesis

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

/-- Root execution starts with the empty substitution, and therefore enters
the cumulative binding-lineage invariant without an assumption. -/
theorem initialState_bindingLineage (resolverSession : LocalSession)
    (goals : List Goal) :
    (initialState resolverSession goals).BindingLineageFrom [] := by
  exact BindingLineage.refl []

/-! ## Concrete left-recursive program

The zero-arity clause below is deliberately tiny: `loop :- loop`.  It has no
clause-local variables, so the only unbounded structures in its execution are
the explicit finite search states and the monotone cut-scope allocator.  This
makes it a discriminating witness that recursion is represented by arbitrarily
long finite prefixes rather than by an eager infinite answer bag or fabricated
completion. -/

private def leftRecursivePredicate : String := "$pleatta_left_recursive"

private theorem leftRecursive_notThrow :
    ¬ BuiltinThrowCall leftRecursivePredicate [] := by
  simp [BuiltinThrowCall]

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
        (leftRecursiveSession (scope + 1)) leftRecursive_notThrow rfl
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
        (leftRecursiveSession 1) leftRecursive_notThrow rfl))

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
    (bindings : Substitution) (session : Session)
    (notThrow : ¬ BuiltinThrowCall predicate arguments)
    (notDatabase : recognizeDatabaseAction predicate arguments = none) :
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
  exact .taskCall scope predicate arguments rest bindings session notThrow
    notDatabase

/-! ## Local `findall/3` specialization -/

/-- Entering `findall/3` allocates an opaque generator cut scope and a
nominally distinct collection scope.  The caller tail and entry substitution
are retained by the certified collector; no provider receives the authority
to emit the bag or schedule the generator.

[SPEC SWI-Prolog manual, `findall/3` and meta-call cut opacity] -/
theorem findall_enters_distinct_delimiters (scope : CutScopeId)
    (template : Term) (generator : Goal) (output : Term)
    (rest : List Goal) (bindings : Substitution) (session : Session) :
    RawStep session
      (.task scope (.findall template generator output :: rest) bindings)
      [] .none (openFindall session).session
      (.running
        (.collectionBoundary (openFindall session).collectionScope scope
          (.cutBoundary (openFindall session).cutScope
            (.task (openFindall session).cutScope [generator] bindings))
          template output bindings rest [])) := by
  exact .taskFindall scope template generator output rest bindings session

/-- One generator answer is consumed internally, materialized, injectively
copied apart, and prepended to the private reverse accumulator.  In
particular, the generator substitution is not an outer observable answer. -/
theorem findall_answer_copies_silently
    (collectionScope : CollectionScopeId) (scope : CutScopeId)
    (body next : Search) (template output : Term)
    (entryBindings : Substitution) (tail : List Goal)
    (reversed : List Term) (answerBindings : Substitution)
    (before after : Session)
    (child : RawStep before body [.answer answerBindings] .none after
      (.running next)) :
    RawStep before
      (.collectionBoundary collectionScope scope body template output
        entryBindings tail reversed)
      [] .none (collectTemplate after template answerBindings).session
      (.running
        (.collectionBoundary collectionScope scope next template output
          entryBindings tail
          ((collectTemplate after template answerBindings).prepared.copied ::
            reversed))) := by
  exact .collectionAnswer collectionScope scope body next template output
    entryBindings tail reversed answerBindings before after child

/-- Generator exhaustion is consumed, the private reverse accumulator is
reversed exactly once, and the resulting proper list is unified against the
caller's output under the original entry substitution.  This pins source
order and occurrence multiplicity without exposing an intermediate bag. -/
theorem findall_exhaustion_builds_ordered_bag
    (collectionScope : CollectionScopeId) (scope : CutScopeId)
    (body : Search) (template output : Term)
    (entryBindings : Substitution) (tail : List Goal)
    (reversed : List Term) (before after : Session)
    (child : RawStep before body [.completed] .none after
      (.terminal .completed)) :
    RawStep before
      (.collectionBoundary collectionScope scope body template output
        entryBindings tail reversed)
      [] .none after
      (.running
        (.task scope
          (.unify output (.list reversed.reverse none) :: tail)
          entryBindings)) := by
  exact .collectionComplete collectionScope scope body template output
    entryBindings tail reversed before after child

/-- `findall/3` is transparent to exceptions: the exact child event batch and
raised terminal packet escape unchanged, and no partial bag is produced. -/
theorem findall_exception_transparent
    (collectionScope : CollectionScopeId) (scope : CutScopeId)
    (body : Search) (template output : Term)
    (entryBindings : Substitution) (tail : List Goal)
    (reversed : List Term) (exception : RaisedException)
    (events : List Observation) (before after : Session)
    (child : RawStep before body events .none after
      (.terminal (.raised exception))) :
    RawStep before
      (.collectionBoundary collectionScope scope body template output
        entryBindings tail reversed)
      events .none after (.terminal (.raised exception)) := by
  exact .collectionRaised collectionScope scope body template output
    entryBindings tail reversed exception events before after child

private def findallWitnessTemplateVar : LogicVar := .source "$findall_x"
private def findallWitnessOutputVar : LogicVar := .source "$findall_bag"
private def findallWitnessLeft : Term := .atom "$left"
private def findallWitnessRight : Term := .atom "$right"
private def findallWitnessTemplate : Term :=
  .variable findallWitnessTemplateVar
private def findallWitnessOutput : Term :=
  .variable findallWitnessOutputVar
private def findallWitnessLeftBindings : Substitution :=
  [(findallWitnessTemplateVar, findallWitnessLeft)]
private def findallWitnessRightBindings : Substitution :=
  [(findallWitnessTemplateVar, findallWitnessRight)]
private def findallWitnessBag : Term :=
  .list [findallWitnessLeft, findallWitnessRight] none
private def findallWitnessResult : Substitution :=
  [(findallWitnessOutputVar,
    Tree.reify (Term.denote findallWitnessBag))]
private def findallWitnessGenerator : Goal :=
  .disjunction
    [.unify findallWitnessTemplate findallWitnessLeft,
     .unify findallWitnessTemplate findallWitnessRight]

private theorem findallWitness_left_resolves :
    UnifyResolution [] findallWitnessTemplate findallWitnessLeft
      findallWitnessLeftBindings := by
  refine ⟨findallWitnessLeftBindings, ?_, by
    simp [findallWitnessLeftBindings]⟩
  simpa [findallWitnessTemplateVar, findallWitnessTemplate,
      findallWitnessLeft, findallWitnessLeftBindings,
      TreeSubstitution.reify, Tree.reify, Term.denote]
    using
      (computes_singleton_left_variable findallWitnessTemplateVar
        findallWitnessLeft (by
          intro equality
          cases equality) (by rfl))

private theorem findallWitness_right_resolves :
    UnifyResolution [] findallWitnessTemplate findallWitnessRight
      findallWitnessRightBindings := by
  refine ⟨findallWitnessRightBindings, ?_, by
    simp [findallWitnessRightBindings]⟩
  simpa [findallWitnessTemplateVar, findallWitnessTemplate,
      findallWitnessRight, findallWitnessRightBindings,
      TreeSubstitution.reify, Tree.reify, Term.denote]
    using
      (computes_singleton_left_variable findallWitnessTemplateVar
        findallWitnessRight (by
          intro equality
          cases equality) (by rfl))

private theorem findallWitness_output_resolves :
    UnifyResolution [] findallWitnessOutput findallWitnessBag
      findallWitnessResult := by
  refine ⟨findallWitnessResult, ?_, by
    simp [findallWitnessResult]⟩
  simpa [findallWitnessOutputVar, findallWitnessOutput,
      findallWitnessBag, findallWitnessResult, findallWitnessLeft,
      findallWitnessRight, TreeSubstitution.reify, Tree.reify, Term.denote]
    using
      (computes_singleton_left_variable findallWitnessOutputVar
        findallWitnessBag (by
          intro equality
          cases equality) (by rfl))

@[simp] private theorem findallWitness_left_copy (session : Session) :
    (collectTemplate session findallWitnessTemplate
      findallWitnessLeftBindings).prepared.copied = findallWitnessLeft := by
  rfl

@[simp] private theorem findallWitness_right_copy (session : Session) :
    (collectTemplate session findallWitnessTemplate
      findallWitnessRightBindings).prepared.copied = findallWitnessRight := by
  rfl

/-- A source-shaped local `findall/3` over two ordered generator branches
executes entirely in the certified layer.  The two internal substitutions are
suppressed, their copied templates retain left-to-right order and occurrence
multiplicity, and exactly one outer answer is followed by completion.

Changing the collector to a set, reversing arrival order, leaking generator
answers, or completing before exhaustion falsifies this exact trace.

[SPEC SWI-Prolog manual, `findall/3`] -/
theorem local_findall_two_answers_exact_trace (scope : CutScopeId)
    (session : Session) :
    StepsN 11
      (.running session
        (.task scope
          [.findall findallWitnessTemplate findallWitnessGenerator
            findallWitnessOutput]
          []))
      [.answer findallWitnessResult, .completed]
      (.terminal
        (collectTemplate
          (collectTemplate (openFindall session).session
            findallWitnessTemplate findallWitnessLeftBindings).session
          findallWitnessTemplate findallWitnessRightBindings).session
        .completed) := by
  let opened := openFindall session
  let inner := opened.cutScope
  let collection := opened.collectionScope
  let leftGoal : Goal :=
    .unify findallWitnessTemplate findallWitnessLeft
  let rightGoal : Goal :=
    .unify findallWitnessTemplate findallWitnessRight
  let leftCopy :=
    collectTemplate opened.session findallWitnessTemplate
      findallWitnessLeftBindings
  let rightCopy :=
    collectTemplate leftCopy.session findallWitnessTemplate
      findallWitnessRightBindings
  let leftElement := leftCopy.prepared.copied
  let rightElement := rightCopy.prepared.copied
  let collectedBag : Term := .list [leftElement, rightElement] none
  let initial : State :=
    .running session
      (.task scope
        [.findall findallWitnessTemplate findallWitnessGenerator
          findallWitnessOutput]
        [])
  let entered : State :=
    .running opened.session
      (.collectionBoundary collection scope
        (.cutBoundary inner
          (.task inner [findallWitnessGenerator] []))
        findallWitnessTemplate findallWitnessOutput [] [] [])
  let branched : State :=
    .running opened.session
      (.collectionBoundary collection scope
        (.cutBoundary inner
          (Search.disjoin inner [leftGoal, rightGoal] [] []))
        findallWitnessTemplate findallWitnessOutput [] [] [])
  let leftSolved : State :=
    .running opened.session
      (.collectionBoundary collection scope
        (.cutBoundary inner
          (.choice inner
            (.task inner [] findallWitnessLeftBindings)
            (.task inner [rightGoal] [])))
        findallWitnessTemplate findallWitnessOutput [] [] [])
  let leftCollected : State :=
    .running leftCopy.session
      (.collectionBoundary collection scope
        (.cutBoundary inner
          (.choice inner .done (.task inner [rightGoal] [])))
        findallWitnessTemplate findallWitnessOutput [] []
        [leftElement])
  let rightPending : State :=
    .running leftCopy.session
      (.collectionBoundary collection scope
        (.cutBoundary inner (.task inner [rightGoal] []))
        findallWitnessTemplate findallWitnessOutput [] []
        [leftElement])
  let rightSolved : State :=
    .running leftCopy.session
      (.collectionBoundary collection scope
        (.cutBoundary inner
          (.task inner [] findallWitnessRightBindings))
        findallWitnessTemplate findallWitnessOutput [] []
        [leftElement])
  let rightCollected : State :=
    .running rightCopy.session
      (.collectionBoundary collection scope
        (.cutBoundary inner .done)
        findallWitnessTemplate findallWitnessOutput [] []
        [rightElement, leftElement])
  let bagPending : State :=
    .running rightCopy.session
      (.task scope
        [.unify findallWitnessOutput collectedBag] [])
  let bagSolved : State :=
    .running rightCopy.session
      (.task scope [] findallWitnessResult)
  let answered : State := .running rightCopy.session .done
  let finished : State := .terminal rightCopy.session .completed
  have leftElement_eq : leftElement = findallWitnessLeft := by
    change
      (collectTemplate opened.session findallWitnessTemplate
        findallWitnessLeftBindings).prepared.copied = findallWitnessLeft
    exact findallWitness_left_copy opened.session
  have rightElement_eq : rightElement = findallWitnessRight := by
    change
      (collectTemplate leftCopy.session findallWitnessTemplate
        findallWitnessRightBindings).prepared.copied = findallWitnessRight
    exact findallWitness_right_copy leftCopy.session
  have enterStep : Transition initial [] entered := by
    dsimp [initial, entered, opened, inner, collection]
    exact .ordinary _ _ _ _ _
      (.taskFindall scope findallWitnessTemplate findallWitnessGenerator
        findallWitnessOutput [] [] session)
  have branchStep : Transition entered [] branched := by
    have raw : RawStep opened.session
        (.collectionBoundary collection scope
          (.cutBoundary inner
            (.task inner [findallWitnessGenerator] []))
          findallWitnessTemplate findallWitnessOutput [] [] [])
        [] .none opened.session
        (.running
          (.collectionBoundary collection scope
            (.cutBoundary inner
              (Search.disjoin inner [leftGoal, rightGoal] [] []))
            findallWitnessTemplate findallWitnessOutput [] [] [])) := by
      apply RawStep.collectionProgress
      · apply RawStep.cutBoundaryProgress
        simpa [findallWitnessGenerator, leftGoal, rightGoal] using
          (RawStep.taskDisjunction inner [leftGoal, rightGoal] [] []
            opened.session)
      · simp [Trace.AnswerFree]
    simpa [entered, branched, RawTarget.toState] using
      (Transition.ordinary _ _ opened.session opened.session _ raw)
  have leftStep : Transition branched [] leftSolved := by
    have raw : RawStep opened.session
        (.collectionBoundary collection scope
          (.cutBoundary inner
            (Search.disjoin inner [leftGoal, rightGoal] [] []))
          findallWitnessTemplate findallWitnessOutput [] [] [])
        [] .none opened.session
        (.running
          (.collectionBoundary collection scope
            (.cutBoundary inner
              (.choice inner
                (.task inner [] findallWitnessLeftBindings)
                (.task inner [rightGoal] [])))
            findallWitnessTemplate findallWitnessOutput [] [] [])) := by
      apply RawStep.collectionProgress
      · simpa [Search.disjoin] using
          (RawStep.cutBoundaryProgress inner _ _ [] opened.session
            opened.session
            (RawStep.choiceProgress inner _ _ _ [] opened.session
              opened.session
              (RawStep.taskUnifySuccess inner findallWitnessTemplate
                findallWitnessLeft [] [] findallWitnessLeftBindings
                opened.session findallWitness_left_resolves)))
      · simp [Trace.AnswerFree]
    simpa [branched, leftSolved, RawTarget.toState] using
      (Transition.ordinary _ _ opened.session opened.session _ raw)
  have collectLeftStep : Transition leftSolved [] leftCollected := by
    dsimp [leftSolved, leftCollected, opened, inner, collection, rightGoal,
      leftCopy, leftElement]
    simpa [RawTarget.toState, opened, inner, collection, rightGoal, leftCopy,
      leftElement] using
      (Transition.ordinary _ _ _ _ _
        (RawStep.collectionAnswer collection scope _ _
          findallWitnessTemplate findallWitnessOutput [] [] []
          findallWitnessLeftBindings opened.session opened.session
          (RawStep.cutBoundaryProgress inner _ _
            [.answer findallWitnessLeftBindings]
            opened.session opened.session
            (RawStep.choiceProgress inner _ _ _
              [.answer findallWitnessLeftBindings]
              opened.session opened.session
              (RawStep.taskAnswer inner findallWitnessLeftBindings
                opened.session)))))
  have switchStep : Transition leftCollected [] rightPending := by
    have raw : RawStep leftCopy.session
        (.collectionBoundary collection scope
          (.cutBoundary inner
            (.choice inner .done (.task inner [rightGoal] [])))
          findallWitnessTemplate findallWitnessOutput [] [] [leftElement])
        [] .none leftCopy.session
        (.running
          (.collectionBoundary collection scope
            (.cutBoundary inner (.task inner [rightGoal] []))
            findallWitnessTemplate findallWitnessOutput [] []
            [leftElement])) := by
      apply RawStep.collectionProgress
      · apply RawStep.cutBoundaryProgress
        apply RawStep.choiceComplete
        exact .done _
      · simp [Trace.AnswerFree]
    simpa [leftCollected, rightPending, RawTarget.toState] using
      (Transition.ordinary _ _ leftCopy.session leftCopy.session _ raw)
  have rightStep : Transition rightPending [] rightSolved := by
    have raw : RawStep leftCopy.session
        (.collectionBoundary collection scope
          (.cutBoundary inner (.task inner [rightGoal] []))
          findallWitnessTemplate findallWitnessOutput [] [] [leftElement])
        [] .none leftCopy.session
        (.running
          (.collectionBoundary collection scope
            (.cutBoundary inner
              (.task inner [] findallWitnessRightBindings))
            findallWitnessTemplate findallWitnessOutput [] []
            [leftElement])) := by
      apply RawStep.collectionProgress
      · apply RawStep.cutBoundaryProgress
        simpa [rightGoal] using
          (RawStep.taskUnifySuccess inner findallWitnessTemplate
            findallWitnessRight [] [] findallWitnessRightBindings
            leftCopy.session findallWitness_right_resolves)
      · simp [Trace.AnswerFree]
    simpa [rightPending, rightSolved, RawTarget.toState] using
      (Transition.ordinary _ _ leftCopy.session leftCopy.session _ raw)
  have collectRightStep : Transition rightSolved [] rightCollected := by
    have raw : RawStep leftCopy.session
        (.collectionBoundary collection scope
          (.cutBoundary inner
            (.task inner [] findallWitnessRightBindings))
          findallWitnessTemplate findallWitnessOutput [] [] [leftElement])
        [] .none rightCopy.session
        (.running
          (.collectionBoundary collection scope
            (.cutBoundary inner .done)
            findallWitnessTemplate findallWitnessOutput [] []
            [rightElement, leftElement])) := by
      exact RawStep.collectionAnswer collection scope _ _
        findallWitnessTemplate findallWitnessOutput [] [] [leftElement]
        findallWitnessRightBindings leftCopy.session leftCopy.session
        (RawStep.cutBoundaryProgress inner _ _
          [.answer findallWitnessRightBindings]
          leftCopy.session leftCopy.session
          (RawStep.taskAnswer inner findallWitnessRightBindings
            leftCopy.session))
    simpa [rightSolved, rightCollected, RawTarget.toState] using
      (Transition.ordinary _ _ leftCopy.session rightCopy.session _ raw)
  have exhaustStep : Transition rightCollected [] bagPending := by
    have raw : RawStep rightCopy.session
        (.collectionBoundary collection scope
          (.cutBoundary inner .done)
          findallWitnessTemplate findallWitnessOutput [] []
          [rightElement, leftElement])
        [] .none rightCopy.session
        (.running
          (.task scope
            [.unify findallWitnessOutput collectedBag] [])) := by
      simpa [collectedBag] using
        (RawStep.collectionComplete collection scope _
          findallWitnessTemplate findallWitnessOutput [] []
          [rightElement, leftElement]
          rightCopy.session rightCopy.session
          (RawStep.cutBoundaryComplete inner .done rightCopy.session
            rightCopy.session (.done rightCopy.session)))
    simpa [rightCollected, bagPending, RawTarget.toState] using
      (Transition.ordinary _ _ rightCopy.session rightCopy.session _ raw)
  have outputStep : Transition bagPending [] bagSolved := by
    have resolved : UnifyResolution [] findallWitnessOutput collectedBag
        findallWitnessResult := by
      simpa only [collectedBag, leftElement_eq, rightElement_eq,
        findallWitnessBag]
        using findallWitness_output_resolves
    have raw : RawStep rightCopy.session
        (.task scope [.unify findallWitnessOutput collectedBag] [])
        [] .none rightCopy.session
        (.running (.task scope [] findallWitnessResult)) :=
      .taskUnifySuccess scope findallWitnessOutput collectedBag [] []
        findallWitnessResult rightCopy.session resolved
    simpa [bagPending, bagSolved, RawTarget.toState] using
      (Transition.ordinary _ _ rightCopy.session rightCopy.session _ raw)
  have answerStep : Transition bagSolved [.answer findallWitnessResult]
      answered := by
    dsimp [bagSolved, answered, rightCopy, leftCopy, opened]
    exact .ordinary _ _ _ _ _
      (.taskAnswer scope findallWitnessResult _)
  have completeStep : Transition answered [.completed] finished := by
    dsimp [answered, finished, rightCopy, leftCopy, opened]
    exact .ordinary _ _ _ _ _ (.done _)
  have one {start finish : State} {events : List Observation}
      (step : Transition start events finish) :
      StepsN 1 start events finish := by
    simpa using
      (StepsN.succ 0 start finish finish events [] step (.zero finish))
  have execution :=
    StepsN.trans (one enterStep)
      (StepsN.trans (one branchStep)
        (StepsN.trans (one leftStep)
          (StepsN.trans (one collectLeftStep)
            (StepsN.trans (one switchStep)
              (StepsN.trans (one rightStep)
                (StepsN.trans (one collectRightStep)
                  (StepsN.trans (one exhaustStep)
                    (StepsN.trans (one outputStep)
                      (StepsN.trans (one answerStep)
                        (one completeStep))))))))))
  simpa [initial, finished, opened, leftCopy, rightCopy] using execution

/-! ### Answer followed by divergence

The next witness distinguishes operational generator traversal from a
blocking provider that can return only a completed finite answer list.  Its
generator succeeds once and then enters the concrete local clause
`loop :- loop`.  The first template is retained privately, while every later
finite prefix remains open and contains only recursive call-open events.
-/

private def findallLoopTemplate : Term := .atom "$kept"
private def findallLoopOutputVar : LogicVar := .source "$loop_bag"
private def findallLoopOutput : Term := .variable findallLoopOutputVar
private def findallLoopGenerator : Goal :=
  .disjunction [.truth, .call leftRecursivePredicate []]

/-- Collection identity zero is deliberate: opening from this session raises
the collection high-water to one, exactly matching `leftRecursiveSession` and
letting the previously certified recursive spine be reused without changing
any allocator field. -/
private def findallLoopInitialSession : Session :=
  { resolver := leftRecursiveResolver
    nextCutScope := 1
    nextCollectionScope := 0 }

private theorem openFindall_loop_initial :
    openFindall findallLoopInitialSession =
      { cutScope := 1
        collectionScope := { index := 0 }
        session := leftRecursiveSession 2 } := by
  rfl

private theorem findallLoop_copy_session :
    (collectTemplate (leftRecursiveSession 2) findallLoopTemplate []).session =
      leftRecursiveSession 2 := by
  rfl

private theorem findallLoop_copy_term :
    (collectTemplate (leftRecursiveSession 2) findallLoopTemplate
      []).prepared.copied = findallLoopTemplate := by
  rfl

private def findallLoopOpenState (depth : Nat) : State :=
  .running (leftRecursiveSession (depth + 3))
    (.collectionBoundary { index := 0 } 0
      (.cutBoundary 1
        (.product 1 (leftRecursiveChain depth 2) []))
      findallLoopTemplate findallLoopOutput [] [] [findallLoopTemplate])

private def findallLoopPulledState (depth : Nat) : State :=
  .running (leftRecursiveSession (depth + 3))
    (.collectionBoundary { index := 0 } 0
      (.cutBoundary 1
        (.product 1 (leftRecursivePulled depth 2) []))
      findallLoopTemplate findallLoopOutput [] [] [findallLoopTemplate])

private theorem findallLoop_pull_transition (depth : Nat) :
    Transition (findallLoopOpenState depth) []
      (findallLoopPulledState depth) := by
  have inner := leftRecursiveChain_pull depth 2
    (leftRecursiveSession (depth + 3))
  have raw : RawStep (leftRecursiveSession (depth + 3))
      (.collectionBoundary { index := 0 } 0
        (.cutBoundary 1
          (.product 1 (leftRecursiveChain depth 2) []))
        findallLoopTemplate findallLoopOutput [] [] [findallLoopTemplate])
      [] .none (leftRecursiveSession (depth + 3))
      (.running
        (.collectionBoundary { index := 0 } 0
          (.cutBoundary 1
            (.product 1 (leftRecursivePulled depth 2) []))
          findallLoopTemplate findallLoopOutput [] []
          [findallLoopTemplate])) := by
    apply RawStep.collectionProgress
    · apply RawStep.cutBoundaryProgress
      apply RawStep.productProgress
      · exact inner
      · simp [Trace.AnswerFree]
    · simp [Trace.AnswerFree]
  simpa [findallLoopOpenState, findallLoopPulledState, RawTarget.toState]
    using
      (Transition.ordinary _ _ (leftRecursiveSession (depth + 3))
        (leftRecursiveSession (depth + 3)) _ raw)

private theorem findallLoop_open_transition (depth : Nat) :
    Transition (findallLoopPulledState depth)
      [.opened leftRecursiveRequest] (findallLoopOpenState (depth + 1)) := by
  have inner :
      RawStep (leftRecursiveSession (depth + 3))
        (leftRecursivePulled depth 2) [.opened leftRecursiveRequest] .none
        (leftRecursiveSession (depth + 4))
        (.running (leftRecursiveChain (depth + 1) 2)) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (leftRecursivePulled_open depth 2)
  have raw : RawStep (leftRecursiveSession (depth + 3))
      (.collectionBoundary { index := 0 } 0
        (.cutBoundary 1
          (.product 1 (leftRecursivePulled depth 2) []))
        findallLoopTemplate findallLoopOutput [] [] [findallLoopTemplate])
      [.opened leftRecursiveRequest] .none
      (leftRecursiveSession (depth + 4))
      (.running
        (.collectionBoundary { index := 0 } 0
          (.cutBoundary 1
            (.product 1 (leftRecursiveChain (depth + 1) 2) []))
          findallLoopTemplate findallLoopOutput [] []
          [findallLoopTemplate])) := by
    apply RawStep.collectionProgress
    · apply RawStep.cutBoundaryProgress
      apply RawStep.productProgress
      · exact inner
      · simp [Trace.AnswerFree]
    · simp [Trace.AnswerFree]
  simpa [findallLoopPulledState, findallLoopOpenState, RawTarget.toState,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (Transition.ordinary _ _ (leftRecursiveSession (depth + 3))
      (leftRecursiveSession (depth + 4)) _ raw)

private theorem findallLoop_cycle (depth : Nat) :
    StepsN 2 (findallLoopOpenState depth) [.opened leftRecursiveRequest]
      (findallLoopOpenState (depth + 1)) := by
  exact StepsN.succ 1 _ _ _ [] [.opened leftRecursiveRequest]
    (findallLoop_pull_transition depth)
    (StepsN.succ 0 _ _ _ [.opened leftRecursiveRequest] []
      (findallLoop_open_transition depth) (StepsN.zero _))

private theorem findallLoop_cycles (cycles : Nat) :
    StepsN (2 * cycles) (findallLoopOpenState 0)
      (leftRecursiveEvents cycles) (findallLoopOpenState cycles) := by
  induction cycles with
  | zero => exact StepsN.zero _
  | succ cycles inductionHypothesis =>
      simpa [leftRecursiveEvents, Nat.mul_succ] using
        (StepsN.trans inductionHypothesis (findallLoop_cycle cycles))

private def findallLoopEnteredState : State :=
  .running (leftRecursiveSession 2)
    (.collectionBoundary { index := 0 } 0
      (.cutBoundary 1
        (.task 1 [findallLoopGenerator] []))
      findallLoopTemplate findallLoopOutput [] [] [])

private def findallLoopBranchedState : State :=
  .running (leftRecursiveSession 2)
    (.collectionBoundary { index := 0 } 0
      (.cutBoundary 1
        (Search.disjoin 1
          [.truth, .call leftRecursivePredicate []] [] []))
      findallLoopTemplate findallLoopOutput [] [] [])

private def findallLoopTruthState : State :=
  .running (leftRecursiveSession 2)
    (.collectionBoundary { index := 0 } 0
      (.cutBoundary 1
        (.choice 1
          (.task 1 [] [])
          (.task 1 [.call leftRecursivePredicate []] [])))
      findallLoopTemplate findallLoopOutput [] [] [])

private def findallLoopCollectedState : State :=
  .running (leftRecursiveSession 2)
    (.collectionBoundary { index := 0 } 0
      (.cutBoundary 1
        (.choice 1 .done
          (.task 1 [.call leftRecursivePredicate []] [])))
      findallLoopTemplate findallLoopOutput [] [] [findallLoopTemplate])

private def findallLoopRightState : State :=
  .running (leftRecursiveSession 2)
    (.collectionBoundary { index := 0 } 0
      (.cutBoundary 1
        (.task 1 [.call leftRecursivePredicate []] []))
      findallLoopTemplate findallLoopOutput [] [] [findallLoopTemplate])

private theorem findallLoop_enter_transition :
    Transition
      (.running findallLoopInitialSession
        (.task 0
          [.findall findallLoopTemplate findallLoopGenerator
            findallLoopOutput]
          []))
      [] findallLoopEnteredState := by
  simpa [findallLoopEnteredState, openFindall_loop_initial,
      RawTarget.toState] using
    (Transition.ordinary _ _ _ _ _
      (RawStep.taskFindall 0 findallLoopTemplate findallLoopGenerator
        findallLoopOutput [] [] findallLoopInitialSession))

private theorem findallLoop_branch_transition :
    Transition findallLoopEnteredState [] findallLoopBranchedState := by
  have raw : RawStep (leftRecursiveSession 2)
      (.collectionBoundary { index := 0 } 0
        (.cutBoundary 1
          (.task 1 [findallLoopGenerator] []))
        findallLoopTemplate findallLoopOutput [] [] [])
      [] .none (leftRecursiveSession 2)
      (.running
        (.collectionBoundary { index := 0 } 0
          (.cutBoundary 1
            (Search.disjoin 1
              [.truth, .call leftRecursivePredicate []] [] []))
          findallLoopTemplate findallLoopOutput [] [] [])) := by
    apply RawStep.collectionProgress
    · apply RawStep.cutBoundaryProgress
      exact RawStep.taskDisjunction 1
        [.truth, .call leftRecursivePredicate []] [] []
        (leftRecursiveSession 2)
    · simp [Trace.AnswerFree]
  simpa [findallLoopEnteredState, findallLoopBranchedState,
      RawTarget.toState] using
    (Transition.ordinary _ _ _ _ _ raw)

private theorem findallLoop_truth_transition :
    Transition findallLoopBranchedState [] findallLoopTruthState := by
  have raw : RawStep (leftRecursiveSession 2)
      (.collectionBoundary { index := 0 } 0
        (.cutBoundary 1
          (Search.disjoin 1
            [.truth, .call leftRecursivePredicate []] [] []))
        findallLoopTemplate findallLoopOutput [] [] [])
      [] .none (leftRecursiveSession 2)
      (.running
        (.collectionBoundary { index := 0 } 0
          (.cutBoundary 1
            (.choice 1
              (.task 1 [] [])
              (.task 1 [.call leftRecursivePredicate []] [])))
          findallLoopTemplate findallLoopOutput [] [] [])) := by
    apply RawStep.collectionProgress
    · apply RawStep.cutBoundaryProgress
      simpa [Search.disjoin] using
        (RawStep.choiceProgress 1
          (.task 1 [.truth] [])
          (.task 1 [.call leftRecursivePredicate []] [])
          (.task 1 [] []) []
          (leftRecursiveSession 2) (leftRecursiveSession 2)
          (RawStep.taskTruth 1 [] [] (leftRecursiveSession 2)))
    · simp [Trace.AnswerFree]
  simpa [findallLoopBranchedState, findallLoopTruthState,
      RawTarget.toState] using
    (Transition.ordinary _ _ _ _ _ raw)

private theorem findallLoop_collect_transition :
    Transition findallLoopTruthState [] findallLoopCollectedState := by
  have child : RawStep (leftRecursiveSession 2)
      (.cutBoundary 1
        (.choice 1
          (.task 1 [] [])
          (.task 1 [.call leftRecursivePredicate []] [])))
      [.answer []] .none (leftRecursiveSession 2)
      (.running
        (.cutBoundary 1
          (.choice 1 .done
            (.task 1 [.call leftRecursivePredicate []] [])))) := by
    exact RawStep.cutBoundaryProgress 1 _ _ [.answer []]
      (leftRecursiveSession 2) (leftRecursiveSession 2)
      (RawStep.choiceProgress 1 _ _ _ [.answer []]
        (leftRecursiveSession 2) (leftRecursiveSession 2)
        (RawStep.taskAnswer 1 [] (leftRecursiveSession 2)))
  have raw : RawStep (leftRecursiveSession 2)
      (.collectionBoundary { index := 0 } 0
        (.cutBoundary 1
          (.choice 1
            (.task 1 [] [])
            (.task 1 [.call leftRecursivePredicate []] [])))
        findallLoopTemplate findallLoopOutput [] [] [])
      [] .none (leftRecursiveSession 2)
      (.running
        (.collectionBoundary { index := 0 } 0
          (.cutBoundary 1
            (.choice 1 .done
              (.task 1 [.call leftRecursivePredicate []] [])))
          findallLoopTemplate findallLoopOutput [] []
          [findallLoopTemplate])) := by
    simpa only [findallLoop_copy_session, findallLoop_copy_term] using
      (RawStep.collectionAnswer { index := 0 } 0 _ _
        findallLoopTemplate findallLoopOutput [] [] [] []
        (leftRecursiveSession 2) (leftRecursiveSession 2) child)
  simpa [findallLoopTruthState, findallLoopCollectedState,
      RawTarget.toState] using
    (Transition.ordinary _ _ _ _ _ raw)

private theorem findallLoop_switch_transition :
    Transition findallLoopCollectedState [] findallLoopRightState := by
  have raw : RawStep (leftRecursiveSession 2)
      (.collectionBoundary { index := 0 } 0
        (.cutBoundary 1
          (.choice 1 .done
            (.task 1 [.call leftRecursivePredicate []] [])))
        findallLoopTemplate findallLoopOutput [] [] [findallLoopTemplate])
      [] .none (leftRecursiveSession 2)
      (.running
        (.collectionBoundary { index := 0 } 0
          (.cutBoundary 1
            (.task 1 [.call leftRecursivePredicate []] []))
          findallLoopTemplate findallLoopOutput [] []
          [findallLoopTemplate])) := by
    apply RawStep.collectionProgress
    · apply RawStep.cutBoundaryProgress
      exact RawStep.choiceComplete 1 .done
        (.task 1 [.call leftRecursivePredicate []] [])
        (leftRecursiveSession 2) (leftRecursiveSession 2)
        (RawStep.done (leftRecursiveSession 2))
    · simp [Trace.AnswerFree]
  simpa [findallLoopCollectedState, findallLoopRightState,
      RawTarget.toState] using
    (Transition.ordinary _ _ _ _ _ raw)

private theorem findallLoop_call_transition :
    Transition findallLoopRightState [.opened leftRecursiveRequest]
      (findallLoopOpenState 0) := by
  have child : RawStep (leftRecursiveSession 2)
      (.cutBoundary 1
        (.task 1 [.call leftRecursivePredicate []] []))
      [.opened leftRecursiveRequest] .none (leftRecursiveSession 3)
      (.running
        (.cutBoundary 1
          (.product 1 (leftRecursiveChain 0 2) []))) := by
    simpa [leftRecursiveRequest, leftRecursiveChain,
        openedFor_leftRecursive, Nat.add_assoc] using
      (RawStep.cutBoundaryProgress 1 _ _
        [.opened leftRecursiveRequest]
        (leftRecursiveSession 2) (leftRecursiveSession 3)
        (RawStep.taskCall 1 leftRecursivePredicate [] [] []
          (leftRecursiveSession 2) leftRecursive_notThrow rfl))
  have raw : RawStep (leftRecursiveSession 2)
      (.collectionBoundary { index := 0 } 0
        (.cutBoundary 1
          (.task 1 [.call leftRecursivePredicate []] []))
        findallLoopTemplate findallLoopOutput [] [] [findallLoopTemplate])
      [.opened leftRecursiveRequest] .none (leftRecursiveSession 3)
      (.running
        (.collectionBoundary { index := 0 } 0
          (.cutBoundary 1
            (.product 1 (leftRecursiveChain 0 2) []))
          findallLoopTemplate findallLoopOutput [] []
          [findallLoopTemplate])) := by
    exact RawStep.collectionProgress { index := 0 } 0 _ _
      findallLoopTemplate findallLoopOutput [] [] [findallLoopTemplate]
      [.opened leftRecursiveRequest] .none
      (leftRecursiveSession 2) (leftRecursiveSession 3) child
      (by simp [Trace.AnswerFree])
  simpa [findallLoopRightState, findallLoopOpenState,
      RawTarget.toState] using
    (Transition.ordinary _ _ _ _ _ raw)

private theorem findallLoop_initial_prefix :
    StepsN 6
      (.running findallLoopInitialSession
        (.task 0
          [.findall findallLoopTemplate findallLoopGenerator
            findallLoopOutput]
          []))
      [.opened leftRecursiveRequest] (findallLoopOpenState 0) := by
  have one {start finish : State} {events : List Observation}
      (step : Transition start events finish) :
      StepsN 1 start events finish := by
    simpa using
      (StepsN.succ 0 start finish finish events [] step (.zero finish))
  exact StepsN.trans (one findallLoop_enter_transition)
    (StepsN.trans (one findallLoop_branch_transition)
      (StepsN.trans (one findallLoop_truth_transition)
        (StepsN.trans (one findallLoop_collect_transition)
          (StepsN.trans (one findallLoop_switch_transition)
            (one findallLoop_call_transition)))))

/-- A source-shaped local `findall/3` succeeds once and then enters the
concrete clause `loop :- loop`.  For every requested finite depth, the one
successful template remains private while the public trace contains only
call-open observations and the machine remains running.  In particular no
partial bag, generator answer, exception, or completion is fabricated before
the generator is exhausted.

The exact positive transition count prevents reflexivity from witnessing the
claim.  Ordinary `findall/3` still collects eagerly until generator exhaustion;
the rejected abstraction is specifically a provider protocol that erases all
pre-exhaustion execution prefixes behind a completed-list response.

[SPEC SWI-Prolog manual, `findall/3`] -/
theorem findall_answer_then_loop_arbitrarily_long_open_prefix
    (cycles : Nat) :
    let events :=
      [.opened leftRecursiveRequest] ++ leftRecursiveEvents cycles
    events.length = cycles + 1 ∧
      (∀ event ∈ events, event = .opened leftRecursiveRequest) ∧
      (Trace.Observation.completed : Observation) ∉ events ∧
      StepsN (2 * cycles + 6)
        (.running findallLoopInitialSession
          (.task 0
            [.findall findallLoopTemplate findallLoopGenerator
              findallLoopOutput]
            []))
        events (findallLoopOpenState cycles) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [leftRecursiveEvents_length]
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
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (StepsN.trans findallLoop_initial_prefix (findallLoop_cycles cycles))

/-- A real local `throw/1` task performs one silent allocation step into an
internal raised packet.  The residual conjunction is discarded rather than
entered, and ordinary clause lookup is excluded by `BuiltinThrowCall`. -/
theorem throw_enters_fresh_raise (scope : CutScopeId) (ball : Term)
    (rest : List Goal) (bindings : Substitution) (session : Session) :
    RawStep session
      (.task scope (.call "throw" [ball] :: rest) bindings) [] .none
      (openThrow session ball bindings).session
      (.running (.raise (openThrow session ball bindings).exception)) := by
  exact .taskThrow scope ball rest bindings session ⟨rfl, rfl⟩

/-- The packet installed by `throw/1` is a certified injective alpha-copy of
the materialized exception term and already satisfies the catch transport
condition. -/
theorem throw_packet_copy_contract (session : Session) (ball : Term)
    (bindings : Substitution) :
    Term.IsFreshCopy
        (openThrow session ball bindings).prepared.materialized
        (openThrow session ball bindings).exception.ball
        (openThrow session ball bindings).prepared.firstFresh
        (openThrow session ball bindings).prepared.nextFresh ∧
      (openThrow session ball bindings).exception.BallStable := by
  exact ⟨openThrow_isFreshCopy session ball bindings,
    openThrow_ballStable session ball bindings⟩

/-- Publicly, local `throw/1` has an exact two-step prefix: a silent fresh-copy
step followed by the raised observation and raised terminal tag.  It cannot be
misread as failure or completion. -/
theorem local_throw_exact_two_steps (scope : CutScopeId) (ball : Term)
    (bindings : Substitution) (session : Session) :
    StepsN 2
      (.running session
        (.task scope [.call "throw" [ball]] bindings))
      [.raised (openThrow session ball bindings).exception.ball]
      (.terminal (openThrow session ball bindings).session
        (.raised (openThrow session ball bindings).exception.ball)) := by
  let opened := openThrow session ball bindings
  let start : State :=
    .running session (.task scope [.call "throw" [ball]] bindings)
  let middle : State := .running opened.session (.raise opened.exception)
  let finish : State := .terminal opened.session (.raised opened.exception.ball)
  have first : Transition start [] middle := by
    exact .ordinary _ _ _ _ _
      (.taskThrow scope ball [] bindings session ⟨rfl, rfl⟩)
  have second : Transition middle [.raised opened.exception.ball] finish := by
    exact .ordinary _ _ _ _ _ (.raise opened.exception opened.session)
  have tail : StepsN 1 middle [.raised opened.exception.ball] finish := by
    simpa using
      (StepsN.succ 0 middle finish finish
        [.raised opened.exception.ball] [] second (.zero finish))
  simpa [start, middle, finish, opened] using
    (StepsN.succ 1 start middle finish []
      [.raised opened.exception.ball] first tail)

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

/-! ## Local `catch/3` specialization witnesses -/

private def catchWitnessVariable : LogicVar := .source "$catcher"
private def catchWitnessException : Term := .atom "$boom"
private def catchWitnessBinding : Substitution :=
  [(catchWitnessVariable, catchWitnessException)]
private def catchWitnessRaised : RaisedException :=
  { ball := catchWitnessException, throwBindings := [] }
private def catchWitnessBoundRaised : RaisedException :=
  { ball := catchWitnessException
    throwBindings := [(catchWitnessVariable, .atom "$body")] }

private def unstableBallVariable : LogicVar := .source "$unstable_ball"
private def unstableBallValue : Term :=
  .compound "$f" [.atom "$a"]
private def unstableBallCatcher : Term :=
  .variable unstableBallVariable
private def unstableBall : Term :=
  .compound "$f" [.variable unstableBallVariable]
private def unstableRaised : RaisedException :=
  { ball := unstableBall
    throwBindings := [(unstableBallVariable, unstableBallValue)] }

private theorem catchWitness_resolves :
    CatchResolution [] (.variable catchWitnessVariable)
      catchWitnessException catchWitnessBinding := by
  refine ⟨catchWitnessBinding, ?_, by simp [catchWitnessBinding]⟩
  simpa [catchWitnessVariable, catchWitnessException, catchWitnessBinding,
      TreeSubstitution.reify, Tree.reify, Term.denote]
    using
      (computes_singleton_left_variable catchWitnessVariable
        catchWitnessException (by
          intro equality
          cases equality) (by rfl))

private theorem catchWitness_selects :
    CatchSelection catchWitnessRaised (.variable catchWitnessVariable) := by
  rcases catchWitness_resolves with ⟨extension, computed, resultEq⟩
  exact ⟨extension, by
    simpa [catchWitnessRaised] using computed⟩

private theorem openThrow_catchWitness_exception (session : Session) :
    (openThrow session catchWitnessException []).exception =
      catchWitnessRaised := by
  rfl

/-- Entering `catch/3` allocates independent cut and exception identities,
keeps the caller tail outside the opaque cut barrier, and starts the protected
goal with exactly the entry substitution.  No external provider participates
in this transition.

[SPEC translator.pl:300-308] -/
theorem catch_enters_distinct_delimiters (scope : CutScopeId)
    (protectedGoal : Goal) (catcher : Term) (handler : Goal)
    (rest : List Goal) (bindings : Substitution) (session : Session) :
    RawStep session
      (.task scope (.catch protectedGoal catcher handler :: rest) bindings)
      [] .none (openCatch session).session
      (.running
        (.product scope
          (.cutBoundary (openCatch session).cutScope
            (.catchBoundary (openCatch session).handlerScope
              (openCatch session).cutScope
              (.task (openCatch session).cutScope [protectedGoal] bindings)
              catcher handler bindings))
          rest)) := by
  exact .taskCatch scope protectedGoal catcher handler rest bindings session

/-- A matching catcher consumes only the raised marker and starts recovery
with the canonical catcher binding.  The exception is not reclassified as
failure or completion. -/
theorem variable_catcher_handles (scope : CutScopeId)
    (handlerScope : ExceptionScopeId) (handler : Goal) (session : Session) :
    RawStep session
      (.catchBoundary handlerScope scope (.raise catchWitnessRaised)
        (.variable catchWitnessVariable) handler [])
      [] .none session
      (.running (.task scope [handler] catchWitnessBinding)) := by
  exact .catchHandled handlerScope scope (.raise catchWitnessRaised)
    (.variable catchWitnessVariable) catchWitnessRaised handler []
    catchWitnessBinding [] session session
    (.raise catchWitnessRaised session) catchWitness_selects
    catchWitness_resolves

/-- The smallest real caught exception executes through the whole certified
control stack: enter distinct delimiters, materialize and copy `throw/1`,
perform SWI's two-phase catcher match, run the recovery goal, emit exactly one
answer, then report completion.  The raised marker is internal to the caught
path and therefore absent from the public trace.

[SPEC translator.pl:300-308]
[SPEC SWI-Prolog manual 4.10, `catch/3` and `throw/1`] -/
theorem ground_throw_caught_exact_trace (scope : CutScopeId)
    (session : Session) :
    StepsN 8
      (.running session
        (.task scope
          [.catch (.call "throw" [catchWitnessException])
            (.variable catchWitnessVariable) .truth]
          []))
      [.answer catchWitnessBinding, .completed]
      (.terminal
        (openThrow (openCatch session).session catchWitnessException []).session
        .completed) := by
  let caught := openCatch session
  let thrown := openThrow caught.session catchWitnessException []
  let protectedGoal : Goal := .call "throw" [catchWitnessException]
  let catcher : Term := .variable catchWitnessVariable
  let inner := caught.cutScope
  let handlerScope := caught.handlerScope
  let initial : State :=
    .running session
      (.task scope [.catch protectedGoal catcher .truth] [])
  let entered : State :=
    .running caught.session
      (.product scope
        (.cutBoundary inner
          (.catchBoundary handlerScope inner
            (.task inner [protectedGoal] []) catcher .truth []))
        [])
  let copied : State :=
    .running thrown.session
      (.product scope
        (.cutBoundary inner
          (.catchBoundary handlerScope inner
            (.raise thrown.exception) catcher .truth []))
        [])
  let recovering : State :=
    .running thrown.session
      (.product scope
        (.cutBoundary inner
          (.task inner [.truth] catchWitnessBinding))
        [])
  let recoveryDone : State :=
    .running thrown.session
      (.product scope
        (.cutBoundary inner
          (.task inner [] catchWitnessBinding))
        [])
  let callerChoice : State :=
    .running thrown.session
      (.choice scope
        (.task scope [] catchWitnessBinding)
        (.product scope (.cutBoundary inner .done) []))
  let answerEmitted : State :=
    .running thrown.session
      (.choice scope .done
        (.product scope (.cutBoundary inner .done) []))
  let alternatives : State :=
    .running thrown.session
      (.product scope (.cutBoundary inner .done) [])
  let finished : State := .terminal thrown.session .completed
  have enterStep : Transition initial [] entered := by
    dsimp [initial, entered, caught, protectedGoal, catcher, inner,
      handlerScope]
    exact .ordinary _ _ _ _ _
      (.taskCatch scope protectedGoal catcher .truth [] [] session)
  have copyStep : Transition entered [] copied := by
    have raw : RawStep caught.session
        (.product scope
          (.cutBoundary inner
            (.catchBoundary handlerScope inner
              (.task inner [protectedGoal] []) catcher .truth []))
          [])
        [] .none thrown.session
        (.running
          (.product scope
            (.cutBoundary inner
              (.catchBoundary handlerScope inner
                (.raise thrown.exception) catcher .truth []))
            [])) := by
      apply RawStep.productProgress
      · apply RawStep.cutBoundaryProgress
        apply RawStep.catchProgress
        exact .taskThrow inner catchWitnessException [] [] caught.session
          ⟨rfl, rfl⟩
      · simp [Trace.AnswerFree]
    exact .ordinary _ _ _ _ _ raw
  have selected : CatchSelection thrown.exception catcher := by
    simpa [thrown, catcher, openThrow_catchWitness_exception] using
      catchWitness_selects
  have resolved : CatchResolution [] catcher thrown.exception.ball
      catchWitnessBinding := by
    simpa [thrown, catcher, openThrow_catchWitness_exception,
      catchWitnessRaised] using
      catchWitness_resolves
  have handleStep : Transition copied [] recovering := by
    have raw : RawStep thrown.session
        (.product scope
          (.cutBoundary inner
            (.catchBoundary handlerScope inner
              (.raise thrown.exception) catcher .truth []))
          [])
        [] .none thrown.session
        (.running
          (.product scope
            (.cutBoundary inner
              (.task inner [.truth] catchWitnessBinding))
            [])) := by
      apply RawStep.productProgress
      · apply RawStep.cutBoundaryProgress
        exact .catchHandled handlerScope inner (.raise thrown.exception)
          catcher thrown.exception .truth [] catchWitnessBinding []
          thrown.session thrown.session (.raise thrown.exception thrown.session)
          selected resolved
      · simp [Trace.AnswerFree]
    exact .ordinary _ _ _ _ _ raw
  have recoveryStep : Transition recovering [] recoveryDone := by
    have raw : RawStep thrown.session
        (.product scope
          (.cutBoundary inner (.task inner [.truth] catchWitnessBinding)) [])
        [] .none thrown.session
        (.running
          (.product scope
            (.cutBoundary inner (.task inner [] catchWitnessBinding)) [])) := by
      apply RawStep.productProgress
      · apply RawStep.cutBoundaryProgress
        exact .taskTruth inner [] catchWitnessBinding thrown.session
      · simp [Trace.AnswerFree]
    exact .ordinary _ _ _ _ _ raw
  have composeStep : Transition recoveryDone [] callerChoice := by
    have raw : RawStep thrown.session
        (.product scope
          (.cutBoundary inner (.task inner [] catchWitnessBinding)) [])
        [] .none thrown.session
        (.running
          (.choice scope
            (.task scope [] catchWitnessBinding)
            (.product scope (.cutBoundary inner .done) []))) := by
      apply RawStep.productAnswer
      apply RawStep.cutBoundaryProgress
      exact .taskAnswer inner catchWitnessBinding thrown.session
    exact .ordinary _ _ _ _ _ raw
  have answerStep : Transition callerChoice
      [.answer catchWitnessBinding] answerEmitted := by
    have raw : RawStep thrown.session
        (.choice scope
          (.task scope [] catchWitnessBinding)
          (.product scope (.cutBoundary inner .done) []))
        [.answer catchWitnessBinding] .none thrown.session
        (.running
          (.choice scope .done
            (.product scope (.cutBoundary inner .done) []))) := by
      apply RawStep.choiceProgress
      exact .taskAnswer scope catchWitnessBinding thrown.session
    exact .ordinary _ _ _ _ _ raw
  have switchStep : Transition answerEmitted [] alternatives := by
    have raw : RawStep thrown.session
        (.choice scope .done
          (.product scope (.cutBoundary inner .done) []))
        [] .none thrown.session
        (.running (.product scope (.cutBoundary inner .done) [])) := by
      apply RawStep.choiceComplete
      exact .done thrown.session
    exact .ordinary _ _ _ _ _ raw
  have completeStep : Transition alternatives [.completed] finished := by
    have raw : RawStep thrown.session
        (.product scope (.cutBoundary inner .done) [])
        [.completed] .none thrown.session (.terminal .completed) := by
      apply RawStep.productComplete
      · apply RawStep.cutBoundaryComplete
        exact .done thrown.session
      · simp [Trace.AnswerFree]
    exact .ordinary _ _ _ _ _ raw
  have execution : StepsN 8 initial
      [.answer catchWitnessBinding, .completed] finished := by
    simpa using
      (StepsN.succ 7 initial entered finished []
        [.answer catchWitnessBinding, .completed] enterStep
        (StepsN.succ 6 entered copied finished []
          [.answer catchWitnessBinding, .completed] copyStep
          (StepsN.succ 5 copied recovering finished []
            [.answer catchWitnessBinding, .completed] handleStep
            (StepsN.succ 4 recovering recoveryDone finished []
              [.answer catchWitnessBinding, .completed] recoveryStep
              (StepsN.succ 3 recoveryDone callerChoice finished []
                [.answer catchWitnessBinding, .completed] composeStep
                (StepsN.succ 2 callerChoice answerEmitted finished
                  [.answer catchWitnessBinding] [.completed] answerStep
                  (StepsN.succ 1 answerEmitted alternatives finished []
                    [.completed] switchStep
                    (StepsN.succ 0 alternatives finished finished
                      [.completed] [] completeStep (.zero finished)))))))))
  simpa [initial, finished, caught, thrown, protectedGoal, catcher] using
    execution

/-- Distinct rigid exception terms do not match.  The exact raised marker and
terminal tag escape unchanged, establishing that the handler relation is not
an always-successful oracle. -/
theorem rigid_catcher_mismatch_escapes (scope : CutScopeId)
    (handlerScope : ExceptionScopeId) (handler : Goal) (session : Session) :
    let raised : RaisedException :=
      { ball := .atom "$actual", throwBindings := [] }
    RawStep session
      (.catchBoundary handlerScope scope (.raise raised)
        (.atom "$expected") handler [])
      [.raised (.atom "$actual")] .none session
      (.terminal (.raised raised)) := by
  dsimp only
  let raised : RaisedException :=
    { ball := .atom "$actual", throwBindings := [] }
  apply RawStep.catchUnmatched handlerScope scope (.raise raised)
    (.atom "$expected") raised handler [] [] session session
    (.raise raised session)
  rintro ⟨extension, computed⟩
  have mostGeneral := computed.isMostGeneral
  have unifies : DenotationalUnifier extension
      (.atom "$expected") (.atom "$actual") :=
    by
      have raw := mostGeneral.1
        (raised.throwBindings.applyTerm (.atom "$expected"), raised.ball)
        (by simp)
      simpa [raised] using raw
  exact distinct_atoms_have_no_denotational_unifier "$expected" "$actual"
    (by decide) ⟨extension, unifies⟩

/-- SWI selects a catcher before unwinding the protected goal.  Therefore a
catcher variable bound to a distinct atom at the throw point rejects the ball,
even though the same variable would match after restoring the empty entry
substitution.  This is the anti-vacuity witness that distinguishes SWI's
documented delayed-backtracking behavior from entry-only ISO matching. -/
theorem throw_time_catcher_binding_can_reject (scope : CutScopeId)
    (handlerScope : ExceptionScopeId) (handler : Goal) (session : Session) :
    CatchResolution [] (.variable catchWitnessVariable)
        catchWitnessException catchWitnessBinding ∧
      RawStep session
        (.catchBoundary handlerScope scope (.raise catchWitnessBoundRaised)
          (.variable catchWitnessVariable) handler [])
        [.raised catchWitnessException] .none session
        (.terminal (.raised catchWitnessBoundRaised)) := by
  refine ⟨catchWitness_resolves, ?_⟩
  apply RawStep.catchUnmatched handlerScope scope
    (.raise catchWitnessBoundRaised) (.variable catchWitnessVariable)
    catchWitnessBoundRaised handler [] [] session session
    (.raise catchWitnessBoundRaised session)
  rintro ⟨extension, computed⟩
  have mostGeneral := computed.isMostGeneral
  have unifies : DenotationalUnifier extension
      (.atom "$body") catchWitnessException := by
    have raw := mostGeneral.1
      (catchWitnessBoundRaised.throwBindings.applyTerm
        (.variable catchWitnessVariable), catchWitnessBoundRaised.ball)
      (by simp)
    simpa [catchWitnessBoundRaised, catchWitnessVariable,
      catchWitnessException, TreeSubstitution.reify, Tree.reify,
      Term.denote, Term.instantiateOne] using raw
  exact distinct_atoms_have_no_denotational_unifier "$body" "$boom"
    (by decide) ⟨extension, unifies⟩

/-- Binding extension alone is insufficient for two-phase catch progress.
If a supposed copied ball aliases a variable in the throw substitution,
pre-unwind selection can succeed even though the entry equation is the cyclic
finite-tree equation `X = f(X)` and has no recovery MGU.  This anti-vacuity
witness makes copied-ball stability a necessary, separately audited premise
rather than hiding it inside the lineage name. -/
theorem copied_ball_stability_is_necessary :
    unstableRaised.ExtendsEntry [] ∧
      CatchSelection unstableRaised unstableBallCatcher ∧
      ¬ unstableRaised.BallStable ∧
      ¬ ∃ result,
        CatchResolution [] unstableBallCatcher unstableRaised.ball result := by
  have lineageWitness : unstableRaised.ExtendsEntry [] := by
    exact ⟨unstableRaised.throwBindings, by simp⟩
  have selected : CatchSelection unstableRaised unstableBallCatcher := by
    let candidate : Substitution :=
      [(unstableBallVariable, .atom "$a")]
    have unifies : DenotationalUnifiesEquations candidate
        [(unstableRaised.throwBindings.applyTerm unstableBallCatcher,
          unstableRaised.ball)] := by
      intro equation member
      simp only [List.mem_singleton] at member
      subst equation
      unfold DenotationalUnifier
      rfl
    rcases ComputesDenotationalMgu.exists_of_unifier candidate unifies with
      ⟨binding, computed⟩
    exact ⟨binding, computed⟩
  have unstable : ¬ unstableRaised.BallStable := by
    intro stable
    simp [RaisedException.BallStable, unstableRaised, unstableBall,
      unstableBallVariable, unstableBallValue, Term.instantiateOne,
      Terms.instantiateOne] at stable
  have noRecovery : ¬ ∃ result,
      CatchResolution [] unstableBallCatcher unstableRaised.ball result := by
    rintro ⟨result, extension, computed, resultEq⟩
    have unifies : DenotationalUnifier extension unstableBallCatcher
        unstableRaised.ball := by
      have normalized := computed.isMostGeneral.1
        (Substitution.applyTerm [] unstableBallCatcher,
          Substitution.applyTerm [] unstableRaised.ball) (by simp)
      simpa only [Substitution.applyTerm_nil] using normalized
    have impossible := Tree.no_finite_unifier_of_occurs_true
      (Canonical.Substitution.denote extension) unstableBallVariable
      (Term.denote unstableBall)
      (by rfl)
      (by intro equality; cases equality)
    apply impossible
    unfold DenotationalUnifier at unifies
    simpa [unstableBallCatcher, unstableRaised, unstableBall,
      Term.denote] using unifies
  exact ⟨lineageWitness, selected, unstable, noRecovery⟩

/-- The exception boundary is cut-transparent, while its enclosing cut
barrier catches the protected goal's commit.  Therefore a cut inside catch
cannot discard an alternative owned by the caller's outer scope. -/
theorem catch_cut_preserves_outer_choice (outer inner : CutScopeId)
    (handlerScope : ExceptionScopeId) (bindings : Substitution)
    (catcher : Term) (handler : Goal) (outside : Search)
    (session : Session) :
    RawStep session
      (.choice outer
        (.cutBoundary inner
          (.catchBoundary handlerScope inner
            (.task inner [.cut] bindings) catcher handler bindings))
        outside)
      [] .none session
      (.running
        (.choice outer
          (.cutBoundary inner
            (.catchBoundary handlerScope inner
              (.task inner [] bindings) catcher handler bindings))
          outside)) := by
  apply RawStep.choiceProgress
  apply RawStep.cutBoundaryCatch
  exact .catchProgress handlerScope inner _ _ catcher handler bindings []
    (.commit inner) session session (.taskCut inner [] bindings session)

/-- Any step that leaves a catch boundary directly in recovery must have
passed both phases of SWI matching: selection under the throw-time bindings,
then canonical reconstruction from the bindings saved on catch entry.  This
inversion prevents either an entry-only false selection or a body-local
binding leak into recovery. -/
theorem catch_recovery_uses_two_phase_matching
    {handlerScope : ExceptionScopeId} {scope : CutScopeId} {body : Search}
    {catcher : Term} {exception : RaisedException} {handler : Goal}
    {entryBindings result : Substitution} {cleanup : List Observation}
    {before after : Session}
    (step : RawStep before
      (.catchBoundary handlerScope scope body catcher handler entryBindings)
      cleanup .none after (.running (.task scope [handler] result)))
    (bodyRaised : RawStep before body (.raised exception.ball :: cleanup) .none
      after (.terminal (.raised exception))) :
    CatchSelection exception catcher ∧
      CatchResolution entryBindings catcher exception.ball result := by
  cases step with
  | catchHandled _ _ _ _ caught _ _ _ _ _ _ child selected resolved =>
      have comparison := RawStep.deterministic child bodyRaised
      rcases comparison with ⟨eventsEq, signalEq, afterEq, targetEq⟩
      cases targetEq
      cases eventsEq
      exact ⟨selected, resolved⟩


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

/-! ## Dynamic-update persistence anti-vacuity -/

private def databaseActionWitnessPayload : Term :=
  .compound "p" [.atom "late"]

private def databaseActionWitnessResult : Term :=
  .variable (.generated 10)

private def databaseActionWitnessResultBindings : Substitution :=
  TreeSubstitution.reify
    [(.generated 10, Term.denote (.atom "true"))]

private def databaseActionWitnessFailure : Goal :=
  .unify (.atom "false") (.atom "true")

private def databaseActionWitnessSession : Session :=
  { resolver := Resolver.witnessSession, nextCutScope := 2 }

private def databaseActionWitnessAfterSession : Session :=
  databaseActionWitnessSession.withDatabase Resolver.witnessAfterAssert

private def databaseActionWitnessEffect : LocalDatabaseEffect :=
  .assertz
    (Resolver.witnessBefore.allocate (Resolver.witnessClause "late"))

private def databaseActionWitnessStart : State :=
  .running databaseActionWitnessSession
    (.choice 0
      (.task 1
        [.call "assertzPredicate"
          [databaseActionWitnessPayload, databaseActionWitnessResult],
          databaseActionWitnessFailure]
        [])
      (.clauses 1 Resolver.witnessPreparedCursor))

private def databaseActionWitnessMiddle : State :=
  .running databaseActionWitnessAfterSession
    (.choice 0
      (.task 1
        [.unify databaseActionWitnessResult (.atom "true"),
          databaseActionWitnessFailure]
        [])
      (.clauses 1 Resolver.witnessPreparedCursor))

private def databaseActionWitnessAfterResult : State :=
  .running databaseActionWitnessAfterSession
    (.choice 0
      (.task 1 [databaseActionWitnessFailure]
        databaseActionWitnessResultBindings)
      (.clauses 1 Resolver.witnessPreparedCursor))

private def databaseActionWitnessFinish : State :=
  .running databaseActionWitnessAfterSession
    (.clauses 1 Resolver.witnessPreparedCursor)

private theorem databaseActionWitnessResult_resolves :
    UnifyResolution [] databaseActionWitnessResult (.atom "true")
      databaseActionWitnessResultBindings := by
  refine ⟨databaseActionWitnessResultBindings, ?_, by simp⟩
  simpa [databaseActionWitnessResult, databaseActionWitnessResultBindings,
    Substitution.applyTerm] using
    (computes_singleton_left_variable (.generated 10) (.atom "true")
      (by simp [Term.denote])
      (by simp [Term.denote, Tree.occurs, Trees.occurs]))

private theorem databaseActionWitnessFailure_clash :
    ¬ ∃ result,
      UnifyResolution databaseActionWitnessResultBindings
        (.atom "false") (.atom "true") result := by
  rintro ⟨result, extension, computed, resultEquality⟩
  have unifies :
      DenotationalUnifier extension
        (.atom "false") (.atom "true") := by
    have raw := computed.isMostGeneral.1
      ((databaseActionWitnessResultBindings.applyTerm (.atom "false")),
        databaseActionWitnessResultBindings.applyTerm (.atom "true"))
      (by simp)
    simpa [databaseActionWitnessResultBindings, TreeSubstitution.reify,
      Tree.reify, Substitution.applyTerm, Term.instantiateOne] using raw
  exact distinct_atoms_have_no_denotational_unifier "false" "true"
    (by decide) ⟨extension, unifies⟩

/-- A dynamic assertion is observed and remains in the persistent session
after its compiler-shaped generated result succeeds and a later rigid goal
fails.  DFS then backtracks into a previously retained right branch.  The
failure's completion marker is correctly consumed by the choice rather than
being exposed as whole-query completion. -/
theorem assertz_effect_survives_failed_branch :
    StepsN 3 databaseActionWitnessStart
      [.effect databaseActionWitnessEffect]
      databaseActionWitnessFinish := by
  have actionStep :
      Transition databaseActionWitnessStart
        [.effect databaseActionWitnessEffect]
        databaseActionWitnessMiddle := by
    exact .ordinary _ _ _ _ _
      (.choiceProgress 0 _ _ _
        [.effect databaseActionWitnessEffect]
        databaseActionWitnessSession databaseActionWitnessAfterSession
        (.taskAssertz 1 databaseActionWitnessPayload
          databaseActionWitnessResult [databaseActionWitnessFailure] []
          databaseActionWitnessSession
          (Resolver.witnessClause "late")
          (predicate := "assertzPredicate")
          (arguments :=
            [databaseActionWitnessPayload, databaseActionWitnessResult])
          rfl rfl))
  have resultStep :
      Transition databaseActionWitnessMiddle []
        databaseActionWitnessAfterResult := by
    exact .ordinary _ _ _ _ _
      (.choiceProgress 0 _ _ _ []
        databaseActionWitnessAfterSession databaseActionWitnessAfterSession
        (.taskUnifySuccess 1 databaseActionWitnessResult (.atom "true")
          [databaseActionWitnessFailure] []
          databaseActionWitnessResultBindings
          databaseActionWitnessAfterSession
          databaseActionWitnessResult_resolves))
  have backtrackStep :
      Transition databaseActionWitnessAfterResult []
        databaseActionWitnessFinish := by
    exact .ordinary _ _ _ _ _
      (.choiceComplete 0 _ _
        databaseActionWitnessAfterSession databaseActionWitnessAfterSession
        (.taskUnifyFailure 1 (.atom "false") (.atom "true")
          [] databaseActionWitnessResultBindings
          databaseActionWitnessAfterSession
          databaseActionWitnessFailure_clash))
  simpa [databaseActionWitnessStart, databaseActionWitnessMiddle,
    databaseActionWitnessAfterResult, databaseActionWitnessFinish] using
    (StepsN.succ 2 databaseActionWitnessStart databaseActionWitnessMiddle
      databaseActionWitnessFinish
      [.effect databaseActionWitnessEffect] [] actionStep
      (StepsN.succ 1 databaseActionWitnessMiddle
        databaseActionWitnessAfterResult databaseActionWitnessFinish
        [] [] resultStep
        (StepsN.succ 0 databaseActionWitnessAfterResult
          databaseActionWitnessFinish databaseActionWitnessFinish
          [] [] backtrackStep (.zero databaseActionWitnessFinish))))

/-- The preceding real execution distinguishes persistent LUV state from
backtrackable control: the parked cursor retains its old ordered snapshot,
while a call prepared from the post-backtrack session sees the assertion. -/
theorem assertz_backtrack_preserves_snapshot_and_updates_future_calls :
    databaseActionWitnessFinish.database =
        Resolver.witnessAfterAssert ∧
      Resolver.witnessPreparedCursor.remaining.map
          (fun branch => branch.sourceId) = [0, 1] ∧
      (prepareCall databaseActionWitnessAfterSession.resolver
          Resolver.witnessRequest).1.remaining.map
          (fun branch => branch.sourceId) = [0, 1, 2] := by
  exact ⟨rfl, Resolver.witness_prepared_snapshot_ids,
    Resolver.witness_prepared_new_call_sees_assertion⟩

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
