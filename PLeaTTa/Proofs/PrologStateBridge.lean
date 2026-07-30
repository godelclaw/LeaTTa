-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologStateBridge
Purpose: Faithful state-side bridge between the independent local-Prolog
  semantics and the fine-grained executable lane.
Trusted boundary: none
Main exports: LocalClauseAgrees, DatabaseRelatesWorld,
  SessionRelatesPersistent, SessionHighWatersExtend, RuntimeAlpha,
  LocalClauseHeadAlphaAgrees, FreshenedClauseAlphaAgrees
-/
import PLeaTTa.Proofs.CompilerAdequacy
import PLeaTTa.Proofs.CompilerSubstitutionAdequacy
import PLeaTTa.Proofs.DemandDrivenStep
import PLeaTTa.Proofs.OpenBindingAgreement
import PLeaTTa.Proofs.ResolutionCounter
import PLeaTTa.PeTTaSpec.PrologGoalSemantics

namespace PLeaTTa.PrologStateBridge

open Metta (Atom)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open PeTTaSpec.PrologCore.GoalSemantics
open CompilerAdequacy
open CompilerSubstitutionAdequacy
open DemandDrivenStep
open OpenBindingAgreement

/-!
The independent resolver and executable machine deliberately use different
representations:

* `Database` retains versioned clause occurrences, while `PWorld` stores only
  the current live executable clauses.
* independent standardization allocates one generated identity per distinct
  clause variable, while the executable appends one fresh `#r<seed>` suffix
  per accepted clause.  Their numeric high-waters are therefore different
  currencies and must not be equated.
* cut, exception, and collection identities are typed nominal control
  resources in `Search`; they have no field in executable `Conf`.

This file first relates the exact current clause projection.  The fresh-name
frontier remains an explicit relation parameter: the later search-state
correspondence must instantiate it with an alpha environment and live-variable
support, rather than smuggling in a false numeric equality.
-/

/-- Exact finite support correspondence, intentionally ignoring occurrence
counts that can differ across semantically equivalent compiler
representations (for example, an `amb` stores its shared output once).
Every executable clause variable must come from an independent variable and
every independent support identity is represented. -/
def ClauseVariableSupportAgrees (reference : LocalClause)
    (executable : PLeaTTa.Clause) : Prop :=
  ∀ name, name ∈ resolutionClauseVars executable ↔
    ∃ identity, identity ∈ reference.variables ∧
      name = logicVarExecutableName identity

/-- One independent definite clause and one executable world entry denote the
same output-last predicate clause.  Source order and duplicate occurrences are
handled by `List.Forall₂` at the database level, not by this per-clause
relation. -/
structure LocalClauseAgrees (reference : LocalClause)
    (executable : String × PLeaTTa.Clause) : Prop where
  predicate : reference.predicate = executable.1
  outputLast :
    ∃ referenceParameters referenceResult,
      reference.arguments = referenceParameters ++ [referenceResult] ∧
        TermsAgree referenceParameters executable.2.params ∧
        TermAgrees referenceResult executable.2.result
  body : GoalsAgree reference.body executable.2.body
  support : ClauseVariableSupportAgrees reference executable.2

/-- A versioned occurrence relates through its clause content.  Creation,
erasure, and occurrence identity remain on the independent side because
`PWorld` intentionally stores only the live projection. -/
def VersionedClauseAgrees (reference : VersionedClause)
    (executable : String × PLeaTTa.Clause) : Prop :=
  LocalClauseAgrees reference.clause executable

/-- All occurrences visible at the database's current generation, in exact
asserta/assertz order and with duplicate multiplicity preserved. -/
def currentVisibleEntries (database : Database) : List VersionedClause :=
  database.history.filter fun entry =>
    entry.visibleAt database.generation

/-- Eager reservation preserves the exact occurrence identity sequence of
the immutable call-start snapshot.  Freshening changes clause variables, not
source occurrence order or multiplicity. -/
private theorem reserveVisible_sourceIds
    (callGeneration : Generation) (arguments : List Term)
    (bindings : Substitution) (freshSeed : Nat)
    (entries : List VersionedClause) :
    (reserveVisible callGeneration arguments bindings freshSeed entries).1.map
        (fun branch => branch.sourceId) =
      entries.map (fun entry => entry.id) := by
  induction entries generalizing freshSeed with
  | nil =>
      rfl
  | cons entry rest inductionHypothesis =>
      simp [reserveVisible, inductionHypothesis]

/-- Exact call-start snapshot relation for the actual prepared protocol
token.  It records the generation and ordered, duplicate-sensitive occurrence
identities; the token contains no live database pointer that could drift after
assertion or retraction. -/
structure PreparedCursorSnapshots (database : Database)
    (request : CallRequest) (cursor : PreparedCursor) : Prop where
  generation : cursor.callGeneration = database.generation
  sourceOrder :
    cursor.remaining.map (fun branch => branch.sourceId) =
      (database.visibleClausesAt database.generation request.predicate
        request.arguments.length).map (fun entry => entry.id)

/-- `prepareCall` establishes the exact immutable snapshot relation. -/
theorem prepareCall_snapshots (session : LocalSession)
    (request : CallRequest) :
    PreparedCursorSnapshots session.database request
      (prepareCall session request).1 := by
  constructor
  · rfl
  · simpa [prepareCall] using
      reserveVisible_sourceIds session.database.generation request.arguments
        request.bindings
        (max session.nextFresh request.generatedCeiling)
        (session.database.visibleClausesAt session.database.generation
          request.predicate request.arguments.length)

/-- Reachability invariant factored over a bare history for the retraction
induction below. -/
private def HistoryGenerationClosed (generation : Generation)
    (history : List VersionedClause) : Prop :=
  ∀ entry ∈ history,
    entry.created ≤ generation ∧
      ∀ erased, entry.erased = some erased → erased ≤ generation

/-- Advancing one generation cannot change the visibility of an unchanged
entry in a closed history.  A live entry remains live; an already erased
entry remains erased. -/
private theorem VersionedClause.visibleAt_succ_of_closed
    {generation : Generation} {entry : VersionedClause}
    (closed :
      entry.created ≤ generation ∧
        ∀ erased, entry.erased = some erased → erased ≤ generation) :
    entry.visibleAt (generation + 1) =
      entry.visibleAt generation := by
  rcases closed with ⟨created, erasedClosed⟩
  cases erased : entry.erased with
  | none =>
      simp [VersionedClause.visibleAt, erased, created,
        Nat.le_trans created (Nat.le_add_right generation 1)]
  | some erasedGeneration =>
      have erasedLe := erasedClosed erasedGeneration erased
      have notOld : ¬ generation < erasedGeneration :=
        Nat.not_lt.mpr erasedLe
      have notNew : ¬ generation + 1 < erasedGeneration :=
        Nat.not_lt.mpr
          (Nat.le_trans erasedLe (Nat.le_add_right generation 1))
      simp [VersionedClause.visibleAt, erased, created,
        Nat.le_trans created (Nat.le_add_right generation 1),
        notOld, notNew]

/-- The live projection of an unchanged closed history is stable across one
generation tick. -/
private theorem filter_visibleAt_succ_of_closed
    (generation : Generation) (history : List VersionedClause)
    (closed : HistoryGenerationClosed generation history) :
    history.filter (fun entry => entry.visibleAt (generation + 1)) =
      history.filter (fun entry => entry.visibleAt generation) := by
  induction history with
  | nil =>
      rfl
  | cons entry rest inductionHypothesis =>
      have headClosed := closed entry (by simp)
      have tailClosed : HistoryGenerationClosed generation rest := by
        intro candidate member
        exact closed candidate (by simp [member])
      simp only [List.filter_cons,
        VersionedClause.visibleAt_succ_of_closed headClosed,
        inductionHypothesis tailClosed]

/-- Successful identity retraction deletes exactly one live occurrence from
the current projection, preserves the source order of every other occurrence,
and closes the updated history at the new generation. -/
private theorem retireFirst_live_projection
    {generation : Generation} {id : ClauseId}
    {before after : List VersionedClause}
    (closed : HistoryGenerationClosed generation before)
    (retired : retireFirst (generation + 1) id before = some after) :
    ∃ left target right,
      before.filter (fun entry => entry.visibleAt generation) =
          left ++ target :: right ∧
        after.filter (fun entry => entry.visibleAt (generation + 1)) =
          left ++ right ∧
        target.id = id ∧
        target.erased = none ∧
        HistoryGenerationClosed (generation + 1) after := by
  induction before generalizing after with
  | nil =>
      simp [retireFirst] at retired
  | cons entry rest inductionHypothesis =>
      have entryClosed := closed entry (by simp)
      have restClosed : HistoryGenerationClosed generation rest := by
        intro candidate member
        exact closed candidate (by simp [member])
      by_cases hit : entry.id = id ∧ entry.erased = none
      · simp only [retireFirst, hit, and_self, if_true,
          Option.some.injEq] at retired
        subst after
        have entryVisible : entry.visibleAt generation = true := by
          rcases entryClosed with ⟨created, _⟩
          simp [VersionedClause.visibleAt, hit.2, created]
        have retiredInvisibleId :
            ({ id := id, clause := entry.clause, created := entry.created,
                erased := some (generation + 1) } :
              VersionedClause).visibleAt (generation + 1) = false := by
          simp [VersionedClause.visibleAt]
        have restStable :=
          filter_visibleAt_succ_of_closed generation rest restClosed
        refine
          ⟨[], entry,
            rest.filter (fun candidate =>
              candidate.visibleAt generation), ?_, ?_,
            hit.1, hit.2, ?_⟩
        · simp [entryVisible]
        · simp only [List.filter_cons, retiredInvisibleId,
            Bool.false_eq_true, if_false, List.nil_append]
          exact restStable
        · intro candidate member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · constructor
            · exact Nat.le_trans entryClosed.1
                (Nat.le_add_right generation 1)
            · intro erasedGeneration erasedEq
              simp only at erasedEq
              have exactGeneration :
                  erasedGeneration = generation + 1 := by
                exact (Option.some.inj erasedEq).symm
              subst erasedGeneration
              exact Nat.le_refl _
          · have tail := restClosed candidate member
            exact
              ⟨Nat.le_trans tail.1 (Nat.le_add_right generation 1),
                fun erasedGeneration erasedEq =>
                  Nat.le_trans (tail.2 erasedGeneration erasedEq)
                    (Nat.le_add_right generation 1)⟩
      · cases tailResult :
          retireFirst (generation + 1) id rest with
        | none =>
            simp [retireFirst, hit, tailResult] at retired
        | some retiredRest =>
            have afterShape : after = entry :: retiredRest := by
              have reversed : entry :: retiredRest = after := by
                simpa [retireFirst, hit, tailResult] using retired
              exact reversed.symm
            subst after
            obtain
              ⟨left, target, right, beforeProjection, afterProjection,
                targetId, targetLive, retiredClosed⟩ :=
              inductionHypothesis restClosed tailResult
            have visibilityStable :=
              VersionedClause.visibleAt_succ_of_closed entryClosed
            by_cases visible : entry.visibleAt generation = true
            · have visibleNext :
                  entry.visibleAt (generation + 1) = true := by
                simpa [visibilityStable] using visible
              refine
                ⟨entry :: left, target, right, ?_, ?_, targetId, targetLive,
                  ?_⟩
              · simp [visible, beforeProjection]
              · simp [visibleNext, afterProjection]
              · intro candidate member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · exact
                    ⟨Nat.le_trans entryClosed.1
                        (Nat.le_add_right generation 1),
                      fun erasedGeneration erasedEq =>
                        Nat.le_trans
                          (entryClosed.2 erasedGeneration erasedEq)
                          (Nat.le_add_right generation 1)⟩
                · exact retiredClosed candidate member
            · have invisible : entry.visibleAt generation = false :=
                Bool.eq_false_of_not_eq_true visible
              have invisibleNext :
                  entry.visibleAt (generation + 1) = false := by
                rw [visibilityStable]
                exact invisible
              refine
                ⟨left, target, right, ?_, ?_, targetId, targetLive, ?_⟩
              · simp [invisible, beforeProjection]
              · simp [invisibleNext, afterProjection]
              · intro candidate member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · exact
                    ⟨Nat.le_trans entryClosed.1
                        (Nat.le_add_right generation 1),
                      fun erasedGeneration erasedEq =>
                        Nat.le_trans
                          (entryClosed.2 erasedGeneration erasedEq)
                          (Nat.le_add_right generation 1)⟩
                · exact retiredClosed candidate member

/-- Every creation/erasure stamp in a reachable history has already occurred
at the database's current generation.  This excludes forged future erasure
stamps and makes the current logical-update view exactly the unerased
occurrences. -/
abbrev DatabaseGenerationClosed :=
  PeTTaSpec.PrologCore.DatabaseActions.DatabaseGenerationClosed

/-- Stable occurrence identities are unique and lie below the allocator
frontier. -/
abbrev DatabaseIdsClosed :=
  PeTTaSpec.PrologCore.DatabaseActions.DatabaseIdsClosed

/-- Complete source-database reachability: timestamp closure together with
stable, allocator-bounded occurrence identities. -/
abbrev DatabaseReachable :=
  PeTTaSpec.PrologCore.DatabaseActions.DatabaseReachable

/-- The executable world's canonical live clause list is exactly the current
projection of the independent logical-update history.  Derived executable
index coherence is included because call dispatch may use the index rather
than the canonical list. -/
structure DatabaseRelatesWorld (database : Database) (world : PWorld) : Prop where
  reachable : DatabaseReachable database
  liveClauses :
    List.Forall₂ VersionedClauseAgrees
      (currentVisibleEntries database) world.progClauses
  clauseIndex : world.ClauseIndexCoherent

/-- Timestamp closure remains available as an explicit projection of the
stronger reachability contract. -/
theorem DatabaseRelatesWorld.generationClosed
    {database : Database} {world : PWorld}
    (agreement : DatabaseRelatesWorld database world) :
    DatabaseGenerationClosed database :=
  agreement.reachable.generationClosed

/-- Stable-ID closure is the second load-bearing projection. -/
theorem DatabaseRelatesWorld.idsClosed
    {database : Database} {world : PWorld}
    (agreement : DatabaseRelatesWorld database world) :
    DatabaseIdsClosed database :=
  agreement.reachable.idsClosed

/-- A relation between the two fresh-allocation frontiers.  It is deliberately
abstract at the persistent-only layer: its sound instantiation depends on the
live independent/executable variable supports and their alpha environment. -/
abbrev FreshFrontierRelation := Nat → Nat → Prop

/-- Persistent-state agreement, parameterized by the honest fresh-frontier
relation supplied by the full search-state bridge.

The three typed control allocators do not appear here.  They are ghost
identities erased by the executable projection; the preservation theorems
below prove that allocating them cannot alter this relation. -/
structure SessionRelatesPersistent
    (freshFrontier : FreshFrontierRelation)
    (session : Session) (persistent : Persistent) : Prop where
  database :
    DatabaseRelatesWorld session.resolver.database persistent.world
  fresh :
    freshFrontier session.resolver.nextFresh persistent.counter

/-- Source-side chronology between a historical activation session and the
current non-backtrackable session.

`SessionRelatesPersistent` projects the current database and fresh frontier
into executable `Persistent`.  It deliberately erases the three typed control
allocators.  This separate certificate retains all four source high-waters
without pretending that the executable counter represents cut, exception, or
collection identities.  It does not claim database reachability: that is
carried by the current `SessionRelatesPersistent` database relation and,
once dynamic body effects are connected, a separate logical-update
generation theorem. -/
structure SessionHighWatersExtend (before after : Session) : Prop where
  fresh :
    before.resolver.nextFresh ≤ after.resolver.nextFresh
  cut :
    before.nextCutScope ≤ after.nextCutScope
  exception :
    before.nextExceptionScope ≤ after.nextExceptionScope
  collection :
    before.nextCollectionScope ≤ after.nextCollectionScope

namespace SessionHighWatersExtend

/-- A session is its own exact chronology origin. -/
theorem refl (session : Session) :
    SessionHighWatersExtend session session :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

/-- Chronology composes across successive non-backtrackable transitions. -/
theorem trans {first middle last : Session}
    (left : SessionHighWatersExtend first middle)
    (right : SessionHighWatersExtend middle last) :
    SessionHighWatersExtend first last :=
  ⟨Nat.le_trans left.fresh right.fresh,
    Nat.le_trans left.cut right.cut,
    Nat.le_trans left.exception right.exception,
    Nat.le_trans left.collection right.collection⟩

/-- Every real independent local-search step advances all four source
high-waters monotonically. -/
theorem of_rawStep {before after : Session} {search : Search}
    {events : List Observation} {signal : Trace.CutSignal}
    {target : RawTarget}
    (step : RawStep before search events signal after target) :
    SessionHighWatersExtend before after :=
  ⟨step.nextFresh_mono, step.nextCutScope_mono,
    step.nextExceptionScope_mono, step.nextCollectionScope_mono⟩

/-- The chronology field is load-bearing: a current session whose fresh
allocator is below its opener cannot satisfy it. -/
theorem rejects_fresh_regression {before after : Session}
    (regressed :
      after.resolver.nextFresh < before.resolver.nextFresh) :
    ¬ SessionHighWatersExtend before after := by
  intro chronology
  exact (Nat.not_lt_of_ge chronology.fresh) regressed

/-- Advancing only the fresh allocator gives a concrete non-identity
chronology witness.  This rules out reading the relation as mere session
equality. -/
theorem strict_fresh_witness (session : Session) :
    SessionHighWatersExtend session
        { session with
          resolver :=
            { session.resolver with
              nextFresh := session.resolver.nextFresh + 1 } } ∧
      session.resolver.nextFresh <
        ({ session with
          resolver :=
            { session.resolver with
              nextFresh := session.resolver.nextFresh + 1 } } :
          Session).resolver.nextFresh := by
  constructor
  · exact
      ⟨Nat.le_succ _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  · exact Nat.lt_succ_self _

end SessionHighWatersExtend

theorem LocalClauseAgrees.arity
    {reference : LocalClause} {executable : String × PLeaTTa.Clause}
    (agreement : LocalClauseAgrees reference executable) :
    reference.arguments.length = executable.2.params.length + 1 := by
  rcases agreement.outputLast with
    ⟨referenceParameters, referenceResult, arguments, parameters, result⟩
  rw [arguments, List.length_append, List.length_singleton,
    parameters.length_eq]

theorem DatabaseRelatesWorld.length_eq
    {database : Database} {world : PWorld}
    (agreement : DatabaseRelatesWorld database world) :
    (currentVisibleEntries database).length = world.progClauses.length :=
  agreement.liveClauses.length_eq

private theorem forall₂_append_singleton
    {α β : Type} {relation : α → β → Prop}
    {left : List α} {right : List β}
    (agreement : List.Forall₂ relation left right)
    {lastLeft : α} {lastRight : β}
    (last : relation lastLeft lastRight) :
    List.Forall₂ relation (left ++ [lastLeft]) (right ++ [lastRight]) := by
  induction agreement with
  | nil => exact .cons last .nil
  | cons head tail inductionHypothesis =>
      exact .cons head inductionHypothesis

/-- An aligned occurrence inside the left list of a `Forall₂` derivation has
an exact corresponding occurrence on the right.  Removing that pair preserves
the relation, including duplicate multiplicity and source order. -/
private theorem forall₂_split_middle
    {α β : Type} {relation : α → β → Prop}
    {left : List α} {target : α} {right : List α}
    {executables : List β}
    (agreement :
      List.Forall₂ relation (left ++ target :: right) executables) :
    ∃ executableLeft executableTarget executableRight,
      executables =
          executableLeft ++ executableTarget :: executableRight ∧
        List.Forall₂ relation left executableLeft ∧
        relation target executableTarget ∧
        List.Forall₂ relation right executableRight := by
  induction left generalizing executables with
  | nil =>
      cases agreement with
      | cons targetAgreement rightAgreement =>
          exact
            ⟨[], _, _, rfl, .nil, targetAgreement, rightAgreement⟩
  | cons sourceHead sourceTail inductionHypothesis =>
      cases executables with
      | nil =>
          cases agreement
      | cons executableHead executableTail =>
          cases agreement with
          | cons headAgreement tailAgreement =>
              obtain
                ⟨executableLeft, executableTarget, executableRight,
                  executableShape, leftAgreement, targetAgreement,
                  rightAgreement⟩ :=
                inductionHypothesis tailAgreement
              refine
                ⟨executableHead :: executableLeft, executableTarget,
                  executableRight, ?_, .cons headAgreement leftAgreement,
                  targetAgreement, rightAgreement⟩
              simp [executableShape]

/-- Concatenating two exact pointwise correspondences preserves their order. -/
private theorem forall₂_append
    {α β : Type} {relation : α → β → Prop}
    {left₁ left₂ : List α} {right₁ right₂ : List β}
    (left : List.Forall₂ relation left₁ right₁)
    (right : List.Forall₂ relation left₂ right₂) :
    List.Forall₂ relation (left₁ ++ left₂) (right₁ ++ right₂) := by
  induction left with
  | nil =>
      exact right
  | cons head tail inductionHypothesis =>
      exact .cons head inductionHypothesis

/-- At the current generation, a reachable occurrence is visible exactly when
it has not been erased. -/
theorem VersionedClause.visibleAt_current_eq_isNone
    {database : Database} (closed : DatabaseGenerationClosed database)
    {entry : VersionedClause} (member : entry ∈ database.history) :
    entry.visibleAt database.generation = entry.erased.isNone := by
  have bounds := closed entry member
  cases erasedEq : entry.erased with
  | none =>
      simp [VersionedClause.visibleAt, erasedEq, bounds.1]
  | some erased =>
      have erasedBound := bounds.2 erased erasedEq
      simp [VersionedClause.visibleAt, erasedEq,
        Nat.not_lt_of_ge erasedBound]

/-- Current visibility can therefore be computed by the simpler unerased
filter on every reachable database. -/
theorem currentVisibleEntries_eq_filter_isNone
    {database : Database} (closed : DatabaseGenerationClosed database) :
    currentVisibleEntries database =
      database.history.filter fun entry => entry.erased.isNone := by
  apply List.filter_congr
  intro entry member
  exact VersionedClause.visibleAt_current_eq_isNone closed member

/-- `assertz` preserves generation closure. -/
theorem DatabaseGenerationClosed.assertz
    {database : Database} (closed : DatabaseGenerationClosed database)
    (clause : LocalClause) :
    DatabaseGenerationClosed (database.assertz clause) := by
  intro entry member
  rw [Database.assertz] at member ⊢
  rcases List.mem_append.mp member with old | new
  · have bounds := closed entry old
    exact ⟨Nat.le_trans bounds.1 (Nat.le_add_right _ _),
      fun erased erasedEq =>
        Nat.le_trans (bounds.2 erased erasedEq) (Nat.le_add_right _ _)⟩
  · simp only [List.mem_singleton] at new
    subst entry
    exact ⟨Nat.le_refl _, by simp [Database.allocate]⟩

/-- `asserta` preserves generation closure. -/
theorem DatabaseGenerationClosed.asserta
    {database : Database} (closed : DatabaseGenerationClosed database)
    (clause : LocalClause) :
    DatabaseGenerationClosed (database.asserta clause) := by
  intro entry member
  rw [Database.asserta] at member ⊢
  rcases List.mem_cons.mp member with new | old
  · subst entry
    exact ⟨Nat.le_refl _, by simp [Database.allocate]⟩
  · have bounds := closed entry old
    exact ⟨Nat.le_trans bounds.1 (Nat.le_add_right _ _),
      fun erased erasedEq =>
        Nat.le_trans (bounds.2 erased erasedEq) (Nat.le_add_right _ _)⟩

/-- A new tail occurrence becomes visible at the new generation after every
previously live occurrence, preserving duplicates. -/
theorem currentVisibleEntries_assertz
    {database : Database} (closed : DatabaseGenerationClosed database)
    (clause : LocalClause) :
    currentVisibleEntries (database.assertz clause) =
      currentVisibleEntries database ++ [database.allocate clause] := by
  rw [currentVisibleEntries_eq_filter_isNone (closed.assertz clause),
    currentVisibleEntries_eq_filter_isNone closed]
  simp [Database.assertz, Database.allocate, List.filter_append]

/-- A new head occurrence becomes visible before every previous live
occurrence. -/
theorem currentVisibleEntries_asserta
    {database : Database} (closed : DatabaseGenerationClosed database)
    (clause : LocalClause) :
    currentVisibleEntries (database.asserta clause) =
      database.allocate clause :: currentVisibleEntries database := by
  rw [currentVisibleEntries_eq_filter_isNone (closed.asserta clause),
    currentVisibleEntries_eq_filter_isNone closed]
  simp [Database.asserta, Database.allocate]

/-- Rebuilding the derived clause index changes no semantic clause occurrence
and establishes the required executable coherence. -/
theorem DatabaseRelatesWorld.reindex
    {database : Database} {world : PWorld}
    (agreement : DatabaseRelatesWorld database world) :
    DatabaseRelatesWorld database world.reindexClauses := by
  refine ⟨agreement.reachable, ?_, world.reindexClauses_coherent⟩
  simpa [PWorld.reindexClauses] using agreement.liveClauses

/-- Any executable successor with the exact back-inserted canonical clause
projection and a coherent derived index relates to the independent `assertz`
successor.  Other executable world metadata may change independently; this
theorem states precisely which projection is semantic for local resolution. -/
theorem DatabaseRelatesWorld.assertz_of_projection
    {database : Database} {world : PWorld}
    (agreement : DatabaseRelatesWorld database world)
    {reference : LocalClause}
    {executable : String × PLeaTTa.Clause}
    {afterWorld : PWorld}
    (clause : LocalClauseAgrees reference executable)
    (projection :
      afterWorld.progClauses = world.progClauses ++ [executable])
    (coherent : afterWorld.ClauseIndexCoherent) :
    DatabaseRelatesWorld (database.assertz reference)
      afterWorld := by
  refine ⟨agreement.reachable.assertz reference, ?_, coherent⟩
  rw [currentVisibleEntries_assertz agreement.generationClosed reference,
    projection]
  have newClause :
      VersionedClauseAgrees (database.allocate reference) executable := by
    simpa [VersionedClauseAgrees, Database.allocate] using clause
  exact forall₂_append_singleton agreement.liveClauses newClause

/-- Appending matching source/executable clauses preserves the exact live
projection, source order, duplicate multiplicity, and executable index
coherence. -/
theorem DatabaseRelatesWorld.assertz
    {database : Database} {world : PWorld}
    (agreement : DatabaseRelatesWorld database world)
    {reference : LocalClause}
    {executable : String × PLeaTTa.Clause}
    (clause : LocalClauseAgrees reference executable) :
    DatabaseRelatesWorld (database.assertz reference)
      (world.appendProgClause executable) := by
  apply agreement.assertz_of_projection clause
  · unfold PWorld.appendProgClause
    split <;> rfl
  · exact
      world.appendProgClause_coherent executable agreement.clauseIndex

/-- Any executable successor with the exact front-inserted canonical clause
projection and a coherent derived index relates to the independent `asserta`
successor. -/
theorem DatabaseRelatesWorld.asserta_of_projection
    {database : Database} {world : PWorld}
    (agreement : DatabaseRelatesWorld database world)
    {reference : LocalClause}
    {executable : String × PLeaTTa.Clause}
    {afterWorld : PWorld}
    (clause : LocalClauseAgrees reference executable)
    (projection :
      afterWorld.progClauses = executable :: world.progClauses)
    (coherent : afterWorld.ClauseIndexCoherent) :
    DatabaseRelatesWorld (database.asserta reference) afterWorld := by
  refine ⟨agreement.reachable.asserta reference, ?_, coherent⟩
  rw [currentVisibleEntries_asserta agreement.generationClosed reference,
    projection]
  exact .cons clause agreement.liveClauses

/-- Prepending matching source/executable clauses preserves the exact live
projection.  `replaceProgClauses` is the executable asserta-shaped update and
rebuilds a ready index. -/
theorem DatabaseRelatesWorld.asserta
    {database : Database} {world : PWorld}
    (agreement : DatabaseRelatesWorld database world)
    {reference : LocalClause}
    {executable : String × PLeaTTa.Clause}
    (clause : LocalClauseAgrees reference executable) :
    DatabaseRelatesWorld (database.asserta reference)
      (world.replaceProgClauses (executable :: world.progClauses)) := by
  apply agreement.asserta_of_projection clause
  · exact PWorld.replaceProgClauses_progClauses world _
  · exact world.replaceProgClauses_coherent _ agreement.clauseIndex

/-- Successful identity retraction removes exactly the aligned executable
occurrence, preserves the source order and duplicate multiplicity of all other
clauses, advances the logical-update generation, and rebuilds a coherent
executable index.

This is deliberately the identity primitive from `metta.pl:279-280`.
Selecting the first content-unifying occurrence and exposing later matches on
backtracking remains a separate MGU/control obligation. -/
theorem DatabaseRelatesWorld.retractId
    {database after : Database} {world : PWorld} {id : ClauseId}
    (agreement : DatabaseRelatesWorld database world)
    (retracted : database.retractId id = some after) :
    ∃ sourceLeft target sourceRight
        executableLeft executableTarget executableRight,
      currentVisibleEntries database =
          sourceLeft ++ target :: sourceRight ∧
        currentVisibleEntries after = sourceLeft ++ sourceRight ∧
        world.progClauses =
          executableLeft ++ executableTarget :: executableRight ∧
        target.id = id ∧
        target.erased = none ∧
        VersionedClauseAgrees target executableTarget ∧
        DatabaseRelatesWorld after
          (world.replaceProgClauses
            (executableLeft ++ executableRight)) := by
  cases retiredHistoryEq :
      retireFirst (database.generation + 1) id database.history with
  | none =>
      simp [Database.retractId, retiredHistoryEq] at retracted
  | some retiredHistory =>
      have afterShape :
          after =
            { database with
              generation := database.generation + 1
              history := retiredHistory } := by
        have reversed :
            { database with
                generation := database.generation + 1
                history := retiredHistory } = after := by
          have someEq :
              some
                  { database with
                    generation := database.generation + 1
                    history := retiredHistory } =
                some after := by
            simpa [Database.retractId, retiredHistoryEq] using retracted
          exact Option.some.inj someEq
        exact reversed.symm
      subst after
      obtain
        ⟨sourceLeft, target, sourceRight, beforeProjection,
          afterProjection, targetId, targetLive, retiredClosed⟩ :=
        retireFirst_live_projection agreement.generationClosed
          retiredHistoryEq
      have aligned :
          List.Forall₂ VersionedClauseAgrees
            (sourceLeft ++ target :: sourceRight) world.progClauses := by
        rw [← beforeProjection]
        exact agreement.liveClauses
      obtain
        ⟨executableLeft, executableTarget, executableRight,
          executableShape, leftAgreement, targetAgreement,
          rightAgreement⟩ :=
        forall₂_split_middle aligned
      have retainedAgreement :
          List.Forall₂ VersionedClauseAgrees
            (sourceLeft ++ sourceRight)
            (executableLeft ++ executableRight) :=
        forall₂_append leftAgreement rightAgreement
      refine
        ⟨sourceLeft, target, sourceRight, executableLeft, executableTarget,
          executableRight, beforeProjection, ?_, executableShape, targetId,
          targetLive, targetAgreement, ?_⟩
      · simpa [currentVisibleEntries] using afterProjection
      · refine
          ⟨?_, ?_,
            world.replaceProgClauses_coherent
              (executableLeft ++ executableRight) agreement.clauseIndex⟩
        · exact agreement.reachable.retractId retracted
        · rw [PWorld.replaceProgClauses_progClauses]
          simpa [currentVisibleEntries, afterProjection] using
            retainedAgreement

/-- A successful identity retraction advances the logical-update generation
exactly once. -/
theorem Database.retractId_generation
    {database after : Database} {id : ClauseId}
    (retracted : database.retractId id = some after) :
    after.generation = database.generation + 1 := by
  cases retiredHistoryEq :
      retireFirst (database.generation + 1) id database.history with
  | none =>
      simp [Database.retractId, retiredHistoryEq] at retracted
  | some retiredHistory =>
      have someEq :
          some
              { database with
                generation := database.generation + 1
                history := retiredHistory } =
            some after := by
        simpa [Database.retractId, retiredHistoryEq] using retracted
      have shape := Option.some.inj someEq
      rw [← shape]

/-- Retraction separates old and new call snapshots without mutating the old
prepared token: the old token remains related to the exact call-start
generation and occurrence order, while a later open observes the successor
generation and the updated database projection.

The concrete resolver witnesses additionally show that a matching retracted
occurrence remains in the old token and is absent from the new one. -/
theorem retractId_snapshot_separation
    {database after : Database} {id : ClauseId}
    (session : LocalSession) (request : CallRequest)
    (retracted : database.retractId id = some after) :
    let beforeSession : LocalSession :=
      { session with database := database }
    let afterSession : LocalSession :=
      { session with database := after }
    PreparedCursorSnapshots database request
        (prepareCall beforeSession request).1 ∧
      PreparedCursorSnapshots after request
        (prepareCall afterSession request).1 ∧
      (prepareCall beforeSession request).1.callGeneration <
        (prepareCall afterSession request).1.callGeneration := by
  dsimp
  refine
    ⟨prepareCall_snapshots { session with database := database } request,
      prepareCall_snapshots { session with database := after } request, ?_⟩
  rw [Database.retractId_generation retracted]
  exact Nat.lt_succ_self _

/-- Empty independent and executable stores agree for every frontier relation
that relates their zero high-waters. -/
theorem empty_session_relates
    (freshFrontier : FreshFrontierRelation)
    (zero : freshFrontier 0 0) :
    SessionRelatesPersistent freshFrontier
      ({} : Session) ({ world := {}, counter := 0 } : Persistent) := by
  constructor
  · constructor
    · exact
        PeTTaSpec.PrologCore.DatabaseActions.DatabaseReachable.empty
    · exact .nil
    · intro ready
      simp at ready
  · exact zero

/-- Changing only nominal scope allocators preserves the executable
persistent projection. -/
theorem SessionRelatesPersistent.of_resolver_eq
    {freshFrontier : FreshFrontierRelation}
    {before after : Session} {persistent : Persistent}
    (agreement :
      SessionRelatesPersistent freshFrontier before persistent)
    (resolver : after.resolver = before.resolver) :
    SessionRelatesPersistent freshFrontier after persistent := by
  constructor
  · simpa [resolver] using agreement.database
  · simpa [resolver] using agreement.fresh

/-- Entering local `catch/3` allocates typed cut/exception identities only;
database and fresh-name projection are unchanged. -/
theorem openCatch_preserves_persistent_relation
    (freshFrontier : FreshFrontierRelation)
    (session : Session) (persistent : Persistent)
    (agreement :
      SessionRelatesPersistent freshFrontier session persistent) :
    SessionRelatesPersistent freshFrontier
      (openCatch session).session persistent := by
  exact agreement.of_resolver_eq rfl

/-- Entering local `findall/3` allocates typed cut/collection identities only;
database and fresh-name projection are unchanged. -/
theorem openFindall_preserves_persistent_relation
    (freshFrontier : FreshFrontierRelation)
    (session : Session) (persistent : Persistent)
    (agreement :
      SessionRelatesPersistent freshFrontier session persistent) :
    SessionRelatesPersistent freshFrontier
      (openFindall session).session persistent := by
  exact agreement.of_resolver_eq rfl

/-- The scope allocators really advance separately.  Their omission from
`SessionRelatesPersistent` is an explicit erasure, not accidental field
conflation. -/
theorem openCatch_scope_projection (session : Session) :
    (openCatch session).session.nextCutScope = session.nextCutScope + 1 ∧
      (openCatch session).session.nextExceptionScope =
        session.nextExceptionScope + 1 ∧
      (openCatch session).session.nextCollectionScope =
        session.nextCollectionScope := by
  exact ⟨rfl, rfl, rfl⟩

theorem openFindall_scope_projection (session : Session) :
    (openFindall session).session.nextCutScope = session.nextCutScope + 1 ∧
      (openFindall session).session.nextExceptionScope =
        session.nextExceptionScope ∧
      (openFindall session).session.nextCollectionScope =
        session.nextCollectionScope + 1 := by
  exact ⟨rfl, rfl, rfl⟩

/-! ### Clause standardization agrees up to a finite alpha bijection -/

/-- Independent fresh identities allocated for one source-ordered variable
support.  The list parameter supplies only the cardinality and stable
first-occurrence order; every output identity is in the generated namespace.
-/
def referenceFreshTargets : Nat → List LogicVar → List LogicVar
  | _, [] => []
  | seed, _ :: rest =>
      .generated seed :: referenceFreshTargets (seed + 1) rest

/-- Executable fresh names allocated for the same source-ordered support by
PeTTa's one-suffix-per-clause convention. -/
def executableFreshTargets (suffix : String)
    (support : List LogicVar) : List String :=
  support.map fun identity =>
    logicVarExecutableName identity ++ suffix

/-- An ordered finite graph presents a bijection between two variable
supports exactly when both projections are duplicate-free and have the same
cardinality.  The graph itself is their positional `zip`; no global choice of
names, counter equality, or answer relation is hidden in this predicate. -/
structure RuntimeAlpha (reference : List LogicVar)
    (executable : List String) : Prop where
  cardinality : reference.length = executable.length
  referenceInjective : reference.Nodup
  executableInjective : executable.Nodup

/-- The finite alpha map itself: positions pair the two ordered supports. -/
def RuntimeAlpha.graph (reference : List LogicVar)
    (executable : List String) : List (LogicVar × String) :=
  reference.zip executable

/-- The graph covers every independent fresh identity exactly once. -/
theorem RuntimeAlpha.graph_reference
    {reference : List LogicVar} {executable : List String}
    (alpha : RuntimeAlpha reference executable) :
    (RuntimeAlpha.graph reference executable).map Prod.fst = reference := by
  exact List.map_fst_zip (Nat.le_of_eq alpha.cardinality)

/-- The graph covers every executable fresh name exactly once. -/
theorem RuntimeAlpha.graph_executable
    {reference : List LogicVar} {executable : List String}
    (alpha : RuntimeAlpha reference executable) :
    (RuntimeAlpha.graph reference executable).map Prod.snd = executable := by
  exact List.map_snd_zip (Nat.le_of_eq alpha.cardinality.symm)

mutual

/-- Structural term agreement under an explicit finite runtime alpha graph.
Unlike compiler-time `TermAgrees`, the variable constructor does not assign
an executable spelling from the independent identity: the graph records the
actual names chosen by the two runtime copiers. -/
inductive AlphaTermAgrees (alpha : List (LogicVar × String)) :
    Term → Atom → Prop where
  | variable {identity : LogicVar} {name : String}
      (linked : (identity, name) ∈ alpha) :
      AlphaTermAgrees alpha (.variable identity) (.var name)
  | atom {name : String} (notTrue : name ≠ "true")
      (notFalse : name ≠ "false") :
      AlphaTermAgrees alpha (.atom name) (.sym name)
  | trueAtom : AlphaTermAgrees alpha (.atom "true") (.sym "True")
  | falseAtom : AlphaTermAgrees alpha (.atom "false") (.sym "False")
  | integer (value : Int) :
      AlphaTermAgrees alpha (.integer value) (.gnd (.int value))
  | float (value : Float) :
      AlphaTermAgrees alpha
        (.float (PLeaTTa.PrologFloatIdentity.ofFloat value))
        (.gnd (.float value))
  | string (value : String) :
      AlphaTermAgrees alpha (.string value) (.gnd (.str value))
  | partialValue {head : String} {terms : List Term}
      {encodedArguments : Atom}
      (arguments : AlphaProperListAgrees alpha terms encodedArguments) :
      AlphaTermAgrees alpha
        (.compound "partial" [.atom head, .list terms none])
        (partialC head encodedArguments)
  | properList {items : List Term} {encoded : Atom}
      (elements : AlphaProperListAgrees alpha items encoded) :
      AlphaTermAgrees alpha (.list items none) encoded

/-- Proper-list counterpart of `AlphaTermAgrees`. -/
inductive AlphaProperListAgrees (alpha : List (LogicVar × String)) :
    List Term → Atom → Prop where
  | nil : AlphaProperListAgrees alpha [] nilA
  | cons {term : Term} {atom : Atom} {terms : List Term} {tail : Atom}
      (head : AlphaTermAgrees alpha term atom)
      (rest : AlphaProperListAgrees alpha terms tail) :
      AlphaProperListAgrees alpha (term :: terms) (consC atom tail)

end

/-- Ordered pointwise term agreement under one runtime alpha graph. -/
inductive AlphaTermsAgree (alpha : List (LogicVar × String)) :
    List Term → List Atom → Prop where
  | nil : AlphaTermsAgree alpha [] []
  | cons {term : Term} {atom : Atom} {terms : List Term}
      {atoms : List Atom}
      (head : AlphaTermAgrees alpha term atom)
      (tail : AlphaTermsAgree alpha terms atoms) :
      AlphaTermsAgree alpha (term :: terms) (atom :: atoms)

/-- Exact freshened head-payload agreement.  This is deliberately separate
from body-goal agreement: runtime cut tagging and the executable-only goal
constructors require their own alpha-preservation layer. -/
structure LocalClauseHeadAlphaAgrees
    (alpha : List (LogicVar × String))
    (reference : LocalClause)
    (executable : String × PLeaTTa.Clause) : Prop where
  predicate : reference.predicate = executable.1
  outputLast :
    ∃ referenceParameters referenceResult,
      reference.arguments = referenceParameters ++ [referenceResult] ∧
        AlphaTermsAgree alpha referenceParameters executable.2.params ∧
        AlphaTermAgrees alpha referenceResult executable.2.result

/-- Suffix renaming commutes with the executable proper-list encoder. -/
theorem renameAtomSuffix_chainOf (suffix : String) (atoms : List Atom) :
    renameAtomSuffix suffix (chainOf atoms) =
      chainOf (atoms.map (renameAtomSuffix suffix)) := by
  induction atoms with
  | nil =>
      simp [chainOf, nilA, renameAtomSuffix_gnd]
  | cons head tail inductionHypothesis =>
      change renameAtomSuffix suffix (consC head (chainOf tail)) =
        consC (renameAtomSuffix suffix head)
          (chainOf (tail.map (renameAtomSuffix suffix)))
      simp [consC, renameAtomSuffix_expr, renameAtomSuffix_sym,
        inductionHypothesis]

/-- Representation agreement transports through one simultaneous independent
freshening and one executable suffix renaming when every supported source
variable is tied to the same finite alpha graph.  This is not executable deep
substitution: suffix targets may themselves resemble source names, so the
simultaneous `renameAtomSuffix` operation remains explicit. -/
theorem termAgrees_alpha_freshen
    {referenceSubstitution : Substitution} {suffix : String}
    {domain : List LogicVar} {alpha : List (LogicVar × String)}
    (variableAgreement :
      ∀ identity, identity ∈ domain →
        ∃ target,
          referenceSubstitution.applyTerm (.variable identity) =
            .variable target ∧
          (target, logicVarExecutableName identity ++ suffix) ∈ alpha)
    {term : Term} {atom : Atom} (agreement : TermAgrees term atom)
    (supported : termVariablesIn domain term) :
    AlphaTermAgrees alpha
      (referenceSubstitution.applyTerm term)
      (renameAtomSuffix suffix atom) := by
  apply TermAgrees.rec
    (motive_1 := fun term atom _ =>
      termVariablesIn domain term →
        AlphaTermAgrees alpha
          (referenceSubstitution.applyTerm term)
          (renameAtomSuffix suffix atom))
    (motive_2 := fun terms atom _ =>
      termsVariablesIn domain terms →
        AlphaProperListAgrees alpha
          (referenceSubstitution.applyTerms terms)
          (renameAtomSuffix suffix atom))
  · intro name member
    obtain ⟨target, applied, linked⟩ :=
      variableAgreement (.source name) member
    rw [applied, renameAtomSuffix_var]
    exact .variable linked
  · intro index member
    obtain ⟨target, applied, linked⟩ :=
      variableAgreement (.generated index) member
    rw [applied, renameAtomSuffix_var]
    exact .variable linked
  · intro name notTrue notFalse _supported
    simpa [renameAtomSuffix_sym] using
      (AlphaTermAgrees.atom (alpha := alpha) notTrue notFalse)
  · intro _supported
    simpa [renameAtomSuffix_sym] using
      (AlphaTermAgrees.trueAtom (alpha := alpha))
  · intro _supported
    simpa [renameAtomSuffix_sym] using
      (AlphaTermAgrees.falseAtom (alpha := alpha))
  · intro value _supported
    simpa [renameAtomSuffix_gnd] using
      (AlphaTermAgrees.integer (alpha := alpha) value)
  · intro value _supported
    simpa [renameAtomSuffix_gnd] using
      (AlphaTermAgrees.float (alpha := alpha) value)
  · intro value _supported
    simpa [renameAtomSuffix_gnd] using
      (AlphaTermAgrees.string (alpha := alpha) value)
  · intro head terms encoded arguments inductionHypothesis termSupport
    have termsSupport : termsVariablesIn domain terms := by
      simpa [termVariablesIn, termsVariablesIn] using termSupport
    simpa [partialC, partialTagA, renameAtomSuffix_expr,
      renameAtomSuffix_chainOf,
      renameAtomSuffix_sym, renameAtomSuffix_gnd] using
      (AlphaTermAgrees.partialValue
        (inductionHypothesis termsSupport))
  · intro items encoded elements inductionHypothesis termSupport
    have itemsSupport : termsVariablesIn domain items := by
      simpa [termVariablesIn] using termSupport
    simpa using
      (AlphaTermAgrees.properList (inductionHypothesis itemsSupport))
  · intro _supported
    simpa [nilA, renameAtomSuffix_gnd] using
      (AlphaProperListAgrees.nil (alpha := alpha))
  · intro term atom terms tail head rest headInduction tailInduction support
    simpa [consC, renameAtomSuffix_expr, renameAtomSuffix_sym] using
      (AlphaProperListAgrees.cons
        (headInduction support.1) (tailInduction support.2))
  · exact agreement
  · exact supported

/-- Ordered-list counterpart of `termAgrees_alpha_freshen`. -/
theorem termsAgree_alpha_freshen
    {referenceSubstitution : Substitution} {suffix : String}
    {domain : List LogicVar} {alpha : List (LogicVar × String)}
    (variableAgreement :
      ∀ identity, identity ∈ domain →
        ∃ target,
          referenceSubstitution.applyTerm (.variable identity) =
            .variable target ∧
          (target, logicVarExecutableName identity ++ suffix) ∈ alpha)
    {terms : List Term} {atoms : List Atom}
    (agreement : TermsAgree terms atoms)
    (supported : termsVariablesIn domain terms) :
    AlphaTermsAgree alpha
      (referenceSubstitution.applyTerms terms)
      (atoms.map (renameAtomSuffix suffix)) := by
  induction agreement with
  | nil =>
      simpa using (AlphaTermsAgree.nil (alpha := alpha))
  | cons head tail inductionHypothesis =>
      simpa [Substitution.applyTerms] using
        (AlphaTermsAgree.cons
          (termAgrees_alpha_freshen variableAgreement head supported.1)
          (inductionHypothesis supported.2))

/-- A term is supported by any finite domain containing its complete
independently computed occurrence list. -/
theorem termVariablesIn_of_occurrences
    (domain : List LogicVar) (term : Term)
    (contained : ∀ identity, identity ∈ termVariables term →
      identity ∈ domain) :
    termVariablesIn domain term := by
  apply Term.rec
    (motive_1 := fun term =>
      (∀ identity, identity ∈ termVariables term → identity ∈ domain) →
        termVariablesIn domain term)
    (motive_2 := fun terms =>
      (∀ identity, identity ∈ termsVariables terms → identity ∈ domain) →
        termsVariablesIn domain terms)
    (motive_3 := fun tail =>
      match tail with
      | none => True
      | some term =>
          (∀ identity, identity ∈ termVariables term →
            identity ∈ domain) →
          termVariablesIn domain term)
  · intro identity support
    exact support identity (by simp [termVariables])
  · intro name support
    trivial
  · intro value support
    trivial
  · intro value support
    trivial
  · intro value support
    trivial
  · intro functor arguments inductionHypothesis support
    apply inductionHypothesis
    intro identity member
    exact support identity (by simpa [termVariables] using member)
  · intro items tail itemsInduction tailInduction support
    cases tail with
    | none =>
        apply itemsInduction
        intro identity member
        exact support identity (by simpa [termVariables] using member)
    | some tail =>
        constructor
        · apply itemsInduction
          intro identity member
          apply support identity
          simp [termVariables, member]
        · apply tailInduction
          intro identity member
          apply support identity
          simp [termVariables, member]
  · intro support
    trivial
  · intro head tail headInduction tailInduction support
    constructor
    · apply headInduction
      intro identity member
      apply support identity
      simp [termsVariables, member]
    · apply tailInduction
      intro identity member
      apply support identity
      simp [termsVariables, member]
  · trivial
  · intro term inductionHypothesis
    exact inductionHypothesis
  · exact contained

/-- Ordered-list counterpart of `termVariablesIn_of_occurrences`. -/
theorem termsVariablesIn_of_occurrences
    (domain : List LogicVar) (terms : List Term)
    (contained : ∀ identity, identity ∈ termsVariables terms →
      identity ∈ domain) :
    termsVariablesIn domain terms := by
  cases terms with
  | nil =>
      trivial
  | cons term terms =>
      constructor
      · apply termVariablesIn_of_occurrences
        intro identity member
        apply contained identity
        simp [termsVariables, member]
      · apply termsVariablesIn_of_occurrences
        intro identity member
        apply contained identity
        simp [termsVariables, member]

/-- Every argument variable is contained in its clause's stable finite
support. -/
theorem LocalClause.arguments_supported (clause : LocalClause) :
    termsVariablesIn clause.variables clause.arguments := by
  apply termsVariablesIn_of_occurrences
  intro identity member
  exact List.mem_eraseDups.mpr (List.mem_append_left _ member)

private theorem nodup_map_of_injective {α β : Type}
    (function : α → β) (injective : Function.Injective function) :
    ∀ values : List α, values.Nodup → (values.map function).Nodup
  | [], _ => .nil
  | value :: values, nodup => by
      rw [List.nodup_cons] at nodup
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro member
        rw [List.mem_map] at member
        obtain ⟨source, sourceMember, equality⟩ := member
        have same : source = value := injective equality
        subst source
        exact nodup.1 sourceMember
      · exact nodup_map_of_injective function injective values nodup.2

private theorem eraseDups_nodup_logicVar :
    ∀ support : List LogicVar, support.eraseDups.Nodup
  | [] => by simp
  | head :: tail => by
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · intro member
        rw [List.mem_eraseDups] at member
        simp at member
      · exact eraseDups_nodup_logicVar
          (tail.filter (fun identity => !identity == head))
termination_by support => support.length
decreasing_by
  have lengthBound :=
    List.length_filter_le (fun identity : LogicVar => !identity == head) tail
  simp only [List.length_cons]
  omega

/-- `LocalClause.variables` is a genuine finite support rather than an
occurrence list: first-occurrence order is retained and duplicates are
removed. -/
theorem LocalClause.variables_nodup (clause : LocalClause) :
    clause.variables.Nodup := by
  exact eraseDups_nodup_logicVar _

/-- The independent standardizer preserves the exact source projection of
its simultaneous freshening substitution. -/
theorem buildFreshening_sources (seed : Nat) (support : List LogicVar) :
    (buildFreshening seed support).1.map Prod.fst = support := by
  induction support generalizing seed with
  | nil => rfl
  | cons head rest inductionHypothesis =>
      simp only [buildFreshening, List.map_cons, inductionHypothesis]

/-- The independent standardizer's target projection is exactly the
consecutive generated support advertised by `referenceFreshTargets`. -/
theorem buildFreshening_targets (seed : Nat) (support : List LogicVar) :
    (buildFreshening seed support).1.map (fun binding =>
      match binding.2 with
      | .variable identity => identity
      | _ => .anonymous 0) =
        referenceFreshTargets seed support := by
  induction support generalizing seed with
  | nil => rfl
  | cons head rest inductionHypothesis =>
      simp only [buildFreshening, List.map_cons, referenceFreshTargets,
        inductionHypothesis]

/-- A finite substitution fixes a variable absent from its complete source
projection.  Replacement targets need no disjointness premise because the
source is never replaced in the first place. -/
theorem applyTerm_variable_of_not_mem_sources
    (bindings : Substitution) (identity : LogicVar)
    (absent : identity ∉ bindings.map Prod.fst) :
    bindings.applyTerm (.variable identity) = .variable identity := by
  induction bindings with
  | nil => rfl
  | cons binding bindings inductionHypothesis =>
      rcases binding with ⟨source, replacement⟩
      have sourceDifferent : identity ≠ source := by
        intro same
        apply absent
        simp [same]
      have tailAbsent : identity ∉ bindings.map Prod.fst := by
        intro member
        apply absent
        simp [member]
      simp [Substitution.applyTerm, inductionHypothesis tailAbsent,
        Term.instantiateOne, sourceDifferent]

/-- `buildFreshening` behaves as a simultaneous renaming on every binding it
creates.  Duplicate-free sources and a starting high-water above the source
syntax prevent a later target from being captured by an earlier source key. -/
theorem buildFreshening_apply_member
    (seed : Nat) (support : List LogicVar)
    (supportNodup : support.Nodup)
    (below : GeneratedBelow seed support)
    {source : LogicVar} {target : Term}
    (member : (source, target) ∈ (buildFreshening seed support).1) :
    (buildFreshening seed support).1.applyTerm (.variable source) =
      target := by
  induction support generalizing seed source target with
  | nil => simp [buildFreshening] at member
  | cons head tail inductionHypothesis =>
      rw [List.nodup_cons] at supportNodup
      simp only [buildFreshening] at member
      rcases List.mem_cons.mp member with first | later
      · have sourceEq : source = head := congrArg Prod.fst first
        have targetEq :
            target = .variable (.generated seed) :=
          congrArg Prod.snd first
        subst source
        subst target
        change Term.instantiateOne head (.variable (.generated seed))
          ((buildFreshening (seed + 1) tail).1.applyTerm
            (.variable head)) =
          .variable (.generated seed)
        rw [applyTerm_variable_of_not_mem_sources]
        · simp [Term.instantiateOne]
        · rw [buildFreshening_sources]
          exact supportNodup.1
      · have tailBelow : GeneratedBelow (seed + 1) tail := by
          intro index indexMember
          have oldBound := below index (by simp [indexMember])
          omega
        have tailResult :=
          inductionHypothesis (seed := seed + 1) supportNodup.2
            tailBelow later
        obtain ⟨index, targetShape, lower, upper⟩ :=
          buildFreshening_target_generated (seed + 1) tail later
        rw [targetShape] at tailResult ⊢
        have targetDifferent : (.generated index : LogicVar) ≠ head := by
          cases head with
          | source name => simp
          | anonymous anonymousIndex => simp
          | generated headIndex =>
              have headBound := below headIndex (by simp)
              intro same
              injection same with indexEq
              omega
        change Term.instantiateOne head (.variable (.generated seed))
          ((buildFreshening (seed + 1) tail).1.applyTerm
            (.variable source)) =
          .variable (.generated index)
        rw [tailResult]
        simp [Term.instantiateOne, targetDifferent]

/-- The source, independent target, and executable suffix target at every
support position are tied together by the actual builder and the runtime
alpha graph. -/
theorem buildFreshening_alpha_member
    (seed : Nat) (support : List LogicVar) (suffix : String)
    {source : LogicVar} (member : source ∈ support) :
    ∃ target,
      (source, .variable target) ∈ (buildFreshening seed support).1 ∧
        (target, logicVarExecutableName source ++ suffix) ∈
          RuntimeAlpha.graph (referenceFreshTargets seed support)
            (executableFreshTargets suffix support) := by
  induction support generalizing seed with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp member with same | later
      · subst source
        refine ⟨.generated seed, ?_, ?_⟩
        · simp [buildFreshening]
        · simp [RuntimeAlpha.graph, referenceFreshTargets,
            executableFreshTargets]
      · obtain ⟨target, targetMember, graphMember⟩ :=
          inductionHypothesis (seed := seed + 1) later
        refine ⟨target, ?_, ?_⟩
        · simp [buildFreshening, targetMember]
        · simp only [RuntimeAlpha.graph, referenceFreshTargets,
            executableFreshTargets, List.map_cons, List.zip_cons_cons,
            List.mem_cons]
          exact Or.inr graphMember

/-- The actual independent clause copier starts above every generated
identity in the stored clause support. -/
theorem LocalClause.freshCopy_generatedBelow
    (clause : LocalClause) (freshSeed : Nat) :
    GeneratedBelow (clause.freshCopy freshSeed).firstFresh
      clause.variables := by
  exact (generatedBelow_variablesGeneratedCeiling clause.variables).mono
    (clause.freshCopy_first_ge_clause freshSeed)

/-- Every original clause variable is sent by the actual independent
freshening substitution to the exact alpha-graph partner of the executable
suffix renamer.  This is the source-to-target link missing from a bare
cardinality/support theorem. -/
theorem LocalClause.freshCopy_alpha_variable
    (clause : LocalClause) (freshSeed : Nat) (suffix : String)
    {source : LogicVar} (member : source ∈ clause.variables) :
    ∃ target,
      (clause.freshCopy freshSeed).freshSubstitution.applyTerm
          (.variable source) =
        .variable target ∧
      (target, logicVarExecutableName source ++ suffix) ∈
        RuntimeAlpha.graph
          (referenceFreshTargets
            (clause.freshCopy freshSeed).firstFresh clause.variables)
          (executableFreshTargets suffix clause.variables) := by
  obtain ⟨target, targetMember, graphMember⟩ :=
    buildFreshening_alpha_member
      (clause.freshCopy freshSeed).firstFresh clause.variables suffix member
  refine ⟨target, ?_, graphMember⟩
  simpa only [LocalClause.freshCopy] using
    (buildFreshening_apply_member
      (clause.freshCopy freshSeed).firstFresh clause.variables
      (LocalClause.variables_nodup clause)
      (LocalClause.freshCopy_generatedBelow clause freshSeed)
      targetMember)

/-- Every identity in a consecutive independent target support is generated
at or above its starting high-water. -/
theorem referenceFreshTargets_generated_lower
    {seed : Nat} {support : List LogicVar} {target : LogicVar}
    (member : target ∈ referenceFreshTargets seed support) :
    ∃ index, target = .generated index ∧ seed ≤ index := by
  induction support generalizing seed with
  | nil => simp [referenceFreshTargets] at member
  | cons head rest inductionHypothesis =>
      simp only [referenceFreshTargets, List.mem_cons] at member
      rcases member with rfl | later
      · exact ⟨seed, rfl, Nat.le_refl seed⟩
      · obtain ⟨index, targetShape, lower⟩ :=
          inductionHypothesis (seed := seed + 1) later
        exact ⟨index, targetShape, Nat.le_trans
          (Nat.le_add_right seed 1) lower⟩

/-- Consecutive independent fresh targets never alias. -/
theorem referenceFreshTargets_nodup (seed : Nat)
    (support : List LogicVar) :
    (referenceFreshTargets seed support).Nodup := by
  induction support generalizing seed with
  | nil => exact .nil
  | cons head rest inductionHypothesis =>
      rw [referenceFreshTargets, List.nodup_cons]
      constructor
      · intro member
        obtain ⟨index, equality, lower⟩ :=
          referenceFreshTargets_generated_lower member
        have indexEq : seed = index := by
          exact LogicVar.generated.inj equality
        omega
      · exact inductionHypothesis (seed + 1)

/-- The executable suffix targets are duplicate-free precisely under the
finite source/generated spelling-freshness premise already required by the
open-binding adequacy layer. -/
theorem executableFreshTargets_nodup
    {support : List LogicVar}
    (supportNodup : support.Nodup)
    (encoding : EncodingInjectiveOn support)
    (suffix : String) :
    (executableFreshTargets suffix support).Nodup := by
  unfold executableFreshTargets
  induction support with
  | nil => exact .nil
  | cons head rest inductionHypothesis =>
      rw [List.nodup_cons] at supportNodup
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro member
        rw [List.mem_map] at member
        obtain ⟨other, otherMember, equality⟩ := member
        have encodedEqual :
            logicVarExecutableName head =
              logicVarExecutableName other :=
          resolution_suffix_injective suffix equality.symm
        have same : head = other :=
          encoding (by simp) (by simp [otherMember]) encodedEqual
        subst other
        exact supportNodup.1 otherMember
      · apply inductionHypothesis supportNodup.2
        intro left right leftMember rightMember equalNames
        exact encoding (by simp [leftMember]) (by simp [rightMember])
          equalNames

theorem referenceFreshTargets_length (seed : Nat)
    (support : List LogicVar) :
    (referenceFreshTargets seed support).length = support.length := by
  induction support generalizing seed with
  | nil => rfl
  | cons head rest inductionHypothesis =>
      simp only [referenceFreshTargets, List.length_cons,
        inductionHypothesis]

private theorem flatten_map_eq_flatMap {α β : Type}
    (values : List α) (function : α → List β) :
    (values.map function).flatten = values.flatMap function := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      simp only [List.map_cons, List.flatten_cons, List.flatMap_cons,
        inductionHypothesis]

mutual

/-- Suffix-renaming one executable atom maps its complete variable-occurrence
list pointwise, preserving occurrence order and multiplicity. -/
theorem renameAtomSuffix_vars_exact (suffix : String) (atom : Atom) :
    (renameAtomSuffix suffix atom).vars =
      atom.vars.map fun name => name ++ suffix := by
  cases atom with
  | sym name => simp [renameAtomSuffix_sym, Atom.vars]
  | var name => simp [renameAtomSuffix_var, Atom.vars]
  | gnd ground => simp [renameAtomSuffix_gnd, Atom.vars]
  | expr atoms =>
      rw [renameAtomSuffix_expr]
      simp only [Atom.vars, flatten_map_eq_flatMap]
      exact renameAtomListSuffix_vars_exact suffix atoms

/-- Ordered-list counterpart of `renameAtomSuffix_vars_exact`. -/
theorem renameAtomListSuffix_vars_exact (suffix : String)
    (atoms : List Atom) :
    (atoms.map (renameAtomSuffix suffix)).flatMap Atom.vars =
      (atoms.flatMap Atom.vars).map fun name => name ++ suffix := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append,
        renameAtomSuffix_vars_exact, renameAtomListSuffix_vars_exact]

end

mutual

/-- Executable goal freshening maps every variable occurrence by the same
clause suffix.  Cut tagging changes no variable support. -/
theorem renameGoalSuffix_vars_exact (suffix : String) (barrier : Nat)
    (goal : PLeaTTa.Goal) :
    specializationGoalVars (renameGoalSuffix suffix barrier goal) =
      (specializationGoalVars goal).map fun name => name ++ suffix := by
  cases goal <;>
    simp only [renameGoalSuffix, specializationGoalVars,
      renameAtomSuffix_vars_exact, renameAtomListSuffix_vars_exact,
      renameGoalsSuffix_vars_exact, renameBranchesSuffix_vars_exact,
      List.map_append, List.map_nil]

/-- Ordered goal-sequence counterpart of
`renameGoalSuffix_vars_exact`. -/
theorem renameGoalsSuffix_vars_exact (suffix : String) (barrier : Nat)
    (goals : List PLeaTTa.Goal) :
    specializationGoalsVars (renameGoalsSuffix suffix barrier goals) =
      (specializationGoalsVars goals).map fun name => name ++ suffix := by
  cases goals with
  | nil => rfl
  | cons goal goals =>
      simp only [renameGoalsSuffix, specializationGoalsVars,
        List.map_append, renameGoalSuffix_vars_exact,
        renameGoalsSuffix_vars_exact]

/-- Nondeterministic branch counterpart of
`renameGoalSuffix_vars_exact`. -/
theorem renameBranchesSuffix_vars_exact (suffix : String) (barrier : Nat)
    (branches : List (Atom × List PLeaTTa.Goal)) :
    specializationBranchVars
        (renameBranchesSuffix suffix barrier branches) =
      (specializationBranchVars branches).map fun name => name ++ suffix := by
  cases branches with
  | nil => rfl
  | cons branch branches =>
      rcases branch with ⟨template, goals⟩
      simp only [renameBranchesSuffix, specializationBranchVars,
        List.map_append, renameAtomSuffix_vars_exact,
        renameGoalsSuffix_vars_exact, renameBranchesSuffix_vars_exact]

end

/-- The actual executable clause copier maps the complete head/body variable
occurrence list pointwise by its selected suffix.  This ties the executable
half of the alpha bridge to `freshenResolutionClause`, rather than to an
invented support list. -/
theorem freshenResolutionClause_vars_exact
    (argsv args : List Atom) (result : Atom)
    (rest : List PLeaTTa.Goal) (binding : Metta.Subst)
    (query : Atom) (seed barrier : Nat) (clause : PLeaTTa.Clause) :
    let suffix :=
      resolutionFreshSuffix argsv result rest binding query seed
    resolutionClauseVars
        (freshenResolutionClause argsv args result rest binding query
          seed barrier clause) =
      (resolutionClauseVars clause).map fun name => name ++ suffix := by
  unfold freshenResolutionClause resolutionClauseVars
  dsimp only
  rw [← renameGoalsSuffix_eq_map,
    renameAtomListSuffix_vars_exact, renameAtomSuffix_vars_exact,
    renameGoalsSuffix_vars_exact]
  simp only [List.map_append]

/-- Complete independent variable-occurrence surface of one stored clause,
before first-occurrence deduplication. -/
def LocalClause.variableOccurrences (clause : LocalClause) : List LogicVar :=
  termsVariables clause.arguments ++ goalsVariables clause.body

/-- The base cross-representation relation is strengthened with exact
variable-occurrence order and multiplicity.  This is intentionally separate
from `LocalClauseAgrees`: deriving it construct-by-construct from
`TermAgrees`/`GoalsAgree` is the next compiler-to-resolver composition lemma,
not an assumption hidden inside alpha-renaming. -/
def ClauseVariableOccurrencesAgree (reference : LocalClause)
    (executable : PLeaTTa.Clause) : Prop :=
  resolutionClauseVars executable =
    (LocalClause.variableOccurrences reference).map logicVarExecutableName

/-- Exact occurrence correspondence is a sufficient, deliberately stronger
way to establish finite support correspondence. -/
theorem ClauseVariableOccurrencesAgree.support
    {reference : LocalClause} {executable : PLeaTTa.Clause}
    (agreement : ClauseVariableOccurrencesAgree reference executable) :
    ClauseVariableSupportAgrees reference executable := by
  intro name
  rw [agreement, List.mem_map]
  constructor
  · rintro ⟨identity, member, equality⟩
    exact ⟨identity, by
      exact List.mem_eraseDups.mpr member, equality.symm⟩
  · rintro ⟨identity, member, equality⟩
    exact ⟨identity, List.mem_eraseDups.mp member, equality.symm⟩

/-- The actual executable copier's variable support is exactly the
suffix-renamed image of the independently related clause support. -/
theorem freshenResolutionClause_support_exact
    {reference : LocalClause} {executable : PLeaTTa.Clause}
    (support : ClauseVariableSupportAgrees reference executable)
    (argsv args : List Atom) (result : Atom)
    (rest : List PLeaTTa.Goal) (binding : Metta.Subst)
    (query : Atom) (seed barrier : Nat) (target : String) :
    target ∈ resolutionClauseVars
        (freshenResolutionClause argsv args result rest binding query
          seed barrier executable) ↔
      ∃ identity, identity ∈ reference.variables ∧
        target = logicVarExecutableName identity ++
          resolutionFreshSuffix argsv result rest binding query seed := by
  rw [freshenResolutionClause_vars_exact, List.mem_map]
  constructor
  · rintro ⟨name, member, equality⟩
    obtain ⟨identity, identityMember, nameShape⟩ :=
      (support name).mp member
    subst name
    exact ⟨identity, identityMember, equality.symm⟩
  · rintro ⟨identity, identityMember, targetShape⟩
    refine ⟨logicVarExecutableName identity, ?_, ?_⟩
    · exact (support _).mpr ⟨identity, identityMember, rfl⟩
    · exact targetShape.symm

/-- One arbitrary finite clause-variable support can be reconciled across
the independent per-variable allocator and the executable per-clause suffix
allocator by an explicit positional alpha bijection.

This is the decisive counter-currency check for the state bridge: the theorem
does not equate the counters, and its encoding premise is falsified by the
known source/generated spelling collision. -/
theorem freshenClause_alpha_agrees
    (clause : LocalClause) (freshSeed : Nat) (suffix : String)
    (encoding : EncodingInjectiveOn clause.variables) :
    RuntimeAlpha
      (referenceFreshTargets
        (clause.freshCopy freshSeed).firstFresh clause.variables)
      (executableFreshTargets suffix clause.variables) := by
  constructor
  · rw [referenceFreshTargets_length]
    simp [executableFreshTargets]
  · exact referenceFreshTargets_nodup _ _
  · exact executableFreshTargets_nodup
      (LocalClause.variables_nodup clause) encoding suffix

/-- The alpha theorem is tied to the actual independent freshening
substitution, not merely to an invented list of fresh names. -/
theorem freshenClause_alpha_reference_projection
    (clause : LocalClause) (freshSeed : Nat) :
    ((clause.freshCopy freshSeed).freshSubstitution.map fun binding =>
      match binding.2 with
      | .variable identity => identity
      | _ => .anonymous 0) =
      referenceFreshTargets
        (clause.freshCopy freshSeed).firstFresh clause.variables := by
  exact buildFreshening_targets _ _

/-- The actual independent and executable clause copiers produce
alpha-related output-last head payloads.  This theorem reaches the terms
the resolver unifies, rather than stopping at occurrence/support equality. -/
theorem freshenClause_head_alpha_agrees
    {reference : LocalClause} {executablePredicate : String}
    {executable : PLeaTTa.Clause}
    (base : LocalClauseAgrees reference
      (executablePredicate, executable))
    (freshSeed : Nat) (argsv args : List Atom) (result : Atom)
    (rest : List PLeaTTa.Goal) (binding : Metta.Subst)
    (query : Atom) (seed barrier : Nat) :
    LocalClauseHeadAlphaAgrees
      (RuntimeAlpha.graph
        (referenceFreshTargets
          (reference.freshCopy freshSeed).firstFresh reference.variables)
        (executableFreshTargets
          (resolutionFreshSuffix argsv result rest binding query seed)
          reference.variables))
      (reference.freshCopy freshSeed).clause
      (executablePredicate,
        freshenResolutionClause argsv args result rest binding query
          seed barrier executable) := by
  rcases base.outputLast with
    ⟨referenceParameters, referenceResult, arguments,
      parameters, resultAgreement⟩
  have argumentsSupported := LocalClause.arguments_supported reference
  rw [arguments, termsVariablesIn_append] at argumentsSupported
  have resultSupported :
      termVariablesIn reference.variables referenceResult := by
    simpa [termsVariablesIn] using argumentsSupported.2
  let suffix :=
    resolutionFreshSuffix argsv result rest binding query seed
  let alpha :=
    RuntimeAlpha.graph
      (referenceFreshTargets
        (reference.freshCopy freshSeed).firstFresh reference.variables)
      (executableFreshTargets suffix reference.variables)
  have variableAgreement :
      ∀ identity, identity ∈ reference.variables →
        ∃ target,
          (reference.freshCopy freshSeed).freshSubstitution.applyTerm
              (.variable identity) =
            .variable target ∧
          (target, logicVarExecutableName identity ++ suffix) ∈ alpha := by
    intro identity member
    exact LocalClause.freshCopy_alpha_variable
      reference freshSeed suffix member
  constructor
  · simpa only [LocalClause.freshCopy_predicate] using base.predicate
  · refine ⟨
      (reference.freshCopy freshSeed).freshSubstitution.applyTerms
        referenceParameters,
      (reference.freshCopy freshSeed).freshSubstitution.applyTerm
        referenceResult,
      ?_, ?_, ?_⟩
    · change
        (reference.freshCopy freshSeed).freshSubstitution.applyTerms
            reference.arguments =
          (reference.freshCopy freshSeed).freshSubstitution.applyTerms
              referenceParameters ++
            [(reference.freshCopy freshSeed).freshSubstitution.applyTerm
              referenceResult]
      rw [arguments, applyTerms_append]
      simp
    · have transported :=
        termsAgree_alpha_freshen variableAgreement parameters
          argumentsSupported.1
      simpa [alpha, suffix, freshenResolutionClause] using transported
    · have transported :=
        termAgrees_alpha_freshen variableAgreement resultAgreement
          resultSupported
      simpa [alpha, suffix, freshenResolutionClause] using transported

/-- One-clause freshening witness for the proved layer.  Both outputs are the
actual independent/executable copier results; their output-last head payloads
are structurally related under an explicit finite alpha bijection, and their
complete head/body variable-occurrence streams use the same original support.
Alpha-preservation for the executable body-goal constructors remains a
separate composition obligation.

Finite support is an explicit field of `LocalClauseAgrees`; it is not inferred
from raw occurrence equality because some compiler representations store a
shared variable fewer times without changing its identity or sharing. -/
structure FreshenedClauseAlphaAgrees
    (reference : LocalClause) (executablePredicate : String)
    (executable : PLeaTTa.Clause) (freshSeed : Nat)
    (argsv args : List Atom) (result : Atom)
    (rest : List PLeaTTa.Goal) (binding : Metta.Subst)
    (query : Atom) (seed barrier : Nat) : Prop where
  base :
    LocalClauseAgrees reference (executablePredicate, executable)
  alpha :
    RuntimeAlpha
      (referenceFreshTargets
        (reference.freshCopy freshSeed).firstFresh reference.variables)
      (executableFreshTargets
        (resolutionFreshSuffix argsv result rest binding query seed)
        reference.variables)
  headPayload :
    LocalClauseHeadAlphaAgrees
      (RuntimeAlpha.graph
        (referenceFreshTargets
          (reference.freshCopy freshSeed).firstFresh reference.variables)
        (executableFreshTargets
          (resolutionFreshSuffix argsv result rest binding query seed)
          reference.variables))
      (reference.freshCopy freshSeed).clause
      (executablePredicate,
        freshenResolutionClause argsv args result rest binding query
          seed barrier executable)
  referenceSources :
    (reference.freshCopy freshSeed).freshSubstitution.map Prod.fst =
      reference.variables
  referenceTargets :
    ((reference.freshCopy freshSeed).freshSubstitution.map fun entry =>
      match entry.2 with
      | .variable identity => identity
      | _ => .anonymous 0) =
      referenceFreshTargets
        (reference.freshCopy freshSeed).firstFresh reference.variables
  referenceTargetShape :
    ∀ source target,
      (source, target) ∈
          (reference.freshCopy freshSeed).freshSubstitution →
        ∃ index, target = .variable (.generated index) ∧
          (reference.freshCopy freshSeed).firstFresh ≤ index ∧
          index < (reference.freshCopy freshSeed).nextFresh
  referenceArguments :
    (reference.freshCopy freshSeed).clause.arguments =
      (reference.freshCopy freshSeed).freshSubstitution.applyTerms
        reference.arguments
  referenceBody :
    (reference.freshCopy freshSeed).clause.body =
      (reference.freshCopy freshSeed).freshSubstitution.applyGoals
        reference.body
  executableOccurrences :
    resolutionClauseVars
        (freshenResolutionClause argsv args result rest binding query
          seed barrier executable) =
      (resolutionClauseVars executable).map fun name =>
        name ++ resolutionFreshSuffix argsv result rest binding query seed
  executableSupport :
    ∀ target,
      target ∈ resolutionClauseVars
          (freshenResolutionClause argsv args result rest binding query
            seed barrier executable) ↔
        ∃ identity, identity ∈ reference.variables ∧
          target = logicVarExecutableName identity ++
            resolutionFreshSuffix argsv result rest binding query seed

/-- The two real clause copiers satisfy `FreshenedClauseAlphaAgrees` for every
base clause whose executable encoding has the independently stated occurrence
correspondence and finite spelling-injectivity certificate. -/
theorem freshenClause_actual_alpha_agrees
    {reference : LocalClause} {executablePredicate : String}
    {executable : PLeaTTa.Clause}
    (base : LocalClauseAgrees reference
      (executablePredicate, executable))
    (encoding : EncodingInjectiveOn reference.variables)
    (freshSeed : Nat) (argsv args : List Atom) (result : Atom)
    (rest : List PLeaTTa.Goal) (binding : Metta.Subst)
    (query : Atom) (seed barrier : Nat) :
    FreshenedClauseAlphaAgrees reference executablePredicate executable
      freshSeed argsv args result rest binding query seed barrier := by
  constructor
  · exact base
  · exact freshenClause_alpha_agrees reference freshSeed _ encoding
  · exact freshenClause_head_alpha_agrees base freshSeed argsv args result
      rest binding query seed barrier
  · exact buildFreshening_sources _ _
  · exact freshenClause_alpha_reference_projection reference freshSeed
  · intro source target member
    obtain ⟨index, targetShape, lower, upper⟩ :=
      buildFreshening_target_generated
        (reference.freshCopy freshSeed).firstFresh reference.variables member
    exact ⟨index, targetShape, lower, by
      simpa only [LocalClause.freshCopy_next] using upper⟩
  · rfl
  · rfl
  · exact freshenResolutionClause_vars_exact _ _ _ _ _ _ _ _ _
  · exact freshenResolutionClause_support_exact base.support
      argsv args result rest binding query seed barrier

/-! ### Anti-vacuity: the fresh counters cannot be identified numerically -/

private def twoVariableLocalClause : LocalClause :=
  { predicate := "p"
    arguments :=
      [.variable (.source "left"), .variable (.source "right")]
    body := [] }

private def twoVariableExecutableClause : PLeaTTa.Clause :=
  { params := [.var "left"]
    result := .var "right"
    body := [] }

private def collidingLocalClause (index : Nat) : LocalClause :=
  { predicate := "collision"
    arguments :=
      [.variable (.source (generatedExecutableName index)),
       .variable (.generated index)]
    body := [] }

/-- The payload relation is stricter than support cardinality: an executable
variable with the wrong alpha partner is rejected even though both sides
still contain exactly one variable. -/
theorem wrong_alpha_head_name_is_rejected :
    ¬ AlphaTermAgrees [(.generated 0, "right#r0")]
      (.variable (.generated 0)) (.var "wrong#r0") := by
  intro agreement
  cases agreement
  simp_all

/-- The alpha theorem's encoding premise excludes a real parser-permitted
clause: a source variable can spell exactly like a compiler-generated one.
Thus `freshenClause_alpha_agrees` cannot be made unconditional without
changing the executable variable representation. -/
theorem colliding_clause_has_no_injective_encoding (index : Nat) :
    ¬ EncodingInjectiveOn (collidingLocalClause index).variables := by
  change ¬ EncodingInjectiveOn
    [.source (generatedExecutableName index), .generated index]
  exact source_generated_pair_not_injective index

/-- One two-variable clause consumes two independent generated identities but
one executable clause suffix.  This concrete witness rules out both
definitionally identifying the frontiers and treating the independent
high-water as bounded by the executable counter. -/
theorem fresh_frontiers_have_different_units :
    (twoVariableLocalClause.freshCopy 0).nextFresh = 2 ∧
      (resolveAlts [twoVariableExecutableClause]
        [.var "caller"] [.var "caller"] (.var "result") [] []
        (.var "query") 1 0).2 = 1 := by
  constructor
  · rfl
  · simp [resolveAlts, twoVariableExecutableClause, prologMatchCompat,
      prologMatchCompatList, freshenResolutionClause,
      resolutionFreshSuffix]

end PLeaTTa.PrologStateBridge
