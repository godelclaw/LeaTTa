-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologStateBridge
Purpose: Faithful state-side bridge between the independent local-Prolog
  semantics and the fine-grained executable lane.
Trusted boundary: none
Main exports: LocalClauseAgrees, DatabaseRelatesWorld,
  SessionRelatesPersistent, RuntimeAlpha, FreshenedClauseAlphaAgrees
-/
import PLeaTTa.Proofs.CompilerAdequacy
import PLeaTTa.Proofs.DemandDrivenStep
import PLeaTTa.Proofs.OpenBindingAgreement
import PLeaTTa.Proofs.ResolutionCounter
import PLeaTTa.PeTTaSpec.PrologGoalSemantics

namespace PLeaTTa.PrologStateBridge

open Metta (Atom)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Resolver
open PeTTaSpec.PrologCore.GoalSemantics
open CompilerAdequacy
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

/-- Every creation/erasure stamp in a reachable history has already occurred
at the database's current generation.  This excludes forged future erasure
stamps and makes the current logical-update view exactly the unerased
occurrences. -/
def DatabaseGenerationClosed (database : Database) : Prop :=
  ∀ entry ∈ database.history,
    entry.created ≤ database.generation ∧
      ∀ erased, entry.erased = some erased →
        erased ≤ database.generation

/-- The executable world's canonical live clause list is exactly the current
projection of the independent logical-update history.  Derived executable
index coherence is included because call dispatch may use the index rather
than the canonical list. -/
structure DatabaseRelatesWorld (database : Database) (world : PWorld) : Prop where
  generationClosed : DatabaseGenerationClosed database
  liveClauses :
    List.Forall₂ VersionedClauseAgrees
      (currentVisibleEntries database) world.progClauses
  clauseIndex : world.ClauseIndexCoherent

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
  refine ⟨agreement.generationClosed, ?_, world.reindexClauses_coherent⟩
  simpa [PWorld.reindexClauses] using agreement.liveClauses

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
  have executableClauses :
      (world.appendProgClause executable).progClauses =
        world.progClauses ++ [executable] := by
    unfold PWorld.appendProgClause
    split <;> rfl
  refine ⟨agreement.generationClosed.assertz reference, ?_,
    world.appendProgClause_coherent executable agreement.clauseIndex⟩
  rw [currentVisibleEntries_assertz agreement.generationClosed reference,
    executableClauses]
  have newClause :
      VersionedClauseAgrees (database.allocate reference) executable := by
    simpa [VersionedClauseAgrees, Database.allocate] using clause
  exact forall₂_append_singleton agreement.liveClauses newClause

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
  refine ⟨agreement.generationClosed.asserta reference, ?_,
    world.replaceProgClauses_coherent _ agreement.clauseIndex⟩
  rw [currentVisibleEntries_asserta agreement.generationClosed reference,
    PWorld.replaceProgClauses_progClauses]
  exact .cons clause agreement.liveClauses

/-- Empty independent and executable stores agree for every frontier relation
that relates their zero high-waters. -/
theorem empty_session_relates
    (freshFrontier : FreshFrontierRelation)
    (zero : freshFrontier 0 0) :
    SessionRelatesPersistent freshFrontier
      ({} : Session) ({ world := {}, counter := 0 } : Persistent) := by
  constructor
  · constructor
    · intro entry member
      simp [Database.empty] at member
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

/-- Full one-clause freshening witness.  Both outputs are the actual
independent/executable copier results; their variable-occurrence streams use
the same original support, and the fresh-name graph is an explicit finite
bijection.

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
  · simp [resolveAlts, twoVariableExecutableClause, matchCompat,
      matchCompatList, freshenResolutionClause, resolutionFreshSuffix]

end PLeaTTa.PrologStateBridge
