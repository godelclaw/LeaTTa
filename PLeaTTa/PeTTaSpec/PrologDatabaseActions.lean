-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.PeTTaSpec.PrologDatabaseActions
Purpose: Independent dynamic-clause actions and first-match retract scanning.
Trusted boundary: none
Main exports:
  DatabaseActionKind, recognizeDatabaseAction, decodePredicateClause,
  RetractScan, DatabaseMutation, DatabaseChronology
-/
import PLeaTTa.PeTTaSpec.PrologResolver

namespace PLeaTTa.PeTTaSpec.PrologCore.DatabaseActions

open OpenSubstitution
open Canonical
open Resolver

/-!
Pinned PeTTa exposes dynamic Prolog clauses through three ordinary predicate
calls:

* `assertzPredicate(G, true) :- assertz(G)`;
* `assertaPredicate(G, true) :- asserta(G)`;
* `retractPredicate(G, true) :- retract(G), !`, with a `false` fallback.

The calls remain call-shaped in the independent language.  This module only
recognizes their exact two-argument shape and gives their source-side data
semantics.  No executable `Atom`, `PWorld`, `Clause`, or dispatch function
appears here.

Retraction is intentionally not an existential choice of a convenient
occurrence.  `RetractScan` inspects the current live occurrence list from
left to right, standardizes every candidate apart, and stops at the first
candidate for which the canonical ordered finite-tree MGU exists.  The scan
is functional, so a later adequacy proof cannot select whichever occurrence
happens to match the executable result.

[SPEC metta.pl:277-280]
[SPEC SWI-Prolog manual 4.14.1.1, logical update view]
-/

/-- The three source-level dynamic predicate operations. -/
inductive DatabaseActionKind where
  | asserta
  | assertz
  | retract
deriving Repr, Inhabited, DecidableEq

/-- Exact call payload selected by the total recognizer. -/
structure DatabaseActionCall where
  kind : DatabaseActionKind
  payload : Term
  result : Term
deriving Repr, Inhabited

/-- Recognize only the exact source predicate names and arities.  A malformed
arity remains an ordinary call rather than being silently reinterpreted as an
effect. -/
def recognizeDatabaseAction (predicate : String) (arguments : List Term) :
    Option DatabaseActionCall :=
  match predicate, arguments with
  | "assertaPredicate", [payload, result] =>
      some { kind := .asserta, payload := payload, result := result }
  | "assertzPredicate", [payload, result] =>
      some { kind := .assertz, payload := payload, result := result }
  | "retractPredicate", [payload, result] =>
      some { kind := .retract, payload := payload, result := result }
  | _, _ => none

/-- Proposition-valued view used by transition premises. -/
def DatabaseActionCall.Recognized (predicate : String)
    (arguments : List Term) (action : DatabaseActionCall) : Prop :=
  recognizeDatabaseAction predicate arguments = some action

theorem DatabaseActionCall.Recognized.deterministic
    {predicate : String} {arguments : List Term}
    {first second : DatabaseActionCall}
    (one : first.Recognized predicate arguments)
    (two : second.Recognized predicate arguments) :
    first = second := by
  rw [DatabaseActionCall.Recognized, one] at two
  exact Option.some.inj two

@[simp] theorem recognizeDatabaseAction_throw (ball : Term) :
    recognizeDatabaseAction "throw" [ball] = none := rfl

/-- A familiar operation name at the wrong arity is not silently promoted to
a database effect. -/
theorem malformed_assertz_is_not_database_action (payload : Term) :
    recognizeDatabaseAction "assertzPredicate" [payload] = none := rfl

/-- Similar-looking ordinary predicates remain ordinary calls. -/
theorem unrecognized_assert_is_not_database_action
    (payload result : Term) :
    recognizeDatabaseAction "assertPredicate" [payload, result] = none := rfl

/-- Read the output-last function-convention shape `p(inputs..., output)`. -/
def predicateCallParts? : Term →
    Option (String × List Term × Term)
  | .compound predicate arguments =>
      match arguments.reverse with
      | [] => none
      | output :: reversedInputs =>
          some (predicate, reversedInputs.reverse, output)
  | _ => none

/-- Translate the right-hand value of source `is/2` into the independent
relation convention. -/
def decodePredicateValueGoals (target : Term) : Term → List Goal
  | .compound predicate inputs =>
      [.call predicate (inputs ++ [target])]
  | value => [.unify target value]

/-- Decode the supported finite definite-clause body: ordered conjunction,
`is/2`, and output-last predicate calls. -/
def decodePredicateBody? : Term → Option (List Goal)
  | .compound "," [left, right] => do
      let leftGoals ← decodePredicateBody? left
      let rightGoals ← decodePredicateBody? right
      pure (leftGoals ++ rightGoals)
  | .compound "is" [target, value] =>
      some (decodePredicateValueGoals target value)
  | call => do
      let (predicate, inputs, output) ← predicateCallParts? call
      pure [.call predicate (inputs ++ [output])]
termination_by body => body

/-- Decode the actual Prolog term produced by PeTTa's `Predicate/2`, not
PLeaTTa's private chain wrapper. -/
def decodePredicateClause : Term → Option LocalClause
  | .compound ":-" [head, body] => do
      let (predicate, inputs, output) ← predicateCallParts? head
      let goals ← decodePredicateBody? body
      pure
        { predicate := predicate
          arguments := inputs ++ [output]
          body := goals }
  | fact => do
      let (predicate, inputs, output) ← predicateCallParts? fact
      pure
        { predicate := predicate
          arguments := inputs ++ [output]
          body := [] }

/-- Declarative name for the deterministic decoder equation. -/
def PredicateClauseDenotes (payload : Term) (clause : LocalClause) : Prop :=
  decodePredicateClause payload = some clause

theorem PredicateClauseDenotes.deterministic
    {payload : Term} {first second : LocalClause}
    (one : PredicateClauseDenotes payload first)
    (two : PredicateClauseDenotes payload second) :
    first = second := by
  rw [PredicateClauseDenotes, one] at two
  exact Option.some.inj two

mutual

/-- Injective-tag syntax encoding used only to feed a whole source goal to
the canonical first-order MGU. -/
def goalSyntaxTerm : Goal → Term
  | .truth => .compound "$goal.truth" []
  | .fail => .compound "$goal.fail" []
  | .unify left right => .compound "$goal.unify" [left, right]
  | .identical left right => .compound "$goal.identical" [left, right]
  | .call predicate arguments =>
      .compound "$goal.call"
        [.atom predicate, .list arguments none]
  | .conjunction goals =>
      .compound "$goal.conjunction"
        [.list (goalsSyntaxTerms goals) none]
  | .disjunction branches =>
      .compound "$goal.disjunction"
        [.list (goalsSyntaxTerms branches) none]
  | .cut => .compound "$goal.cut" []
  | .ifThenElse condition thenBranch elseBranch =>
      .compound "$goal.ifThenElse"
        [goalSyntaxTerm condition, goalSyntaxTerm thenBranch,
          goalSyntaxTerm elseBranch]
  | .softCut condition thenBranch elseBranch =>
      .compound "$goal.softCut"
        [goalSyntaxTerm condition, goalSyntaxTerm thenBranch,
          goalSyntaxTerm elseBranch]
  | .negation goal =>
      .compound "$goal.negation" [goalSyntaxTerm goal]
  | .once goal =>
      .compound "$goal.once" [goalSyntaxTerm goal]
  | .findall template goal output =>
      .compound "$goal.findall" [template, goalSyntaxTerm goal, output]
  | .catch goal exception handler =>
      .compound "$goal.catch"
        [goalSyntaxTerm goal, exception, goalSyntaxTerm handler]
  | .transaction goal =>
      .compound "$goal.transaction" [goalSyntaxTerm goal]
  | .withMutex mutex goal =>
      .compound "$goal.withMutex" [mutex, goalSyntaxTerm goal]
  | .forall generator test =>
      .compound "$goal.forall"
        [goalSyntaxTerm generator, goalSyntaxTerm test]

/-- Ordered encoding of a goal list. -/
def goalsSyntaxTerms : List Goal → List Term
  | [] => []
  | goal :: goals => goalSyntaxTerm goal :: goalsSyntaxTerms goals

end

/-- Encode a complete clause, including body control structure, as one
first-order term. -/
def clauseSyntaxTerm (clause : LocalClause) : Term :=
  .compound "$clause"
    [.atom clause.predicate,
      .list clause.arguments none,
      .list (goalsSyntaxTerms clause.body) none]

/-- One ordered scan result.  `nextFresh` includes every candidate copy
examined before the committed result or exhaustion. -/
inductive RetractOutcome where
  | matched (entry : VersionedClause) (extension : Substitution)
      (nextFresh : Nat)
  | missing (nextFresh : Nat)
deriving Repr, Inhabited

def RetractOutcome.nextFresh : RetractOutcome → Nat
  | .matched _ _ nextFresh | .missing nextFresh => nextFresh

/-- Source-order, first-unifying retract scan over an already-frozen live
occurrence list. -/
inductive RetractScan (pattern : LocalClause) :
    Nat → List VersionedClause → RetractOutcome → Prop where
  | exhausted (freshSeed : Nat) :
      RetractScan pattern freshSeed [] (.missing freshSeed)
  | matched (freshSeed : Nat) (entry : VersionedClause)
      (rest : List VersionedClause) (extension : Substitution)
      (computed :
        ComputesDenotationalMgu
          [(clauseSyntaxTerm pattern,
            clauseSyntaxTerm (entry.clause.freshCopy freshSeed).clause)]
          extension) :
      RetractScan pattern freshSeed (entry :: rest)
        (.matched entry extension
          (entry.clause.freshCopy freshSeed).nextFresh)
  | skipped (freshSeed : Nat) (entry : VersionedClause)
      (rest : List VersionedClause) (outcome : RetractOutcome)
      (clash :
        ¬ ∃ extension,
          ComputesDenotationalMgu
            [(clauseSyntaxTerm pattern,
              clauseSyntaxTerm (entry.clause.freshCopy freshSeed).clause)]
            extension)
      (tail :
        RetractScan pattern
          (entry.clause.freshCopy freshSeed).nextFresh rest outcome) :
      RetractScan pattern freshSeed (entry :: rest) outcome

namespace RetractScan

/-- Every finite occurrence list has one scan result. -/
theorem exists_scan (pattern : LocalClause) :
    ∀ (freshSeed : Nat) (entries : List VersionedClause),
      ∃ outcome, RetractScan pattern freshSeed entries outcome
  | freshSeed, [] => ⟨.missing freshSeed, .exhausted freshSeed⟩
  | freshSeed, entry :: rest => by
      classical
      by_cases computes :
          ∃ extension,
            ComputesDenotationalMgu
              [(clauseSyntaxTerm pattern,
                clauseSyntaxTerm
                  (entry.clause.freshCopy freshSeed).clause)]
              extension
      · let extension := Classical.choose computes
        exact
          ⟨.matched entry extension
              (entry.clause.freshCopy freshSeed).nextFresh,
            .matched freshSeed entry rest extension
              (Classical.choose_spec computes)⟩
      · rcases exists_scan pattern
          (entry.clause.freshCopy freshSeed).nextFresh rest with
        ⟨outcome, tail⟩
        exact ⟨outcome, .skipped freshSeed entry rest outcome computes tail⟩

/-- The ordered scan cannot choose a later matching occurrence or a different
MGU spelling. -/
theorem deterministic {pattern : LocalClause} {freshSeed : Nat}
    {entries : List VersionedClause} {first second : RetractOutcome}
    (one : RetractScan pattern freshSeed entries first)
    (two : RetractScan pattern freshSeed entries second) :
    first = second := by
  induction one generalizing second with
  | exhausted =>
      cases two
      rfl
  | matched freshSeed entry rest extension computed =>
      cases two with
      | matched _ _ _ other otherComputed =>
          have same :=
            ComputesDenotationalMgu.unique computed otherComputed
          subst other
          rfl
      | skipped _ _ _ _ clash _ =>
          exact False.elim (clash ⟨extension, computed⟩)
  | skipped freshSeed entry rest outcome clash tail inductionHypothesis =>
      cases two with
      | matched _ _ _ extension computed =>
          exact False.elim (clash ⟨extension, computed⟩)
      | skipped _ _ _ other _ otherTail =>
          exact inductionHypothesis otherTail

private theorem freshCopy_next_ge (clause : LocalClause) (freshSeed : Nat) :
    freshSeed ≤ (clause.freshCopy freshSeed).nextFresh := by
  apply Nat.le_trans (clause.freshCopy_first_ge_seed freshSeed)
  rw [clause.freshCopy_next]
  exact Nat.le_add_right _ _

/-- Scanning never restores a stale source fresh-name high-water. -/
theorem nextFresh_mono {pattern : LocalClause} {freshSeed : Nat}
    {entries : List VersionedClause} {outcome : RetractOutcome}
    (scan : RetractScan pattern freshSeed entries outcome) :
    freshSeed ≤ outcome.nextFresh := by
  induction scan with
  | exhausted => exact Nat.le_refl _
  | matched freshSeed entry =>
      exact freshCopy_next_ge entry.clause freshSeed
  | skipped freshSeed entry rest outcome clash tail inductionHypothesis =>
      exact Nat.le_trans (freshCopy_next_ge entry.clause freshSeed)
        inductionHypothesis

/-- A matched outcome names an occurrence from the scanned live list. -/
theorem matched_mem_aux {pattern : LocalClause} {freshSeed : Nat}
    {entries : List VersionedClause} {outcome : RetractOutcome}
    (scan : RetractScan pattern freshSeed entries outcome) :
    ∀ {entry : VersionedClause} {extension : Substitution}
        {nextFresh : Nat},
      outcome = .matched entry extension nextFresh → entry ∈ entries := by
  induction scan with
  | exhausted =>
      intro entry extension nextFresh equality
      cases equality
  | matched =>
      intro entry extension nextFresh equality
      cases equality
      simp
  | skipped freshSeed head rest outcome clash tail inductionHypothesis =>
      intro entry extension nextFresh equality
      exact List.mem_cons_of_mem head (inductionHypothesis equality)

/-- A matched occurrence comes from the scanned live list. -/
theorem matched_mem {pattern : LocalClause} {freshSeed : Nat}
    {entries : List VersionedClause} {entry : VersionedClause}
    {extension : Substitution} {nextFresh : Nat}
    (scan :
      RetractScan pattern freshSeed entries
        (.matched entry extension nextFresh)) :
    entry ∈ entries :=
  matched_mem_aux scan rfl

end RetractScan

/-- Current live occurrence list in exact database order. -/
def currentEntries (database : Database) : List VersionedClause :=
  database.history.filter fun entry =>
    entry.visibleAt database.generation

/-- Every timestamp in a reachable independent history has already occurred.
In particular, a currently visible occurrence cannot carry a forged erasure
stamp from a future generation. -/
def DatabaseGenerationClosed (database : Database) : Prop :=
  ∀ entry ∈ database.history,
    entry.created ≤ database.generation ∧
      ∀ erased, entry.erased = some erased →
        erased ≤ database.generation

namespace DatabaseGenerationClosed

theorem empty : DatabaseGenerationClosed Database.empty := by
  simp [DatabaseGenerationClosed, Database.empty]

theorem asserta {database : Database}
    (closed : DatabaseGenerationClosed database) (clause : LocalClause) :
    DatabaseGenerationClosed (database.asserta clause) := by
  intro entry member
  rw [Database.asserta] at member ⊢
  rcases List.mem_cons.mp member with new | old
  · subst entry
    exact ⟨Nat.le_refl _, by simp [Database.allocate]⟩
  · have bounds := closed entry old
    exact
      ⟨Nat.le_trans bounds.1 (Nat.le_add_right _ _),
        fun erased erasedEq =>
          Nat.le_trans (bounds.2 erased erasedEq)
            (Nat.le_add_right _ _)⟩

theorem assertz {database : Database}
    (closed : DatabaseGenerationClosed database) (clause : LocalClause) :
    DatabaseGenerationClosed (database.assertz clause) := by
  intro entry member
  rw [Database.assertz] at member ⊢
  rcases List.mem_append.mp member with old | new
  · have bounds := closed entry old
    exact
      ⟨Nat.le_trans bounds.1 (Nat.le_add_right _ _),
        fun erased erasedEq =>
          Nat.le_trans (bounds.2 erased erasedEq)
            (Nat.le_add_right _ _)⟩
  · simp only [List.mem_singleton] at new
    subst entry
    exact ⟨Nat.le_refl _, by simp [Database.allocate]⟩

private theorem history_closed_succ
    {generation : Generation} {history : List VersionedClause}
    (closed :
      ∀ entry ∈ history,
        entry.created ≤ generation ∧
          ∀ erased, entry.erased = some erased → erased ≤ generation) :
    ∀ entry ∈ history,
      entry.created ≤ generation + 1 ∧
        ∀ erased, entry.erased = some erased → erased ≤ generation + 1 := by
  intro entry member
  have bounds := closed entry member
  exact
    ⟨Nat.le_trans bounds.1 (Nat.le_add_right _ _),
      fun erased erasedEq =>
        Nat.le_trans (bounds.2 erased erasedEq) (Nat.le_add_right _ _)⟩

private theorem retireFirst_preserves_closed
    {generation : Generation} {id : ClauseId}
    {before after : List VersionedClause}
    (closed :
      ∀ entry ∈ before,
        entry.created ≤ generation ∧
          ∀ erased, entry.erased = some erased → erased ≤ generation)
    (retired : retireFirst (generation + 1) id before = some after) :
    ∀ entry ∈ after,
      entry.created ≤ generation + 1 ∧
        ∀ erased, entry.erased = some erased → erased ≤ generation + 1 := by
  induction before generalizing after with
  | nil =>
      simp [retireFirst] at retired
  | cons head rest inductionHypothesis =>
      have headClosed := closed head (by simp)
      have restClosed :
          ∀ entry ∈ rest,
            entry.created ≤ generation ∧
              ∀ erased, entry.erased = some erased →
                erased ≤ generation := by
        intro entry member
        exact closed entry (by simp [member])
      by_cases hit : head.id = id ∧ head.erased = none
      · simp only [retireFirst, hit, and_self, if_true,
          Option.some.injEq] at retired
        subst after
        intro entry member
        rcases List.mem_cons.mp member with current | tail
        · subst entry
          exact
            ⟨Nat.le_trans headClosed.1 (Nat.le_add_right _ _), by
              intro erased erasedEq
              exact Nat.le_of_eq (Option.some.inj erasedEq).symm⟩
        · exact history_closed_succ restClosed entry tail
      · simp only [retireFirst, hit, if_false] at retired
        cases tailEq : retireFirst (generation + 1) id rest with
        | none =>
            simp [tailEq] at retired
        | some retiredTail =>
            have afterEq : after = head :: retiredTail := by
              simpa [tailEq] using retired.symm
            subst after
            intro entry member
            rcases List.mem_cons.mp member with current | tail
            · subst entry
              exact history_closed_succ closed head (by simp)
            · exact
                inductionHypothesis restClosed tailEq entry tail

theorem retractId {database after : Database}
    (closed : DatabaseGenerationClosed database) {id : ClauseId}
    (retracted : database.retractId id = some after) :
    DatabaseGenerationClosed after := by
  cases retiredHistoryEq :
      retireFirst (database.generation + 1) id database.history with
  | none =>
      simp [Database.retractId, retiredHistoryEq] at retracted
  | some retiredHistory =>
      have afterEq :
          after =
            { database with
              generation := database.generation + 1
              history := retiredHistory } := by
        have someEq :
            some
                { database with
                  generation := database.generation + 1
                  history := retiredHistory } =
              some after := by
          simpa [Database.retractId, retiredHistoryEq] using retracted
        exact (Option.some.inj someEq).symm
      subst after
      exact retireFirst_preserves_closed closed retiredHistoryEq

end DatabaseGenerationClosed

/-- Stable occurrence identities in a reachable database are unique and every
allocated identity lies strictly below the next allocator value.  Both halves
are load-bearing: uniqueness makes `retractId` resolve the occurrence selected
by `RetractScan`, while the upper bound makes fresh assertion preserve
uniqueness. -/
def DatabaseIdsClosed (database : Database) : Prop :=
  let ids := database.history.map fun entry => entry.id
  ids.Nodup ∧ ∀ id ∈ ids, id < database.nextId

namespace DatabaseIdsClosed

theorem empty : DatabaseIdsClosed Database.empty := by
  simp [DatabaseIdsClosed, Database.empty]

theorem asserta {database : Database}
    (closed : DatabaseIdsClosed database) (clause : LocalClause) :
    DatabaseIdsClosed (database.asserta clause) := by
  rcases closed with ⟨nodup, below⟩
  constructor
  · simp only [Database.asserta, List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup⟩
    intro member
    obtain ⟨entry, entryMember, idEquality⟩ := List.mem_map.mp member
    have bound := below entry.id
      (List.mem_map.mpr ⟨entry, entryMember, rfl⟩)
    exact (Nat.ne_of_lt bound) idEquality
  · intro id member
    simp only [Database.asserta, List.map_cons, List.mem_cons] at member ⊢
    rcases member with current | old
    · subst id
      exact Nat.lt_succ_self _
    · exact Nat.lt_trans (below id old) (Nat.lt_succ_self _)

theorem assertz {database : Database}
    (closed : DatabaseIdsClosed database) (clause : LocalClause) :
    DatabaseIdsClosed (database.assertz clause) := by
  rcases closed with ⟨nodup, below⟩
  constructor
  · simp only [Database.assertz, List.map_append, List.map_singleton]
    apply List.nodup_append.mpr
    refine ⟨nodup, by simp, ?_⟩
    intro oldId oldMember newId newMember equality
    simp only [List.mem_singleton] at newMember
    subst newId
    have bound := below oldId oldMember
    exact (Nat.ne_of_lt bound) (by assumption)
  · intro id member
    simp only [Database.assertz, List.map_append, List.map_singleton,
      List.mem_append, List.mem_singleton] at member ⊢
    rcases member with old | current
    · exact Nat.lt_trans (below id old) (Nat.lt_succ_self _)
    · subst id
      exact Nat.lt_succ_self _

private theorem retireFirst_ids
    {generation : Generation} {id : ClauseId}
    {before after : List VersionedClause}
    (retired : retireFirst generation id before = some after) :
    after.map (fun entry => entry.id) =
      before.map (fun entry => entry.id) := by
  induction before generalizing after with
  | nil =>
      simp [retireFirst] at retired
  | cons head rest inductionHypothesis =>
      by_cases hit : head.id = id ∧ head.erased = none
      · simp only [retireFirst, hit, and_self, if_true,
          Option.some.injEq] at retired
        subst after
        simp [hit.1]
      · cases tailEq : retireFirst generation id rest with
        | none =>
            simp [retireFirst, hit, tailEq] at retired
        | some retiredTail =>
            have afterEq : after = head :: retiredTail := by
              simpa [retireFirst, hit, tailEq] using retired.symm
            subst after
            simp only [List.map_cons, List.cons.injEq, true_and]
            exact inductionHypothesis tailEq

theorem retractId {database after : Database}
    (closed : DatabaseIdsClosed database) {id : ClauseId}
    (retracted : database.retractId id = some after) :
    DatabaseIdsClosed after := by
  cases retiredHistoryEq :
      retireFirst (database.generation + 1) id database.history with
  | none =>
      simp [Database.retractId, retiredHistoryEq] at retracted
  | some retiredHistory =>
      have afterEq :
          after =
            { database with
              generation := database.generation + 1
              history := retiredHistory } := by
        have someEq :
            some
                { database with
                  generation := database.generation + 1
                  history := retiredHistory } =
              some after := by
          simpa [Database.retractId, retiredHistoryEq] using retracted
        exact (Option.some.inj someEq).symm
      subst after
      have idsEq := retireFirst_ids retiredHistoryEq
      rcases closed with ⟨nodup, below⟩
      constructor
      · simpa [idsEq] using nodup
      · intro candidate member
        exact below candidate (by simpa [idsEq] using member)

private theorem entry_eq_of_mem_id_eq_aux
    {history : List VersionedClause}
    (nodup : (history.map fun entry => entry.id).Nodup)
    {first second : VersionedClause}
    (firstMember : first ∈ history) (secondMember : second ∈ history)
    (sameId : first.id = second.id) : first = second := by
  induction history with
  | nil => simp at firstMember
  | cons head tail inductionHypothesis =>
      rw [List.map_cons, List.nodup_cons] at nodup
      rcases List.mem_cons.mp firstMember with firstHead | firstTail
      · subst first
        rcases List.mem_cons.mp secondMember with secondHead | secondTail
        · exact secondHead.symm
        · have secondIdMember :
              second.id ∈ tail.map (fun entry => entry.id) :=
            List.mem_map.mpr ⟨second, secondTail, rfl⟩
          exact False.elim
            (nodup.1 (by simpa [sameId] using secondIdMember))
      · rcases List.mem_cons.mp secondMember with secondHead | secondTail
        · subst second
          have firstIdMember :
              first.id ∈ tail.map (fun entry => entry.id) :=
            List.mem_map.mpr ⟨first, firstTail, rfl⟩
          exact False.elim
            (nodup.1 (by simpa [sameId] using firstIdMember))
        · exact inductionHypothesis nodup.2 firstTail secondTail

/-- A stable identity names at most one historical occurrence. -/
theorem entry_eq_of_mem_id_eq {database : Database}
    (closed : DatabaseIdsClosed database)
    {first second : VersionedClause}
    (firstMember : first ∈ database.history)
    (secondMember : second ∈ database.history)
    (sameId : first.id = second.id) : first = second :=
  entry_eq_of_mem_id_eq_aux closed.1 firstMember secondMember sameId

end DatabaseIdsClosed

/-- Complete reachability invariant for the independent logical-update
database. -/
structure DatabaseReachable (database : Database) : Prop where
  generationClosed : DatabaseGenerationClosed database
  idsClosed : DatabaseIdsClosed database

namespace DatabaseReachable

theorem empty : DatabaseReachable Database.empty :=
  ⟨DatabaseGenerationClosed.empty, DatabaseIdsClosed.empty⟩

theorem asserta {database : Database}
    (reachable : DatabaseReachable database) (clause : LocalClause) :
    DatabaseReachable (database.asserta clause) :=
  ⟨reachable.generationClosed.asserta clause,
    reachable.idsClosed.asserta clause⟩

theorem assertz {database : Database}
    (reachable : DatabaseReachable database) (clause : LocalClause) :
    DatabaseReachable (database.assertz clause) :=
  ⟨reachable.generationClosed.assertz clause,
    reachable.idsClosed.assertz clause⟩

theorem retractId {database after : Database}
    (reachable : DatabaseReachable database) {id : ClauseId}
    (retracted : database.retractId id = some after) :
    DatabaseReachable after :=
  ⟨reachable.generationClosed.retractId retracted,
    reachable.idsClosed.retractId retracted⟩

end DatabaseReachable

private theorem exists_retireFirst_of_mem_unerased
    {entry : VersionedClause} {history : List VersionedClause}
    (member : entry ∈ history) (live : entry.erased = none)
    (generation : Generation) :
    ∃ after, retireFirst generation entry.id history = some after := by
  induction history with
  | nil => simp at member
  | cons head rest inductionHypothesis =>
      rcases List.mem_cons.mp member with current | tail
      · subst head
        exact
          ⟨{ entry with erased := some generation } :: rest, by
            simp [retireFirst, live]⟩
      · by_cases hit : head.id = entry.id ∧ head.erased = none
        · exact
            ⟨{ head with erased := some generation } :: rest, by
              simp [retireFirst, hit]⟩
        · obtain ⟨retiredTail, retired⟩ :=
            inductionHypothesis tail
          exact
            ⟨head :: retiredTail, by
              simp [retireFirst, hit, retired]⟩

/-- Every entry in the current projection of a reachable database is
retractable.  This is the progress fact connecting an ordered successful scan
to the identity mutation primitive. -/
theorem exists_retractId_of_mem_currentEntries
    {database : Database} (reachable : DatabaseReachable database)
    {entry : VersionedClause} (member : entry ∈ currentEntries database) :
    ∃ after, database.retractId entry.id = some after := by
  have filtered := List.mem_filter.mp member
  have inHistory := filtered.1
  have visible : entry.visibleAt database.generation = true := by
    simpa using filtered.2
  have live : entry.erased = none := by
    have bounds := reachable.generationClosed entry inHistory
    cases erasedEq : entry.erased with
    | none => rfl
    | some erased =>
        have erasedLe := bounds.2 erased erasedEq
        have generationLt :
            database.generation < erased := by
          have semantic :=
            (VersionedClause.visibleAt_eq_true_iff entry
              database.generation).mp visible
          simpa [VersionedClause.VisibleAt, erasedEq] using semantic.2
        exact False.elim ((Nat.not_lt_of_ge erasedLe) generationLt)
  obtain ⟨retiredHistory, retired⟩ :=
    exists_retireFirst_of_mem_unerased inHistory live
      (database.generation + 1)
  exact
    ⟨{ database with
        generation := database.generation + 1
        history := retiredHistory }, by
      simp [Database.retractId, retired]⟩

/-- Typed observable mutation.  Occurrence identity and content are retained,
so duplicate assertions and the exact committed retraction remain visible. -/
inductive LocalDatabaseEffect where
  | asserta (entry : VersionedClause)
  | assertz (entry : VersionedClause)
  | retract (entry : VersionedClause)
deriving Repr, Inhabited

/-- One exact database mutation. -/
inductive DatabaseMutation :
    Database → LocalDatabaseEffect → Database → Prop where
  | asserta (database : Database) (clause : LocalClause) :
      DatabaseMutation database
        (.asserta (database.allocate clause))
        (database.asserta clause)
  | assertz (database : Database) (clause : LocalClause) :
      DatabaseMutation database
        (.assertz (database.allocate clause))
        (database.assertz clause)
  | retract {database after : Database} {entry : VersionedClause}
      (reachable : DatabaseReachable database)
      (selected : entry ∈ currentEntries database)
      (retired : database.retractId entry.id = some after) :
      DatabaseMutation database (.retract entry) after

namespace DatabaseMutation

/-- Every successful database mutation advances the logical-update
generation exactly once.  In particular, a successful retract cannot be
silently represented as a same-generation world replacement. -/
theorem generation_eq_succ
    {before after : Database} {effect : LocalDatabaseEffect}
    (mutation : DatabaseMutation before effect after) :
    after.generation = before.generation + 1 := by
  cases mutation with
  | asserta => rfl
  | assertz => rfl
  | retract _ _ retracted =>
      exact Database.retractId_generation retracted

theorem preserves_generationClosed
    {before after : Database} {effect : LocalDatabaseEffect}
    (mutation : DatabaseMutation before effect after)
    (closed : DatabaseGenerationClosed before) :
    DatabaseGenerationClosed after := by
  cases mutation with
  | asserta clause => exact closed.asserta clause
  | assertz clause => exact closed.assertz clause
  | retract reachable selected retired => exact closed.retractId retired

theorem preserves_idsClosed
    {before after : Database} {effect : LocalDatabaseEffect}
    (mutation : DatabaseMutation before effect after)
    (closed : DatabaseIdsClosed before) :
    DatabaseIdsClosed after := by
  cases mutation with
  | asserta clause => exact closed.asserta clause
  | assertz clause => exact closed.assertz clause
  | retract reachable selected retired => exact closed.retractId retired

theorem preserves_reachable
    {before after : Database} {effect : LocalDatabaseEffect}
    (mutation : DatabaseMutation before effect after)
    (reachable : DatabaseReachable before) :
    DatabaseReachable after :=
  ⟨mutation.preserves_generationClosed reachable.generationClosed,
    mutation.preserves_idsClosed reachable.idsClosed⟩

/-- A reported retract effect names a current occurrence whose identity cannot
resolve to any different historical occurrence. -/
theorem retract_effect_exact
    {before after : Database} {entry : VersionedClause}
    (mutation : DatabaseMutation before (.retract entry) after) :
    entry ∈ currentEntries before ∧
      ∀ other ∈ before.history, other.id = entry.id → other = entry := by
  cases mutation with
  | retract reachable selected retired =>
      refine ⟨selected, ?_⟩
      intro other otherMember sameId
      have selectedHistory := (List.mem_filter.mp selected).1
      exact reachable.idsClosed.entry_eq_of_mem_id_eq
        otherMember selectedHistory sameId

end DatabaseMutation

/-- Reflexive-transitive logical-update chronology with the exact ordered
mutation trace retained. -/
inductive DatabaseChronology :
    Database → List LocalDatabaseEffect → Database → Prop where
  | refl (database : Database) :
      DatabaseChronology database [] database
  | step {before middle after : Database}
      {effect : LocalDatabaseEffect} {effects : List LocalDatabaseEffect}
      (head : DatabaseMutation before effect middle)
      (tail : DatabaseChronology middle effects after) :
      DatabaseChronology before (effect :: effects) after

namespace DatabaseChronology

/-- The endpoint generation is the start generation plus the exact number of
ordered successful mutations.  This is stronger than monotonicity and keeps
the mutation trace from being a decorative payload. -/
theorem generation_eq_add_length
    {before after : Database} {effects : List LocalDatabaseEffect}
    (chronology : DatabaseChronology before effects after) :
    after.generation = before.generation + effects.length := by
  induction chronology with
  | refl => simp
  | step mutation tail inductionHypothesis =>
      rw [inductionHypothesis, mutation.generation_eq_succ]
      simp [Nat.add_comm, Nat.add_left_comm]

/-- Logical-update generations never regress along a real chronology. -/
theorem generation_mono
    {before after : Database} {effects : List LocalDatabaseEffect}
    (chronology : DatabaseChronology before effects after) :
    before.generation ≤ after.generation := by
  rw [chronology.generation_eq_add_length]
  exact Nat.le_add_right _ _

/-- A well-formed reachable history remains generation-closed across every
ordered mutation chronology. -/
theorem preserves_generationClosed
    {before after : Database} {effects : List LocalDatabaseEffect}
    (chronology : DatabaseChronology before effects after)
    (closed : DatabaseGenerationClosed before) :
    DatabaseGenerationClosed after := by
  induction chronology with
  | refl => exact closed
  | step mutation tail inductionHypothesis =>
      exact inductionHypothesis
        (mutation.preserves_generationClosed closed)

theorem preserves_idsClosed
    {before after : Database} {effects : List LocalDatabaseEffect}
    (chronology : DatabaseChronology before effects after)
    (closed : DatabaseIdsClosed before) :
    DatabaseIdsClosed after := by
  induction chronology with
  | refl => exact closed
  | step mutation tail inductionHypothesis =>
      exact inductionHypothesis (mutation.preserves_idsClosed closed)

theorem preserves_reachable
    {before after : Database} {effects : List LocalDatabaseEffect}
    (chronology : DatabaseChronology before effects after)
    (reachable : DatabaseReachable before) :
    DatabaseReachable after :=
  ⟨chronology.preserves_generationClosed reachable.generationClosed,
    chronology.preserves_idsClosed reachable.idsClosed⟩

/-- Chronologies compose without reordering effects. -/
theorem trans {first middle last : Database}
    {left right : List LocalDatabaseEffect}
    (one : DatabaseChronology first left middle)
    (two : DatabaseChronology middle right last) :
    DatabaseChronology first (left ++ right) last := by
  induction one with
  | refl => simpa using two
  | step head tail inductionHypothesis =>
      exact .step head (inductionHypothesis two)

end DatabaseChronology

/-! ## Anti-vacuity: duplicate identities mislabel retraction -/

private def duplicateIdFirst : VersionedClause :=
  { id := 0
    clause :=
      { predicate := "first"
        arguments := [.atom "a"]
        body := [] }
    created := 0 }

private def duplicateIdSecond : VersionedClause :=
  { id := 0
    clause :=
      { predicate := "second"
        arguments := [.atom "b"]
        body := [] }
    created := 0 }

private def duplicateIdDatabase : Database :=
  { generation := 0
    nextId := 1
    history := [duplicateIdFirst, duplicateIdSecond] }

private def duplicateIdAfter : Database :=
  { generation := 1
    nextId := 1
    history :=
      [{ duplicateIdFirst with erased := some 1 }, duplicateIdSecond] }

/-- Timestamp closure alone admits a forged history with duplicate stable
identities.  The complete reachability invariant rejects it. -/
theorem duplicate_id_generation_closure_is_insufficient :
    DatabaseGenerationClosed duplicateIdDatabase ∧
      ¬ DatabaseReachable duplicateIdDatabase := by
  constructor
  · intro entry member
    simp only [duplicateIdDatabase, List.mem_cons] at member
    rcases member with rfl | rfl | impossible
    · simp [duplicateIdFirst]
    · simp [duplicateIdSecond]
    · simp at impossible
  · intro reachable
    rcases reachable.idsClosed with ⟨nodup, _⟩
    simp [duplicateIdDatabase, duplicateIdFirst, duplicateIdSecond] at nodup

/-- If duplicate IDs were admitted, selecting the second live occurrence and
retiring by its advertised identity would retire the distinct first
occurrence instead.  This is the concrete mislabeling excluded by
`DatabaseReachable`. -/
theorem duplicate_id_retract_can_mislabel_selected_occurrence :
    duplicateIdSecond ∈ currentEntries duplicateIdDatabase ∧
      duplicateIdDatabase.retractId duplicateIdSecond.id =
        some duplicateIdAfter ∧
      duplicateIdSecond ∈ currentEntries duplicateIdAfter ∧
      duplicateIdFirst ∉ currentEntries duplicateIdAfter ∧
      duplicateIdFirst ≠ duplicateIdSecond := by
  simp [duplicateIdDatabase, duplicateIdAfter, duplicateIdFirst,
    duplicateIdSecond, currentEntries, Database.retractId, retireFirst,
    VersionedClause.visibleAt]

end PLeaTTa.PeTTaSpec.PrologCore.DatabaseActions
