-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologActivationMacro
Purpose: Characterize executable local-clause activation before composing it
  with the independent demand-driven resolver.
Trusted boundary: none
Main exports: ResolutionScan, resolveAlts_scan,
  resolveAlts_counter_exact, resolveAlts_alts_leading_full_head_eq
-/
import PLeaTTa.Proofs.PrologGoalAlpha
import PLeaTTa.Semantics

namespace PLeaTTa.PrologActivationMacro

open Metta (Atom Subst)
open PeTTaSpec.PrologCore.Resolver

/-!
`resolveAlts` performs only a finite conservative candidate scan.  It drops a
wrong-arity or syntactically incompatible clause without allocating a suffix;
every retained clause receives one suffix and becomes one alternative in
source order.  Full head unification is not hidden in that scan: it is the
first executable equality goal of the retained alternative.

The independent resolver deliberately does more work at pull time.  A later
activation macro may therefore stutter over an independently reserved clause
that this finite scan drops, but that stutter is ranked by the shrinking
finite cursor.  This file first states the executable side independently;
neither the reference semantics nor `resolveAlts` is redefined.
-/

/-- The exact conservative predicate used by `resolveAlts` to retain one
clause.  It includes the output slot separately from the input parameter
list. -/
def resolutionClauseRetained (argsv : List Atom) (resv : Atom)
    (clause : Clause) : Bool :=
  clause.params.length == argsv.length &&
    prologMatchCompatList argsv clause.params &&
    prologMatchCompat resv clause.result

/-- The exact alternative minted for one retained clause at one executable
suffix seed.  The complete input-plus-output head equality is first, before
the freshened body and the caller continuation. -/
def resolutionAlt (argsv args : List Atom) (res : Atom)
    (rest : List Goal) (binding : Subst) (qterm : Atom)
    (barrier seed : Nat) (clause : Clause) : Alt :=
  let copied :=
    freshenResolutionClause argsv args res rest binding qterm seed barrier
      clause
  .br
    (Goal.eq (Atom.expr (args ++ [res]))
        (Atom.expr (copied.params ++ [copied.result])) ::
      copied.body ++ rest)
    binding

/-- Forward source-order presentation of the executable's finite scan.
Unlike the implementation's reverse-accumulating `foldl`, this definition
exposes retained order directly. -/
def scanResolution (argsv args : List Atom) (res : Atom)
    (rest : List Goal) (binding : Subst) (qterm : Atom)
    (barrier : Nat) : List Clause → Nat → List Alt × Nat
  | [], counter => ([], counter)
  | clause :: clauses, counter =>
      if resolutionClauseRetained argsv (PLeaTTa.subst binding res) clause then
        let tail := scanResolution argsv args res rest binding qterm barrier
          clauses (counter + 1)
        (resolutionAlt argsv args res rest binding qterm barrier counter
            clause :: tail.1,
          tail.2)
      else
        scanResolution argsv args res rest binding qterm barrier clauses
          counter

/-- Declarative scan certificate.  A skipped clause contributes neither an
alternative nor a counter increment; a retained clause contributes exactly
one source-ordered alternative at the current counter. -/
inductive ResolutionScan (argsv args : List Atom) (res : Atom)
    (rest : List Goal) (binding : Subst) (qterm : Atom)
    (barrier : Nat) : List Clause → Nat → List Alt → Nat → Prop where
  | nil (counter : Nat) :
      ResolutionScan argsv args res rest binding qterm barrier
        [] counter [] counter
  | skipped (clause : Clause) (clauses : List Clause)
      (counter finalCounter : Nat) (alts : List Alt)
      (skipped :
        resolutionClauseRetained argsv (PLeaTTa.subst binding res) clause =
          false)
      (tail : ResolutionScan argsv args res rest binding qterm barrier
        clauses counter alts finalCounter) :
      ResolutionScan argsv args res rest binding qterm barrier
        (clause :: clauses) counter alts finalCounter
  | retained (clause : Clause) (clauses : List Clause)
      (counter finalCounter : Nat) (alts : List Alt)
      (retained :
        resolutionClauseRetained argsv (PLeaTTa.subst binding res) clause =
          true)
      (tail : ResolutionScan argsv args res rest binding qterm barrier
        clauses (counter + 1) alts finalCounter) :
      ResolutionScan argsv args res rest binding qterm barrier
        (clause :: clauses) counter
        (resolutionAlt argsv args res rest binding qterm barrier counter
          clause :: alts)
        finalCounter

theorem scanResolution_certified (argsv args : List Atom) (res : Atom)
    (rest : List Goal) (binding : Subst) (qterm : Atom)
    (barrier : Nat) (clauses : List Clause) (counter : Nat) :
    ResolutionScan argsv args res rest binding qterm barrier clauses counter
      (scanResolution argsv args res rest binding qterm barrier clauses
        counter).1
      (scanResolution argsv args res rest binding qterm barrier clauses
        counter).2 := by
  induction clauses generalizing counter with
  | nil =>
      exact .nil counter
  | cons clause clauses inductionHypothesis =>
      simp only [scanResolution]
      cases retained :
          resolutionClauseRetained argsv (PLeaTTa.subst binding res) clause
      · exact .skipped clause clauses counter _ _ retained
          (inductionHypothesis counter)
      · exact .retained clause clauses counter _ _ retained
          (inductionHypothesis (counter + 1))

/-- A declarative scan certificate determines the exact functional result.
This rules out a second certificate that silently permutes or deduplicates
retained occurrences. -/
theorem ResolutionScan.result_eq
    {argsv args : List Atom} {res : Atom} {rest : List Goal}
    {binding : Subst} {qterm : Atom} {barrier : Nat}
    {clauses : List Clause} {counter : Nat} {alts : List Alt}
    {finalCounter : Nat}
    (scan : ResolutionScan argsv args res rest binding qterm barrier
      clauses counter alts finalCounter) :
    scanResolution argsv args res rest binding qterm barrier clauses counter =
      (alts, finalCounter) := by
  induction scan with
  | nil counter =>
      rfl
  | skipped clause clauses counter finalCounter alts skipped tail
      inductionHypothesis =>
      simp only [scanResolution, skipped, Bool.false_eq_true, if_false]
      exact inductionHypothesis
  | retained clause clauses counter finalCounter alts retained tail
      inductionHypothesis =>
      simp only [scanResolution, retained, if_true]
      rw [inductionHypothesis]

/-- The certificate relation is deterministic on both the ordered
alternative bank and the final counter. -/
theorem ResolutionScan.deterministic
    {argsv args : List Atom} {res : Atom} {rest : List Goal}
    {binding : Subst} {qterm : Atom} {barrier : Nat}
    {clauses : List Clause} {counter : Nat}
    {firstAlts secondAlts : List Alt} {firstCounter secondCounter : Nat}
    (first : ResolutionScan argsv args res rest binding qterm barrier
      clauses counter firstAlts firstCounter)
    (second : ResolutionScan argsv args res rest binding qterm barrier
      clauses counter secondAlts secondCounter) :
    firstAlts = secondAlts ∧ firstCounter = secondCounter := by
  have equality :
      (firstAlts, firstCounter) = (secondAlts, secondCounter) :=
    first.result_eq.symm.trans second.result_eq
  exact ⟨congrArg Prod.fst equality, congrArg Prod.snd equality⟩

private def resolutionFoldStep (argsv args : List Atom) (res : Atom)
    (rest : List Goal) (binding : Subst) (qterm : Atom)
    (barrier : Nat) (acc : List Alt × Nat) (clause : Clause) :
    List Alt × Nat :=
  if clause.params.length != argsv.length then acc
  else if !prologMatchCompatList argsv clause.params then acc
  else if !prologMatchCompat (PLeaTTa.subst binding res) clause.result then acc
  else
    (resolutionAlt argsv args res rest binding qterm barrier acc.2 clause ::
        acc.1,
      acc.2 + 1)

private theorem resolutionFoldStep_eq (argsv args : List Atom) (res : Atom)
    (rest : List Goal) (binding : Subst) (qterm : Atom)
    (barrier : Nat) (acc : List Alt × Nat) (clause : Clause) :
    resolutionFoldStep argsv args res rest binding qterm barrier acc clause =
      if resolutionClauseRetained argsv (PLeaTTa.subst binding res) clause then
        (resolutionAlt argsv args res rest binding qterm barrier acc.2 clause ::
            acc.1,
          acc.2 + 1)
      else acc := by
  unfold resolutionFoldStep resolutionClauseRetained
  cases arity : clause.params.length == argsv.length <;>
    cases params :
      prologMatchCompatList argsv clause.params <;>
    cases result :
      prologMatchCompat (PLeaTTa.subst binding res) clause.result <;>
    simp_all

private theorem foldl_resolutionFoldStep_eq_scanResolution
    (argsv args : List Atom) (res : Atom) (rest : List Goal)
    (binding : Subst) (qterm : Atom) (barrier : Nat)
    (clauses : List Clause) (reversed : List Alt) (counter : Nat) :
    clauses.foldl
        (resolutionFoldStep argsv args res rest binding qterm barrier)
        (reversed, counter) =
      let scanned :=
        scanResolution argsv args res rest binding qterm barrier clauses counter
      (scanned.1.reverse ++ reversed, scanned.2) := by
  induction clauses generalizing reversed counter with
  | nil => rfl
  | cons clause clauses inductionHypothesis =>
      simp only [List.foldl_cons, scanResolution]
      rw [resolutionFoldStep_eq]
      cases retained :
          resolutionClauseRetained argsv (PLeaTTa.subst binding res) clause
      · simp only [Bool.false_eq_true, if_false]
        exact inductionHypothesis reversed counter
      · simp only [if_true]
        rw [inductionHypothesis
          (resolutionAlt argsv args res rest binding qterm barrier counter
            clause :: reversed)
          (counter + 1)]
        simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

/-- The implementation's reverse-accumulating fold is exactly the
source-order scan above.  This is an equation about the actual `resolveAlts`,
not a replacement algorithm. -/
theorem resolveAlts_eq_scanResolution (clauses : List Clause)
    (argsv args : List Atom) (res : Atom) (rest : List Goal)
    (binding : Subst) (qterm : Atom) (barrier counter : Nat) :
    resolveAlts clauses argsv args res rest binding qterm barrier counter =
      scanResolution argsv args res rest binding qterm barrier clauses
        counter := by
  unfold resolveAlts
  change
    (let folded := clauses.foldl
        (resolutionFoldStep argsv args res rest binding qterm barrier)
        ([], counter);
      (folded.1.reverse, folded.2)) =
      scanResolution argsv args res rest binding qterm barrier clauses counter
  rw [foldl_resolutionFoldStep_eq_scanResolution]
  simp

/-- The actual executable result carries the declarative scan certificate. -/
theorem resolveAlts_scan (clauses : List Clause)
    (argsv args : List Atom) (res : Atom) (rest : List Goal)
    (binding : Subst) (qterm : Atom) (barrier counter : Nat) :
    ResolutionScan argsv args res rest binding qterm barrier clauses counter
      (resolveAlts clauses argsv args res rest binding qterm barrier counter).1
      (resolveAlts clauses argsv args res rest binding qterm barrier counter).2 := by
  rw [resolveAlts_eq_scanResolution]
  exact scanResolution_certified argsv args res rest binding qterm barrier
    clauses counter

/-- Number of clauses retained by the exact executable candidate predicate. -/
def retainedClauseCount (argsv : List Atom) (resv : Atom)
    (clauses : List Clause) : Nat :=
  (clauses.filter (resolutionClauseRetained argsv resv)).length

theorem ResolutionScan.counter_exact
    {argsv args : List Atom} {res : Atom} {rest : List Goal}
    {binding : Subst} {qterm : Atom} {barrier : Nat}
    {clauses : List Clause} {counter : Nat} {alts : List Alt}
    {finalCounter : Nat}
    (scan : ResolutionScan argsv args res rest binding qterm barrier
      clauses counter alts finalCounter) :
    finalCounter =
      counter +
        retainedClauseCount argsv (PLeaTTa.subst binding res) clauses := by
  induction scan with
  | nil counter => rfl
  | skipped clause clauses counter finalCounter alts skipped tail ih =>
      simp [retainedClauseCount, skipped, ih]
  | retained clause clauses counter finalCounter alts retained tail ih =>
      simp [retainedClauseCount, retained, ih, Nat.add_assoc]
      omega

theorem ResolutionScan.length_exact
    {argsv args : List Atom} {res : Atom} {rest : List Goal}
    {binding : Subst} {qterm : Atom} {barrier : Nat}
    {clauses : List Clause} {counter : Nat} {alts : List Alt}
    {finalCounter : Nat}
    (scan : ResolutionScan argsv args res rest binding qterm barrier
      clauses counter alts finalCounter) :
    alts.length =
      retainedClauseCount argsv (PLeaTTa.subst binding res) clauses := by
  induction scan with
  | nil counter => rfl
  | skipped clause clauses counter finalCounter alts skipped tail ih =>
      simp [retainedClauseCount, skipped, ih]
  | retained clause clauses counter finalCounter alts retained tail ih =>
      simp [retainedClauseCount, retained, ih]

/-- The returned counter advances by exactly one per retained clause and by
zero for every dropped clause. -/
theorem resolveAlts_counter_exact (clauses : List Clause)
    (argsv args : List Atom) (res : Atom) (rest : List Goal)
    (binding : Subst) (qterm : Atom) (barrier counter : Nat) :
    (resolveAlts clauses argsv args res rest binding qterm barrier counter).2 =
      counter +
        retainedClauseCount argsv (PLeaTTa.subst binding res) clauses := by
  exact (resolveAlts_scan clauses argsv args res rest binding qterm barrier
    counter).counter_exact

/-- Alternative multiplicity is exactly retained-clause multiplicity; the
scan never deduplicates extensionally equal clauses. -/
theorem resolveAlts_length_exact (clauses : List Clause)
    (argsv args : List Atom) (res : Atom) (rest : List Goal)
    (binding : Subst) (qterm : Atom) (barrier counter : Nat) :
    (resolveAlts clauses argsv args res rest binding qterm barrier counter).1.length =
      retainedClauseCount argsv (PLeaTTa.subst binding res) clauses := by
  exact (resolveAlts_scan clauses argsv args res rest binding qterm barrier
    counter).length_exact

/-- A retained alternative's first goal is the complete input-plus-output
head equality.  No body or continuation goal can execute before it. -/
theorem resolutionAlt_leading_full_head_eq
    (argsv args : List Atom) (res : Atom) (rest : List Goal)
    (binding : Subst) (qterm : Atom) (barrier seed : Nat)
    (clause : Clause) :
    ∃ copied,
      copied =
          freshenResolutionClause argsv args res rest binding qterm seed
            barrier clause ∧
      resolutionAlt argsv args res rest binding qterm barrier seed clause =
        .br
          (Goal.eq (Atom.expr (args ++ [res]))
              (Atom.expr (copied.params ++ [copied.result])) ::
            copied.body ++ rest)
          binding := by
  exact ⟨_, rfl, rfl⟩

theorem ResolutionScan.alts_leading_full_head_eq
    {argsv args : List Atom} {res : Atom} {rest : List Goal}
    {binding : Subst} {qterm : Atom} {barrier : Nat}
    {clauses : List Clause} {counter : Nat} {alts : List Alt}
    {finalCounter : Nat}
    (scan : ResolutionScan argsv args res rest binding qterm barrier
      clauses counter alts finalCounter)
    {alt : Alt} (member : alt ∈ alts) :
    ∃ seed clause copied,
      clause ∈ clauses ∧
      resolutionClauseRetained argsv (PLeaTTa.subst binding res) clause =
        true ∧
      copied =
        freshenResolutionClause argsv args res rest binding qterm seed barrier
          clause ∧
      alt =
        .br
          (Goal.eq (Atom.expr (args ++ [res]))
              (Atom.expr (copied.params ++ [copied.result])) ::
            copied.body ++ rest)
          binding := by
  induction scan with
  | nil counter =>
      simp at member
  | skipped clause clauses counter finalCounter alts skipped tail ih =>
      obtain ⟨seed, origin, copied, originMember, retained, copiedEq, altEq⟩ :=
        ih member
      exact ⟨seed, origin, copied, by simp [originMember], retained, copiedEq,
        altEq⟩
  | retained clause clauses counter finalCounter alts retained tail ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · refine ⟨counter, clause,
          freshenResolutionClause argsv args res rest binding qterm counter
            barrier clause,
          by simp, retained, rfl, rfl⟩
      · obtain ⟨seed, origin, copied, originMember, originRetained, copiedEq,
          altEq⟩ := ih member
        exact ⟨seed, origin, copied, by simp [originMember], originRetained,
          copiedEq, altEq⟩

/-- Every actual executable resolution alternative exposes the full head
equality before any body goal. -/
theorem resolveAlts_alts_leading_full_head_eq
    (clauses : List Clause) (argsv args : List Atom) (res : Atom)
    (rest : List Goal) (binding : Subst) (qterm : Atom)
    (barrier counter : Nat) {alt : Alt}
    (member : alt ∈
      (resolveAlts clauses argsv args res rest binding qterm barrier
        counter).1) :
    ∃ seed clause copied,
      clause ∈ clauses ∧
      resolutionClauseRetained argsv (PLeaTTa.subst binding res) clause =
        true ∧
      copied =
        freshenResolutionClause argsv args res rest binding qterm seed barrier
          clause ∧
      alt =
        .br
          (Goal.eq (Atom.expr (args ++ [res]))
              (Atom.expr (copied.params ++ [copied.result])) ::
            copied.body ++ rest)
          binding := by
  exact (resolveAlts_scan clauses argsv args res rest binding qterm barrier
    counter).alts_leading_full_head_eq member

theorem resolutionClauseRetained_true_iff
    (argsv : List Atom) (resv : Atom) (clause : Clause) :
    resolutionClauseRetained argsv resv clause = true ↔
      clause.params.length = argsv.length ∧
        prologMatchCompatList argsv clause.params = true ∧
        prologMatchCompat resv clause.result = true := by
  simp [resolutionClauseRetained, Bool.and_eq_true, and_assoc]

/-- If the complete retained head equality fails, the sealed machine consumes
that alternative before its body or continuation.  The transition changes no
answer, world, or fresh counter; only DFS control is pulled forward. -/
theorem leading_full_head_eq_failure_is_silent
    (program : Prog) (grounding : Metta.GroundingTable)
    (conf : Conf) (left right : Atom) (bodyAndRest : List Goal)
    (binding : Subst)
    (current :
      conf.cur = some (Goal.eq left right :: bodyAndRest, binding))
    (failure : unifyB binding left right = none) :
    Step program grounding conf (pull { conf with cur := none }) ∧
      (pull { conf with cur := none }).answers = conf.answers ∧
      (pull { conf with cur := none }).world = conf.world ∧
      (pull { conf with cur := none }).counter = conf.counter := by
  refine ⟨.eq_fail conf left right bodyAndRest binding current failure, ?_⟩
  have answers :
      (pull { conf with cur := none }).answers = conf.answers := by
    unfold pull
    generalize outcomeEq :
      pullAuxTracked conf.barriers conf.alts = outcome
    rcases outcome with ⟨outcome, barriers⟩
    cases outcome <;> rfl
  have world :
      (pull { conf with cur := none }).world = conf.world := by
    unfold pull
    generalize outcomeEq :
      pullAuxTracked conf.barriers conf.alts = outcome
    rcases outcome with ⟨outcome, barriers⟩
    cases outcome <;> rfl
  have counter :
      (pull { conf with cur := none }).counter = conf.counter := by
    unfold pull
    generalize outcomeEq :
      pullAuxTracked conf.barriers conf.alts = outcome
    rcases outcome with ⟨outcome, barriers⟩
    cases outcome <;> rfl
  exact ⟨answers, world, counter⟩

/-! ## Anti-vacuity witnesses for the activation macro -/

private def incompatibleParameterClause : Clause :=
  { params := [.sym "other"]
    result := .var "out"
    body := [.eq (.sym "parameter-body") (.sym "parameter-body")] }

private def incompatibleOutputClause : Clause :=
  { params := [.sym "input"]
    result := .sym "other-output"
    body := [.eq (.sym "output-body") (.sym "output-body")] }

private def repeatedVariableClause : Clause :=
  { params := [.var "shared", .var "shared"]
    result := .sym "ok"
    body := [.eq (.sym "body") (.sym "body")] }

private def firstOrderedClause : Clause :=
  { params := [.sym "input"]
    result := .sym "first"
    body := [.eq (.sym "first-body") (.sym "first-body")] }

private def secondOrderedClause : Clause :=
  { params := [.sym "input"]
    result := .sym "second"
    body := [.eq (.sym "second-body") (.sym "second-body")] }

private def retainedVariableOutputClause : Clause :=
  { params := [.sym "input"]
    result := .var "out"
    body := [] }

private def droppedReferenceClause : LocalClause :=
  { predicate := "p"
    arguments := [.atom "other", .variable (.source "droppedOut")]
    body := [] }

private def retainedReferenceClause : LocalClause :=
  { predicate := "p"
    arguments := [.atom "input", .variable (.source "retainedOut")]
    body := [] }

private def frontierGapSession : LocalSession :=
  { database :=
      (Database.empty.assertz droppedReferenceClause).assertz
        retainedReferenceClause
    nextFresh := 0 }

private def frontierGapRequest : CallRequest :=
  { predicate := "p"
    arguments := [.atom "input", .variable (.source "queryOut")]
    bindings := [] }

/-- A parameter-position clash is genuinely dropped and consumes no suffix
counter. -/
theorem incompatible_parameter_clause_is_dropped :
    resolveAlts [incompatibleParameterClause]
      [.sym "input"] [.sym "input"] (.var "result") [] []
      (.var "query") 1 7 = ([], 7) := by
  rfl

/-- The independently important output slot participates in conservative
candidate pruning too. -/
theorem incompatible_output_clause_is_dropped :
    resolveAlts [incompatibleOutputClause]
      [.sym "input"] [.sym "input"] (.sym "wanted-output") [] []
      (.var "query") 1 7 = ([], 7) := by
  rw [resolveAlts_eq_scanResolution]
  have dropped :
      resolutionClauseRetained [.sym "input"]
          (PLeaTTa.subst [] (.sym "wanted-output"))
          incompatibleOutputClause = false := by
    rw [PLeaTTa.subst_nil]
    rfl
  simp only [scanResolution, dropped, Bool.false_eq_true, if_false]

/-- The two resolvers' freshness frontiers have genuinely different units.
The independent call-start snapshot reserves a generated identity even for
the leading clause that full MGU will reject; the executable conservative
scan drops that clause before allocating a suffix and advances only for the
retained occurrence.  A later activation macro must therefore relate
frontiers monotonically rather than identify their numeric values. -/
theorem dropped_clause_reservation_creates_frontier_gap :
    (prepareCall frontierGapSession frontierGapRequest).2.nextFresh = 2 ∧
      (resolveAlts
        [incompatibleParameterClause, retainedVariableOutputClause]
        [.sym "input"] [.sym "input"] (.var "queryOut") [] []
        (.var "query") 1 0).2 = 1 := by
  constructor
  · rfl
  · rw [resolveAlts_eq_scanResolution]
    simp [scanResolution, resolutionClauseRetained,
      incompatibleParameterClause, retainedVariableOutputClause,
      prologMatchCompatList, prologMatchCompat, PLeaTTa.subst_nil]

/-- Conservative compatibility does not pretend to be a full MGU test.  A
repeated-variable head is retained for unequal actual arguments, but its
leading complete head equality then fails. -/
theorem repeated_variable_doomed_alt_is_retained :
    resolveAlts [repeatedVariableClause]
      [.sym "left", .sym "right"] [.sym "left", .sym "right"] (.sym "ok")
      [] [] (.var "query") 1 0 =
      ([resolutionAlt
          [.sym "left", .sym "right"] [.sym "left", .sym "right"]
          (.sym "ok") [] [] (.var "query") 1 0 repeatedVariableClause],
        1) ∧
    unifyB []
      (.expr [.sym "left", .sym "right", .sym "ok"])
      (.expr [.var "shared#r0", .var "shared#r0", .sym "ok"]) = none := by
  constructor
  · rw [resolveAlts_eq_scanResolution]
    have retained :
        resolutionClauseRetained [.sym "left", .sym "right"]
            (PLeaTTa.subst [] (.sym "ok"))
            repeatedVariableClause = true := by
      rw [PLeaTTa.subst_nil]
      rfl
    simp only [scanResolution, retained, if_true]
  · simp [unifyB, unifyTopExact, Metta.Unify.unifyTopWith,
      Atom.size, Metta.Unify.unifyRoundsWith,
      Metta.Unify.decomposeAllWith,
      Metta.Unify.decomposeEqWith, Metta.Unify.decomposeListWith,
      Metta.Subst.occurs,
      Metta.Subst.apply, Metta.Subst.lookup]

/-- The dual witness prevents the doomed-alt test from passing because every
repeated-variable head was accidentally rejected. -/
theorem repeated_variable_equal_actuals_succeed :
    ∃ result,
      unifyB []
        (.expr [.sym "same", .sym "same", .sym "ok"])
        (.expr [.var "shared#r0", .var "shared#r0", .sym "ok"]) =
          some result := by
  refine ⟨[("shared#r0", .sym "same")], ?_⟩
  simp [unifyB, unifyTopExact, Metta.Unify.unifyTopWith,
    Atom.size, Metta.Unify.unifyRoundsWith,
    Metta.Unify.decomposeAllWith,
    Metta.Unify.decomposeEqWith, Metta.Unify.decomposeListWith,
    Metta.Subst.occurs, Metta.Subst.compose, Metta.Subst.extend,
    Metta.Subst.erase,
    Metta.Subst.apply, Metta.Subst.lookup]

/-- Two retained occurrences remain in source order with exact duplicate
multiplicity and consecutive retained-clause seeds. -/
theorem two_retained_clauses_keep_source_order :
    resolveAlts [firstOrderedClause, secondOrderedClause]
      [.sym "input"] [.sym "input"] (.var "result") [] []
      (.var "query") 1 4 =
      ([resolutionAlt [.sym "input"] [.sym "input"] (.var "result") [] []
          (.var "query") 1 4 firstOrderedClause,
        resolutionAlt [.sym "input"] [.sym "input"] (.var "result") [] []
          (.var "query") 1 5 secondOrderedClause],
        6) := by
  rw [resolveAlts_eq_scanResolution]
  simp [scanResolution, resolutionClauseRetained, firstOrderedClause,
    secondOrderedClause, prologMatchCompatList, prologMatchCompat]

/-- Reversing those two alternatives is observably a different bank.  This
guards source-order preservation against a set- or permutation-based
characterization. -/
theorem swapped_retained_order_is_rejected :
    (resolveAlts [firstOrderedClause, secondOrderedClause]
      [.sym "input"] [.sym "input"] (.var "result") [] []
      (.var "query") 1 4).1 ≠
      [resolutionAlt [.sym "input"] [.sym "input"] (.var "result") [] []
          (.var "query") 1 5 secondOrderedClause,
       resolutionAlt [.sym "input"] [.sym "input"] (.var "result") [] []
          (.var "query") 1 4 firstOrderedClause] := by
  rw [two_retained_clauses_keep_source_order]
  simp [resolutionAlt, firstOrderedClause, secondOrderedClause,
    freshenResolutionClause, resolutionFreshSuffix, resolutionCompactSuffix,
    renameAtomSuffix, renameGoalSuffix]

end PLeaTTa.PrologActivationMacro
