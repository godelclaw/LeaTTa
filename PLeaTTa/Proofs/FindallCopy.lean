-- SPDX-License-Identifier: Apache-2.0

import PLeaTTa.Proofs.ResolutionCounter

/-!
# Certified residual-value copying for `findall/3`

The executable collector copies one already-materialized answer at a time.
This file states the content contract independently of a particular example:
each output is an injective common-suffix alpha-variant of the corresponding
input, list order and multiplicity are preserved by `List.Forall₂`, and the
global resolution-name high-water is threaded monotonically.

The concrete witnesses at the end guard the two different requirements that
are easy to conflate: different solutions must receive different variables,
while repeated occurrences inside one solution must retain their sharing.
-/

namespace PLeaTTa.FindallCopy

open Metta (Atom)

/-- One executable copied atom is a structural alpha-variant obtained with an
injective common-suffix renaming.  This relation says nothing about the
implementation's chosen suffix or counter. -/
def AtomCopyAgrees (source copied : Atom) : Prop :=
  ∃ suffix : String,
    copied = renameAtomSuffix suffix source ∧
      Function.Injective (fun name : String => name ++ suffix)

theorem copyFindallAtom_agrees (counter : Nat) (source : Atom) :
    AtomCopyAgrees source (copyFindallAtom counter source).value := by
  unfold AtomCopyAgrees copyFindallAtom
  split
  next closed =>
    refine ⟨resolutionCompactSuffix counter, ?_, resolution_suffix_injective _⟩
    exact
      (renameAtomSuffix_eq_self_of_resolutionAtomClosed
        (resolutionCompactSuffix counter) source closed).symm
  next _ =>
    exact
      ⟨resolutionCompactSuffix (advanceCounterPastAtoms counter [source]),
        rfl, resolution_suffix_injective _⟩

/-- The bag copier neither drops, duplicates, nor reorders solutions: every
source answer is paired with exactly one structural alpha-copy at the same
list position. -/
theorem copyFindallBag_agrees :
    ∀ (counter : Nat) (sources : List Atom),
      List.Forall₂ AtomCopyAgrees sources
        (copyFindallBag counter sources).values
  | _, [] => .nil
  | counter, source :: rest => by
      simp only [copyFindallBag]
      exact .cons (copyFindallAtom_agrees counter source)
        (copyFindallBag_agrees (copyFindallAtom counter source).counter rest)

/-- Every variable emitted by one non-ground copy is allocated strictly above
the counter supplied to that copy.  Closed values have no variables, so the
statement also holds for them without a special premise. -/
theorem copyFindallAtom_value_above_input
    (counter : Nat) (source : Atom) (name : String)
    (member : name ∈ (copyFindallAtom counter source).value.vars) :
    counter < resolutionSeedHighWaterName name := by
  unfold copyFindallAtom at member
  split at member
  next closed =>
    have noVars : source.vars = [] :=
      (PersistentSubst.atomClosed_eq_true_iff_vars_nil source).mp closed
    simp [noVars] at member
  next _ =>
    obtain ⟨sourceName, _, rfl⟩ :=
      (mem_renameAtomSuffix_vars
        (resolutionCompactSuffix
          (advanceCounterPastAtoms counter [source]))
        source _).mp member
    rw [resolutionSeedHighWaterName_append_compact]
    exact Nat.lt_succ_of_le (Nat.le_max_left _ _)

/-- Every variable in a copied bag is strictly above the allocator supplied
at the beginning of the bag.  This is the forward half of cross-solution
freshness: later solutions cannot reuse an earlier returned high-water. -/
theorem copyFindallBag_value_above_input :
    ∀ (counter : Nat) (sources : List Atom) (copied : Atom),
      copied ∈ (copyFindallBag counter sources).values →
      ∀ name ∈ copied.vars,
        counter < resolutionSeedHighWaterName name
  | _, [], _, member => by
      simp [copyFindallBag] at member
  | counter, source :: rest, copied, member => by
      simp only [copyFindallBag, List.mem_cons] at member
      rcases member with rfl | member
      · exact copyFindallAtom_value_above_input counter source
      · intro name nameMember
        exact lt_of_le_of_lt
          (copyFindallAtom_counter_mono counter source)
          (copyFindallBag_value_above_input
            (copyFindallAtom counter source).counter rest copied member
            name nameMember)

/-- Variable identities of different copied solutions are pairwise disjoint.
The statement is independent of the source names: even hostile names already
ending in `#r<n>` are scanned before allocation, and later solutions start
strictly above the preceding copy's returned high-water. -/
theorem copyFindallBag_pairwise_variable_disjoint
    (counter : Nat) (sources : List Atom) :
    (copyFindallBag counter sources).values.Pairwise
      (fun left right => List.Disjoint left.vars right.vars) := by
  induction sources generalizing counter with
  | nil =>
      simp [copyFindallBag]
  | cons source rest ih =>
      simp only [copyFindallBag, List.pairwise_cons]
      constructor
      · intro right rightMember
        rw [List.disjoint_left]
        intro name leftMember rightNameMember
        have leftBound :
            resolutionSeedHighWaterName name ≤
              (copyFindallAtom counter source).counter :=
          (PersistentSubst.resolutionSeedHighWaterNames_le_iff
            (copyFindallAtom counter source).value.vars
            (copyFindallAtom counter source).counter).mp
              (copyFindallAtom_value_below counter source)
              name leftMember
        have rightBound :
            (copyFindallAtom counter source).counter <
              resolutionSeedHighWaterName name :=
          copyFindallBag_value_above_input
            (copyFindallAtom counter source).counter rest right
            rightMember name rightNameMember
        omega
      · exact ih (counter := (copyFindallAtom counter source).counter)

/-! ## Bounded local copy microsteps

The executable helper above is the finite macro-spec.  The state and
relations below expose its work without moving answer construction into a
generic oracle protocol.  Every transition consumes exactly one source
solution, invokes the certified local `copyFindallAtom`, and prepends the
result to a private reverse accumulator. -/

/-- Finite local state for copying a residual-answer bag.  The source list and
reverse accumulator are private certified data; no constructor can emit an
answer, host effect, exception, or scheduling choice. -/
structure BagCopyState where
  remaining : List Atom
  copiedRev : List Atom
  counter : Nat
deriving Repr

/-- Initial state for one completed generator's materialized answer list. -/
def BagCopyState.initial (counter : Nat) (sources : List Atom) :
    BagCopyState :=
  { remaining := sources, copiedRev := [], counter := counter }

/-- One bounded certified copy microstep.  Its only constructor consumes the
head source value and obtains the output exclusively from `copyFindallAtom`. -/
inductive BagCopyStep : BagCopyState → BagCopyState → Prop where
  | next (counter : Nat) (source : Atom) (remaining copiedRev : List Atom) :
      BagCopyStep
        { remaining := source :: remaining
          copiedRev := copiedRev
          counter := counter }
        { remaining := remaining
          copiedRev :=
            (copyFindallAtom counter source).value :: copiedRev
          counter := (copyFindallAtom counter source).counter }

/-- Exact step-counted closure for the bounded copy phase. -/
inductive BagCopyStepsN : Nat → BagCopyState → BagCopyState → Prop where
  | zero (state : BagCopyState) : BagCopyStepsN 0 state state
  | succ (n : Nat) (before middle after : BagCopyState) :
      BagCopyStep before middle →
      BagCopyStepsN n middle after →
      BagCopyStepsN (n + 1) before after

/-- The one-step relation is functional; an oracle cannot choose a different
copied value, counter, or source order. -/
theorem BagCopyStep.deterministic
    {before first second : BagCopyState}
    (left : BagCopyStep before first)
    (right : BagCopyStep before second) :
    first = second := by
  cases left
  cases right
  rfl

/-- Every nonempty copy state has exactly the certified next transition. -/
theorem BagCopyStep.progress
    (counter : Nat) (source : Atom) (remaining copiedRev : List Atom) :
    ∃ next,
      BagCopyStep
        { remaining := source :: remaining
          copiedRev := copiedRev
          counter := counter }
        next := by
  let copied := copyFindallAtom counter source
  exact
    ⟨{ remaining := remaining
       copiedRev := copied.value :: copiedRev
       counter := copied.counter },
      .next counter source remaining copiedRev⟩

/-- Running the local microstep relation to exhaustion is exactly the
executable `copyFindallBag` fold.  The number of steps is the number of source
solutions; no copy is erased into a zero-step quotient. -/
theorem BagCopyStepsN.run :
    ∀ (counter : Nat) (sources copiedRev : List Atom),
      BagCopyStepsN sources.length
        { remaining := sources
          copiedRev := copiedRev
          counter := counter }
        { remaining := []
          copiedRev :=
            (copyFindallBag counter sources).values.reverse ++ copiedRev
          counter := (copyFindallBag counter sources).counter }
  | counter, [], copiedRev => by
      simpa [copyFindallBag] using
        (BagCopyStepsN.zero
          { remaining := []
            copiedRev := copiedRev
            counter := counter })
  | counter, source :: remaining, copiedRev => by
      let copied := copyFindallAtom counter source
      have first :
          BagCopyStep
            { remaining := source :: remaining
              copiedRev := copiedRev
              counter := counter }
            { remaining := remaining
              copiedRev := copied.value :: copiedRev
              counter := copied.counter } :=
        .next counter source remaining copiedRev
      have tail :=
        BagCopyStepsN.run copied.counter remaining
          (copied.value :: copiedRev)
      have combined :=
        BagCopyStepsN.succ remaining.length _ _ _ first tail
      simpa [copyFindallBag, copied, List.reverse_cons, List.append_assoc]
        using combined

/-- Starting from an empty accumulator, reversing the terminal accumulator
recovers the macro copier's exact source-order result. -/
theorem BagCopyStepsN.run_initial (counter : Nat) (sources : List Atom) :
    BagCopyStepsN sources.length (BagCopyState.initial counter sources)
      { remaining := []
        copiedRev := (copyFindallBag counter sources).values.reverse
        counter := (copyFindallBag counter sources).counter } := by
  simpa [BagCopyState.initial] using
    BagCopyStepsN.run counter sources []

/-- Each microstep advances neither the source list nor the allocator
backwards. -/
theorem BagCopyStep.remaining_length_succ
    {before after : BagCopyState} (step : BagCopyStep before after) :
    before.remaining.length = after.remaining.length + 1 := by
  cases step
  rfl

theorem BagCopyStep.counter_mono
    {before after : BagCopyState} (step : BagCopyStep before after) :
    before.counter ≤ after.counter := by
  cases step
  exact copyFindallAtom_counter_mono _ _

/-- Closed answers are reused exactly and consume no fresh seed. -/
theorem copyFindallAtom_closed
    (counter : Nat) (source : Atom)
    (closed : resolutionAtomClosed source = true) :
    copyFindallAtom counter source =
      { value := source, counter := counter } := by
  simp [copyFindallAtom, closed]

/-- Exact variable case, exposing the repaired starting seed used by the
compact global allocator. -/
theorem copyFindallAtom_var (counter : Nat) (name : String) :
    let seed := advanceCounterPastAtoms counter [.var name]
    copyFindallAtom counter (.var name) =
      { value := .var (name ++ resolutionCompactSuffix seed)
        counter := seed + 1 } := by
  simp [copyFindallAtom, resolutionAtomClosed, PersistentSubst.atomClosed,
    renameAtomSuffix_var]

theorem compact_copy_name_ne_source (name : String) (seed : Nat) :
    name ++ resolutionCompactSuffix seed ≠ name := by
  intro equality
  have lengths := congrArg String.length equality
  simp [resolutionCompactSuffix] at lengths

/-- Two copies of the same residual source variable use distinct terminal
allocation seeds, hence cannot alias across solutions. -/
theorem copyFindallBag_two_same_variables_separate
    (counter : Nat) (name : String) :
    let firstSeed := advanceCounterPastAtoms counter [.var name]
    let secondSeed :=
      advanceCounterPastAtoms (firstSeed + 1) [.var name]
    (copyFindallBag counter [.var name, .var name]).values =
        [.var (name ++ resolutionCompactSuffix firstSeed),
          .var (name ++ resolutionCompactSuffix secondSeed)] ∧
      name ++ resolutionCompactSuffix firstSeed ≠
        name ++ resolutionCompactSuffix secondSeed := by
  dsimp only
  rw [show copyFindallBag counter [.var name, .var name] =
      let first := copyFindallAtom counter (.var name)
      let tail := copyFindallBag first.counter [.var name]
      { values := first.value :: tail.values, counter := tail.counter } from rfl]
  rw [copyFindallAtom_var]
  simp only [copyFindallBag]
  rw [copyFindallAtom_var]
  constructor
  · rfl
  · intro equality
    have seedEquality := congrArg resolutionSeedHighWaterName equality
    simp only [resolutionSeedHighWaterName_append_compact] at seedEquality
    have secondAfterFirst :
        advanceCounterPastAtoms
            (advanceCounterPastAtoms counter [.var name] + 1) [.var name] ≥
          advanceCounterPastAtoms counter [.var name] + 1 :=
      advanceCounterPastAtoms_mono _ _
    omega

/-- Concrete anti-vacuity witness for cross-solution separation. -/
theorem two_solution_copy_witness :
    ∃ first second : String,
      (copyFindallBag 0 [.var "x", .var "x"]).values =
        [.var first, .var second] ∧ first ≠ second := by
  let firstSeed := advanceCounterPastAtoms 0 [.var "x"]
  let secondSeed := advanceCounterPastAtoms (firstSeed + 1) [.var "x"]
  refine
    ⟨"x" ++ resolutionCompactSuffix firstSeed,
      "x" ++ resolutionCompactSuffix secondSeed, ?_, ?_⟩
  · exact
      (copyFindallBag_two_same_variables_separate 0 "x").1
  · exact
      (copyFindallBag_two_same_variables_separate 0 "x").2

/-- Concrete dual witness: one solution containing two occurrences uses one
renaming, so its internal sharing is retained. -/
theorem intra_solution_sharing_witness :
    let source : Atom := .expr [.sym "pair", .var "x", .var "x"]
    let seed := advanceCounterPastAtoms 0 [source]
    (copyFindallBag 0 [source]).values =
        [.expr
          [.sym "pair",
            .var ("x" ++ resolutionCompactSuffix seed),
            .var ("x" ++ resolutionCompactSuffix seed)]] ∧
      (copyFindallBag 0 [source]).counter = seed + 1 := by
  dsimp only
  simp [copyFindallBag, copyFindallAtom, resolutionAtomClosed,
    PersistentSubst.atomClosed, PersistentSubst.atomsClosed,
    renameAtomSuffix, List.attach]

/-- The repair is stronger than a concrete numeral: every variable's occupied
terminal seed is strictly below the counter returned by its copy. -/
theorem copyFindallAtom_var_repairs_occupied_seed
    (counter : Nat) (name : String) :
    resolutionSeedHighWaterName name <
      (copyFindallAtom counter (.var name)).counter := by
  rw [copyFindallAtom_var]
  unfold advanceCounterPastAtoms resolutionSeedHighWaterAtoms
    resolutionSeedHighWaterAtom
  simp only [Atom.vars, resolutionSeedHighWaterNames]
  omega

/-- Fixed hostile-name anti-vacuity witness instantiating the repair theorem. -/
theorem occupied_seed_repair_witness :
    resolutionSeedHighWaterName "x#r4" <
      (copyFindallAtom 0 (.var "x#r4")).counter :=
  copyFindallAtom_var_repairs_occupied_seed 0 "x#r4"

end PLeaTTa.FindallCopy
