-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.PeTTaSpec.PrologCopy
Purpose: Independent finite-tree copying with injective fresh alpha-renaming.
Trusted boundary: none
Main exports: Term.IsFreshCopy, PreparedTermCopy, prepareTermCopy
-/
import Mathlib.Data.List.Basic
import PLeaTTa.PeTTaSpec.PrologResolver

namespace PLeaTTa.PeTTaSpec.PrologCore

open OpenSubstitution
open Resolver

/-!
ISO `throw/1` and Prolog collectors copy finite terms while preserving variable
sharing.  This module isolates that common operation from exception and
collection control.  A copy is an injective alpha-renaming of exactly the
variables occurring in the materialized input term.  Its targets occupy a
reserved half-open interval in the generated-variable namespace.

The allocator starts above both the caller-provided high-water and every
generated identity still live in the current substitution or materialized
term.  Consequently applying the old substitution to the copied term is a
no-op.  This is the freshness fact consumed by two-phase catch selection and,
later, copied-template `findall/3`.

[SPEC ISO Prolog `copy_term/2` finite-tree variable renaming]
[SPEC SWI-Prolog `throw/1`, exception argument is copied]
-/

mutual

/-- Rename every logical variable in one finite independent term. -/
def Term.renameVariables (rename : LogicVar → LogicVar) : Term → Term
  | .variable identity => .variable (rename identity)
  | .atom name => .atom name
  | .integer value => .integer value
  | .float value => .float value
  | .string value => .string value
  | .compound functor arguments =>
      .compound functor (Terms.renameVariables rename arguments)
  | .list items none => .list (Terms.renameVariables rename items) none
  | .list items (some tail) =>
      .list (Terms.renameVariables rename items)
        (some (Term.renameVariables rename tail))

/-- Pointwise variable renaming for a finite ordered term sequence. -/
def Terms.renameVariables (rename : LogicVar → LogicVar) : List Term → List Term
  | [] => []
  | term :: terms =>
      Term.renameVariables rename term :: Terms.renameVariables rename terms

end

mutual

/-- Renaming a finite term maps its ordered variable-occurrence list
pointwise.  This accounting lemma keeps later allocator proofs independent of
the recursive spelling of `Term.renameVariables`. -/
theorem termVariables_renameVariables
    (rename : LogicVar → LogicVar) (term : Term) :
    termVariables (term.renameVariables rename) =
      (termVariables term).map rename :=
  match term with
  | .variable identity => by
      simp [Term.renameVariables, termVariables]
  | .atom name => by
      simp [Term.renameVariables, termVariables]
  | .integer value => by
      simp [Term.renameVariables, termVariables]
  | .float value => by
      simp [Term.renameVariables, termVariables]
  | .string value => by
      simp [Term.renameVariables, termVariables]
  | .compound functor arguments => by
      simp only [Term.renameVariables, termVariables]
      exact termsVariables_renameVariables rename arguments
  | .list items none => by
      simp only [Term.renameVariables, termVariables]
      exact termsVariables_renameVariables rename items
  | .list items (some tail) => by
      simp only [Term.renameVariables, termVariables, List.map_append]
      rw [termsVariables_renameVariables rename items,
        termVariables_renameVariables rename tail]

/-- Sequence counterpart of `termVariables_renameVariables`. -/
theorem termsVariables_renameVariables
    (rename : LogicVar → LogicVar) (terms : List Term) :
    termsVariables (Terms.renameVariables rename terms) =
      (termsVariables terms).map rename :=
  match terms with
  | [] => by
      simp [Terms.renameVariables, termsVariables]
  | term :: terms => by
      simp only [Terms.renameVariables, termsVariables, List.map_append]
      rw [termVariables_renameVariables rename term,
        termsVariables_renameVariables rename terms]

end

mutual

/-- Every variable in a term is generated at or above `lower`. -/
def Term.GeneratedAtLeast (lower : Nat) : Term → Prop
  | .variable (.generated index) => lower ≤ index
  | .variable (.source _) | .variable (.anonymous _) => False
  | .atom _ | .integer _ | .float _ | .string _ => True
  | .compound _ arguments => Terms.GeneratedAtLeast lower arguments
  | .list items none => Terms.GeneratedAtLeast lower items
  | .list items (some tail) =>
      Terms.GeneratedAtLeast lower items ∧ tail.GeneratedAtLeast lower

/-- Every variable in an ordered term sequence is generated at/above `lower`. -/
def Terms.GeneratedAtLeast (lower : Nat) : List Term → Prop
  | [] => True
  | term :: terms =>
      term.GeneratedAtLeast lower ∧ Terms.GeneratedAtLeast lower terms

end

mutual

/-- Lowering the allocation floor preserves structural generated-variable
support. -/
theorem generatedAtLeast_mono_term
    {smaller larger : Nat} (ordered : smaller ≤ larger) :
    ∀ {term : Term}, term.GeneratedAtLeast larger →
      term.GeneratedAtLeast smaller
  | .variable (.generated _index), above => Nat.le_trans ordered above
  | .variable (.source _), impossible => False.elim impossible
  | .variable (.anonymous _), impossible => False.elim impossible
  | .atom _, _ => trivial
  | .integer _, _ => trivial
  | .float _, _ => trivial
  | .string _, _ => trivial
  | .compound _ _arguments, above =>
      generatedAtLeast_mono_terms ordered above
  | .list _items none, above =>
      generatedAtLeast_mono_terms ordered above
  | .list _items (some _tail), above =>
      ⟨generatedAtLeast_mono_terms ordered above.1,
        generatedAtLeast_mono_term ordered above.2⟩

/-- Ordered-sequence counterpart of `generatedAtLeast_mono_term`. -/
theorem generatedAtLeast_mono_terms
    {smaller larger : Nat} (ordered : smaller ≤ larger) :
    ∀ {terms : List Term}, Terms.GeneratedAtLeast larger terms →
      Terms.GeneratedAtLeast smaller terms
  | [], _ => trivial
  | _ :: _, above =>
      ⟨generatedAtLeast_mono_term ordered above.1,
        generatedAtLeast_mono_terms ordered above.2⟩

end

mutual

/-- Every variable occurrence in a structurally generated-above term has a
concrete generated index at or above the advertised floor. -/
theorem generatedAtLeast_index_of_mem_term
    {lower : Nat} {identity : LogicVar} :
    ∀ {term : Term}, term.GeneratedAtLeast lower →
      identity ∈ termVariables term →
        ∃ index, identity = .generated index ∧ lower ≤ index
  | .variable (.generated index), above, member => by
      simp only [termVariables, List.mem_singleton] at member
      subst identity
      exact ⟨index, rfl, above⟩
  | .variable (.source _), impossible, _ => False.elim impossible
  | .variable (.anonymous _), impossible, _ => False.elim impossible
  | .atom _, _, member => by simp [termVariables] at member
  | .integer _, _, member => by simp [termVariables] at member
  | .float _, _, member => by simp [termVariables] at member
  | .string _, _, member => by simp [termVariables] at member
  | .compound _ _, above, member =>
      generatedAtLeast_index_of_mem_terms above member
  | .list _ none, above, member =>
      generatedAtLeast_index_of_mem_terms above member
  | .list _ (some _), above, member => by
      simp only [termVariables, List.mem_append] at member
      rcases member with member | member
      · exact generatedAtLeast_index_of_mem_terms above.1 member
      · exact generatedAtLeast_index_of_mem_term above.2 member

/-- Ordered-sequence counterpart of
`generatedAtLeast_index_of_mem_term`. -/
theorem generatedAtLeast_index_of_mem_terms
    {lower : Nat} {identity : LogicVar} :
    ∀ {terms : List Term}, Terms.GeneratedAtLeast lower terms →
      identity ∈ termsVariables terms →
        ∃ index, identity = .generated index ∧ lower ≤ index
  | [], _, member => by simp [termsVariables] at member
  | _ :: _, above, member => by
      simp only [termsVariables, List.mem_append] at member
      rcases member with member | member
      · exact generatedAtLeast_index_of_mem_term above.1 member
      · exact generatedAtLeast_index_of_mem_terms above.2 member

end


mutual

/-- Renaming every variable into the generated namespace above `lower`
establishes the structural range predicate. -/
theorem renameTermVariables_generatedAtLeast
    (rename : LogicVar → LogicVar) (lower : Nat)
    (range : ∀ identity, ∃ index,
      rename identity = .generated index ∧ lower ≤ index)
    (term : Term) :
    (term.renameVariables rename).GeneratedAtLeast lower :=
  match term with
  | .variable identity => by
      obtain ⟨index, renamed, bound⟩ := range identity
      simp [Term.renameVariables, Term.GeneratedAtLeast, renamed, bound]
  | .atom name => by trivial
  | .integer value => by trivial
  | .float value => by trivial
  | .string value => by trivial
  | .compound functor arguments => by
      exact renameTermsVariables_generatedAtLeast rename lower range arguments
  | .list items tail => by
      cases tail with
      | none =>
          exact renameTermsVariables_generatedAtLeast rename lower range items
      | some tail =>
          exact ⟨renameTermsVariables_generatedAtLeast rename lower range items,
            renameTermVariables_generatedAtLeast rename lower range tail⟩
termination_by 2 * sizeOf term
decreasing_by all_goals (simp_wf; omega)

/-- Sequence counterpart of `Term.renameVariables_generatedAtLeast`. -/
theorem renameTermsVariables_generatedAtLeast
    (rename : LogicVar → LogicVar) (lower : Nat)
    (range : ∀ identity, ∃ index,
      rename identity = .generated index ∧ lower ≤ index)
    (terms : List Term) :
    Terms.GeneratedAtLeast lower (Terms.renameVariables rename terms) :=
  match terms with
  | [] => by trivial
  | term :: terms => by
      exact ⟨renameTermVariables_generatedAtLeast rename lower range term,
        renameTermsVariables_generatedAtLeast rename lower range terms⟩
termination_by 2 * sizeOf terms + 1
decreasing_by all_goals (simp_wf; omega)

end


/-- A variable lies strictly below the generated allocation boundary.  Source
and anonymous identities are automatically distinct from every generated
target and therefore satisfy the predicate at every boundary. -/
def LogicVar.GeneratedBelowBoundary (lower : Nat) : LogicVar → Prop
  | .source _ | .anonymous _ => True
  | .generated index => index < lower

theorem LogicVar.GeneratedBelowBoundary.ne_generated_atLeast
    {lower index : Nat} {source : LogicVar}
    (below : source.GeneratedBelowBoundary lower) (above : lower ≤ index) :
    source ≠ .generated index := by
  cases source with
  | source name => exact LogicVar.source_ne_generated name index
  | anonymous anonymousIndex =>
      exact LogicVar.anonymous_ne_generated anonymousIndex index
  | generated sourceIndex =>
      change sourceIndex < lower at below
      intro same
      have indexEquality : sourceIndex = index := by
        injection same
      have atLeast : lower ≤ sourceIndex := by
        simpa [indexEquality] using above
      exact (Nat.not_lt_of_ge atLeast) below

mutual

/-- Replacing a variable below the allocation boundary cannot affect a term
whose variables are all at or above that boundary. -/
theorem instantiateTerm_eq_self_of_generatedAtLeast
    {lower : Nat} {source : LogicVar} {replacement : Term}
    (below : source.GeneratedBelowBoundary lower)
    (term : Term) (above : Term.GeneratedAtLeast lower term) :
    Term.instantiateOne source replacement term = term :=
  match term, above with
  | .variable (.generated index), above => by
      have different : .generated index ≠ source :=
        Ne.symm (below.ne_generated_atLeast above)
      simp [Term.instantiateOne, different]
  | .variable (.source name), impossible => False.elim impossible
  | .variable (.anonymous index), impossible => False.elim impossible
  | .atom name, _ => rfl
  | .integer value, _ => rfl
  | .float value, _ => rfl
  | .string value, _ => rfl
  | .compound functor arguments, above => by
      simp only [Term.instantiateOne]
      rw [instantiateTerms_eq_self_of_generatedAtLeast
        (replacement := replacement) below arguments above]
  | .list items none, above => by
      simp only [Term.instantiateOne]
      rw [instantiateTerms_eq_self_of_generatedAtLeast
        (replacement := replacement) below items above]
  | .list items (some tail), above => by
      simp only [Term.instantiateOne]
      rw [instantiateTerms_eq_self_of_generatedAtLeast
          (replacement := replacement) below items above.1,
        instantiateTerm_eq_self_of_generatedAtLeast
          (replacement := replacement) below tail above.2]
termination_by 2 * sizeOf term
decreasing_by all_goals (simp_wf; omega)

/-- Sequence counterpart of
`Term.instantiateOne_eq_self_of_generatedAtLeast`. -/
theorem instantiateTerms_eq_self_of_generatedAtLeast
    {lower : Nat} {source : LogicVar} {replacement : Term}
    (below : source.GeneratedBelowBoundary lower)
    (terms : List Term) (above : Terms.GeneratedAtLeast lower terms) :
    Terms.instantiateOne source replacement terms = terms :=
  match terms, above with
  | [], _ => rfl
  | term :: terms, above => by
      change Term.GeneratedAtLeast lower term ∧
        Terms.GeneratedAtLeast lower terms at above
      have head :=
        instantiateTerm_eq_self_of_generatedAtLeast
          (replacement := replacement) below term above.1
      have tail :=
        instantiateTerms_eq_self_of_generatedAtLeast
          (replacement := replacement) below terms above.2
      rw [Terms.instantiateOne, head, tail]
termination_by 2 * sizeOf terms + 1
decreasing_by all_goals (simp_wf; omega)

end


/-- Every substitution domain is below a generated allocation boundary. -/
def Substitution.DomainsBelow (lower : Nat) : Substitution → Prop
  | [] => True
  | (source, _) :: bindings =>
      source.GeneratedBelowBoundary lower ∧
        Substitution.DomainsBelow lower bindings

/-- The existing generated-ceiling invariant implies the domain-only view
needed for substitution stability. -/
theorem Substitution.domainsBelow_of_generatedBelow
    {lower : Nat} {bindings : Substitution}
    (below : GeneratedBelow lower (substitutionVariables bindings)) :
    Substitution.DomainsBelow lower bindings := by
  induction bindings with
  | nil => trivial
  | cons binding bindings inductionHypothesis =>
      rcases binding with ⟨source, replacement⟩
      constructor
      · cases source with
        | source name => trivial
        | anonymous index => trivial
        | generated index =>
            apply below index
            simp [substitutionVariables]
      · apply inductionHypothesis
        intro index member
        apply below index
        simp [substitutionVariables, member]

/-- A substitution whose domains are below the allocation boundary acts as
the identity on a term made only of variables allocated above it. -/
theorem Substitution.applyTerm_eq_self_of_generatedAtLeast
    {lower : Nat} {bindings : Substitution} {term : Term}
    (domains : Substitution.DomainsBelow lower bindings)
    (above : term.GeneratedAtLeast lower) :
    bindings.applyTerm term = term := by
  induction bindings with
  | nil => rfl
  | cons binding bindings inductionHypothesis =>
      rcases binding with ⟨source, replacement⟩
      rcases domains with ⟨sourceBelow, tailBelow⟩
      simp only [Substitution.applyTerm]
      rw [inductionHypothesis tailBelow,
        instantiateTerm_eq_self_of_generatedAtLeast sourceBelow term above]

namespace Copy

/-- Distinct source variables occurring in a term, in stable first-occurrence
order. -/
def copyVariables (term : Term) : List LogicVar :=
  (termVariables term).eraseDups

/-- Canonical injective renaming for a finite term. -/
def copyRename (firstFresh : Nat) (term : Term) (identity : LogicVar) :
    LogicVar :=
  .generated (firstFresh + (copyVariables term).idxOf identity)

/-- Deterministic finite alpha-copy at a caller-selected allocation boundary. -/
def copyTerm (firstFresh : Nat) (term : Term) : Term :=
  term.renameVariables (copyRename firstFresh term)

/-- Exclusive upper bound of the variables allocated by `copyTerm`. -/
def copyNextFresh (firstFresh : Nat) (term : Term) : Nat :=
  firstFresh + (copyVariables term).length

/-- Independent semantic characterization of a finite fresh copy.  The target
is an injective alpha-renaming on the variables that actually occur, and every
renamed variable lies inside the advertised allocation interval. -/
def Term.IsFreshCopy (source copied : Term) (firstFresh nextFresh : Nat) : Prop :=
  ∃ rename : LogicVar → LogicVar,
    copied = source.renameVariables rename ∧
      (∀ identity, identity ∈ termVariables source →
        ∃ index, rename identity = .generated index ∧
          firstFresh ≤ index ∧ index < nextFresh) ∧
      (∀ left, left ∈ termVariables source →
        ∀ right, right ∈ termVariables source →
          rename left = rename right → left = right)

/-- `copyTerm` satisfies the independent fresh-copy characterization. -/
theorem copyTerm_isFreshCopy (firstFresh : Nat) (term : Term) :
    Term.IsFreshCopy term (copyTerm firstFresh term) firstFresh
      (copyNextFresh firstFresh term) := by
  refine ⟨copyRename firstFresh term, rfl, ?_, ?_⟩
  · intro identity member
    have inVariables : identity ∈ copyVariables term := by
      exact List.mem_eraseDups.mpr member
    refine ⟨firstFresh + (copyVariables term).idxOf identity,
      rfl, by omega, ?_⟩
    have indexBound := List.idxOf_lt_length_of_mem inVariables
    simp only [copyNextFresh]
    omega
  · intro left leftMember right rightMember same
    have leftIn : left ∈ copyVariables term :=
      List.mem_eraseDups.mpr leftMember
    have rightIn : right ∈ copyVariables term :=
      List.mem_eraseDups.mpr rightMember
    have indexSame : (copyVariables term).idxOf left =
        (copyVariables term).idxOf right := by
      simpa [copyRename] using same
    exact (List.idxOf_inj leftIn).mp indexSame

/-- Every output variable of `copyTerm` lies at or above its reservation
start. -/
theorem copyTerm_generatedAtLeast (firstFresh : Nat) (term : Term) :
    (copyTerm firstFresh term).GeneratedAtLeast firstFresh := by
  exact renameTermVariables_generatedAtLeast
    (copyRename firstFresh term) firstFresh
    (fun identity =>
      ⟨firstFresh + (copyVariables term).idxOf identity,
        rfl, Nat.le_add_right firstFresh _⟩)
    term

/-- Every generated identity emitted by `copyTerm` lies strictly below the
exclusive upper bound returned by `copyNextFresh`.  Together with
`copyTerm_generatedAtLeast`, this pins the copy to its advertised half-open
allocation interval. -/
theorem copyTerm_generatedBelowNextFresh (firstFresh : Nat) (term : Term) :
    GeneratedBelow (copyNextFresh firstFresh term)
      (termVariables (copyTerm firstFresh term)) := by
  rw [copyTerm, termVariables_renameVariables]
  intro index member
  rcases List.mem_map.mp member with ⟨identity, identityMember, renamed⟩
  have active : identity ∈ copyVariables term :=
    List.mem_eraseDups.mpr identityMember
  have position := List.idxOf_lt_length_of_mem active
  simp only [copyRename] at renamed
  injection renamed with indexEq
  simp only [copyNextFresh]
  omega

/-- A freshly copied term is variable-disjoint from every older term whose
generated identities lie below the copy's reservation start.  This is the
allocator-facing separation lemma used when a collector prepends one new
solution to an already copied bag. -/
theorem copyTerm_variables_disjoint_of_generatedBelow
    (firstFresh : Nat) (source older : Term)
    (olderBelow : GeneratedBelow firstFresh (termVariables older)) :
    List.Disjoint (termVariables (copyTerm firstFresh source))
      (termVariables older) := by
  rw [List.disjoint_left]
  intro identity copiedMember olderMember
  rw [copyTerm, termVariables_renameVariables] at copiedMember
  rcases List.mem_map.mp copiedMember with
    ⟨sourceIdentity, sourceMember, copiedEq⟩
  have active : sourceIdentity ∈ copyVariables source :=
    List.mem_eraseDups.mpr sourceMember
  have position := List.idxOf_lt_length_of_mem active
  simp only [copyRename] at copiedEq
  subst identity
  have below := olderBelow
    (firstFresh + (copyVariables source).idxOf sourceIdentity) olderMember
  omega

/-- Complete deterministic copy preparation from a raw term and current
substitution.  The raw term is materialized first, as ISO `throw/1` requires;
the materialized value is then copied apart. -/
structure PreparedTermCopy where
  materialized : Term
  copied : Term
  firstFresh : Nat
  nextFresh : Nat
deriving Repr, Inhabited

def prepareTermCopy (allocatorHighWater : Nat) (bindings : Substitution)
    (raw : Term) : PreparedTermCopy :=
  let materialized := bindings.applyTerm raw
  let liveVariables :=
    substitutionVariables bindings ++ termVariables materialized
  let firstFresh :=
    max allocatorHighWater (variablesGeneratedCeiling liveVariables)
  { materialized := materialized
    copied := copyTerm firstFresh materialized
    firstFresh := firstFresh
    nextFresh := copyNextFresh firstFresh materialized }

@[simp] theorem prepareTermCopy_materialized (allocatorHighWater : Nat)
    (bindings : Substitution) (raw : Term) :
    (prepareTermCopy allocatorHighWater bindings raw).materialized =
      bindings.applyTerm raw := rfl

theorem prepareTermCopy_first_ge_allocator (allocatorHighWater : Nat)
    (bindings : Substitution) (raw : Term) :
    allocatorHighWater ≤
      (prepareTermCopy allocatorHighWater bindings raw).firstFresh := by
  exact Nat.le_max_left _ _

theorem prepareTermCopy_next_ge_first (allocatorHighWater : Nat)
    (bindings : Substitution) (raw : Term) :
    (prepareTermCopy allocatorHighWater bindings raw).firstFresh ≤
      (prepareTermCopy allocatorHighWater bindings raw).nextFresh := by
  simp only [prepareTermCopy, copyNextFresh]
  omega

theorem prepareTermCopy_next_ge_allocator (allocatorHighWater : Nat)
    (bindings : Substitution) (raw : Term) :
    allocatorHighWater ≤
      (prepareTermCopy allocatorHighWater bindings raw).nextFresh :=
  Nat.le_trans (prepareTermCopy_first_ge_allocator _ _ _)
    (prepareTermCopy_next_ge_first _ _ _)

/-- Prepared copying really is injective alpha-copying of the materialized
term, not merely a fresh-looking output. -/
theorem prepareTermCopy_isFreshCopy (allocatorHighWater : Nat)
    (bindings : Substitution) (raw : Term) :
    Term.IsFreshCopy
      (prepareTermCopy allocatorHighWater bindings raw).materialized
      (prepareTermCopy allocatorHighWater bindings raw).copied
      (prepareTermCopy allocatorHighWater bindings raw).firstFresh
      (prepareTermCopy allocatorHighWater bindings raw).nextFresh := by
  exact copyTerm_isFreshCopy _ _

/-- The reservation start dominates every generated identity already live in
the substitution (both domains and values) and in the materialized exception
term.  This is the allocator-side half of the no-capture argument. -/
theorem prepareTermCopy_first_dominates_live (allocatorHighWater : Nat)
    (bindings : Substitution) (raw : Term) :
    GeneratedBelow
      (prepareTermCopy allocatorHighWater bindings raw).firstFresh
      (substitutionVariables bindings ++
        termVariables
          (prepareTermCopy allocatorHighWater bindings raw).materialized) := by
  let materialized := bindings.applyTerm raw
  let liveVariables :=
    substitutionVariables bindings ++ termVariables materialized
  let ceiling := variablesGeneratedCeiling liveVariables
  have allBelow : GeneratedBelow ceiling liveVariables :=
    generatedBelow_variablesGeneratedCeiling liveVariables
  simpa [prepareTermCopy, materialized, liveVariables, ceiling] using
    allBelow.mono (Nat.le_max_right allocatorHighWater ceiling)

/-- The old substitution cannot capture or rewrite any variable in the
prepared copy.  This is the exact stability property required by two-phase
exception matching. -/
theorem prepareTermCopy_stable (allocatorHighWater : Nat)
    (bindings : Substitution) (raw : Term) :
    bindings.applyTerm
      (prepareTermCopy allocatorHighWater bindings raw).copied =
      (prepareTermCopy allocatorHighWater bindings raw).copied := by
  let materialized := bindings.applyTerm raw
  let liveVariables :=
    substitutionVariables bindings ++ termVariables materialized
  let ceiling := variablesGeneratedCeiling liveVariables
  let firstFresh := max allocatorHighWater ceiling
  have belowFirst : GeneratedBelow firstFresh
      (substitutionVariables bindings ++ termVariables materialized) := by
    simpa [firstFresh, materialized, prepareTermCopy] using
      prepareTermCopy_first_dominates_live allocatorHighWater bindings raw
  have bindingsBelow : GeneratedBelow firstFresh
      (substitutionVariables bindings) := by
    intro index member
    apply belowFirst index
    exact List.mem_append_left _ member
  apply Substitution.applyTerm_eq_self_of_generatedAtLeast
    (Substitution.domainsBelow_of_generatedBelow bindingsBelow)
  exact copyTerm_generatedAtLeast firstFresh materialized

/-! ## Concrete anti-vacuity witnesses

These small computed theorems pin the three semantic properties that are easy
to lose in an apparently plausible copy routine: materialization must happen
before renaming, repeated occurrences must remain aliases, and distinct source
variables must receive distinct generated identities. -/

/-- A bound source variable is materialized before copying.  A copy-before-
materialization implementation would produce a generated variable here. -/
theorem materialize_before_copy_witness :
    let source : LogicVar := .source "$x"
    let bindings : Substitution := [(source, .atom "$bound")]
    let prepared := prepareTermCopy 7 bindings (.variable source)
    prepared.materialized = .atom "$bound" ∧
      prepared.copied = .atom "$bound" ∧
      prepared.nextFresh = prepared.firstFresh := by
  exact ⟨rfl, rfl, rfl⟩

/-- Two occurrences of the same source variable remain the same generated
variable after copying; sharing is preserved rather than duplicated. -/
theorem repeated_variable_sharing_witness :
    copyTerm 7
        (.compound "$pair"
          [.variable (.source "$x"), .variable (.source "$x")]) =
      .compound "$pair"
        [.variable (.generated 7), .variable (.generated 7)] := by
  rfl

/-- Distinct source variables receive distinct consecutive generated
identities in stable first-occurrence order. -/
theorem distinct_variables_separated_witness :
    copyTerm 7
        (.compound "$pair"
          [.variable (.source "$x"), .variable (.source "$y")]) =
      .compound "$pair"
        [.variable (.generated 7), .variable (.generated 8)] ∧
      LogicVar.generated 7 ≠ LogicVar.generated 8 := by
  exact ⟨rfl, by decide⟩

/-- A generated identity already live in a substitution value raises the
reservation start even when it is not a substitution domain.  This guards the
global-high-water argument against checking domains only. -/
theorem substitution_value_raises_copy_boundary_witness :
    let bindings : Substitution :=
      [(.source "$x", .variable (.generated 12))]
    let prepared :=
      prepareTermCopy 3 bindings (.variable (.source "$y"))
    prepared.firstFresh = 13 ∧
      prepared.copied = .variable (.generated 13) ∧
      prepared.nextFresh = 14 := by
  exact ⟨rfl, rfl, rfl⟩

end Copy

end PLeaTTa.PeTTaSpec.PrologCore
