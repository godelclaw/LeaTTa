-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.OpenBindingAgreement
Purpose: Relate independent open substitutions to executable substitutions
  without identifying their variable representations by definition.
Trusted boundary: none
Main exports: EncodingInjectiveOn, TermStateAgrees, BindingsAgreeOn,
  alias_bindings_agree_on_pair, resolved_bindings_agree_on_pair
-/
import PLeaTTa.Proofs.ObservationAgreement
import PLeaTTa.Proofs.Unification
import PLeaTTa.PeTTaSpec.OpenOrdered

namespace PLeaTTa.OpenBindingAgreement

open Metta (Atom Subst)
open PLeaTTa.CompilerAdequacy
open PLeaTTa.PeTTaSpec.PrologCore
open PLeaTTa.PeTTaSpec.PrologCore.OpenSubstitution

/-- Executable spelling of one compiler-generated variable.  This is the
representation named by `TermAgrees.generatedVariable`; it is not a
freshness claim. -/
def generatedExecutableName (index : Nat) : String :=
  compilerGeneratedName index

/-- Current executable spelling of each independent logical-variable
identity.  Distinct independent namespaces are deliberately retained in
`LogicVar`; this projection exposes where the executable string namespace can
identify them. -/
def logicVarExecutableName : LogicVar → String
  | .source name => name
  | .generated index => generatedExecutableName index
  | .anonymous index => "_ anonymous " ++ toString index

/-- The executable variable-name projection is injective on exactly the
finite identities relevant to a source/translation slice.  The domain must be
derived independently from source and generated variables; an empty domain is
not a supported-source certificate. -/
def EncodingInjectiveOn (domain : List LogicVar) : Prop :=
  ∀ {left right}, left ∈ domain → right ∈ domain →
    logicVarExecutableName left = logicVarExecutableName right → left = right

/-- A source variable can use exactly the spelling allocated to a generated
compiler variable.  The parser permits this spelling, so freshness cannot be
omitted from a universal composition theorem. -/
theorem source_generated_encoding_collision (index : Nat) :
    logicVarExecutableName (.source (generatedExecutableName index)) =
      logicVarExecutableName (.generated index) := by
  rfl

/-- Concrete negative witness: the current executable projection is not
injective on a colliding source/generated pair. -/
theorem source_generated_pair_not_injective (index : Nat) :
    ¬ EncodingInjectiveOn
      [.source (generatedExecutableName index), .generated index] := by
  intro injective
  have equality := injective
    (left := .source (generatedExecutableName index))
    (right := .generated index) (by simp) (by simp)
    (source_generated_encoding_collision index)
  exact LogicVar.source_ne_generated (generatedExecutableName index) index
    equality

/-- A single source/generated pair has an injective executable encoding
exactly under the explicit freshness premise used by later simulation
lemmas. -/
theorem source_generated_pair_injective (name : String) (index : Nat)
    (fresh : name ≠ generatedExecutableName index) :
    EncodingInjectiveOn [.source name, .generated index] := by
  intro left right leftMember rightMember sameName
  simp only [List.mem_cons, List.not_mem_nil, or_false] at leftMember rightMember
  rcases leftMember with rfl | rfl <;>
    rcases rightMember with rfl | rfl
  · rfl
  · exact False.elim (fresh sameName)
  · exact False.elim (fresh sameName.symm)
  · rfl

/-- One independently specified term and its executable representation still
agree after applying the independent and executable finite substitutions.
This is an open-term relation: it does not force either result to be ground. -/
def TermStateAgrees (reference : Substitution) (executable : Subst)
    (term : Term) (atom : Atom) : Prop :=
  TermAgrees (reference.applyTerm term) (PLeaTTa.subst executable atom)

/-- Pointwise cross-representation agreement on an explicit finite set of
term/atom pairs.  Each pair must agree both before and after substitution, so
the relation cannot manufacture a representation correspondence merely from
the desired post-state. -/
def BindingsAgreeOn (reference : Substitution) (executable : Subst)
    (pairs : List (Term × Atom)) : Prop :=
  ∀ pair, pair ∈ pairs →
    TermAgrees pair.1 pair.2 ∧
      TermStateAgrees reference executable pair.1 pair.2

/-- Select one post-substitution agreement from a finite binding agreement. -/
theorem BindingsAgreeOn.term {reference : Substitution} {executable : Subst}
    {pairs : List (Term × Atom)} (agreement : BindingsAgreeOn reference executable pairs)
    {term : Term} {atom : Atom} (member : (term, atom) ∈ pairs) :
    TermStateAgrees reference executable term atom :=
  (agreement (term, atom) member).2

/-- Empty substitutions preserve every already-established compiler
representation agreement. -/
theorem termStateAgrees_empty {term : Term} {atom : Atom}
    (agreement : TermAgrees term atom) :
    TermStateAgrees [] [] term atom := by
  unfold TermStateAgrees
  change TermAgrees term (PLeaTTa.subst [] atom)
  rw [PLeaTTa.subst_eq_self_of_domain_free [] atom]
  · exact agreement
  · intro name _member
    simp [Metta.Subst.lookup]

/-- The source variable and one compiler-generated result variable, paired
with their independently related executable atoms. -/
def sourceGeneratedPairs (name : String) (index : Nat) :
    List (Term × Atom) :=
  [(.variable (.source name), .var name),
   (.variable (.generated index), .var (generatedExecutableName index))]

/-- Independent alias state produced when a source variable is unified with
one generated result variable. -/
def aliasReferenceBinding (name : String) (index : Nat) : Substitution :=
  [(.source name, .variable (.generated index))]

/-- Executable counterpart of `aliasReferenceBinding`. -/
def aliasExecutableBinding (name : String) (index : Nat) : Subst :=
  [(name, .var (generatedExecutableName index))]

/-- The aliased source variable agrees after both substitutions. -/
theorem alias_source_agrees (name : String) (index : Nat)
    (fresh : name ≠ generatedExecutableName index) :
    TermStateAgrees (aliasReferenceBinding name index)
      (aliasExecutableBinding name index)
      (.variable (.source name)) (.var name) := by
  simp [TermStateAgrees, aliasReferenceBinding, aliasExecutableBinding,
    Term.instantiateOne, PLeaTTa.subst, PLeaTTa.substN,
    Metta.Subst.lookup, Ne.symm fresh]
  exact TermAgrees.generatedVariable index

/-- The generated target itself remains unbound and agrees through a fresh
source-variable alias. -/
theorem alias_generated_agrees (name : String) (index : Nat)
    (fresh : name ≠ generatedExecutableName index) :
    TermStateAgrees (aliasReferenceBinding name index)
      (aliasExecutableBinding name index)
      (.variable (.generated index))
      (.var (generatedExecutableName index)) := by
  simp [TermStateAgrees, aliasReferenceBinding, aliasExecutableBinding,
    Term.instantiateOne, PLeaTTa.subst, PLeaTTa.substN,
    Metta.Subst.lookup, Ne.symm fresh]
  exact TermAgrees.generatedVariable index

/-- The complete two-variable alias state is related across representations.
The source/generated name-freshness premise is explicit rather than hidden in
the executable spelling. -/
theorem alias_bindings_agree_on_pair (name : String) (index : Nat)
    (fresh : name ≠ generatedExecutableName index) :
    BindingsAgreeOn (aliasReferenceBinding name index)
      (aliasExecutableBinding name index) (sourceGeneratedPairs name index) := by
  intro pair member
  simp only [sourceGeneratedPairs, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl
  · exact ⟨.sourceVariable name, alias_source_agrees name index fresh⟩
  · exact ⟨.generatedVariable index,
      alias_generated_agrees name index fresh⟩

/-- Independent state after the generated target and its source alias both
resolve to one integer. -/
def resolvedReferenceBinding (name : String) (index : Nat)
    (value : Int) : Substitution :=
  [(.generated index, .integer value),
   (.source name, .variable (.generated index))]

/-- Executable counterpart of `resolvedReferenceBinding`. -/
def resolvedExecutableBinding (name : String) (index : Nat)
    (value : Int) : Subst :=
  [(name, .gnd (.int value)),
   (generatedExecutableName index, .gnd (.int value))]

/-- The source identity denotes the resolved integer on both sides. -/
theorem resolved_source_agrees (name : String) (index : Nat)
    (value : Int) :
    TermStateAgrees (resolvedReferenceBinding name index value)
      (resolvedExecutableBinding name index value)
      (.variable (.source name)) (.var name) := by
  unfold TermStateAgrees
  rw [show
    (resolvedReferenceBinding name index value).applyTerm
        (.variable (.source name)) = .integer value by
      simp [resolvedReferenceBinding, Substitution.applyTerm,
        Term.instantiateOne]]
  simp [resolvedExecutableBinding, PLeaTTa.subst, PLeaTTa.substN,
    Metta.Subst.lookup]
  exact TermAgrees.integer value

/-- The generated identity denotes the same resolved integer on both sides. -/
theorem resolved_generated_agrees (name : String) (index : Nat)
    (value : Int) :
    TermStateAgrees (resolvedReferenceBinding name index value)
      (resolvedExecutableBinding name index value)
      (.variable (.generated index))
      (.var (generatedExecutableName index)) := by
  unfold TermStateAgrees
  rw [show
    (resolvedReferenceBinding name index value).applyTerm
        (.variable (.generated index)) = .integer value by
      simp [resolvedReferenceBinding, Substitution.applyTerm,
        Term.instantiateOne]]
  simp [resolvedExecutableBinding, PLeaTTa.subst, PLeaTTa.substN,
    Metta.Subst.lookup]
  exact TermAgrees.integer value

/-- Resolution preserves the complete two-variable relation. -/
theorem resolved_bindings_agree_on_pair (name : String) (index : Nat)
    (value : Int) :
    BindingsAgreeOn (resolvedReferenceBinding name index value)
      (resolvedExecutableBinding name index value)
      (sourceGeneratedPairs name index) := by
  intro pair member
  simp only [sourceGeneratedPairs, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl
  · exact ⟨.sourceVariable name, resolved_source_agrees name index value⟩
  · exact ⟨.generatedVariable index,
      resolved_generated_agrees name index value⟩

/-- An independent state in which a colliding source identity and generated
identity carry deliberately distinct integer values. -/
def splitCollisionReferenceBinding (index : Nat) (left right : Int) :
    Substitution :=
  [(.source (generatedExecutableName index), .integer left),
   (.generated index, .integer right)]

private theorem TermAgrees.integer_atom {value : Int} {atom : Atom}
    (agreement : TermAgrees (.integer value) atom) :
    atom = .gnd (.int value) := by
  cases agreement
  rfl

/-- Representation-level consequence of the collision: no single executable
substitution can model distinct values for the colliding independent source
and generated identities.  This is a counterexample to any universal bridge
that omits name freshness. -/
theorem collision_cannot_represent_distinct_integers (index : Nat)
    (left right : Int) (different : left ≠ right)
    (executable : Subst) :
    ¬ (TermStateAgrees (splitCollisionReferenceBinding index left right)
          executable
          (.variable (.source (generatedExecutableName index)))
          (.var (generatedExecutableName index)) ∧
       TermStateAgrees (splitCollisionReferenceBinding index left right)
          executable (.variable (.generated index))
          (.var (generatedExecutableName index))) := by
  rintro ⟨sourceAgreement, generatedAgreement⟩
  unfold TermStateAgrees at sourceAgreement generatedAgreement
  rw [show
    (splitCollisionReferenceBinding index left right).applyTerm
        (.variable (.source (generatedExecutableName index))) =
      .integer left by
        simp [splitCollisionReferenceBinding, Substitution.applyTerm,
          Term.instantiateOne]] at sourceAgreement
  rw [show
    (splitCollisionReferenceBinding index left right).applyTerm
        (.variable (.generated index)) = .integer right by
      simp [splitCollisionReferenceBinding, Substitution.applyTerm,
        Term.instantiateOne]] at generatedAgreement
  have sameAtom : Atom.gnd (.int left) = .gnd (.int right) :=
    (TermAgrees.integer_atom sourceAgreement).symm.trans
      (TermAgrees.integer_atom generatedAgreement)
  have valueEquality : left = right := by simpa using sameAtom
  exact different valueEquality

end PLeaTTa.OpenBindingAgreement
