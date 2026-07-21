/-
Module: PLeaTTa.PeTTaSpec.TypedSharedResult
Purpose: Independent semantic specification of the one Prolog output shared
  by every branch of pinned typed-function dispatch.
Trusted boundary: none
Main exports: TermUnifier, IsMostGeneralUnifier,
  ResolvesTypedSharedResult, singleton_variable_is_mgu
-/
import PLeaTTa.PeTTaSpec.OpenSubstitution

namespace PLeaTTa.PeTTaSpec.PrologCore.TypedSharedResult

open OpenSubstitution

/-! ## Declarative first-order unification content

These definitions say what a unifier means without choosing an elimination
algorithm or a variable orientation.  In particular, they do not mention
PLeaTTa's executable `unifyTopExact`.  The later adequacy bridge may prove
that a deterministic executable substitution realizes one of these semantic
MGUs without making that orientation part of pinned PeTTa's specification.
-/

/-- One finite independent substitution makes both terms syntactically equal. -/
def TermUnifier (binding : Substitution) (left right : Term) : Prop :=
  binding.applyTerm left = binding.applyTerm right

/-- Pointwise unification of an ordered equation sequence. -/
def UnifiesEquations (binding : Substitution)
    (equations : List (Term × Term)) : Prop :=
  ∀ equation, equation ∈ equations →
    TermUnifier binding equation.1 equation.2

/-- `specific` is an instance of `general`.  Equality is required for every
independent term, not only for the variables occurring in one test corpus. -/
def FactorsThrough (specific general : Substitution) : Prop :=
  ∃ residual : Substitution, ∀ term : Term,
    specific.applyTerm term =
      residual.applyTerm (general.applyTerm term)

/-- Semantic MGU: a unifier through which every other finite unifier factors.
No deterministic variable-name orientation is built into this definition. -/
def IsMostGeneralUnifier (binding : Substitution)
    (equations : List (Term × Term)) : Prop :=
  UnifiesEquations binding equations ∧
    ∀ candidate, UnifiesEquations candidate equations →
      FactorsThrough candidate binding

/-! ## Structural substitution laws used by the MGU proof -/

namespace Substitution

@[simp] theorem applyTerm_atom (bindings : Substitution) (name : String) :
    bindings.applyTerm (.atom name) = .atom name := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      cases binding
      simp only [OpenSubstitution.Substitution.applyTerm, induction,
        Term.instantiateOne]

@[simp] theorem applyTerm_integer (bindings : Substitution) (value : Int) :
    bindings.applyTerm (.integer value) = .integer value := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      cases binding
      simp only [OpenSubstitution.Substitution.applyTerm, induction,
        Term.instantiateOne]

@[simp] theorem applyTerm_float (bindings : Substitution) (value : Float) :
    bindings.applyTerm (.float value) = .float value := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      cases binding
      simp only [OpenSubstitution.Substitution.applyTerm, induction,
        Term.instantiateOne]

@[simp] theorem applyTerm_string (bindings : Substitution) (value : String) :
    bindings.applyTerm (.string value) = .string value := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      cases binding
      simp only [OpenSubstitution.Substitution.applyTerm, induction,
        Term.instantiateOne]

@[simp] theorem applyTerm_compound (bindings : Substitution)
    (functor : String) (arguments : List Term) :
    bindings.applyTerm (.compound functor arguments) =
      .compound functor (bindings.applyTerms arguments) := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      cases binding
      simp only [OpenSubstitution.Substitution.applyTerm,
        OpenSubstitution.Substitution.applyTerms, induction,
        Term.instantiateOne]

@[simp] theorem applyTerm_list_none (bindings : Substitution)
    (items : List Term) :
    bindings.applyTerm (.list items none) =
      .list (bindings.applyTerms items) none := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      cases binding
      simp only [OpenSubstitution.Substitution.applyTerm,
        OpenSubstitution.Substitution.applyTerms, induction,
        Term.instantiateOne]

@[simp] theorem applyTerm_list_some (bindings : Substitution)
    (items : List Term) (tail : Term) :
    bindings.applyTerm (.list items (some tail)) =
      .list (bindings.applyTerms items) (some (bindings.applyTerm tail)) := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      cases binding
      simp only [OpenSubstitution.Substitution.applyTerm,
        OpenSubstitution.Substitution.applyTerms, induction,
        Term.instantiateOne]

end Substitution

mutual

/-- A replacement is invisible to a substitution which already identifies
the replaced variable with the replacement. -/
theorem Substitution.applyTerm_instantiateOne_of_unifier
    (bindings : Substitution) (source : LogicVar) (replacement : Term)
    (unifies : TermUnifier bindings (.variable source) replacement) :
    (term : Term) →
      bindings.applyTerm (Term.instantiateOne source replacement term) =
        bindings.applyTerm term := by
  intro term
  cases term with
  | «variable» identity =>
      by_cases same : identity = source
      · subst identity
        simpa [Term.instantiateOne, TermUnifier] using unifies.symm
      · simp [Term.instantiateOne, same]
  | atom name => rfl
  | integer value => rfl
  | float value => rfl
  | string value => rfl
  | compound functor arguments =>
      simp only [Term.instantiateOne, Substitution.applyTerm_compound,
        Term.compound.injEq, true_and]
      exact Substitution.applyTerms_instantiateOne_of_unifier bindings source
        replacement unifies arguments
  | list items tail =>
      cases tail with
      | none =>
          simp only [Term.instantiateOne, Substitution.applyTerm_list_none,
            Term.list.injEq]
          exact ⟨Substitution.applyTerms_instantiateOne_of_unifier bindings
            source replacement unifies items, trivial⟩
      | some finalTail =>
          simp only [Term.instantiateOne, Substitution.applyTerm_list_some,
            Term.list.injEq, Option.some.injEq]
          exact ⟨Substitution.applyTerms_instantiateOne_of_unifier bindings
              source replacement unifies items,
            Substitution.applyTerm_instantiateOne_of_unifier bindings source
              replacement unifies finalTail⟩

/-- Ordered-list companion to replacement absorption. -/
theorem Substitution.applyTerms_instantiateOne_of_unifier
    (bindings : Substitution) (source : LogicVar) (replacement : Term)
    (unifies : TermUnifier bindings (.variable source) replacement) :
    (terms : List Term) →
      bindings.applyTerms (Terms.instantiateOne source replacement terms) =
        bindings.applyTerms terms := by
  intro terms
  cases terms with
  | nil => rfl
  | cons term terms =>
      simp only [Terms.instantiateOne, Substitution.applyTerms_cons,
        List.cons.injEq]
      exact ⟨Substitution.applyTerm_instantiateOne_of_unifier bindings source
          replacement unifies term,
        Substitution.applyTerms_instantiateOne_of_unifier bindings source
          replacement unifies terms⟩

end

mutual

/-- A variable-free-for-`source` term is unchanged by one replacement. -/
theorem Term.instantiateOne_eq_self_of_occurs_false
    (source : LogicVar) (replacement : Term) :
    (term : Term) → Term.occurs source term = false →
      Term.instantiateOne source replacement term = term := by
  intro term absent
  cases term with
  | «variable» identity =>
      simp only [Term.occurs, decide_eq_false_iff_not] at absent
      simp [Term.instantiateOne, absent]
  | atom name => rfl
  | integer value => rfl
  | float value => rfl
  | string value => rfl
  | compound functor arguments =>
      simp only [Term.occurs] at absent
      simp only [Term.instantiateOne, Term.compound.injEq, true_and]
      exact Terms.instantiateOne_eq_self_of_occurs_false source replacement
        arguments absent
  | list items tail =>
      cases tail with
      | none =>
          simp only [Term.occurs] at absent
          rw [Term.instantiateOne,
            Terms.instantiateOne_eq_self_of_occurs_false source replacement
              items absent]
      | some finalTail =>
          simp only [Term.occurs, Bool.or_eq_false_iff] at absent
          rw [Term.instantiateOne,
            Terms.instantiateOne_eq_self_of_occurs_false source replacement
              items absent.1,
            Term.instantiateOne_eq_self_of_occurs_false source replacement
              finalTail absent.2]

/-- Ordered-list companion to occurrence-free replacement. -/
theorem Terms.instantiateOne_eq_self_of_occurs_false
    (source : LogicVar) (replacement : Term) :
    (terms : List Term) → Terms.occurs source terms = false →
      Terms.instantiateOne source replacement terms = terms := by
  intro terms absent
  cases terms with
  | nil => rfl
  | cons term terms =>
      simp only [Terms.occurs, Bool.or_eq_false_iff] at absent
      simp only [Terms.instantiateOne, List.cons.injEq]
      exact ⟨Term.instantiateOne_eq_self_of_occurs_false source replacement
          term absent.1,
        Terms.instantiateOne_eq_self_of_occurs_false source replacement terms
          absent.2⟩

end


/-- Eliminating one fresh variable is a semantic MGU, not merely a unifier.
This is the first shared-output constraint generated by pinned `maplist/3`.
The occurs premise states the finite-tree fragment explicitly; SWI rational
trees outside it remain an anchoring boundary rather than being conflated. -/
theorem singleton_variable_is_mgu (source : LogicVar) (value : Term)
    (absent : Term.occurs source value = false) :
    IsMostGeneralUnifier [(source, value)]
      [(.variable source, value)] := by
  constructor
  · intro equation member
    simp only [List.mem_singleton] at member
    subst equation
    unfold TermUnifier
    simp only [Substitution.applyTerm_singleton, Term.instantiateOne]
    exact (Term.instantiateOne_eq_self_of_occurs_false source value value
      absent).symm
  · intro candidate candidateUnifies
    have identifies : TermUnifier candidate (.variable source) value :=
      candidateUnifies (.variable source, value) (by simp)
    refine ⟨candidate, ?_⟩
    intro term
    simpa only [Substitution.applyTerm_singleton] using
      (Substitution.applyTerm_instantiateOne_of_unifier candidate source value
        identifies term).symm

/-- Distinct rigid atoms have no semantic unifier.  This negative example
prevents `TermUnifier` from degenerating into an always-true relation. -/
theorem distinct_atoms_have_no_unifier (left right : String)
    (different : left ≠ right) :
    ¬ ∃ binding, TermUnifier binding (.atom left) (.atom right) := by
  rintro ⟨binding, unifies⟩
  simp only [TermUnifier, Substitution.applyTerm_atom, Term.atom.injEq]
    at unifies
  exact different unifies

/-! ## Ordered shared-result resolution -/

/-- Independent typed branch: result template paired with its ordered goals. -/
abbrev TypedBranch := Term × List Goal

/-- The one shared output contributes one equation per raw branch, in source
order and with duplicates retained. [SPEC translator.pl:320-321,349-358] -/
def sharedResultEquations (shared : Term)
    (branches : List TypedBranch) : List (Term × Term) :=
  branches.map fun branch => (shared, branch.1)

/-- Apply one finite semantic substitution to a branch result and all goals. -/
def instantiateBranch (binding : Substitution)
    (branch : TypedBranch) : TypedBranch :=
  (binding.applyTerm branch.1, binding.applyGoals branch.2)

/-- Ordered pointwise branch instantiation; `List.map` preserves duplicates. -/
def instantiateBranches (binding : Substitution)
    (branches : List TypedBranch) : List TypedBranch :=
  branches.map (instantiateBranch binding)

/-- Independent meaning of resolving the `Out` shared by pinned typed
dispatch.  Any semantic MGU is acceptable here; deterministic orientation is
an executable refinement obligation, not a PeTTa language rule. -/
inductive ResolvesTypedSharedResult (shared : Term)
    (rawBranches : List TypedBranch) :
    Term → List TypedBranch → Prop where
  | byMgu (binding : Substitution)
      (mostGeneral : IsMostGeneralUnifier binding
        (sharedResultEquations shared rawBranches)) :
      ResolvesTypedSharedResult shared rawBranches
        (binding.applyTerm shared)
        (instantiateBranches binding rawBranches)

/-- Resolution exposes one semantic MGU and its exact ordered map. -/
theorem ResolvesTypedSharedResult.witness
    {shared result : Term} {raw resolved : List TypedBranch}
    (resolution : ResolvesTypedSharedResult shared raw result resolved) :
    ∃ binding,
      IsMostGeneralUnifier binding (sharedResultEquations shared raw) ∧
      result = binding.applyTerm shared ∧
      resolved = instantiateBranches binding raw := by
  cases resolution with
  | byMgu binding mostGeneral => exact ⟨binding, mostGeneral, rfl, rfl⟩

/-- Shared-output resolution preserves branch count exactly. -/
theorem ResolvesTypedSharedResult.length_eq
    {shared result : Term} {raw resolved : List TypedBranch}
    (resolution : ResolvesTypedSharedResult shared raw result resolved) :
    resolved.length = raw.length := by
  cases resolution
  simp [instantiateBranches]

/-- The semantic MGU identifies the shared result with every raw branch
result. -/
theorem IsMostGeneralUnifier.shared_branch_result
    {binding : Substitution} {shared : Term}
    {branches : List TypedBranch}
    (mostGeneral : IsMostGeneralUnifier binding
      (sharedResultEquations shared branches))
    {branch : TypedBranch} (member : branch ∈ branches) :
    binding.applyTerm branch.1 = binding.applyTerm shared := by
  exact (mostGeneral.1 (shared, branch.1)
    (List.mem_map_of_mem member)).symm

/-- Every resolved branch result equals the resolved shared result.  Together
with `witness`'s exact `List.map` equation, this preserves source index, order,
and duplicate multiplicity rather than reducing branches to a set. -/
theorem ResolvesTypedSharedResult.member_result_eq
    {shared result : Term} {raw resolved : List TypedBranch}
    (resolution : ResolvesTypedSharedResult shared raw result resolved)
    {branch : TypedBranch} (member : branch ∈ resolved) :
    branch.1 = result := by
  cases resolution with
  | byMgu binding mostGeneral =>
      simp only [instantiateBranches, List.mem_map] at member
      obtain ⟨rawBranch, rawMember, rfl⟩ := member
      exact mostGeneral.shared_branch_result rawMember

/-- Any two resolved branch results are equal, even when duplicate source
chains contributed duplicate branches. -/
theorem ResolvesTypedSharedResult.branch_results_pairwise
    {shared result : Term} {raw resolved : List TypedBranch}
    (resolution : ResolvesTypedSharedResult shared raw result resolved)
    {left right : TypedBranch} (leftMember : left ∈ resolved)
    (rightMember : right ∈ resolved) :
    left.1 = right.1 := by
  exact (resolution.member_result_eq leftMember).trans
    (resolution.member_result_eq rightMember).symm

/-- Positive compound/list example: a fresh shared output resolves to the
properly nested `partial/2` term with a singleton semantic MGU. -/
theorem partial_value_shared_result_resolves
    (output : LogicVar) (head : String) (arguments : List Term)
    (fresh : Terms.occurs output arguments = false) :
    ResolvesTypedSharedResult (.variable output)
      [(.compound "partial" [.atom head, .list arguments none], [])]
      (.compound "partial" [.atom head, .list arguments none])
      [(.compound "partial" [.atom head, .list arguments none], [])] := by
  let value := Term.compound "partial" [.atom head, .list arguments none]
  have absent : Term.occurs output value = false := by
    simp [value, Term.occurs, Terms.occurs, fresh]
  have mostGeneral : IsMostGeneralUnifier [(output, value)]
      (sharedResultEquations (.variable output) [(value, [])]) := by
    simpa [sharedResultEquations] using
      singleton_variable_is_mgu output value absent
  have resolution := ResolvesTypedSharedResult.byMgu [(output, value)]
    mostGeneral
  simpa [value, instantiateBranches, instantiateBranch,
    Substitution.applyTerm_singleton, Term.instantiateOne,
    Term.instantiateOne_eq_self_of_occurs_false output value value absent,
    Terms.instantiateOne_eq_self_of_occurs_false output value arguments fresh]
    using resolution

end PLeaTTa.PeTTaSpec.PrologCore.TypedSharedResult
