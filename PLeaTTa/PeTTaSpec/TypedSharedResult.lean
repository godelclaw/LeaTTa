/-
Module: PLeaTTa.PeTTaSpec.TypedSharedResult
Purpose: Independent semantic specification of the one Prolog output shared
  by every branch of pinned typed-function dispatch.
Trusted boundary: none
Main exports: TermUnifier, IsMostGeneralUnifier, OrderedMguFold,
  ResolvesTypedSharedResult, IsMostGeneralUnifier.extend_one
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

@[simp] theorem applyTerm_float (bindings : Substitution)
    (value : PLeaTTa.PrologFloatIdentity) :
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

/-! ## Incremental semantic MGUs

Pinned typed dispatch contributes its shared-output equations from left to
right.  The executable compiler uses a monadic fold, but the independent
content is simpler: an MGU for a prefix can be extended by an MGU for the
next equation after applying the prefix substitution.  This section proves
that algebra once, without choosing the executable unifier's variable
orientation.
-/

/-- Two ordered equation collections have exactly the same semantic
unifiers.  This is useful for reducing same-headed compound equations to
their genuinely varying arguments without introducing an algorithm. -/
def SameUnifiers (left right : List (Term × Term)) : Prop :=
  ∀ binding, UnifiesEquations binding left ↔
    UnifiesEquations binding right

/-- MGU status transports across an extensional equality of unifier sets. -/
theorem IsMostGeneralUnifier.transport
    {binding : Substitution} {left right : List (Term × Term)}
    (mostGeneral : IsMostGeneralUnifier binding left)
    (same : SameUnifiers left right) :
    IsMostGeneralUnifier binding right := by
  constructor
  · exact (same binding).mp mostGeneral.1
  · intro candidate candidateUnifies
    exact mostGeneral.2 candidate ((same candidate).mpr candidateUnifies)

/-- The empty substitution is the semantic MGU of no equations. -/
theorem empty_is_mgu_nil : IsMostGeneralUnifier [] [] := by
  constructor
  · intro equation member
    simp at member
  · intro candidate _candidateUnifies
    exact ⟨candidate, fun _term => rfl⟩

/-- A reflexive equation contributes no binding. -/
theorem empty_is_mgu_reflexive (term : Term) :
    IsMostGeneralUnifier [] [(term, term)] := by
  constructor
  · intro equation member
    simp only [List.mem_singleton] at member
    subst equation
    rfl
  · intro candidate _candidateUnifies
    exact ⟨candidate, fun _term => rfl⟩

/-- Incremental MGU composition.  `base` handles the ordered prefix;
`extension` handles the next equation after the prefix has been applied.
Their append is therefore an MGU for the prefix followed by that equation.
No idempotence or deterministic orientation assumption is needed. -/
theorem IsMostGeneralUnifier.extend_one
    {base extension : Substitution}
    {equations : List (Term × Term)} {left right : Term}
    (baseMgu : IsMostGeneralUnifier base equations)
    (extensionMgu : IsMostGeneralUnifier extension
      [(base.applyTerm left, base.applyTerm right)]) :
    IsMostGeneralUnifier (extension ++ base)
      (equations ++ [(left, right)]) := by
  constructor
  · intro equation member
    rcases List.mem_append.mp member with old | next
    · unfold TermUnifier
      rw [Substitution.applyTerm_append, Substitution.applyTerm_append]
      exact congrArg (extension.applyTerm) (baseMgu.1 equation old)
    · simp only [List.mem_singleton] at next
      subst equation
      unfold TermUnifier
      rw [Substitution.applyTerm_append, Substitution.applyTerm_append]
      exact extensionMgu.1
        (base.applyTerm left, base.applyTerm right) (by simp)
  · intro candidate candidateUnifies
    have candidatePrefix : UnifiesEquations candidate equations := by
      intro equation member
      exact candidateUnifies equation (List.mem_append_left _ member)
    rcases baseMgu.2 candidate candidatePrefix with
      ⟨residual, candidateFactors⟩
    have residualNext : UnifiesEquations residual
        [(base.applyTerm left, base.applyTerm right)] := by
      intro equation member
      simp only [List.mem_singleton] at member
      subst equation
      unfold TermUnifier
      rw [← candidateFactors left, ← candidateFactors right]
      exact candidateUnifies (left, right) (by simp)
    rcases extensionMgu.2 residual residualNext with
      ⟨final, residualFactors⟩
    refine ⟨final, ?_⟩
    intro term
    rw [candidateFactors term, residualFactors (base.applyTerm term),
      Substitution.applyTerm_append]

/-- Independent left-to-right construction of a semantic MGU.  Each step
only requires an MGU for the next already-instantiated equation; it does not
prescribe how that MGU is computed or orient variable aliases. -/
inductive OrderedMguFold : List (Term × Term) → Substitution → Prop where
  | nil : OrderedMguFold [] []
  | snoc {equations : List (Term × Term)} {base extension : Substitution}
      {left right : Term}
      (prior : OrderedMguFold equations base)
      (next : IsMostGeneralUnifier extension
        [(base.applyTerm left, base.applyTerm right)]) :
      OrderedMguFold (equations ++ [(left, right)]) (extension ++ base)

/-- Every independent incremental MGU fold denotes an MGU for the complete
ordered equation sequence. -/
theorem OrderedMguFold.isMostGeneral
    {equations : List (Term × Term)} {binding : Substitution}
    (fold : OrderedMguFold equations binding) :
    IsMostGeneralUnifier binding equations := by
  induction fold with
  | nil => exact empty_is_mgu_nil
  | snoc prior next induction => exact induction.extend_one next

/-! ### A nontrivial later-branch witness

The first incomplete typed branch fixes `Out` to a `partial/2` value.  A
later branch with the same head can then contribute a variable alias inside
the encoded proper argument list.  These lemmas show that the compound/list
constraint has exactly the same unifiers as that alias and construct the MGU
for the two shared-output equations incrementally.
-/

/-- Independent one-argument partial value used by the later-branch proof. -/
def unaryPartialTerm (head : String) (argument : Term) : Term :=
  .compound "partial" [.atom head, .list [argument] none]

/-- Same-headed unary partial values are unifiable exactly when their sole
arguments are.  Compound and proper-list structure is compared
declaratively through substitution, not by an executable decomposition
procedure. -/
theorem unaryPartialTerm_same_unifiers (head : String)
    (left right : Term) :
    SameUnifiers [(left, right)]
      [(unaryPartialTerm head left, unaryPartialTerm head right)] := by
  intro binding
  constructor <;> intro unifies equation member
  · simp only [List.mem_singleton] at member
    subst equation
    have argumentEquality := unifies (left, right) (by simp)
    change binding.applyTerm left = binding.applyTerm right at argumentEquality
    change binding.applyTerm (unaryPartialTerm head left) =
      binding.applyTerm (unaryPartialTerm head right)
    simpa [unaryPartialTerm] using argumentEquality
  · simp only [List.mem_singleton] at member
    subst equation
    have compoundEquality := unifies
      (unaryPartialTerm head left, unaryPartialTerm head right) (by simp)
    change binding.applyTerm (unaryPartialTerm head left) =
      binding.applyTerm (unaryPartialTerm head right) at compoundEquality
    change binding.applyTerm left = binding.applyTerm right
    simpa [unaryPartialTerm] using compoundEquality

/-- Eliminating a fresh variable alias is also an MGU when the alias is
nested at the corresponding argument of same-headed `partial/2` values. -/
theorem unaryPartial_alias_is_mgu (head : String)
    (source target : LogicVar) (distinct : source ≠ target) :
    IsMostGeneralUnifier [(source, .variable target)]
      [(unaryPartialTerm head (.variable source),
        unaryPartialTerm head (.variable target))] := by
  have absent : Term.occurs source (.variable target) = false := by
    simp [Term.occurs, Ne.symm distinct]
  exact (singleton_variable_is_mgu source (.variable target) absent).transport
    (unaryPartialTerm_same_unifiers head (.variable source)
      (.variable target))

/-- Two incomplete typed branches whose partial values share a head, have
arity one, and carry distinct variable arguments have the expected
incremental MGU: first bind `output` to the first partial value, then alias
its differing argument to the second branch's argument. -/
theorem two_unary_partial_branches_is_mgu (head : String)
    (output left right : LogicVar) (outputNeLeft : output ≠ left)
    (outputNeRight : output ≠ right) (leftNeRight : left ≠ right) :
    IsMostGeneralUnifier
      [(left, .variable right),
       (output, unaryPartialTerm head (.variable left))]
      [(.variable output, unaryPartialTerm head (.variable left)),
       (.variable output, unaryPartialTerm head (.variable right))] := by
  let firstValue := unaryPartialTerm head (.variable left)
  let secondValue := unaryPartialTerm head (.variable right)
  have firstAbsent : Term.occurs output firstValue = false := by
    simp [firstValue, unaryPartialTerm, Term.occurs, Terms.occurs,
      Ne.symm outputNeLeft]
  have secondAbsent : Term.occurs output secondValue = false := by
    simp [secondValue, unaryPartialTerm, Term.occurs, Terms.occurs,
      Ne.symm outputNeRight]
  have firstMgu : IsMostGeneralUnifier [(output, firstValue)]
      [(.variable output, firstValue)] :=
    singleton_variable_is_mgu output firstValue firstAbsent
  have nextMgu : IsMostGeneralUnifier [(left, .variable right)]
      [(Substitution.applyTerm [(output, firstValue)] (.variable output),
        Substitution.applyTerm [(output, firstValue)] secondValue)] := by
    rw [show Substitution.applyTerm [(output, firstValue)]
          (.variable output) = firstValue by
        simp [Substitution.applyTerm, Term.instantiateOne],
      show Substitution.applyTerm [(output, firstValue)] secondValue =
          secondValue by
        exact Term.instantiateOne_eq_self_of_occurs_false output firstValue
          secondValue secondAbsent]
    exact unaryPartial_alias_is_mgu head left right leftNeRight
  simpa [firstValue, secondValue] using firstMgu.extend_one nextMgu

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

/-- An incremental left-to-right MGU construction can be used directly as a
shared-result resolution witness. -/
theorem OrderedMguFold.resolvesTypedSharedResult
    {shared result : Term} {raw resolved : List TypedBranch}
    {binding : Substitution}
    (fold : OrderedMguFold (sharedResultEquations shared raw) binding)
    (resultEq : result = binding.applyTerm shared)
    (resolvedEq : resolved = instantiateBranches binding raw) :
    ResolvesTypedSharedResult shared raw result resolved := by
  subst result
  subst resolved
  exact .byMgu binding fold.isMostGeneral

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

/-- Nontrivial two-branch resolution witness.  The first partial binds the
shared output, the second aliases one nested argument, and both ordered goal
lists are instantiated in place without reordering or deduplication. -/
theorem two_unary_partial_branches_resolve (head : String)
    (output left right : LogicVar) (outputNeLeft : output ≠ left)
    (outputNeRight : output ≠ right) (leftNeRight : left ≠ right)
    (firstGoals secondGoals : List Goal) :
    let binding : Substitution :=
      [(left, .variable right),
       (output, unaryPartialTerm head (.variable left))]
    ResolvesTypedSharedResult (.variable output)
      [(unaryPartialTerm head (.variable left), firstGoals),
       (unaryPartialTerm head (.variable right), secondGoals)]
      (unaryPartialTerm head (.variable right))
      [(unaryPartialTerm head (.variable right),
          binding.applyGoals firstGoals),
       (unaryPartialTerm head (.variable right),
          binding.applyGoals secondGoals)] := by
  dsimp only
  let binding : Substitution :=
    [(left, .variable right),
     (output, unaryPartialTerm head (.variable left))]
  have mostGeneral : IsMostGeneralUnifier binding
      [(.variable output, unaryPartialTerm head (.variable left)),
       (.variable output, unaryPartialTerm head (.variable right))] := by
    simpa [binding] using
      two_unary_partial_branches_is_mgu head output left right
        outputNeLeft outputNeRight leftNeRight
  have sharedMostGeneral : IsMostGeneralUnifier binding
      (sharedResultEquations (.variable output)
        [(unaryPartialTerm head (.variable left), firstGoals),
         (unaryPartialTerm head (.variable right), secondGoals)]) := by
    simpa [sharedResultEquations] using mostGeneral
  have resolution :=
    ResolvesTypedSharedResult.byMgu binding sharedMostGeneral
  simpa [binding, instantiateBranches, instantiateBranch,
    Substitution.applyTerm, Term.instantiateOne, Terms.instantiateOne,
    unaryPartialTerm, outputNeLeft, outputNeRight, leftNeRight,
    Ne.symm outputNeLeft, Ne.symm outputNeRight, Ne.symm leftNeRight] using
    resolution

end PLeaTTa.PeTTaSpec.PrologCore.TypedSharedResult
