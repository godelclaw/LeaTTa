/-
Module: PLeaTTa.PeTTaSpec.OpenSubstitution
Purpose: Independent open-term substitution semantics for translation-time
  Prolog variable sharing and its explicit-equality normalization.
Trusted boundary: none
Main exports: Substitution, Unifies, ContinuationRespectsInstantiation,
  explicit_alias_prefix_equivalent_to_shared
-/
import PLeaTTa.PeTTaSpec.PrologCore

namespace PLeaTTa.PeTTaSpec.PrologCore.OpenSubstitution

/-! ### Capture-free replacement of one logical-variable identity

Pinned `build_branch/4` aliases two existing Prolog variables. There are no
binders in the generated target term/goal syntax, so replacing one identity by
an open term is capture-free. These functions are independent of PLeaTTa's
executable `Atom`, `Goal`, and substitution implementations.
-/

mutual

/-- Replace one logical-variable identity throughout an independent term. -/
def Term.instantiateOne (source : LogicVar) (replacement : Term) :
    Term → Term
  | .variable identity =>
      if identity = source then replacement else .variable identity
  | .atom name => .atom name
  | .integer value => .integer value
  | .float value => .float value
  | .string value => .string value
  | .compound functor arguments =>
      .compound functor (Terms.instantiateOne source replacement arguments)
  | .list items none =>
      .list (Terms.instantiateOne source replacement items) none
  | .list items (some tail) =>
      .list (Terms.instantiateOne source replacement items)
        (some (Term.instantiateOne source replacement tail))

/-- Ordered pointwise one-variable replacement for independent terms. -/
def Terms.instantiateOne (source : LogicVar) (replacement : Term) :
    List Term → List Term
  | [] => []
  | term :: terms =>
      Term.instantiateOne source replacement term ::
        Terms.instantiateOne source replacement terms

end

mutual

/-- Replace one logical-variable identity throughout an independent goal. -/
def Goal.instantiateOne (source : LogicVar) (replacement : Term) :
    Goal → Goal
  | .truth => .truth
  | .fail => .fail
  | .unify left right =>
      .unify (Term.instantiateOne source replacement left)
        (Term.instantiateOne source replacement right)
  | .identical left right =>
      .identical (Term.instantiateOne source replacement left)
        (Term.instantiateOne source replacement right)
  | .call predicate arguments =>
      .call predicate (Terms.instantiateOne source replacement arguments)
  | .conjunction goals =>
      .conjunction (Goals.instantiateOne source replacement goals)
  | .disjunction branches =>
      .disjunction (Goals.instantiateOne source replacement branches)
  | .cut => .cut
  | .ifThenElse condition thenBranch elseBranch =>
      .ifThenElse (Goal.instantiateOne source replacement condition)
        (Goal.instantiateOne source replacement thenBranch)
        (Goal.instantiateOne source replacement elseBranch)
  | .softCut condition thenBranch elseBranch =>
      .softCut (Goal.instantiateOne source replacement condition)
        (Goal.instantiateOne source replacement thenBranch)
        (Goal.instantiateOne source replacement elseBranch)
  | .negation goal =>
      .negation (Goal.instantiateOne source replacement goal)
  | .once goal => .once (Goal.instantiateOne source replacement goal)
  | .findall template goal output =>
      .findall (Term.instantiateOne source replacement template)
        (Goal.instantiateOne source replacement goal)
        (Term.instantiateOne source replacement output)
  | .catch goal exception handler =>
      .catch (Goal.instantiateOne source replacement goal)
        (Term.instantiateOne source replacement exception)
        (Goal.instantiateOne source replacement handler)
  | .transaction goal =>
      .transaction (Goal.instantiateOne source replacement goal)
  | .withMutex mutex goal =>
      .withMutex (Term.instantiateOne source replacement mutex)
        (Goal.instantiateOne source replacement goal)
  | .forall generator test =>
      .forall (Goal.instantiateOne source replacement generator)
        (Goal.instantiateOne source replacement test)

/-- Ordered pointwise one-variable replacement for independent goals. -/
def Goals.instantiateOne (source : LogicVar) (replacement : Term) :
    List Goal → List Goal
  | [] => []
  | goal :: goals =>
      Goal.instantiateOne source replacement goal ::
        Goals.instantiateOne source replacement goals

end

/-! ### Finite open substitutions

New extensions are prepended, so application traverses the older tail first
and the newer head last. This resolves chains such as `x ↦ y, y ↦ 42` to
`x ↦ 42`. General compound decomposition remains part of the full ordered
Prolog semantics.
-/

/-- Finite partial substitution over independent logical-variable identities. -/
abbrev Substitution := List (LogicVar × Term)

namespace Substitution

/-- Sequentially instantiate an independent term with all finite bindings. -/
def applyTerm : Substitution → Term → Term
  | [], term => term
  | (source, replacement) :: bindings, term =>
      Term.instantiateOne source replacement (applyTerm bindings term)

/-- Sequentially instantiate an ordered independent term sequence. -/
def applyTerms : Substitution → List Term → List Term
  | [], terms => terms
  | (source, replacement) :: bindings, terms =>
      Terms.instantiateOne source replacement (applyTerms bindings terms)

/-- Sequentially instantiate an independent goal with all finite bindings. -/
def applyGoal : Substitution → Goal → Goal
  | [], goal => goal
  | (source, replacement) :: bindings, goal =>
      Goal.instantiateOne source replacement (applyGoal bindings goal)

/-- Sequentially instantiate an ordered independent goal sequence. -/
def applyGoals : Substitution → List Goal → List Goal
  | [], goals => goals
  | (source, replacement) :: bindings, goals =>
      Goals.instantiateOne source replacement (applyGoals bindings goals)

@[simp] theorem applyTerm_nil (term : Term) :
    applyTerm [] term = term := rfl

@[simp] theorem applyTerms_nil (terms : List Term) :
    applyTerms [] terms = terms := rfl

@[simp] theorem applyGoal_nil (goal : Goal) :
    applyGoal [] goal = goal := rfl

@[simp] theorem applyGoals_nil (goals : List Goal) :
    applyGoals [] goals = goals := rfl

@[simp] theorem applyTerms_empty (bindings : Substitution) :
    applyTerms bindings [] = [] := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      cases binding
      simp only [applyTerms, induction, Terms.instantiateOne]

@[simp] theorem applyGoals_empty (bindings : Substitution) :
    applyGoals bindings [] = [] := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      cases binding
      simp only [applyGoals, induction, Goals.instantiateOne]

@[simp] theorem applyTerm_singleton (source : LogicVar) (replacement term : Term) :
    applyTerm [(source, replacement)] term =
      Term.instantiateOne source replacement term := rfl

@[simp] theorem applyTerms_singleton (source : LogicVar) (replacement : Term)
    (terms : List Term) :
    applyTerms [(source, replacement)] terms =
      Terms.instantiateOne source replacement terms := rfl

@[simp] theorem applyGoal_singleton (source : LogicVar) (replacement : Term)
    (goal : Goal) :
    applyGoal [(source, replacement)] goal =
      Goal.instantiateOne source replacement goal := rfl

@[simp] theorem applyGoals_singleton (source : LogicVar) (replacement : Term)
    (goals : List Goal) :
    applyGoals [(source, replacement)] goals =
      Goals.instantiateOne source replacement goals := rfl

@[simp] theorem applyTerms_cons (bindings : Substitution) (term : Term)
    (terms : List Term) :
    applyTerms bindings (term :: terms) =
      applyTerm bindings term :: applyTerms bindings terms := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      cases binding
      simp only [applyTerms, applyTerm, Terms.instantiateOne, induction]

@[simp] theorem applyGoals_cons (bindings : Substitution) (goal : Goal)
    (goals : List Goal) :
    applyGoals bindings (goal :: goals) =
      applyGoal bindings goal :: applyGoals bindings goals := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      cases binding
      simp only [applyGoals, applyGoal, Goals.instantiateOne, induction]

@[simp] theorem applyGoal_truth (bindings : Substitution) :
    applyGoal bindings .truth = .truth := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      cases binding
      simp only [applyGoal, induction, Goal.instantiateOne]

@[simp] theorem applyGoal_fail (bindings : Substitution) :
    applyGoal bindings .fail = .fail := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      cases binding
      simp only [applyGoal, induction, Goal.instantiateOne]

@[simp] theorem applyGoal_unify (bindings : Substitution) (left right : Term) :
    applyGoal bindings (.unify left right) =
      .unify (applyTerm bindings left) (applyTerm bindings right) := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      cases binding
      simp only [applyGoal, applyTerm, induction, Goal.instantiateOne]

@[simp] theorem applyGoal_identical (bindings : Substitution)
    (left right : Term) :
    applyGoal bindings (.identical left right) =
      .identical (applyTerm bindings left) (applyTerm bindings right) := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      cases binding
      simp only [applyGoal, applyTerm, induction, Goal.instantiateOne]

@[simp] theorem applyGoal_call (bindings : Substitution) (predicate : String)
    (arguments : List Term) :
    applyGoal bindings (.call predicate arguments) =
      .call predicate (applyTerms bindings arguments) := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      cases binding
      simp only [applyGoal, applyTerms, induction, Goal.instantiateOne]

@[simp] theorem applyGoal_conjunction (bindings : Substitution)
    (goals : List Goal) :
    applyGoal bindings (.conjunction goals) =
      .conjunction (applyGoals bindings goals) := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      cases binding
      simp only [applyGoal, applyGoals, induction, Goal.instantiateOne]

@[simp] theorem applyGoal_disjunction (bindings : Substitution)
    (branches : List Goal) :
    applyGoal bindings (.disjunction branches) =
      .disjunction (applyGoals bindings branches) := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      cases binding
      simp only [applyGoal, applyGoals, induction, Goal.instantiateOne]

@[simp] theorem applyGoal_ifThenElse (bindings : Substitution)
    (condition thenBranch elseBranch : Goal) :
    applyGoal bindings (.ifThenElse condition thenBranch elseBranch) =
      .ifThenElse (applyGoal bindings condition)
        (applyGoal bindings thenBranch) (applyGoal bindings elseBranch) := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      cases binding
      simp only [applyGoal, induction, Goal.instantiateOne]

@[simp] theorem applyGoal_once (bindings : Substitution) (goal : Goal) :
    applyGoal bindings (.once goal) = .once (applyGoal bindings goal) := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      cases binding
      simp only [applyGoal, induction, Goal.instantiateOne]

@[simp] theorem applyGoal_withMutex (bindings : Substitution) (mutex : Term)
    (goal : Goal) :
    applyGoal bindings (.withMutex mutex goal) =
      .withMutex (applyTerm bindings mutex) (applyGoal bindings goal) := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      cases binding
      simp only [applyGoal, applyTerm, induction, Goal.instantiateOne]

end Substitution

mutual

/-- Whether an independent logical-variable identity occurs in a term. -/
def Term.occurs (identity : LogicVar) : Term → Bool
  | .variable candidate => decide (candidate = identity)
  | .atom _ => false
  | .integer _ => false
  | .float _ => false
  | .string _ => false
  | .compound _ arguments => Terms.occurs identity arguments
  | .list items none => Terms.occurs identity items
  | .list items (some tail) =>
      Terms.occurs identity items || Term.occurs identity tail

/-- Occurrence over an ordered independent term sequence. -/
def Terms.occurs (identity : LogicVar) : List Term → Bool
  | [] => false
  | term :: terms =>
      Term.occurs identity term || Terms.occurs identity terms

end

/-- Independent open unification fragment needed for branch aliases.

`RootUnifies` acts only on operands after the current substitution has been
applied. Its ordered rules model reflexivity, left-variable elimination, then
right-variable elimination when the left operand is not a variable. This
priority makes variable-variable orientation deterministic. Unsupported
compound decomposition has no rule yet rather than being silently interpreted
as failure. -/
inductive RootUnifies : Term → Term → Substitution → Prop where
  | reflexive (term : Term) : RootUnifies term term []
  | bindLeft (source : LogicVar) (value : Term)
      (different : value ≠ .variable source)
      (occurs : Term.occurs source value = false) :
      RootUnifies (.variable source) value [(source, value)]
  | bindRight (value : Term) (target : LogicVar)
      (notVariable : ∀ identity, value ≠ .variable identity)
      (occurs : Term.occurs target value = false) :
      RootUnifies value (.variable target) [(target, value)]

/-- Open unification first instantiates both operands with the current state,
then prepends the deterministic root extension. [SPEC metta.pl unification;
translator.pl:394-397 for the alias instance] -/
inductive Unifies : Substitution → Term → Term → Substitution → Prop where
  | normalize (bindings extension : Substitution) (left right : Term)
      (root : RootUnifies (bindings.applyTerm left)
        (bindings.applyTerm right) extension) :
      Unifies bindings left right (extension ++ bindings)

/-- A distinct fresh-variable alias from the empty substitution has exactly
the singleton substitution required by the explicit equality normalization. -/
theorem unifies_empty_distinct_alias_output {source target : LogicVar}
    {result : Substitution} (distinct : source ≠ target)
    (unification :
      Unifies [] (.variable source) (.variable target) result) :
    result = [(source, .variable target)] := by
  cases unification with
  | @normalize extension _ _ root =>
      cases root with
      | reflexive => exact False.elim (distinct rfl)
      | bindLeft => rfl
      | bindRight _ _ notVariable _ =>
          exact False.elim (notVariable source rfl)

/-- The explicit equality prefix has an independent unification derivation. -/
theorem unifies_empty_distinct_alias (source target : LogicVar)
    (distinct : source ≠ target) :
    Unifies [] (.variable source) (.variable target)
      [(source, .variable target)] := by
  apply Unifies.normalize [] [(source, .variable target)]
    (.variable source) (.variable target)
  exact .bindLeft source (.variable target)
    (by simpa using Ne.symm distinct)
    (by simp [Term.occurs, Ne.symm distinct])

/-- Existing aliases are instantiated before a new root binding: after
`source = target`, unifying `source` with an integer binds `target`, while the
older alias remains in the substitution tail. -/
theorem unifies_alias_source_with_integer (source target : LogicVar)
    (value : Int) :
    Unifies [(source, .variable target)] (.variable source) (.integer value)
      [(target, .integer value), (source, .variable target)] := by
  apply Unifies.normalize [(source, .variable target)]
    [(target, .integer value)] (.variable source) (.integer value)
  simpa [Substitution.applyTerm, Term.instantiateOne] using
    (RootUnifies.bindLeft target (.integer value)
      (by intro equality; cases equality)
      (by rfl))

/-- Open Prolog identity compares instantiated syntax without grounding open
variables. This differs essentially from the older total-valuation model. -/
def Identical (bindings : Substitution) (left right : Term) : Prop :=
  bindings.applyTerm left = bindings.applyTerm right

/-- Before aliasing, two distinct open variables are not Prolog-identical. -/
theorem empty_distinct_variables_not_identical (source target : LogicVar)
    (distinct : source ≠ target) :
    ¬ Identical [] (.variable source) (.variable target) := by
  simpa [Identical] using distinct

/-- After the singleton alias, the two open variables are Prolog-identical. -/
theorem singleton_alias_makes_variables_identical (source target : LogicVar) :
    Identical [(source, .variable target)]
      (.variable source) (.variable target) := by
  simp [Identical, Term.instantiateOne]

/-- Chained alias/value bindings resolve transitively under open identity. -/
theorem chained_alias_integer_is_identical (source target : LogicVar)
    (value : Int) :
    Identical [(target, .integer value), (source, .variable target)]
      (.variable source) (.integer value) := by
  simp [Identical, Substitution.applyTerm, Term.instantiateOne]

/-! ### Agreement after moving an initial substitution into syntax -/

/-- A carried state and a syntax-instantiated state agree relative to an
initial substitution when every independent query term has the same open
instance on both sides. -/
def StateAgrees (initial carried instantiated : Substitution) : Prop :=
  ∀ term,
    carried.applyTerm term =
      instantiated.applyTerm (initial.applyTerm term)

/-- Ordered pointwise state agreement for complete answer bags. The inductive
list shape makes order and multiplicity preservation explicit. -/
inductive AnswerBagsAgree (initial : Substitution) :
    List Substitution → List Substitution → Prop where
  | nil : AnswerBagsAgree initial [] []
  | cons {carried instantiated : Substitution}
      {carriedAnswers instantiatedAnswers : List Substitution}
      (head : StateAgrees initial carried instantiated)
      (tail : AnswerBagsAgree initial carriedAnswers instantiatedAnswers) :
      AnswerBagsAgree initial (carried :: carriedAnswers)
        (instantiated :: instantiatedAnswers)

/-- Moving the initial substitution into syntax begins from related states. -/
theorem StateAgrees.initial (initial : Substitution) :
    StateAgrees initial initial [] := by
  intro term
  rfl

/-- With no moved substitution, every state agrees with itself. -/
theorem StateAgrees.reflexive (bindings : Substitution) :
    StateAgrees [] bindings bindings := by
  intro term
  rfl

/-- Ordered bag agreement preserves answer count, hence multiplicity. -/
theorem AnswerBagsAgree.length_eq {initial : Substitution}
    {carried instantiated : List Substitution}
    (agreement : AnswerBagsAgree initial carried instantiated) :
    carried.length = instantiated.length := by
  induction agreement with
  | nil => rfl
  | cons _ _ induction => simp [induction]

/-- An agreeing answer bag is empty on one side exactly when it is empty on
the other. -/
theorem AnswerBagsAgree.carried_nil_iff {initial : Substitution}
    {carried instantiated : List Substitution}
    (agreement : AnswerBagsAgree initial carried instantiated) :
    carried = [] ↔ instantiated = [] := by
  cases agreement <;> simp

/-- Ordered bag agreement composes across source-ordered concatenation. -/
theorem AnswerBagsAgree.append {initial : Substitution}
    {leftCarried rightCarried leftInstantiated rightInstantiated :
      List Substitution}
    (left : AnswerBagsAgree initial leftCarried leftInstantiated)
    (right : AnswerBagsAgree initial rightCarried rightInstantiated) :
    AnswerBagsAgree initial (leftCarried ++ rightCarried)
      (leftInstantiated ++ rightInstantiated) := by
  induction left with
  | nil => exact right
  | cons head _ induction => exact .cons head induction

/-- Truncating both related answer bags to the first answer preserves ordered
agreement, the key structural fact for `once` and ordinary `if`. -/
theorem AnswerBagsAgree.take_one {initial : Substitution}
    {carried instantiated : List Substitution}
    (agreement : AnswerBagsAgree initial carried instantiated) :
    AnswerBagsAgree initial (carried.take 1) (instantiated.take 1) := by
  cases agreement with
  | nil => exact .nil
  | cons head tail => exact .cons head .nil

/-- Open identity is invariant when an initial substitution is moved from the
state into both operand terms. -/
theorem StateAgrees.identical_iff {initial carried instantiated : Substitution}
    (agreement : StateAgrees initial carried instantiated)
    (left right : Term) :
    Identical carried left right ↔
      Identical instantiated (initial.applyTerm left)
        (initial.applyTerm right) := by
  unfold Identical
  rw [agreement left, agreement right]

/-- Abstract continuation observations used to state the normalization law
without assuming the unfinished call/effect semantics. -/
abbrev Continuation (Observation : Type) :=
  Substitution → List Goal → Observation → Prop

/-- A continuation respects instantiation when carrying a finite substitution
in its state is observationally equivalent to applying that substitution to
the remaining goal sequence. Proving this law for the complete ordered
Prolog semantics is the explicit remaining bridge obligation. -/
def ContinuationRespectsInstantiation {Observation : Type}
    (observe : Continuation Observation) : Prop :=
  ∀ bindings goals observation,
    observe bindings goals observation ↔
      observe [] (bindings.applyGoals goals) observation

/-- Execute only the explicit variable-alias prefix, then hand the resulting
open substitution and untouched continuation to an abstract observer. -/
def ObservesAfterAlias {Observation : Type}
    (observe : Continuation Observation) (bindings : Substitution)
    (source target : LogicVar) (goals : List Goal)
    (observation : Observation) : Prop :=
  ∃ result,
    Unifies bindings (.variable source) (.variable target) result ∧
      observe result goals observation

/-- Parametric alias-normalization theorem.

For every continuation semantics that proves the explicit substitution law,
executing a fresh alias equality is observationally equivalent to native
Prolog's translation-time sharing, represented by replacing the shared
identity throughout the remaining goals. This theorem does not assume that
the unfinished full ordered semantics satisfies the premise. -/
theorem explicit_alias_prefix_equivalent_to_shared {Observation : Type}
    (observe : Continuation Observation)
    (respects : ContinuationRespectsInstantiation observe)
    (source target : LogicVar) (distinct : source ≠ target)
    (goals : List Goal) (observation : Observation) :
    ObservesAfterAlias observe [] source target goals observation ↔
      observe []
        (Goals.instantiateOne source (.variable target) goals) observation := by
  constructor
  · rintro ⟨result, unification, observed⟩
    have resultEq :=
      unifies_empty_distinct_alias_output distinct unification
    subst result
    exact (respects [(source, .variable target)] goals observation).mp observed
  · intro observed
    refine ⟨[(source, .variable target)],
      unifies_empty_distinct_alias source target distinct, ?_⟩
    exact (respects [(source, .variable target)] goals observation).mpr observed

/-- The pinned nonempty variable-branch rule produces exactly the alias shape
consumed by the parametric normalization theorem. The final equivalence still
retains `ContinuationRespectsInstantiation` as an explicit premise; this
connects the source rule to the semantic obligation without declaring the
unfinished full ordered semantics adequate by definition. -/
theorem normalized_variable_branch_alias_semantics {Observation : Type}
    (observe : Continuation Observation)
    (respects : ContinuationRespectsInstantiation observe)
    (source target : LogicVar) (distinct : source ≠ target)
    (branchGoals aliases continuation : List Goal)
    (template : Term) (branch : Goal)
    (translation : BuildsBranchNormalized (.variable target)
      (.variable source) branchGoals aliases template branch)
    (nonempty : 0 < Goals.flatWidth branchGoals)
    (observation : Observation) :
    aliases = [.unify (.variable source) (.variable target)] ∧
      template = .variable target ∧ branch = .conjunction branchGoals ∧
      (ObservesAfterAlias observe [] source target continuation observation ↔
        observe []
          (Goals.instantiateOne source (.variable target) continuation)
          observation) := by
  obtain ⟨aliasesEq, templateEq, branchEq⟩ :=
    translation.variable_nonempty_shape nonempty
  exact ⟨aliasesEq, templateEq, branchEq,
    explicit_alias_prefix_equivalent_to_shared observe respects source target
      distinct continuation observation⟩

end PLeaTTa.PeTTaSpec.PrologCore.OpenSubstitution
