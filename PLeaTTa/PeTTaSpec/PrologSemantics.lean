/-
Module: PLeaTTa.PeTTaSpec.PrologSemantics
Purpose: Independent declarative semantics for the pure definite-clause
  fragment of the pinned PeTTa target language.
Trusted boundary: none
Main exports: GroundTerm, PureGoal, Holds, DeclarativelyEquivalent
-/
import PLeaTTa.PeTTaSpec.PrologCore

namespace PLeaTTa.PeTTaSpec.PrologCore.Declarative

/-- Ground first-order terms used to interpret pure Prolog clauses. -/
inductive GroundTerm where
  | atom (name : String)
  | integer (value : Int)
  | float (value : Float)
  | string (value : String)
  | compound (functor : String) (arguments : List GroundTerm)
  | list (items : List GroundTerm) (tail : Option GroundTerm)
deriving Repr

/-- A total assignment supplies the Herbrand value of every source variable.
Clause-local variables receive their own independently chosen assignment in
the call rule below. -/
abbrev Valuation := LogicVar → GroundTerm

/- Denotation of independent Prolog terms under a total assignment. -/
mutual

def denoteTerm (valuation : Valuation) : Term → GroundTerm
  | .variable identity => valuation identity
  | .atom name => .atom name
  | .integer value => .integer value
  | .float value => .float value
  | .string value => .string value
  | .compound functor arguments =>
      .compound functor (denoteTerms valuation arguments)
  | .list items none => .list (denoteTerms valuation items) none
  | .list items (some tail) =>
      .list (denoteTerms valuation items) (some (denoteTerm valuation tail))
termination_by structural term => term

def denoteTerms (valuation : Valuation) : List Term → List GroundTerm
  | [] => []
  | term :: terms =>
      denoteTerm valuation term :: denoteTerms valuation terms
termination_by structural terms => terms

end

/-- Pure goals with ordinary first-order declarative meaning.  Operational
features such as cut, clause order, multiplicity, exceptions, and effects are
intentionally absent; they require the separate operational semantics. -/
inductive PureGoal where
  | truth
  | fail
  | unify (left right : Term)
  | call (predicate : String) (arguments : List Term)
  | conjunction (goals : List PureGoal)
  | disjunction (branches : List PureGoal)
deriving Repr

/-- A pure definite clause. -/
structure Clause where
  predicate : String
  parameters : List Term
  body : List PureGoal
deriving Repr

abbrev Program := List Clause

mutual

/-- Declarative satisfaction of one pure goal.  A call chooses a program
clause and a separate valuation for its local variables, relates caller
arguments to the clause head extensionally, and satisfies the clause body. -/
inductive Holds (program : Program) : Valuation → PureGoal → Prop where
  | truth (valuation : Valuation) : Holds program valuation .truth
  | unify (valuation : Valuation) (left right : Term)
      (agreement : denoteTerm valuation left = denoteTerm valuation right) :
      Holds program valuation (.unify left right)
  | call (callerValuation : Valuation) (predicate : String)
      (arguments : List Term) (clause : Clause)
      (clauseValuation : Valuation)
      (inProgram : clause ∈ program)
      (samePredicate : clause.predicate = predicate)
      (sameArguments :
        denoteTerms callerValuation arguments =
          denoteTerms clauseValuation clause.parameters)
      (body : HoldsAll program clauseValuation clause.body) :
      Holds program callerValuation (.call predicate arguments)
  | conjunction (valuation : Valuation) (goals : List PureGoal)
      (body : HoldsAll program valuation goals) :
      Holds program valuation (.conjunction goals)
  | disjunction (valuation : Valuation) (branches : List PureGoal)
      (branch : PureGoal) (inBranches : branch ∈ branches)
      (chosen : Holds program valuation branch) :
      Holds program valuation (.disjunction branches)

/-- Left-to-right conjunction at the declarative level.  This relation
records success only; operational ordering and answer multiplicity are not
claimed here. -/
inductive HoldsAll (program : Program) : Valuation → List PureGoal → Prop where
  | nil (valuation : Valuation) : HoldsAll program valuation []
  | cons (valuation : Valuation) (goal : PureGoal) (goals : List PureGoal)
      (head : Holds program valuation goal)
      (tail : HoldsAll program valuation goals) :
      HoldsAll program valuation (goal :: goals)

end

/-- Two pure goal sequences have the same declarative success set. -/
def DeclarativelyEquivalent (program : Program)
    (left right : List PureGoal) : Prop :=
  ∀ valuation, HoldsAll program valuation left ↔
    HoldsAll program valuation right

/-- Pinned PeTTa's pure definition `empty(_) :- fail`. -/
def emptyClause : Clause where
  predicate := "empty"
  parameters := [.variable (.anonymous 0)]
  body := [.fail]

def emptyProgram : Program := [emptyClause]

/-- Positive example: truth is satisfied under every valuation. -/
theorem truth_has_declarative_solution (program : Program)
    (valuation : Valuation) : Holds program valuation .truth :=
  .truth valuation

/-- Positive example: a term always unifies declaratively with itself. -/
theorem reflexive_unification_has_declarative_solution (program : Program)
    (valuation : Valuation) (term : Term) :
    Holds program valuation (.unify term term) :=
  .unify valuation term term rfl

/-- Failure has no declarative solution. -/
theorem fail_has_no_declarative_solution (program : Program)
    (valuation : Valuation) : ¬ Holds program valuation .fail := by
  intro solution
  cases solution

/-- A conjunction beginning with failure has no declarative solution. -/
theorem fail_cons_has_no_declarative_solution (program : Program)
    (valuation : Valuation) (rest : List PureGoal) :
    ¬ HoldsAll program valuation (.fail :: rest) := by
  intro solution
  cases solution with
  | cons _ _ _ head _ => exact fail_has_no_declarative_solution program valuation head

/-- The pinned `empty/1` predicate has no solution for any caller argument. -/
theorem empty_call_has_no_declarative_solution (valuation : Valuation)
    (argument : Term) :
    ¬ Holds emptyProgram valuation (.call "empty" [argument]) := by
  intro solution
  cases solution with
  | call _ _ _ clause clauseValuation inProgram _ _ body =>
      have clauseEq : clause = emptyClause := by
        simpa [emptyProgram] using inProgram
      subst clause
      exact fail_cons_has_no_declarative_solution emptyProgram
        clauseValuation [] (by simpa [emptyClause] using body)

/-- Distinct truth atoms cannot satisfy unification. -/
theorem false_unification_has_no_declarative_solution
    (valuation : Valuation) :
    ¬ Holds emptyProgram valuation
      (.unify (.atom "true") (.atom "false")) := by
  intro solution
  cases solution with
  | unify _ _ _ agreement => simp [denoteTerm] at agreement

/-- Native PeTTa's `empty(Result)` and PLeaTTa's explicit false equality
have the same declarative success set.  This theorem is deliberately only
about pure success/failure; it does not claim operational order or effects. -/
theorem empty_call_false_unification_equivalent (result : Term) :
    DeclarativelyEquivalent emptyProgram
      [.call "empty" [result]]
      [.unify (.atom "true") (.atom "false")] := by
  intro valuation
  constructor
  · intro solution
    cases solution with
    | cons _ _ _ head _ =>
        exact False.elim
          (empty_call_has_no_declarative_solution valuation result head)
  · intro solution
    cases solution with
    | cons _ _ _ head _ =>
        exact False.elim
          (false_unification_has_no_declarative_solution valuation head)

namespace Ordered

/-- Abstract, ordered meaning of a predicate call.  The independent core does
not assume an executable clause store: later adequacy instantiates this
interface with pinned, clause-ordered resolution. -/
abbrev CallSemantics :=
  String → List Term → Valuation → List Valuation → Prop

mutual

/-- Sequential operational observations for the first pinned Prolog fragment.
The result list preserves answer order and multiplicity. Unsupported effects
have no rule yet rather than being silently interpreted as failure. -/
inductive Runs (calls : CallSemantics) :
    Valuation → Goal → List Valuation → Prop where
  | truth (valuation : Valuation) :
      Runs calls valuation .truth [valuation]
  | fail (valuation : Valuation) :
      Runs calls valuation .fail []
  | unifySuccess (valuation : Valuation) (left right : Term)
      (agreement : denoteTerm valuation left = denoteTerm valuation right) :
      Runs calls valuation (.unify left right) [valuation]
  | unifyFailure (valuation : Valuation) (left right : Term)
      (disagreement : denoteTerm valuation left ≠ denoteTerm valuation right) :
      Runs calls valuation (.unify left right) []
  | call (valuation : Valuation) (predicate : String) (arguments : List Term)
      (answers : List Valuation)
      (invoked : calls predicate arguments valuation answers) :
      Runs calls valuation (.call predicate arguments) answers
  | conjunction (valuation : Valuation) (goals : List Goal)
      (answers : List Valuation)
      (body : RunsAll calls valuation goals answers) :
      Runs calls valuation (.conjunction goals) answers
  | disjunction (valuation : Valuation) (branches : List Goal)
      (answers : List Valuation)
      (body : RunsBranches calls valuation branches answers) :
      Runs calls valuation (.disjunction branches) answers
  -- [SPEC translator.pl:127-128] `once/1` commits to the first answer of the
  -- complete ordered body observation, or preserves failure when it is empty.
  | once (valuation : Valuation) (goal : Goal)
      (bodyAnswers : List Valuation)
      (body : Runs calls valuation goal bodyAnswers) :
      Runs calls valuation (.once goal) (bodyAnswers.take 1)
  -- [SPEC translator.pl:136-137] In the supported single-threaded
  -- observation model, the mutex excludes no competing transition.  It must
  -- preserve the complete ordered observation of its body.
  | withMutex (valuation : Valuation) (mutex : Term) (goal : Goal)
      (answers : List Valuation)
      (body : Runs calls valuation goal answers) :
      Runs calls valuation (.withMutex mutex goal) answers

/-- Left-to-right conjunction.  Every answer from the head feeds the tail in
the same order, and each tail answer bag is concatenated without deduplication. -/
inductive RunsAll (calls : CallSemantics) :
    Valuation → List Goal → List Valuation → Prop where
  | nil (valuation : Valuation) : RunsAll calls valuation [] [valuation]
  | cons (valuation : Valuation) (goal : Goal) (goals : List Goal)
      (headAnswers answers : List Valuation)
      (head : Runs calls valuation goal headAnswers)
      (tail : RunsMany calls headAnswers goals answers) :
      RunsAll calls valuation (goal :: goals) answers

/-- Ordered monadic bind of a valuation list through a conjunction tail. -/
inductive RunsMany (calls : CallSemantics) :
    List Valuation → List Goal → List Valuation → Prop where
  | nil (goals : List Goal) : RunsMany calls [] goals []
  | cons (valuation : Valuation) (valuations : List Valuation)
      (goals : List Goal) (headAnswers tailAnswers : List Valuation)
      (head : RunsAll calls valuation goals headAnswers)
      (tail : RunsMany calls valuations goals tailAnswers) :
      RunsMany calls (valuation :: valuations) goals
        (headAnswers ++ tailAnswers)

/-- Ordered disjunction: branch answer bags are concatenated in source order. -/
inductive RunsBranches (calls : CallSemantics) :
    Valuation → List Goal → List Valuation → Prop where
  | nil (valuation : Valuation) : RunsBranches calls valuation [] []
  | cons (valuation : Valuation) (branch : Goal) (branches : List Goal)
      (headAnswers tailAnswers : List Valuation)
      (head : Runs calls valuation branch headAnswers)
      (tail : RunsBranches calls valuation branches tailAnswers) :
      RunsBranches calls valuation (branch :: branches)
        (headAnswers ++ tailAnswers)

end

/-- Equality of complete ordered observations in the sequential fragment. -/
def Equivalent (calls : CallSemantics) (left right : Goal) : Prop :=
  ∀ valuation answers,
    Runs calls valuation left answers ↔ Runs calls valuation right answers

/-- Equality of complete ordered observations for two goal sequences. -/
def AllEquivalent (calls : CallSemantics) (left right : List Goal) : Prop :=
  ∀ valuation answers,
    RunsAll calls valuation left answers ↔
      RunsAll calls valuation right answers

/-- Running an empty conjunction tail over an ordered answer bag is the
identity operation, including duplicates. -/
theorem runsMany_empty (calls : CallSemantics) (valuations : List Valuation) :
    RunsMany calls valuations [] valuations := by
  induction valuations with
  | nil => exact .nil []
  | cons valuation valuations tail =>
      exact .cons valuation valuations [] [valuation] valuations
        (.nil valuation) tail

/-- The empty conjunction tail has no other ordered observation. -/
theorem runsMany_empty_output {calls : CallSemantics}
    {valuations answers : List Valuation}
    (execution : RunsMany calls valuations [] answers) :
    answers = valuations := by
  induction valuations generalizing answers with
  | nil =>
      cases execution
      rfl
  | cons valuation valuations ih =>
      cases execution with
      | cons _ _ _ headAnswers tailAnswers head tail =>
          cases head
          simpa using congrArg (fun rest => valuation :: rest) (ih tail)

/-- Mutex wrapping is observationally inert only under the explicitly
sequential model: it preserves the body's answers, order, and multiplicity. -/
theorem withMutex_equivalent (calls : CallSemantics) (mutex : Term)
    (goal : Goal) : Equivalent calls (.withMutex mutex goal) goal := by
  intro valuation answers
  constructor
  · intro execution
    cases execution with
    | withMutex _ _ _ _ body => exact body
  · intro execution
    exact .withMutex valuation mutex goal answers execution

/-- The exact compiler normalization used by the sequential engine: a native
singleton `with_mutex(M, Conjunction)` has the same ordered observation as the
unwrapped body goal list. -/
theorem withMutex_conjunction_all_equivalent (calls : CallSemantics)
    (mutex : Term) (goals : List Goal) :
    AllEquivalent calls [.withMutex mutex (.conjunction goals)] goals := by
  intro valuation answers
  constructor
  · intro execution
    cases execution with
    | cons _ _ _ headAnswers _ head tail =>
        cases head with
        | withMutex _ _ _ _ body =>
            cases body with
            | conjunction _ _ _ bodyExecution =>
                have output := runsMany_empty_output tail
                simpa [output] using bodyExecution
  · intro execution
    exact .cons valuation (.withMutex mutex (.conjunction goals)) [] answers
      answers
      (.withMutex valuation mutex (.conjunction goals) answers
        (.conjunction valuation goals answers execution))
      (runsMany_empty calls answers)

/-- Every independent `once` observation contains at most one answer. -/
theorem once_answers_length_le_one {calls : CallSemantics}
    {valuation : Valuation} {goal : Goal} {answers : List Valuation}
    (execution : Runs calls valuation (.once goal) answers) :
    answers.length ≤ 1 := by
  cases execution with
  | once _ _ bodyAnswers _ =>
      simpa using Nat.min_le_left 1 bodyAnswers.length

/-- Positive first-answer example: `once` removes the second successful
branch while retaining the first. -/
theorem once_duplicate_truth_keeps_first (calls : CallSemantics)
    (valuation : Valuation) :
    Runs calls valuation (.once (.disjunction [.truth, .truth])) [valuation] := by
  have body :
      Runs calls valuation (.disjunction [.truth, .truth])
        [valuation, valuation] :=
    .disjunction valuation [.truth, .truth] [valuation, valuation]
      (.cons valuation .truth [.truth] [valuation] [valuation]
        (.truth valuation)
        (.cons valuation .truth [] [valuation] []
          (.truth valuation) (.nil valuation)))
  simpa using Runs.once valuation (.disjunction [.truth, .truth])
    [valuation, valuation] body

/-- Failure remains failure under `once`. -/
theorem once_failure_has_no_answer (calls : CallSemantics)
    (valuation : Valuation) : Runs calls valuation (.once .fail) [] := by
  simpa using Runs.once valuation .fail [] (.fail valuation)

/-- Negative multiplicity example: `once` can never return two copies. -/
theorem once_cannot_return_two {calls : CallSemantics}
    {valuation : Valuation} {goal : Goal} :
    ¬ Runs calls valuation (.once goal) [valuation, valuation] := by
  intro execution
  have bound := once_answers_length_le_one execution
  simp at bound

/-- Positive ordered example: two successful branches retain both answers. -/
theorem duplicate_truth_preserves_multiplicity (calls : CallSemantics)
    (valuation : Valuation) :
    Runs calls valuation (.disjunction [.truth, .truth])
      [valuation, valuation] := by
  exact .disjunction valuation [.truth, .truth] [valuation, valuation]
    (.cons valuation .truth [.truth] [valuation] [valuation]
      (.truth valuation)
      (.cons valuation .truth [] [valuation] []
        (.truth valuation) (.nil valuation)))

/-- Negative ordered example: failure cannot manufacture an answer. -/
theorem fail_cannot_return_valuation (calls : CallSemantics)
    (valuation : Valuation) : ¬ Runs calls valuation .fail [valuation] := by
  intro execution
  cases execution

end Ordered

end PLeaTTa.PeTTaSpec.PrologCore.Declarative
