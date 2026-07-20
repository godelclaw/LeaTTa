/-
Module: PLeaTTa.PeTTaSpec.OpenOrdered
Purpose: Independent left-to-right ordered semantics over open substitutions
  for the first pinned Prolog control fragment.
Trusted boundary: none
Main exports: Runs, RunsAll, alias_then_identity_succeeds,
  if_before_alias_fails, if_after_alias_succeeds
-/
import PLeaTTa.PeTTaSpec.OpenSubstitution

namespace PLeaTTa.PeTTaSpec.PrologCore.OpenOrdered

open OpenSubstitution

/-- Abstract ordered meaning of a predicate call over open substitutions.
Clause-ordered resolution will instantiate this interface later. -/
abbrev CallSemantics :=
  String → List Term → Substitution → List Substitution → Prop

mutual

/-- Ordered observations for the first open Prolog control fragment.

Answers retain order and multiplicity. Unification is deliberately limited to
the independently specified fragment in `OpenSubstitution.Unifies`; a missing
rule is not silently treated as failure unless non-derivability is proved.
Unsupported effects and control operators have no rule yet. -/
inductive Runs (calls : CallSemantics) :
    Substitution → Goal → List Substitution → Prop where
  | truth (bindings : Substitution) :
      Runs calls bindings .truth [bindings]
  | fail (bindings : Substitution) :
      Runs calls bindings .fail []
  | unifySuccess (bindings result : Substitution) (left right : Term)
      (unification : Unifies bindings left right result) :
      Runs calls bindings (.unify left right) [result]
  | unifyFailure (bindings : Substitution) (left right : Term)
      (failure : ∀ result, ¬ Unifies bindings left right result) :
      Runs calls bindings (.unify left right) []
  | identicalSuccess (bindings : Substitution) (left right : Term)
      (identity : Identical bindings left right) :
      Runs calls bindings (.identical left right) [bindings]
  | identicalFailure (bindings : Substitution) (left right : Term)
      (different : ¬ Identical bindings left right) :
      Runs calls bindings (.identical left right) []
  | call (bindings : Substitution) (predicate : String)
      (arguments : List Term) (answers : List Substitution)
      (invoked : calls predicate arguments bindings answers) :
      Runs calls bindings (.call predicate arguments) answers
  | conjunction (bindings : Substitution) (goals : List Goal)
      (answers : List Substitution)
      (body : RunsAll calls bindings goals answers) :
      Runs calls bindings (.conjunction goals) answers
  | disjunction (bindings : Substitution) (branches : List Goal)
      (answers : List Substitution)
      (body : RunsBranches calls bindings branches answers) :
      Runs calls bindings (.disjunction branches) answers
  -- ISO-style `(Condition -> Then ; Else)`: commit to the first successful
  -- condition answer, or run the else branch from the original state when the
  -- condition has no answer. [SPEC translator.pl:151-162]
  | ifThenElseSuccess (bindings first : Substitution)
      (remainingConditionAnswers : List Substitution)
      (condition thenBranch elseBranch : Goal)
      (answers : List Substitution)
      (conditionRun :
        Runs calls bindings condition (first :: remainingConditionAnswers))
      (thenRun : Runs calls first thenBranch answers) :
      Runs calls bindings (.ifThenElse condition thenBranch elseBranch) answers
  | ifThenElseFailure (bindings : Substitution)
      (condition thenBranch elseBranch : Goal)
      (answers : List Substitution)
      (conditionRun : Runs calls bindings condition [])
      (elseRun : Runs calls bindings elseBranch answers) :
      Runs calls bindings (.ifThenElse condition thenBranch elseBranch) answers
  | once (bindings : Substitution) (goal : Goal)
      (bodyAnswers : List Substitution)
      (body : Runs calls bindings goal bodyAnswers) :
      Runs calls bindings (.once goal) (bodyAnswers.take 1)
  | withMutex (bindings : Substitution) (mutex : Term) (goal : Goal)
      (answers : List Substitution)
      (body : Runs calls bindings goal answers) :
      Runs calls bindings (.withMutex mutex goal) answers

/-- Left-to-right conjunction over open substitutions. -/
inductive RunsAll (calls : CallSemantics) :
    Substitution → List Goal → List Substitution → Prop where
  | nil (bindings : Substitution) : RunsAll calls bindings [] [bindings]
  | cons (bindings : Substitution) (goal : Goal) (goals : List Goal)
      (headAnswers answers : List Substitution)
      (head : Runs calls bindings goal headAnswers)
      (tail : RunsMany calls headAnswers goals answers) :
      RunsAll calls bindings (goal :: goals) answers

/-- Ordered monadic bind of an answer bag through a conjunction tail. -/
inductive RunsMany (calls : CallSemantics) :
    List Substitution → List Goal → List Substitution → Prop where
  | nil (goals : List Goal) : RunsMany calls [] goals []
  | cons (bindings : Substitution) (remaining : List Substitution)
      (goals : List Goal) (headAnswers tailAnswers : List Substitution)
      (head : RunsAll calls bindings goals headAnswers)
      (tail : RunsMany calls remaining goals tailAnswers) :
      RunsMany calls (bindings :: remaining) goals
        (headAnswers ++ tailAnswers)

/-- Ordered disjunction concatenates complete branch answer bags. -/
inductive RunsBranches (calls : CallSemantics) :
    Substitution → List Goal → List Substitution → Prop where
  | nil (bindings : Substitution) : RunsBranches calls bindings [] []
  | cons (bindings : Substitution) (branch : Goal) (branches : List Goal)
      (headAnswers tailAnswers : List Substitution)
      (head : Runs calls bindings branch headAnswers)
      (tail : RunsBranches calls bindings branches tailAnswers) :
      RunsBranches calls bindings (branch :: branches)
        (headAnswers ++ tailAnswers)

end

/-- Running an empty conjunction tail preserves every open answer, including
duplicates and their order. -/
theorem runsMany_empty (calls : CallSemantics)
    (answers : List Substitution) : RunsMany calls answers [] answers := by
  induction answers with
  | nil => exact .nil []
  | cons bindings answers tail =>
      exact .cons bindings answers [] [bindings] answers
        (.nil bindings) tail

/-- A fresh explicit alias followed by Prolog identity succeeds and returns
the singleton open substitution. -/
theorem alias_then_identity_succeeds (calls : CallSemantics)
    (source target : LogicVar) (distinct : source ≠ target) :
    RunsAll calls []
      [.unify (.variable source) (.variable target),
       .identical (.variable source) (.variable target)]
      [[(source, .variable target)]] := by
  let alias : Substitution := [(source, .variable target)]
  have unification :
      Unifies [] (.variable source) (.variable target) alias :=
    unifies_empty_distinct_alias source target distinct
  have identity : Identical alias (.variable source) (.variable target) :=
    singleton_alias_makes_variables_identical source target
  have identityRun :
      RunsAll calls alias
        [.identical (.variable source) (.variable target)] [alias] :=
    .cons alias (.identical (.variable source) (.variable target)) [] [alias]
      [alias] (.identicalSuccess alias _ _ identity)
      (runsMany_empty calls [alias])
  exact .cons [] (.unify (.variable source) (.variable target))
    [.identical (.variable source) (.variable target)] [alias] [alias]
    (.unifySuccess [] alias _ _ unification)
    (.cons alias [] [.identical (.variable source) (.variable target)]
      [alias] [] identityRun (.nil _))

/-- The same identity-controlled conditional fails before distinct open
variables are aliased. -/
theorem if_before_alias_fails (calls : CallSemantics)
    (source target : LogicVar) (distinct : source ≠ target) :
    Runs calls []
      (.ifThenElse (.identical (.variable source) (.variable target))
        .truth .fail) [] := by
  exact .ifThenElseFailure [] _ _ _ []
    (.identicalFailure [] _ _
      (empty_distinct_variables_not_identical source target distinct))
    (.fail [])

/-- After the singleton alias, the identical conditional takes its true
branch and preserves the open substitution. -/
theorem if_after_alias_succeeds (calls : CallSemantics)
    (source target : LogicVar) :
    Runs calls [(source, .variable target)]
      (.ifThenElse (.identical (.variable source) (.variable target))
        .truth .fail)
      [[(source, .variable target)]] := by
  let alias : Substitution := [(source, .variable target)]
  exact .ifThenElseSuccess alias alias [] _ _ _ [alias]
    (.identicalSuccess alias _ _
      (singleton_alias_makes_variables_identical source target))
    (.truth alias)

/-- The compiler's explicit alias prefix makes the immediately following
identity-controlled `if` take its true branch from an initially empty open
substitution. -/
theorem alias_then_if_succeeds (calls : CallSemantics)
    (source target : LogicVar) (distinct : source ≠ target) :
    RunsAll calls []
      [.unify (.variable source) (.variable target),
       .ifThenElse (.identical (.variable source) (.variable target))
         .truth .fail]
      [[(source, .variable target)]] := by
  let alias : Substitution := [(source, .variable target)]
  have unification :
      Unifies [] (.variable source) (.variable target) alias :=
    unifies_empty_distinct_alias source target distinct
  have branchRun : RunsAll calls alias
      [.ifThenElse (.identical (.variable source) (.variable target))
        .truth .fail] [alias] :=
    .cons alias _ [] [alias] [alias]
      (if_after_alias_succeeds calls source target)
      (runsMany_empty calls [alias])
  exact .cons [] (.unify (.variable source) (.variable target))
    [.ifThenElse (.identical (.variable source) (.variable target))
      .truth .fail] [alias] [alias]
    (.unifySuccess [] alias _ _ unification)
    (.cons alias [] _ [alias] [] branchRun (.nil _))

/-- A two-answer condition commits to its first answer before executing the
then branch; condition multiplicity cannot leak past ordinary `if`. -/
theorem if_commits_to_first_condition_answer (calls : CallSemantics)
    (condition : Goal) (first second : Substitution)
    (conditionRun : Runs calls [] condition [first, second]) :
    Runs calls [] (.ifThenElse condition .truth .fail) [first] :=
  .ifThenElseSuccess [] first [second] condition .truth .fail [first]
    conditionRun (.truth first)

end PLeaTTa.PeTTaSpec.PrologCore.OpenOrdered
