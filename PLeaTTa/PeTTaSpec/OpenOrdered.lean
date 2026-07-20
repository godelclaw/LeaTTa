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

/-- Primitive two-way congruence obligations for moving one fixed initial
substitution into syntax. Structural control-flow congruence is proved below;
only unification and the abstract call interface remain premises. -/
structure PrimitiveBisimulation (calls : CallSemantics)
    (initial : Substitution) : Prop where
  unifyForward {carried instantiated : Substitution} {left right : Term}
      {carriedResult : Substitution} :
    StateAgrees initial carried instantiated →
      Unifies carried left right carriedResult →
      ∃ instantiatedResult,
        Unifies instantiated (initial.applyTerm left)
          (initial.applyTerm right) instantiatedResult ∧
        StateAgrees initial carriedResult instantiatedResult
  unifyBackward {carried instantiated : Substitution} {left right : Term}
      {instantiatedResult : Substitution} :
    StateAgrees initial carried instantiated →
      Unifies instantiated (initial.applyTerm left)
        (initial.applyTerm right) instantiatedResult →
      ∃ carriedResult,
        Unifies carried left right carriedResult ∧
        StateAgrees initial carriedResult instantiatedResult
  callForward {carried instantiated : Substitution} {predicate : String}
      {arguments : List Term} {carriedAnswers : List Substitution} :
    StateAgrees initial carried instantiated →
      calls predicate arguments carried carriedAnswers →
      ∃ instantiatedAnswers,
        calls predicate (initial.applyTerms arguments) instantiated
          instantiatedAnswers ∧
        AnswerBagsAgree initial carriedAnswers instantiatedAnswers
  callBackward {carried instantiated : Substitution} {predicate : String}
      {arguments : List Term} {instantiatedAnswers : List Substitution} :
    StateAgrees initial carried instantiated →
      calls predicate (initial.applyTerms arguments) instantiated
        instantiatedAnswers →
      ∃ carriedAnswers,
        calls predicate arguments carried carriedAnswers ∧
        AnswerBagsAgree initial carriedAnswers instantiatedAnswers

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

/-! ### Structural forward substitution congruence

The four execution judgments are mutually inductive. Their generated mutual
recursors, rather than a separate size measure, ensure every recursive appeal
below is to an actual derivation subtree.
-/

private abbrev RunsForward (calls : CallSemantics) (initial : Substitution)
    (carried : Substitution) (goal : Goal) (answers : List Substitution)
    (_execution : Runs calls carried goal answers) : Prop :=
  ∀ {instantiated}, StateAgrees initial carried instantiated →
    ∃ instantiatedAnswers,
      Runs calls instantiated (initial.applyGoal goal) instantiatedAnswers ∧
      AnswerBagsAgree initial answers instantiatedAnswers

private abbrev RunsAllForward (calls : CallSemantics) (initial : Substitution)
    (carried : Substitution) (goals : List Goal)
    (answers : List Substitution)
    (_execution : RunsAll calls carried goals answers) : Prop :=
  ∀ {instantiated}, StateAgrees initial carried instantiated →
    ∃ instantiatedAnswers,
      RunsAll calls instantiated (initial.applyGoals goals)
        instantiatedAnswers ∧
      AnswerBagsAgree initial answers instantiatedAnswers

private abbrev RunsManyForward (calls : CallSemantics) (initial : Substitution)
    (carriedInputs : List Substitution)
    (goals : List Goal) (answers : List Substitution)
    (_execution : RunsMany calls carriedInputs goals answers) : Prop :=
  ∀ {instantiatedInputs},
    AnswerBagsAgree initial carriedInputs instantiatedInputs →
    ∃ instantiatedAnswers,
      RunsMany calls instantiatedInputs (initial.applyGoals goals)
        instantiatedAnswers ∧
      AnswerBagsAgree initial answers instantiatedAnswers

private abbrev RunsBranchesForward (calls : CallSemantics)
    (initial : Substitution) (carried : Substitution) (branches : List Goal)
    (answers : List Substitution)
    (_execution : RunsBranches calls carried branches answers) : Prop :=
  ∀ {instantiated}, StateAgrees initial carried instantiated →
    ∃ instantiatedAnswers,
      RunsBranches calls instantiated (initial.applyGoals branches)
        instantiatedAnswers ∧
      AnswerBagsAgree initial answers instantiatedAnswers

section ForwardHandlers

variable {calls : CallSemantics} {initial : Substitution}

private theorem forwardTruth
    (_primitives : PrimitiveBisimulation calls initial)
    (bindings : Substitution) :
    RunsForward calls initial bindings .truth [bindings] (.truth bindings) := by
  intro instantiated states
  exact ⟨[instantiated], by simpa using Runs.truth instantiated,
    .cons states .nil⟩

private theorem forwardFail
    (_primitives : PrimitiveBisimulation calls initial)
    (bindings : Substitution) :
    RunsForward calls initial bindings .fail [] (.fail bindings) := by
  intro instantiated states
  exact ⟨[], by simpa using Runs.fail instantiated, .nil⟩

private theorem forwardUnifySuccess
    (primitives : PrimitiveBisimulation calls initial)
    (bindings result : Substitution)
    (left right : Term) (unification : Unifies bindings left right result) :
    RunsForward calls initial bindings (.unify left right) [result]
      (.unifySuccess bindings result left right unification) := by
  intro instantiated states
  obtain ⟨instantiatedResult, rightUnification, resultAgreement⟩ :=
    primitives.unifyForward states unification
  exact ⟨[instantiatedResult], by
      simpa using Runs.unifySuccess instantiated instantiatedResult
        (initial.applyTerm left) (initial.applyTerm right) rightUnification,
    .cons resultAgreement .nil⟩

private theorem forwardUnifyFailure
    (primitives : PrimitiveBisimulation calls initial)
    (bindings : Substitution)
    (left right : Term)
    (failure : ∀ result, ¬ Unifies bindings left right result) :
    RunsForward calls initial bindings (.unify left right) []
      (.unifyFailure bindings left right failure) := by
  intro instantiated states
  have rightFailure : ∀ result,
      ¬ Unifies instantiated (initial.applyTerm left)
        (initial.applyTerm right) result := by
    intro result rightUnification
    obtain ⟨carriedResult, leftUnification, _⟩ :=
      primitives.unifyBackward states rightUnification
    exact failure carriedResult leftUnification
  exact ⟨[], by
      simpa using Runs.unifyFailure instantiated
        (initial.applyTerm left) (initial.applyTerm right) rightFailure,
    .nil⟩

private theorem forwardIdenticalSuccess
    (_primitives : PrimitiveBisimulation calls initial)
    (bindings : Substitution)
    (left right : Term) (identity : Identical bindings left right) :
    RunsForward calls initial bindings (.identical left right) [bindings]
      (.identicalSuccess bindings left right identity) := by
  intro instantiated states
  have rightIdentity := (states.identical_iff left right).mp identity
  exact ⟨[instantiated], by
      simpa using Runs.identicalSuccess instantiated
        (initial.applyTerm left) (initial.applyTerm right) rightIdentity,
    .cons states .nil⟩

private theorem forwardIdenticalFailure
    (_primitives : PrimitiveBisimulation calls initial)
    (bindings : Substitution)
    (left right : Term) (different : ¬ Identical bindings left right) :
    RunsForward calls initial bindings (.identical left right) []
      (.identicalFailure bindings left right different) := by
  intro instantiated states
  have rightDifferent :
      ¬ Identical instantiated (initial.applyTerm left)
        (initial.applyTerm right) := by
    exact fun rightIdentity =>
      different ((states.identical_iff left right).mpr rightIdentity)
  exact ⟨[], by
      simpa using Runs.identicalFailure instantiated
        (initial.applyTerm left) (initial.applyTerm right) rightDifferent,
    .nil⟩

private theorem forwardCall
    (primitives : PrimitiveBisimulation calls initial)
    (bindings : Substitution) (predicate : String)
    (arguments : List Term) (answers : List Substitution)
    (invoked : calls predicate arguments bindings answers) :
    RunsForward calls initial bindings (.call predicate arguments) answers
      (.call bindings predicate arguments answers invoked) := by
  intro instantiated states
  obtain ⟨instantiatedAnswers, rightCall, answerAgreement⟩ :=
    primitives.callForward states invoked
  exact ⟨instantiatedAnswers, by
      simpa using Runs.call instantiated predicate
        (initial.applyTerms arguments) instantiatedAnswers rightCall,
    answerAgreement⟩

private theorem forwardConjunction
    (_primitives : PrimitiveBisimulation calls initial)
    (bindings : Substitution)
    (goals : List Goal) (answers : List Substitution)
    (body : RunsAll calls bindings goals answers)
    (bodyForward : RunsAllForward calls initial bindings goals answers body) :
    RunsForward calls initial bindings (.conjunction goals) answers
      (.conjunction bindings goals answers body) := by
  intro instantiated states
  obtain ⟨instantiatedAnswers, rightBody, answerAgreement⟩ :=
    bodyForward states
  exact ⟨instantiatedAnswers, by
      simpa using Runs.conjunction instantiated
        (initial.applyGoals goals) instantiatedAnswers rightBody,
    answerAgreement⟩

private theorem forwardDisjunction
    (_primitives : PrimitiveBisimulation calls initial)
    (bindings : Substitution)
    (branches : List Goal) (answers : List Substitution)
    (body : RunsBranches calls bindings branches answers)
    (bodyForward : RunsBranchesForward calls initial bindings branches answers body) :
    RunsForward calls initial bindings (.disjunction branches) answers
      (.disjunction bindings branches answers body) := by
  intro instantiated states
  obtain ⟨instantiatedAnswers, rightBody, answerAgreement⟩ :=
    bodyForward states
  exact ⟨instantiatedAnswers, by
      simpa using Runs.disjunction instantiated
        (initial.applyGoals branches) instantiatedAnswers rightBody,
    answerAgreement⟩

private theorem forwardIfSuccess
    (_primitives : PrimitiveBisimulation calls initial)
    (bindings first : Substitution)
    (remaining : List Substitution) (condition thenBranch elseBranch : Goal)
    (answers : List Substitution)
    (conditionRun : Runs calls bindings condition (first :: remaining))
    (thenRun : Runs calls first thenBranch answers)
    (conditionForward :
      RunsForward calls initial bindings condition (first :: remaining) conditionRun)
    (thenForward : RunsForward calls initial first thenBranch answers thenRun) :
    RunsForward calls initial bindings
      (.ifThenElse condition thenBranch elseBranch) answers
      (.ifThenElseSuccess bindings first remaining condition thenBranch
        elseBranch answers conditionRun thenRun) := by
  intro instantiated states
  obtain ⟨instantiatedConditionAnswers, rightCondition,
      conditionAgreement⟩ := conditionForward states
  cases conditionAgreement with
  | cons firstAgreement remainingAgreement =>
      obtain ⟨instantiatedAnswers, rightThen, answerAgreement⟩ :=
        thenForward firstAgreement
      exact ⟨instantiatedAnswers, by
          simpa using Runs.ifThenElseSuccess instantiated _ _
            (initial.applyGoal condition) (initial.applyGoal thenBranch)
            (initial.applyGoal elseBranch) instantiatedAnswers rightCondition
            rightThen,
        answerAgreement⟩

private theorem forwardIfFailure
    (_primitives : PrimitiveBisimulation calls initial)
    (bindings : Substitution)
    (condition thenBranch elseBranch : Goal) (answers : List Substitution)
    (conditionRun : Runs calls bindings condition [])
    (elseRun : Runs calls bindings elseBranch answers)
    (conditionForward : RunsForward calls initial bindings condition [] conditionRun)
    (elseForward : RunsForward calls initial bindings elseBranch answers elseRun) :
    RunsForward calls initial bindings
      (.ifThenElse condition thenBranch elseBranch) answers
      (.ifThenElseFailure bindings condition thenBranch elseBranch answers
        conditionRun elseRun) := by
  intro instantiated states
  obtain ⟨instantiatedConditionAnswers, rightCondition,
      conditionAgreement⟩ := conditionForward states
  cases conditionAgreement
  obtain ⟨instantiatedAnswers, rightElse, answerAgreement⟩ :=
    elseForward states
  exact ⟨instantiatedAnswers, by
      simpa using Runs.ifThenElseFailure instantiated
        (initial.applyGoal condition) (initial.applyGoal thenBranch)
        (initial.applyGoal elseBranch) instantiatedAnswers rightCondition
        rightElse,
    answerAgreement⟩

private theorem forwardOnce
    (_primitives : PrimitiveBisimulation calls initial)
    (bindings : Substitution) (goal : Goal)
    (bodyAnswers : List Substitution)
    (body : Runs calls bindings goal bodyAnswers)
    (bodyForward : RunsForward calls initial bindings goal bodyAnswers body) :
    RunsForward calls initial bindings (.once goal) (bodyAnswers.take 1)
      (.once bindings goal bodyAnswers body) := by
  intro instantiated states
  obtain ⟨instantiatedBodyAnswers, rightBody, bodyAgreement⟩ :=
    bodyForward states
  exact ⟨instantiatedBodyAnswers.take 1, by
      simpa using Runs.once instantiated (initial.applyGoal goal)
        instantiatedBodyAnswers rightBody,
    bodyAgreement.take_one⟩

private theorem forwardWithMutex
    (_primitives : PrimitiveBisimulation calls initial)
    (bindings : Substitution) (mutex : Term)
    (goal : Goal) (answers : List Substitution)
    (body : Runs calls bindings goal answers)
    (bodyForward : RunsForward calls initial bindings goal answers body) :
    RunsForward calls initial bindings (.withMutex mutex goal) answers
      (.withMutex bindings mutex goal answers body) := by
  intro instantiated states
  obtain ⟨instantiatedAnswers, rightBody, answerAgreement⟩ :=
    bodyForward states
  exact ⟨instantiatedAnswers, by
      simpa using Runs.withMutex instantiated (initial.applyTerm mutex)
        (initial.applyGoal goal) instantiatedAnswers rightBody,
    answerAgreement⟩

private theorem forwardAllNil
    (_primitives : PrimitiveBisimulation calls initial)
    (bindings : Substitution) :
    RunsAllForward calls initial bindings [] [bindings] (.nil bindings) := by
  intro instantiated states
  exact ⟨[instantiated], by simpa using RunsAll.nil instantiated,
    .cons states .nil⟩

private theorem forwardAllCons
    (_primitives : PrimitiveBisimulation calls initial)
    (bindings : Substitution) (goal : Goal)
    (goals : List Goal) (headAnswers answers : List Substitution)
    (head : Runs calls bindings goal headAnswers)
    (tail : RunsMany calls headAnswers goals answers)
    (headForward : RunsForward calls initial bindings goal headAnswers head)
    (tailForward : RunsManyForward calls initial headAnswers goals answers tail) :
    RunsAllForward calls initial bindings (goal :: goals) answers
      (.cons bindings goal goals headAnswers answers head tail) := by
  intro instantiated states
  obtain ⟨instantiatedHeadAnswers, rightHead, headAgreement⟩ :=
    headForward states
  obtain ⟨instantiatedAnswers, rightTail, answerAgreement⟩ :=
    tailForward headAgreement
  exact ⟨instantiatedAnswers, by
      simpa using RunsAll.cons instantiated (initial.applyGoal goal)
        (initial.applyGoals goals) instantiatedHeadAnswers
        instantiatedAnswers rightHead rightTail,
    answerAgreement⟩

private theorem forwardManyNil
    (_primitives : PrimitiveBisimulation calls initial)
    (goals : List Goal) :
    RunsManyForward calls initial [] goals [] (.nil goals) := by
  intro instantiatedInputs inputAgreement
  cases inputAgreement
  exact ⟨[], .nil (initial.applyGoals goals), .nil⟩

private theorem forwardManyCons
    (_primitives : PrimitiveBisimulation calls initial)
    (bindings : Substitution)
    (remaining : List Substitution) (goals : List Goal)
    (headAnswers tailAnswers : List Substitution)
    (head : RunsAll calls bindings goals headAnswers)
    (tail : RunsMany calls remaining goals tailAnswers)
    (headForward : RunsAllForward calls initial bindings goals headAnswers head)
    (tailForward : RunsManyForward calls initial remaining goals tailAnswers tail) :
    RunsManyForward calls initial (bindings :: remaining) goals
      (headAnswers ++ tailAnswers)
      (.cons bindings remaining goals headAnswers tailAnswers head tail) := by
  intro instantiatedInputs inputAgreement
  cases inputAgreement with
  | cons stateAgreement remainingAgreement =>
      obtain ⟨instantiatedHeadAnswers, rightHead, headAgreement⟩ :=
        headForward stateAgreement
      obtain ⟨instantiatedTailAnswers, rightTail, tailAgreement⟩ :=
        tailForward remainingAgreement
      exact ⟨instantiatedHeadAnswers ++ instantiatedTailAnswers,
        .cons _ _ _ _ _ rightHead rightTail,
        headAgreement.append tailAgreement⟩

private theorem forwardBranchesNil
    (_primitives : PrimitiveBisimulation calls initial)
    (bindings : Substitution) :
    RunsBranchesForward calls initial bindings [] [] (.nil bindings) := by
  intro instantiated states
  exact ⟨[], by simpa using RunsBranches.nil instantiated, .nil⟩

private theorem forwardBranchesCons
    (_primitives : PrimitiveBisimulation calls initial)
    (bindings : Substitution) (branch : Goal)
    (branches : List Goal) (headAnswers tailAnswers : List Substitution)
    (head : Runs calls bindings branch headAnswers)
    (tail : RunsBranches calls bindings branches tailAnswers)
    (headForward : RunsForward calls initial bindings branch headAnswers head)
    (tailForward :
      RunsBranchesForward calls initial bindings branches tailAnswers tail) :
    RunsBranchesForward calls initial bindings (branch :: branches)
      (headAnswers ++ tailAnswers)
      (.cons bindings branch branches headAnswers tailAnswers head tail) := by
  intro instantiated states
  obtain ⟨instantiatedHeadAnswers, rightHead, headAgreement⟩ :=
    headForward states
  obtain ⟨instantiatedTailAnswers, rightTail, tailAgreement⟩ :=
    tailForward states
  exact ⟨instantiatedHeadAnswers ++ instantiatedTailAnswers,
    by
      simpa using
        (RunsBranches.cons instantiated (initial.applyGoal branch)
          (initial.applyGoals branches) instantiatedHeadAnswers
          instantiatedTailAnswers rightHead rightTail),
    headAgreement.append tailAgreement⟩

end ForwardHandlers

private theorem runsForwardRec {calls : CallSemantics}
    {initial carried : Substitution} {goal : Goal}
    {answers : List Substitution}
    (primitives : PrimitiveBisimulation calls initial)
    (execution : Runs calls carried goal answers) :
    RunsForward calls initial carried goal answers execution :=
  Runs.rec (motive_1 := RunsForward calls initial)
    (motive_2 := RunsAllForward calls initial)
    (motive_3 := RunsManyForward calls initial)
    (motive_4 := RunsBranchesForward calls initial)
    (forwardTruth primitives) (forwardFail primitives)
    (forwardUnifySuccess primitives) (forwardUnifyFailure primitives)
    (forwardIdenticalSuccess primitives) (forwardIdenticalFailure primitives)
    (forwardCall primitives) (forwardConjunction primitives)
    (forwardDisjunction primitives) (forwardIfSuccess primitives)
    (forwardIfFailure primitives) (forwardOnce primitives)
    (forwardWithMutex primitives) (forwardAllNil primitives)
    (forwardAllCons primitives) (forwardManyNil primitives)
    (forwardManyCons primitives) (forwardBranchesNil primitives)
    (forwardBranchesCons primitives) execution

private theorem runsAllForwardRec {calls : CallSemantics}
    {initial carried : Substitution} {goals : List Goal}
    {answers : List Substitution}
    (primitives : PrimitiveBisimulation calls initial)
    (execution : RunsAll calls carried goals answers) :
    RunsAllForward calls initial carried goals answers execution :=
  RunsAll.rec (motive_1 := RunsForward calls initial)
    (motive_2 := RunsAllForward calls initial)
    (motive_3 := RunsManyForward calls initial)
    (motive_4 := RunsBranchesForward calls initial)
    (forwardTruth primitives) (forwardFail primitives)
    (forwardUnifySuccess primitives) (forwardUnifyFailure primitives)
    (forwardIdenticalSuccess primitives) (forwardIdenticalFailure primitives)
    (forwardCall primitives) (forwardConjunction primitives)
    (forwardDisjunction primitives) (forwardIfSuccess primitives)
    (forwardIfFailure primitives) (forwardOnce primitives)
    (forwardWithMutex primitives) (forwardAllNil primitives)
    (forwardAllCons primitives) (forwardManyNil primitives)
    (forwardManyCons primitives) (forwardBranchesNil primitives)
    (forwardBranchesCons primitives) execution

private theorem runsManyForwardRec {calls : CallSemantics}
    {initial : Substitution} {carriedInputs : List Substitution}
    {goals : List Goal} {answers : List Substitution}
    (primitives : PrimitiveBisimulation calls initial)
    (execution : RunsMany calls carriedInputs goals answers) :
    RunsManyForward calls initial carriedInputs goals answers execution :=
  RunsMany.rec (motive_1 := RunsForward calls initial)
    (motive_2 := RunsAllForward calls initial)
    (motive_3 := RunsManyForward calls initial)
    (motive_4 := RunsBranchesForward calls initial)
    (forwardTruth primitives) (forwardFail primitives)
    (forwardUnifySuccess primitives) (forwardUnifyFailure primitives)
    (forwardIdenticalSuccess primitives) (forwardIdenticalFailure primitives)
    (forwardCall primitives) (forwardConjunction primitives)
    (forwardDisjunction primitives) (forwardIfSuccess primitives)
    (forwardIfFailure primitives) (forwardOnce primitives)
    (forwardWithMutex primitives) (forwardAllNil primitives)
    (forwardAllCons primitives) (forwardManyNil primitives)
    (forwardManyCons primitives) (forwardBranchesNil primitives)
    (forwardBranchesCons primitives) execution

private theorem runsBranchesForwardRec {calls : CallSemantics}
    {initial carried : Substitution} {branches : List Goal}
    {answers : List Substitution}
    (primitives : PrimitiveBisimulation calls initial)
    (execution : RunsBranches calls carried branches answers) :
    RunsBranchesForward calls initial carried branches answers execution :=
  RunsBranches.rec (motive_1 := RunsForward calls initial)
    (motive_2 := RunsAllForward calls initial)
    (motive_3 := RunsManyForward calls initial)
    (motive_4 := RunsBranchesForward calls initial)
    (forwardTruth primitives) (forwardFail primitives)
    (forwardUnifySuccess primitives) (forwardUnifyFailure primitives)
    (forwardIdenticalSuccess primitives) (forwardIdenticalFailure primitives)
    (forwardCall primitives) (forwardConjunction primitives)
    (forwardDisjunction primitives) (forwardIfSuccess primitives)
    (forwardIfFailure primitives) (forwardOnce primitives)
    (forwardWithMutex primitives) (forwardAllNil primitives)
    (forwardAllCons primitives) (forwardManyNil primitives)
    (forwardManyCons primitives) (forwardBranchesNil primitives)
    (forwardBranchesCons primitives) execution

/-- Forward half of substitution congruence for one open goal. Structural
control flow is derived; only the primitive bisimulation contract is assumed. -/
theorem Runs.forward {calls : CallSemantics} {initial carried : Substitution}
    {goal : Goal} {answers : List Substitution}
    (primitives : PrimitiveBisimulation calls initial)
    (execution : Runs calls carried goal answers) :
    ∀ {instantiated}, StateAgrees initial carried instantiated →
      ∃ instantiatedAnswers,
        Runs calls instantiated (initial.applyGoal goal) instantiatedAnswers ∧
        AnswerBagsAgree initial answers instantiatedAnswers :=
  runsForwardRec primitives execution

/-- Forward substitution congruence for left-to-right conjunction. -/
theorem RunsAll.forward {calls : CallSemantics}
    {initial carried : Substitution} {goals : List Goal}
    {answers : List Substitution}
    (primitives : PrimitiveBisimulation calls initial)
    (execution : RunsAll calls carried goals answers) :
    ∀ {instantiated}, StateAgrees initial carried instantiated →
      ∃ instantiatedAnswers,
        RunsAll calls instantiated (initial.applyGoals goals)
          instantiatedAnswers ∧
        AnswerBagsAgree initial answers instantiatedAnswers :=
  runsAllForwardRec primitives execution

/-- Forward substitution congruence for ordered monadic answer binding. -/
theorem RunsMany.forward {calls : CallSemantics}
    {initial : Substitution} {carriedInputs : List Substitution}
    {goals : List Goal} {answers : List Substitution}
    (primitives : PrimitiveBisimulation calls initial)
    (execution : RunsMany calls carriedInputs goals answers) :
    ∀ {instantiatedInputs},
      AnswerBagsAgree initial carriedInputs instantiatedInputs →
      ∃ instantiatedAnswers,
        RunsMany calls instantiatedInputs (initial.applyGoals goals)
          instantiatedAnswers ∧
        AnswerBagsAgree initial answers instantiatedAnswers :=
  runsManyForwardRec primitives execution

/-- Forward substitution congruence for source-ordered disjunction. -/
theorem RunsBranches.forward {calls : CallSemantics}
    {initial carried : Substitution} {branches : List Goal}
    {answers : List Substitution}
    (primitives : PrimitiveBisimulation calls initial)
    (execution : RunsBranches calls carried branches answers) :
    ∀ {instantiated}, StateAgrees initial carried instantiated →
      ∃ instantiatedAnswers,
        RunsBranches calls instantiated (initial.applyGoals branches)
          instantiatedAnswers ∧
        AnswerBagsAgree initial answers instantiatedAnswers :=
  runsBranchesForwardRec primitives execution

/-- Running an empty conjunction tail preserves every open answer, including
duplicates and their order. -/
theorem runsMany_empty (calls : CallSemantics)
    (answers : List Substitution) : RunsMany calls answers [] answers := by
  induction answers with
  | nil => exact .nil []
  | cons bindings answers tail =>
      exact .cons bindings answers [] [bindings] answers
        (.nil bindings) tail

/-- A single goal has the same ordered answer bag as its `Runs` derivation. -/
theorem runsAll_singleton {calls : CallSemantics} {bindings : Substitution}
    {goal : Goal} {answers : List Substitution}
    (execution : Runs calls bindings goal answers) :
    RunsAll calls bindings [goal] answers :=
  .cons bindings goal [] answers answers execution
    (runsMany_empty calls answers)

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

/-- A later value unification resolves through the earlier alias, and the
following identity test observes the transitive value. -/
theorem alias_then_bind_integer_succeeds (calls : CallSemantics)
    (source target : LogicVar) (distinct : source ≠ target) (value : Int) :
    RunsAll calls []
      [.unify (.variable source) (.variable target),
       .unify (.variable source) (.integer value),
       .identical (.variable source) (.integer value)]
      [[(target, .integer value), (source, .variable target)]] := by
  let alias : Substitution := [(source, .variable target)]
  let bound : Substitution :=
    [(target, .integer value), (source, .variable target)]
  have aliasRun :
      Runs calls [] (.unify (.variable source) (.variable target)) [alias] :=
    .unifySuccess [] alias _ _
      (unifies_empty_distinct_alias source target distinct)
  have valueRun :
      Runs calls alias (.unify (.variable source) (.integer value)) [bound] :=
    .unifySuccess alias bound _ _
      (unifies_alias_source_with_integer source target value)
  have identityRun :
      Runs calls bound (.identical (.variable source) (.integer value))
        [bound] :=
    .identicalSuccess bound _ _
      (chained_alias_integer_is_identical source target value)
  have tailRun : RunsAll calls alias
      [.unify (.variable source) (.integer value),
       .identical (.variable source) (.integer value)] [bound] :=
    .cons alias _ [_] [bound] [bound] valueRun
      (.cons bound [] [_] [bound] []
        (runsAll_singleton identityRun) (.nil _))
  exact .cons [] _ [_, _] [alias] [bound] aliasRun
    (.cons alias [] [_, _] [bound] [] tailRun (.nil _))

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
