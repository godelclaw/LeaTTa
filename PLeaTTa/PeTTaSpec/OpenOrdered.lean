/-
Module: PLeaTTa.PeTTaSpec.OpenOrdered
Purpose: Independent left-to-right ordered semantics over open substitutions
  for the first pinned Prolog control fragment.
Trusted boundary: none
Main exports: Runs, RunsAll, AliasFinalizationBisimulation,
  aliasFinalizationBisimulation, alias_then_identity_succeeds,
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

/-- The remaining primitive seam after open unification is discharged: a
predicate-call relation must itself respect moving the initial substitution
into its argument syntax. -/
structure CallBisimulation (calls : CallSemantics)
    (initial : Substitution) : Prop where
  forward {carried instantiated : Substitution} {predicate : String}
      {arguments : List Term} {carriedAnswers : List Substitution} :
    StateAgrees initial carried instantiated →
      calls predicate arguments carried carriedAnswers →
      ∃ instantiatedAnswers,
        calls predicate (initial.applyTerms arguments) instantiated
          instantiatedAnswers ∧
        AnswerBagsAgree initial carriedAnswers instantiatedAnswers
  backward {carried instantiated : Substitution} {predicate : String}
      {arguments : List Term} {instantiatedAnswers : List Substitution} :
    StateAgrees initial carried instantiated →
      calls predicate (initial.applyTerms arguments) instantiated
        instantiatedAnswers →
      ∃ carriedAnswers,
        calls predicate arguments carried carriedAnswers ∧
        AnswerBagsAgree initial carriedAnswers instantiatedAnswers

/-- The independent open unifier satisfies both primitive substitution
contracts; only the separately stated predicate-call contract is assumed. -/
theorem PrimitiveBisimulation.ofCalls {calls : CallSemantics}
    {initial : Substitution} (callAgreement : CallBisimulation calls initial) :
    PrimitiveBisimulation calls initial where
  unifyForward := fun states unification =>
    Unifies.moveInitialForward states unification
  unifyBackward := fun states unification =>
    Unifies.moveInitialBackward states unification
  callForward := fun states invoked => callAgreement.forward states invoked
  callBackward := fun states invoked => callAgreement.backward states invoked

/-- Call semantics with no available predicates, useful for the call-free
normalized control fragment. -/
def NoCalls : CallSemantics := fun _predicate _arguments _bindings _answers =>
  False

/-- Empty call semantics is substitution invariant vacuously. -/
theorem noCallsBisimulation (initial : Substitution) :
    CallBisimulation NoCalls initial where
  forward := by
    intro carried instantiated predicate arguments carriedAnswers states call
    exact False.elim call
  backward := by
    intro carried instantiated predicate arguments instantiatedAnswers states
      call
    exact False.elim call

/-- Concrete primitive bisimulation for the call-free fragment. -/
theorem PrimitiveBisimulation.noCalls (initial : Substitution) :
    PrimitiveBisimulation NoCalls initial :=
  .ofCalls (noCallsBisimulation initial)

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

/-! ### Structural backward substitution congruence

The reverse direction retains the original syntax as an explicit preimage.
This is necessary because substitution is intentionally not injective: two
different variables may instantiate to the same term.
-/

private abbrev RunsBackward (calls : CallSemantics) (initial : Substitution)
    (instantiated : Substitution) (instantiatedGoal : Goal)
    (instantiatedAnswers : List Substitution)
    (_execution :
      Runs calls instantiated instantiatedGoal instantiatedAnswers) : Prop :=
  ∀ {carried originalGoal}, StateAgrees initial carried instantiated →
    initial.applyGoal originalGoal = instantiatedGoal →
    ∃ carriedAnswers,
      Runs calls carried originalGoal carriedAnswers ∧
      AnswerBagsAgree initial carriedAnswers instantiatedAnswers

private abbrev RunsAllBackward (calls : CallSemantics)
    (initial : Substitution) (instantiated : Substitution)
    (instantiatedGoals : List Goal)
    (instantiatedAnswers : List Substitution)
    (_execution :
      RunsAll calls instantiated instantiatedGoals instantiatedAnswers) :
    Prop :=
  ∀ {carried originalGoals}, StateAgrees initial carried instantiated →
    initial.applyGoals originalGoals = instantiatedGoals →
    ∃ carriedAnswers,
      RunsAll calls carried originalGoals carriedAnswers ∧
      AnswerBagsAgree initial carriedAnswers instantiatedAnswers

private abbrev RunsManyBackward (calls : CallSemantics)
    (initial : Substitution) (instantiatedInputs : List Substitution)
    (instantiatedGoals : List Goal)
    (instantiatedAnswers : List Substitution)
    (_execution :
      RunsMany calls instantiatedInputs instantiatedGoals
        instantiatedAnswers) : Prop :=
  ∀ {carriedInputs originalGoals},
    AnswerBagsAgree initial carriedInputs instantiatedInputs →
    initial.applyGoals originalGoals = instantiatedGoals →
    ∃ carriedAnswers,
      RunsMany calls carriedInputs originalGoals carriedAnswers ∧
      AnswerBagsAgree initial carriedAnswers instantiatedAnswers

private abbrev RunsBranchesBackward (calls : CallSemantics)
    (initial : Substitution) (instantiated : Substitution)
    (instantiatedBranches : List Goal)
    (instantiatedAnswers : List Substitution)
    (_execution :
      RunsBranches calls instantiated instantiatedBranches
        instantiatedAnswers) : Prop :=
  ∀ {carried originalBranches}, StateAgrees initial carried instantiated →
    initial.applyGoals originalBranches = instantiatedBranches →
    ∃ carriedAnswers,
      RunsBranches calls carried originalBranches carriedAnswers ∧
      AnswerBagsAgree initial carriedAnswers instantiatedAnswers

section BackwardHandlers

variable {calls : CallSemantics} {initial : Substitution}

private theorem backwardTruth
    (_primitives : PrimitiveBisimulation calls initial)
    (instantiated : Substitution) :
    RunsBackward calls initial instantiated .truth [instantiated]
      (.truth instantiated) := by
  intro carried originalGoal states goalEq
  cases originalGoal <;> simp_all
  exact ⟨[carried], .truth carried, .cons states .nil⟩

private theorem backwardFail
    (_primitives : PrimitiveBisimulation calls initial)
    (instantiated : Substitution) :
    RunsBackward calls initial instantiated .fail [] (.fail instantiated) := by
  intro carried originalGoal states goalEq
  cases originalGoal <;> simp_all
  exact ⟨[], .fail carried, .nil⟩

private theorem backwardUnifySuccess
    (primitives : PrimitiveBisimulation calls initial)
    (instantiated instantiatedResult : Substitution) (left right : Term)
    (unification : Unifies instantiated left right instantiatedResult) :
    RunsBackward calls initial instantiated (.unify left right)
      [instantiatedResult]
      (.unifySuccess instantiated instantiatedResult left right unification) := by
  intro carried originalGoal states goalEq
  cases originalGoal <;> simp_all
  case unify originalLeft originalRight =>
    rw [← goalEq.1, ← goalEq.2] at unification
    obtain ⟨carriedResult, leftUnification, resultAgreement⟩ :=
      primitives.unifyBackward states unification
    exact ⟨[carriedResult],
      .unifySuccess carried carriedResult originalLeft originalRight
        leftUnification,
      .cons resultAgreement .nil⟩

private theorem backwardUnifyFailure
    (primitives : PrimitiveBisimulation calls initial)
    (instantiated : Substitution) (left right : Term)
    (failure : ∀ result, ¬ Unifies instantiated left right result) :
    RunsBackward calls initial instantiated (.unify left right) []
      (.unifyFailure instantiated left right failure) := by
  intro carried originalGoal states goalEq
  cases originalGoal <;> simp_all
  case unify originalLeft originalRight =>
    rw [← goalEq.1, ← goalEq.2] at failure
    have carriedFailure : ∀ result,
        ¬ Unifies carried originalLeft originalRight result := by
      intro result leftUnification
      obtain ⟨instantiatedResult, rightUnification, _⟩ :=
        primitives.unifyForward states leftUnification
      exact failure instantiatedResult rightUnification
    exact ⟨[],
      .unifyFailure carried originalLeft originalRight carriedFailure,
      .nil⟩

private theorem backwardIdenticalSuccess
    (_primitives : PrimitiveBisimulation calls initial)
    (instantiated : Substitution) (left right : Term)
    (identity : Identical instantiated left right) :
    RunsBackward calls initial instantiated (.identical left right)
      [instantiated]
      (.identicalSuccess instantiated left right identity) := by
  intro carried originalGoal states goalEq
  cases originalGoal <;> simp_all
  case identical originalLeft originalRight =>
    rw [← goalEq.1, ← goalEq.2] at identity
    have carriedIdentity :=
      (states.identical_iff originalLeft originalRight).mpr identity
    exact ⟨[carried],
      .identicalSuccess carried originalLeft originalRight carriedIdentity,
      .cons states .nil⟩

private theorem backwardIdenticalFailure
    (_primitives : PrimitiveBisimulation calls initial)
    (instantiated : Substitution) (left right : Term)
    (different : ¬ Identical instantiated left right) :
    RunsBackward calls initial instantiated (.identical left right) []
      (.identicalFailure instantiated left right different) := by
  intro carried originalGoal states goalEq
  cases originalGoal <;> simp_all
  case identical originalLeft originalRight =>
    rw [← goalEq.1, ← goalEq.2] at different
    have carriedDifferent : ¬ Identical carried originalLeft originalRight :=
      fun carriedIdentity =>
        different
          ((states.identical_iff originalLeft originalRight).mp
            carriedIdentity)
    exact ⟨[],
      .identicalFailure carried originalLeft originalRight carriedDifferent,
      .nil⟩

private theorem backwardCall
    (primitives : PrimitiveBisimulation calls initial)
    (instantiated : Substitution) (predicate : String)
    (arguments : List Term) (instantiatedAnswers : List Substitution)
    (invoked :
      calls predicate arguments instantiated instantiatedAnswers) :
    RunsBackward calls initial instantiated (.call predicate arguments)
      instantiatedAnswers
      (.call instantiated predicate arguments instantiatedAnswers invoked) := by
  intro carried originalGoal states goalEq
  cases originalGoal <;> simp_all
  case call originalPredicate originalArguments =>
    rw [← goalEq.2] at invoked
    obtain ⟨carriedAnswers, leftCall, answerAgreement⟩ :=
      primitives.callBackward states invoked
    exact ⟨carriedAnswers,
      .call carried predicate originalArguments carriedAnswers leftCall,
      answerAgreement⟩

private theorem backwardConjunction
    (_primitives : PrimitiveBisimulation calls initial)
    (instantiated : Substitution) (goals : List Goal)
    (instantiatedAnswers : List Substitution)
    (body : RunsAll calls instantiated goals instantiatedAnswers)
    (bodyBackward :
      RunsAllBackward calls initial instantiated goals instantiatedAnswers
        body) :
    RunsBackward calls initial instantiated (.conjunction goals)
      instantiatedAnswers
      (.conjunction instantiated goals instantiatedAnswers body) := by
  intro carried originalGoal states goalEq
  cases originalGoal <;> simp_all
  case conjunction originalGoals =>
    obtain ⟨carriedAnswers, leftBody, answerAgreement⟩ :=
      bodyBackward states goalEq
    exact ⟨carriedAnswers,
      .conjunction carried originalGoals carriedAnswers leftBody,
      answerAgreement⟩

private theorem backwardDisjunction
    (_primitives : PrimitiveBisimulation calls initial)
    (instantiated : Substitution) (branches : List Goal)
    (instantiatedAnswers : List Substitution)
    (body : RunsBranches calls instantiated branches instantiatedAnswers)
    (bodyBackward :
      RunsBranchesBackward calls initial instantiated branches
        instantiatedAnswers body) :
    RunsBackward calls initial instantiated (.disjunction branches)
      instantiatedAnswers
      (.disjunction instantiated branches instantiatedAnswers body) := by
  intro carried originalGoal states goalEq
  cases originalGoal <;> simp_all
  case disjunction originalBranches =>
    obtain ⟨carriedAnswers, leftBody, answerAgreement⟩ :=
      bodyBackward states goalEq
    exact ⟨carriedAnswers,
      .disjunction carried originalBranches carriedAnswers leftBody,
      answerAgreement⟩

private theorem backwardIfSuccess
    (_primitives : PrimitiveBisimulation calls initial)
    (instantiated first : Substitution) (remaining : List Substitution)
    (condition thenBranch elseBranch : Goal)
    (instantiatedAnswers : List Substitution)
    (conditionRun :
      Runs calls instantiated condition (first :: remaining))
    (thenRun : Runs calls first thenBranch instantiatedAnswers)
    (conditionBackward :
      RunsBackward calls initial instantiated condition (first :: remaining)
        conditionRun)
    (thenBackward :
      RunsBackward calls initial first thenBranch instantiatedAnswers
        thenRun) :
    RunsBackward calls initial instantiated
      (.ifThenElse condition thenBranch elseBranch) instantiatedAnswers
      (.ifThenElseSuccess instantiated first remaining condition thenBranch
        elseBranch instantiatedAnswers conditionRun thenRun) := by
  intro carried originalGoal states goalEq
  cases originalGoal <;> simp_all
  case ifThenElse originalCondition originalThen originalElse =>
    obtain ⟨carriedConditionAnswers, leftCondition, conditionAgreement⟩ :=
      conditionBackward states goalEq.1
    cases conditionAgreement with
    | cons firstAgreement remainingAgreement =>
        obtain ⟨carriedAnswers, leftThen, answerAgreement⟩ :=
          thenBackward firstAgreement goalEq.2.1
        exact ⟨carriedAnswers,
          .ifThenElseSuccess carried _ _ originalCondition originalThen
            originalElse carriedAnswers leftCondition leftThen,
          answerAgreement⟩

private theorem backwardIfFailure
    (_primitives : PrimitiveBisimulation calls initial)
    (instantiated : Substitution) (condition thenBranch elseBranch : Goal)
    (instantiatedAnswers : List Substitution)
    (conditionRun : Runs calls instantiated condition [])
    (elseRun : Runs calls instantiated elseBranch instantiatedAnswers)
    (conditionBackward :
      RunsBackward calls initial instantiated condition [] conditionRun)
    (elseBackward :
      RunsBackward calls initial instantiated elseBranch instantiatedAnswers
        elseRun) :
    RunsBackward calls initial instantiated
      (.ifThenElse condition thenBranch elseBranch) instantiatedAnswers
      (.ifThenElseFailure instantiated condition thenBranch elseBranch
        instantiatedAnswers conditionRun elseRun) := by
  intro carried originalGoal states goalEq
  cases originalGoal <;> simp_all
  case ifThenElse originalCondition originalThen originalElse =>
    obtain ⟨carriedConditionAnswers, leftCondition, conditionAgreement⟩ :=
      conditionBackward states goalEq.1
    cases conditionAgreement
    obtain ⟨carriedAnswers, leftElse, answerAgreement⟩ :=
      elseBackward states goalEq.2.2
    exact ⟨carriedAnswers,
      .ifThenElseFailure carried originalCondition originalThen originalElse
        carriedAnswers leftCondition leftElse,
      answerAgreement⟩

private theorem backwardOnce
    (_primitives : PrimitiveBisimulation calls initial)
    (instantiated : Substitution) (goal : Goal)
    (instantiatedBodyAnswers : List Substitution)
    (body : Runs calls instantiated goal instantiatedBodyAnswers)
    (bodyBackward :
      RunsBackward calls initial instantiated goal instantiatedBodyAnswers
        body) :
    RunsBackward calls initial instantiated (.once goal)
      (instantiatedBodyAnswers.take 1)
      (.once instantiated goal instantiatedBodyAnswers body) := by
  intro carried originalGoal states goalEq
  cases originalGoal <;> simp_all
  case once originalBody =>
    obtain ⟨carriedBodyAnswers, leftBody, bodyAgreement⟩ :=
      bodyBackward states goalEq
    exact ⟨carriedBodyAnswers.take 1,
      .once carried originalBody carriedBodyAnswers leftBody,
      bodyAgreement.take_one⟩

private theorem backwardWithMutex
    (_primitives : PrimitiveBisimulation calls initial)
    (instantiated : Substitution) (mutex : Term) (goal : Goal)
    (instantiatedAnswers : List Substitution)
    (body : Runs calls instantiated goal instantiatedAnswers)
    (bodyBackward :
      RunsBackward calls initial instantiated goal instantiatedAnswers body) :
    RunsBackward calls initial instantiated (.withMutex mutex goal)
      instantiatedAnswers
      (.withMutex instantiated mutex goal instantiatedAnswers body) := by
  intro carried originalGoal states goalEq
  cases originalGoal <;> simp_all
  case withMutex originalMutex originalBody =>
    obtain ⟨carriedAnswers, leftBody, answerAgreement⟩ :=
      bodyBackward states goalEq.2
    exact ⟨carriedAnswers,
      .withMutex carried originalMutex originalBody carriedAnswers leftBody,
      answerAgreement⟩

private theorem backwardAllNil
    (_primitives : PrimitiveBisimulation calls initial)
    (instantiated : Substitution) :
    RunsAllBackward calls initial instantiated [] [instantiated]
      (.nil instantiated) := by
  intro carried originalGoals states goalsEq
  cases originalGoals <;> simp_all
  exact ⟨[carried], .nil carried, .cons states .nil⟩

private theorem backwardAllCons
    (_primitives : PrimitiveBisimulation calls initial)
    (instantiated : Substitution) (goal : Goal) (goals : List Goal)
    (instantiatedHeadAnswers instantiatedAnswers : List Substitution)
    (head : Runs calls instantiated goal instantiatedHeadAnswers)
    (tail :
      RunsMany calls instantiatedHeadAnswers goals instantiatedAnswers)
    (headBackward :
      RunsBackward calls initial instantiated goal instantiatedHeadAnswers
        head)
    (tailBackward :
      RunsManyBackward calls initial instantiatedHeadAnswers goals
        instantiatedAnswers tail) :
    RunsAllBackward calls initial instantiated (goal :: goals)
      instantiatedAnswers
      (.cons instantiated goal goals instantiatedHeadAnswers
        instantiatedAnswers head tail) := by
  intro carried originalGoals states goalsEq
  cases originalGoals with
  | nil => simp at goalsEq
  | cons originalGoal originalGoals =>
      simp at goalsEq
      obtain ⟨carriedHeadAnswers, leftHead, headAgreement⟩ :=
        headBackward states goalsEq.1
      obtain ⟨carriedAnswers, leftTail, answerAgreement⟩ :=
        tailBackward headAgreement goalsEq.2
      exact ⟨carriedAnswers,
        .cons carried originalGoal originalGoals carriedHeadAnswers
          carriedAnswers leftHead leftTail,
        answerAgreement⟩

private theorem backwardManyNil
    (_primitives : PrimitiveBisimulation calls initial)
    (goals : List Goal) :
    RunsManyBackward calls initial [] goals [] (.nil goals) := by
  intro carriedInputs originalGoals inputAgreement goalsEq
  cases inputAgreement
  exact ⟨[], .nil originalGoals, .nil⟩

private theorem backwardManyCons
    (_primitives : PrimitiveBisimulation calls initial)
    (instantiated : Substitution) (remaining : List Substitution)
    (goals : List Goal)
    (instantiatedHeadAnswers instantiatedTailAnswers : List Substitution)
    (head :
      RunsAll calls instantiated goals instantiatedHeadAnswers)
    (tail :
      RunsMany calls remaining goals instantiatedTailAnswers)
    (headBackward :
      RunsAllBackward calls initial instantiated goals
        instantiatedHeadAnswers head)
    (tailBackward :
      RunsManyBackward calls initial remaining goals instantiatedTailAnswers
        tail) :
    RunsManyBackward calls initial (instantiated :: remaining) goals
      (instantiatedHeadAnswers ++ instantiatedTailAnswers)
      (.cons instantiated remaining goals instantiatedHeadAnswers
        instantiatedTailAnswers head tail) := by
  intro carriedInputs originalGoals inputAgreement goalsEq
  cases inputAgreement with
  | cons stateAgreement remainingAgreement =>
      obtain ⟨carriedHeadAnswers, leftHead, headAgreement⟩ :=
        headBackward stateAgreement goalsEq
      obtain ⟨carriedTailAnswers, leftTail, tailAgreement⟩ :=
        tailBackward remainingAgreement goalsEq
      exact ⟨carriedHeadAnswers ++ carriedTailAnswers,
        .cons _ _ originalGoals carriedHeadAnswers carriedTailAnswers
          leftHead leftTail,
        headAgreement.append tailAgreement⟩

private theorem backwardBranchesNil
    (_primitives : PrimitiveBisimulation calls initial)
    (instantiated : Substitution) :
    RunsBranchesBackward calls initial instantiated [] []
      (.nil instantiated) := by
  intro carried originalBranches states branchesEq
  cases originalBranches <;> simp_all
  exact ⟨[], .nil carried, .nil⟩

private theorem backwardBranchesCons
    (_primitives : PrimitiveBisimulation calls initial)
    (instantiated : Substitution) (branch : Goal) (branches : List Goal)
    (instantiatedHeadAnswers instantiatedTailAnswers : List Substitution)
    (head : Runs calls instantiated branch instantiatedHeadAnswers)
    (tail :
      RunsBranches calls instantiated branches instantiatedTailAnswers)
    (headBackward :
      RunsBackward calls initial instantiated branch instantiatedHeadAnswers
        head)
    (tailBackward :
      RunsBranchesBackward calls initial instantiated branches
        instantiatedTailAnswers tail) :
    RunsBranchesBackward calls initial instantiated (branch :: branches)
      (instantiatedHeadAnswers ++ instantiatedTailAnswers)
      (.cons instantiated branch branches instantiatedHeadAnswers
        instantiatedTailAnswers head tail) := by
  intro carried originalBranches states branchesEq
  cases originalBranches with
  | nil => simp at branchesEq
  | cons originalBranch originalBranches =>
      simp at branchesEq
      obtain ⟨carriedHeadAnswers, leftHead, headAgreement⟩ :=
        headBackward states branchesEq.1
      obtain ⟨carriedTailAnswers, leftTail, tailAgreement⟩ :=
        tailBackward states branchesEq.2
      exact ⟨carriedHeadAnswers ++ carriedTailAnswers,
        .cons carried originalBranch originalBranches carriedHeadAnswers
          carriedTailAnswers leftHead leftTail,
        headAgreement.append tailAgreement⟩

end BackwardHandlers

private theorem runsBackwardRec {calls : CallSemantics}
    {initial instantiated : Substitution} {instantiatedGoal : Goal}
    {instantiatedAnswers : List Substitution}
    (primitives : PrimitiveBisimulation calls initial)
    (execution :
      Runs calls instantiated instantiatedGoal instantiatedAnswers) :
    RunsBackward calls initial instantiated instantiatedGoal
      instantiatedAnswers execution :=
  Runs.rec (motive_1 := RunsBackward calls initial)
    (motive_2 := RunsAllBackward calls initial)
    (motive_3 := RunsManyBackward calls initial)
    (motive_4 := RunsBranchesBackward calls initial)
    (backwardTruth primitives) (backwardFail primitives)
    (backwardUnifySuccess primitives) (backwardUnifyFailure primitives)
    (backwardIdenticalSuccess primitives)
    (backwardIdenticalFailure primitives) (backwardCall primitives)
    (backwardConjunction primitives) (backwardDisjunction primitives)
    (backwardIfSuccess primitives) (backwardIfFailure primitives)
    (backwardOnce primitives) (backwardWithMutex primitives)
    (backwardAllNil primitives) (backwardAllCons primitives)
    (backwardManyNil primitives) (backwardManyCons primitives)
    (backwardBranchesNil primitives) (backwardBranchesCons primitives)
    execution

private theorem runsAllBackwardRec {calls : CallSemantics}
    {initial instantiated : Substitution} {instantiatedGoals : List Goal}
    {instantiatedAnswers : List Substitution}
    (primitives : PrimitiveBisimulation calls initial)
    (execution :
      RunsAll calls instantiated instantiatedGoals instantiatedAnswers) :
    RunsAllBackward calls initial instantiated instantiatedGoals
      instantiatedAnswers execution :=
  RunsAll.rec (motive_1 := RunsBackward calls initial)
    (motive_2 := RunsAllBackward calls initial)
    (motive_3 := RunsManyBackward calls initial)
    (motive_4 := RunsBranchesBackward calls initial)
    (backwardTruth primitives) (backwardFail primitives)
    (backwardUnifySuccess primitives) (backwardUnifyFailure primitives)
    (backwardIdenticalSuccess primitives)
    (backwardIdenticalFailure primitives) (backwardCall primitives)
    (backwardConjunction primitives) (backwardDisjunction primitives)
    (backwardIfSuccess primitives) (backwardIfFailure primitives)
    (backwardOnce primitives) (backwardWithMutex primitives)
    (backwardAllNil primitives) (backwardAllCons primitives)
    (backwardManyNil primitives) (backwardManyCons primitives)
    (backwardBranchesNil primitives) (backwardBranchesCons primitives)
    execution

private theorem runsManyBackwardRec {calls : CallSemantics}
    {initial : Substitution}
    {instantiatedInputs : List Substitution}
    {instantiatedGoals : List Goal}
    {instantiatedAnswers : List Substitution}
    (primitives : PrimitiveBisimulation calls initial)
    (execution :
      RunsMany calls instantiatedInputs instantiatedGoals
        instantiatedAnswers) :
    RunsManyBackward calls initial instantiatedInputs instantiatedGoals
      instantiatedAnswers execution :=
  RunsMany.rec (motive_1 := RunsBackward calls initial)
    (motive_2 := RunsAllBackward calls initial)
    (motive_3 := RunsManyBackward calls initial)
    (motive_4 := RunsBranchesBackward calls initial)
    (backwardTruth primitives) (backwardFail primitives)
    (backwardUnifySuccess primitives) (backwardUnifyFailure primitives)
    (backwardIdenticalSuccess primitives)
    (backwardIdenticalFailure primitives) (backwardCall primitives)
    (backwardConjunction primitives) (backwardDisjunction primitives)
    (backwardIfSuccess primitives) (backwardIfFailure primitives)
    (backwardOnce primitives) (backwardWithMutex primitives)
    (backwardAllNil primitives) (backwardAllCons primitives)
    (backwardManyNil primitives) (backwardManyCons primitives)
    (backwardBranchesNil primitives) (backwardBranchesCons primitives)
    execution

private theorem runsBranchesBackwardRec {calls : CallSemantics}
    {initial instantiated : Substitution}
    {instantiatedBranches : List Goal}
    {instantiatedAnswers : List Substitution}
    (primitives : PrimitiveBisimulation calls initial)
    (execution :
      RunsBranches calls instantiated instantiatedBranches
        instantiatedAnswers) :
    RunsBranchesBackward calls initial instantiated instantiatedBranches
      instantiatedAnswers execution :=
  RunsBranches.rec (motive_1 := RunsBackward calls initial)
    (motive_2 := RunsAllBackward calls initial)
    (motive_3 := RunsManyBackward calls initial)
    (motive_4 := RunsBranchesBackward calls initial)
    (backwardTruth primitives) (backwardFail primitives)
    (backwardUnifySuccess primitives) (backwardUnifyFailure primitives)
    (backwardIdenticalSuccess primitives)
    (backwardIdenticalFailure primitives) (backwardCall primitives)
    (backwardConjunction primitives) (backwardDisjunction primitives)
    (backwardIfSuccess primitives) (backwardIfFailure primitives)
    (backwardOnce primitives) (backwardWithMutex primitives)
    (backwardAllNil primitives) (backwardAllCons primitives)
    (backwardManyNil primitives) (backwardManyCons primitives)
    (backwardBranchesNil primitives) (backwardBranchesCons primitives)
    execution

/-- Reverse half of substitution congruence for one open goal. The original
goal is retained explicitly because substitution need not be injective. -/
theorem Runs.backward {calls : CallSemantics}
    {initial carried instantiated : Substitution} {originalGoal : Goal}
    {instantiatedAnswers : List Substitution}
    (primitives : PrimitiveBisimulation calls initial)
    (states : StateAgrees initial carried instantiated)
    (execution :
      Runs calls instantiated (initial.applyGoal originalGoal)
        instantiatedAnswers) :
    ∃ carriedAnswers,
      Runs calls carried originalGoal carriedAnswers ∧
      AnswerBagsAgree initial carriedAnswers instantiatedAnswers :=
  runsBackwardRec primitives execution states rfl

/-- Reverse substitution congruence for left-to-right conjunction. -/
theorem RunsAll.backward {calls : CallSemantics}
    {initial carried instantiated : Substitution}
    {originalGoals : List Goal} {instantiatedAnswers : List Substitution}
    (primitives : PrimitiveBisimulation calls initial)
    (states : StateAgrees initial carried instantiated)
    (execution :
      RunsAll calls instantiated (initial.applyGoals originalGoals)
        instantiatedAnswers) :
    ∃ carriedAnswers,
      RunsAll calls carried originalGoals carriedAnswers ∧
      AnswerBagsAgree initial carriedAnswers instantiatedAnswers :=
  runsAllBackwardRec primitives execution states rfl

/-- Reverse substitution congruence for ordered monadic answer binding. -/
theorem RunsMany.backward {calls : CallSemantics}
    {initial : Substitution}
    {carriedInputs instantiatedInputs : List Substitution}
    {originalGoals : List Goal} {instantiatedAnswers : List Substitution}
    (primitives : PrimitiveBisimulation calls initial)
    (inputs : AnswerBagsAgree initial carriedInputs instantiatedInputs)
    (execution :
      RunsMany calls instantiatedInputs (initial.applyGoals originalGoals)
        instantiatedAnswers) :
    ∃ carriedAnswers,
      RunsMany calls carriedInputs originalGoals carriedAnswers ∧
      AnswerBagsAgree initial carriedAnswers instantiatedAnswers :=
  runsManyBackwardRec primitives execution inputs rfl

/-- Reverse substitution congruence for source-ordered disjunction. -/
theorem RunsBranches.backward {calls : CallSemantics}
    {initial carried instantiated : Substitution}
    {originalBranches : List Goal}
    {instantiatedAnswers : List Substitution}
    (primitives : PrimitiveBisimulation calls initial)
    (states : StateAgrees initial carried instantiated)
    (execution :
      RunsBranches calls instantiated (initial.applyGoals originalBranches)
        instantiatedAnswers) :
    ∃ carriedAnswers,
      RunsBranches calls carried originalBranches carriedAnswers ∧
      AnswerBagsAgree initial carriedAnswers instantiatedAnswers :=
  runsBranchesBackwardRec primitives execution states rfl

/-- Big-step substitution bisimulation for one goal, with ordered answer bags
related pointwise rather than identified as raw substitution lists. -/
structure InstantiationBisimulation (calls : CallSemantics)
    (initial carried instantiated : Substitution) (goal : Goal) : Prop where
  forward : ∀ {carriedAnswers},
    Runs calls carried goal carriedAnswers →
      ∃ instantiatedAnswers,
        Runs calls instantiated (initial.applyGoal goal)
          instantiatedAnswers ∧
        AnswerBagsAgree initial carriedAnswers instantiatedAnswers
  backward : ∀ {instantiatedAnswers},
    Runs calls instantiated (initial.applyGoal goal) instantiatedAnswers →
      ∃ carriedAnswers,
        Runs calls carried goal carriedAnswers ∧
        AnswerBagsAgree initial carriedAnswers instantiatedAnswers

/-- The structural forward and backward proofs form a big-step bisimulation
whenever the primitive call contract is available. -/
theorem instantiationBisimulation {calls : CallSemantics}
    {initial carried instantiated : Substitution} {goal : Goal}
    (primitives : PrimitiveBisimulation calls initial)
    (states : StateAgrees initial carried instantiated) :
    InstantiationBisimulation calls initial carried instantiated goal where
  forward := fun execution => execution.forward primitives states
  backward := fun execution => execution.backward primitives states

/-- Concrete call-free substitution bisimulation. Open unification is proved
internally, and there is no predicate-call premise left. -/
theorem noCallsInstantiationBisimulation
    (initial carried instantiated : Substitution) (goal : Goal)
    (states : StateAgrees initial carried instantiated) :
    InstantiationBisimulation NoCalls initial carried instantiated goal :=
  instantiationBisimulation (.noCalls initial) states

/-- Big-step substitution bisimulation for a left-to-right goal sequence. -/
structure GoalsInstantiationBisimulation (calls : CallSemantics)
    (initial carried instantiated : Substitution) (goals : List Goal) : Prop where
  forward : ∀ {carriedAnswers},
    RunsAll calls carried goals carriedAnswers →
      ∃ instantiatedAnswers,
        RunsAll calls instantiated (initial.applyGoals goals)
          instantiatedAnswers ∧
        AnswerBagsAgree initial carriedAnswers instantiatedAnswers
  backward : ∀ {instantiatedAnswers},
    RunsAll calls instantiated (initial.applyGoals goals)
      instantiatedAnswers →
      ∃ carriedAnswers,
        RunsAll calls carried goals carriedAnswers ∧
        AnswerBagsAgree initial carriedAnswers instantiatedAnswers

/-- The sequence-level structural proofs form a big-step bisimulation under
the same primitive contract. -/
theorem goalsInstantiationBisimulation {calls : CallSemantics}
    {initial carried instantiated : Substitution} {goals : List Goal}
    (primitives : PrimitiveBisimulation calls initial)
    (states : StateAgrees initial carried instantiated) :
    GoalsInstantiationBisimulation calls initial carried instantiated goals
    where
  forward := fun execution => execution.forward primitives states
  backward := fun execution => execution.backward primitives states

/-- Concrete call-free substitution bisimulation for a goal sequence. -/
theorem noCallsGoalsInstantiationBisimulation
    (initial carried instantiated : Substitution) (goals : List Goal)
    (states : StateAgrees initial carried instantiated) :
    GoalsInstantiationBisimulation NoCalls initial carried instantiated goals :=
  goalsInstantiationBisimulation (.noCalls initial) states

/-! ### Whole-prefix alias finalization

Pinned `build_branch/4` performs variable sharing while translating the
surrounding construct.  `ResolvesAliasGoals` describes that ordered prefix
independently.  The following lemmas first show that the prefix has exactly
the resolved runtime state, then use the substitution bisimulation above to
move that state through the complete continuation syntax.
-/

/-- A successfully resolved alias prefix can be prepended to any continuation
execution.  The prefix has one answer at every step, so no order or
multiplicity choice is introduced. -/
theorem resolvesAliasGoals_runPrefixThen
    {calls : CallSemantics} {initial resolved : Substitution}
    {aliases continuation : List Goal} {answers : List Substitution}
    (resolution : ResolvesAliasGoals initial aliases resolved)
    (continuationRun : RunsAll calls resolved continuation answers) :
    RunsAll calls initial (aliases ++ continuation) answers := by
  induction resolution with
  | nil bindings => simpa using continuationRun
  | cons bindings middle result left right goals head tail induction =>
      have tailRun : RunsAll calls middle (goals ++ continuation) answers :=
        induction continuationRun
      refine .cons bindings (.unify left right) (goals ++ continuation)
        [middle] answers (.unifySuccess bindings middle left right head) ?_
      simpa using RunsMany.cons middle [] (goals ++ continuation)
        answers [] tailRun (.nil (goals ++ continuation))

/-- Conversely, any execution of a resolvable alias prefix must pass through
the uniquely resolved state before executing the continuation. -/
theorem resolvesAliasGoals_stripPrefix
    {calls : CallSemantics} {initial resolved : Substitution}
    {aliases continuation : List Goal} {answers : List Substitution}
    (resolution : ResolvesAliasGoals initial aliases resolved)
    (execution : RunsAll calls initial (aliases ++ continuation) answers) :
    RunsAll calls resolved continuation answers := by
  induction resolution generalizing answers with
  | nil bindings => simpa using execution
  | cons bindings middle result left right goals head tail induction =>
      cases execution with
      | cons _ _ _ headAnswers answers headRun tailRun =>
          cases headRun with
          | unifySuccess _ actualMiddle _ _ actual =>
              have middleEquality := head.deterministic actual
              subst actualMiddle
              cases tailRun with
              | cons _ remaining _ tailAnswers remainingAnswers
                  continuationRun remainingRun =>
                  cases remainingRun
                  simpa using induction continuationRun
          | unifyFailure _ _ _ failure =>
              exact False.elim (failure middle head)

/-- A resolved alias prefix and direct execution from its result state have
identical ordered answer bags. -/
theorem resolvesAliasGoals_runsAll_iff
    {calls : CallSemantics} {initial resolved : Substitution}
    {aliases continuation : List Goal} {answers : List Substitution}
    (resolution : ResolvesAliasGoals initial aliases resolved) :
    RunsAll calls initial (aliases ++ continuation) answers ↔
      RunsAll calls resolved continuation answers := by
  constructor
  · exact resolvesAliasGoals_stripPrefix resolution
  · exact resolvesAliasGoals_runPrefixThen resolution

/-- Bidirectional ordered semantics of global alias finalization.  The left
side executes the independent explicit-equality prefix.  The right side starts
from an empty state after applying the independently resolved substitution to
the continuation.  `AnswerBagsAgree` relates answers pointwise, preserving
their order and multiplicity without identifying distinct substitution
representations by definition. -/
structure AliasFinalizationBisimulation (calls : CallSemantics)
    (initial : Substitution) (aliases : List Goal) (resolved : Substitution)
    (continuation : List Goal) : Prop where
  forward : ∀ {explicitAnswers},
    RunsAll calls initial (aliases ++ continuation) explicitAnswers →
      ∃ finalizedAnswers,
        RunsAll calls [] (resolved.applyGoals continuation)
          finalizedAnswers ∧
        AnswerBagsAgree resolved explicitAnswers finalizedAnswers
  backward : ∀ {finalizedAnswers},
    RunsAll calls [] (resolved.applyGoals continuation) finalizedAnswers →
      ∃ explicitAnswers,
        RunsAll calls initial (aliases ++ continuation) explicitAnswers ∧
        AnswerBagsAgree resolved explicitAnswers finalizedAnswers

/-- Universal alias-finalization theorem for every continuation whose
primitive calls respect substitution. -/
theorem aliasFinalizationBisimulation
    {calls : CallSemantics} {initial resolved : Substitution}
    {aliases continuation : List Goal}
    (resolution : ResolvesAliasGoals initial aliases resolved)
    (primitives : PrimitiveBisimulation calls resolved) :
    AliasFinalizationBisimulation calls initial aliases resolved continuation
    where
  forward := by
    intro explicitAnswers execution
    have continuationRun :=
      resolvesAliasGoals_stripPrefix resolution execution
    exact continuationRun.forward primitives (StateAgrees.initial resolved)
  backward := by
    intro finalizedAnswers execution
    obtain ⟨explicitAnswers, continuationRun, answersAgree⟩ :=
      execution.backward primitives (StateAgrees.initial resolved)
    exact ⟨explicitAnswers,
      resolvesAliasGoals_runPrefixThen resolution continuationRun,
      answersAgree⟩

/-- Concrete call-free instance with no remaining primitive premise. -/
theorem noCallsAliasFinalizationBisimulation
    {initial resolved : Substitution} {aliases continuation : List Goal}
    (resolution : ResolvesAliasGoals initial aliases resolved) :
    AliasFinalizationBisimulation NoCalls initial aliases resolved
      continuation :=
  aliasFinalizationBisimulation resolution (.noCalls resolved)

/-- Universal independent alias-finalization theorem specialized to the
ledger produced by pinned `build_superpose_branches/3`.  The translator
relation proves the ledger shape, and the abstract call semantics must respect
the resolved substitution.  Executable name-encoding injectivity remains a
separate compiler-bridge obligation rather than being smuggled into this
independent theorem. -/
theorem translatesSuperposeBranches_aliasFinalization
    {calls : CallSemantics} {state : TranslatorState} {target : LogicVar}
    {counter nextCounter : Nat} {sources : List Metta.Atom}
    {aliases branches : List Goal}
    (translation : TranslatesSuperposeBranches state (.variable target)
      counter sources aliases branches nextCounter)
    (primitives : ∀ resolved, AliasStateFor target resolved →
      PrimitiveBisimulation calls resolved) :
    ∃ resolved,
      AliasStateFor target resolved ∧
      AliasFinalizationBisimulation calls [] aliases resolved
        [.disjunction branches] := by
  obtain ⟨resolved, resolution, stateInvariant⟩ :=
    aliasGoalsFor_resolvesFromEmpty translation.aliasGoalsFor
  exact ⟨resolved, stateInvariant,
    aliasFinalizationBisimulation resolution
      (primitives resolved stateInvariant)⟩

/-- Call-free specialization with no abstract primitive premise. -/
theorem translatesSuperposeBranches_noCallsAliasFinalization
    {state : TranslatorState} {target : LogicVar}
    {counter nextCounter : Nat} {sources : List Metta.Atom}
    {aliases branches : List Goal}
    (translation : TranslatesSuperposeBranches state (.variable target)
      counter sources aliases branches nextCounter) :
    ∃ resolved,
      AliasStateFor target resolved ∧
      AliasFinalizationBisimulation NoCalls [] aliases resolved
        [.disjunction branches] := by
  exact translatesSuperposeBranches_aliasFinalization translation
    (fun resolved _ => .noCalls resolved)

/-- Executing the explicit alias equality yields a state whose call-free
continuation is bisimilar to applying the alias throughout the continuation
syntax. This is the ordered semantic instance required by normalized variable
branches, still separate from the executable `Step` bridge. -/
theorem explicitAliasPrefix_noCalls_bisimulation (source target : LogicVar)
    (distinct : source ≠ target) (goals : List Goal) :
    ∃ alias,
      Unifies [] (.variable source) (.variable target) alias ∧
      GoalsInstantiationBisimulation NoCalls alias alias [] goals := by
  let alias : Substitution := [(source, .variable target)]
  refine ⟨alias, unifies_empty_distinct_alias source target distinct, ?_⟩
  exact noCallsGoalsInstantiationBisimulation alias alias [] goals
    (StateAgrees.initial alias)

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
