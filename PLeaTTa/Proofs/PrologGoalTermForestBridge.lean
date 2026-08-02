-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologGoalTermForestBridge
Purpose: Extract the complete ordered term forest from alpha-agreeing local
  control, including nested and executable-hidden compiler fields
Trusted boundary: none
Main exports: AlphaTermForest, AlphaGoalsAgree.termForest,
  NormalizedAlphaGoalsAgree.exists_complete_termForest,
  TaskPayloadAgrees.materializeControlForest
-/
import PLeaTTa.Proofs.PrologResidualForestBridge

namespace PLeaTTa.PrologGoalTermForestBridge

open Metta (Atom)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Resolver
open CompilerSubstitutionAdequacy
open PrologGoalAlpha
open PrologOrdinaryStepBridge
open PrologRecursiveCallPayloadBridge
open PrologStateBridge

/-- Ordered alpha term agreement appends without changing either side's
position or multiplicity. -/
theorem AlphaTermsAgree.append
    {alpha : List (LogicVar × String)}
    {leftReferences rightReferences : List Term}
    {leftExecutables rightExecutables : List Atom}
    (left : AlphaTermsAgree alpha leftReferences leftExecutables)
    (right : AlphaTermsAgree alpha rightReferences rightExecutables) :
    AlphaTermsAgree alpha (leftReferences ++ rightReferences)
      (leftExecutables ++ rightExecutables) := by
  induction left with
  | nil => simpa using right
  | cons head tail inductionHypothesis =>
      simpa using AlphaTermsAgree.cons head inductionHypothesis

/-- One proof-indexed ordered forest of corresponding term leaves.  The
agreement field makes it impossible to list a source term without its exact
runtime-alpha counterpart. -/
structure AlphaTermForest (alpha : List (LogicVar × String)) where
  references : List Term
  executables : List Atom
  agreement : AlphaTermsAgree alpha references executables

namespace AlphaTermForest

/-- Empty forest for term-free control. -/
def empty (alpha : List (LogicVar × String)) : AlphaTermForest alpha :=
  ⟨[], [], .nil⟩

/-- Singleton forest for one term leaf. -/
def singleton
    {alpha : List (LogicVar × String)} {reference : Term}
    {executable : Atom}
    (agreement : AlphaTermAgrees alpha reference executable) :
    AlphaTermForest alpha :=
  ⟨[reference], [executable], .cons agreement .nil⟩

/-- Existing ordered term-list agreement is already a forest. -/
def ofTerms
    {alpha : List (LogicVar × String)} {references : List Term}
    {executables : List Atom}
    (agreement : AlphaTermsAgree alpha references executables) :
    AlphaTermForest alpha :=
  ⟨references, executables, agreement⟩

/-- Append two forests while retaining the shared alpha. -/
def append
    {alpha : List (LogicVar × String)}
    (left right : AlphaTermForest alpha) : AlphaTermForest alpha :=
  ⟨left.references ++ right.references,
    left.executables ++ right.executables,
    PLeaTTa.PrologGoalTermForestBridge.AlphaTermsAgree.append
      left.agreement right.agreement⟩

/-- Complete independent variable occurrence list of the extracted forest. -/
def referenceVariables
    {alpha : List (LogicVar × String)} (forest : AlphaTermForest alpha) :
    List LogicVar :=
  forest.references.flatMap termVariables

/-- Complete runtime-name occurrence list of the extracted paired leaves.
Executable control may contain derived carry atoms whose names are covered by
these leaves even when the derived atom itself has no independent term peer. -/
def executableVariables
    {alpha : List (LogicVar × String)} (forest : AlphaTermForest alpha) :
    List String :=
  forest.executables.flatMap Atom.vars

end AlphaTermForest

/-- The resolver's mutually recursive occurrence traversal is extensionally
the same ordered flattening used by `AlphaTermForest.referenceVariables`. -/
@[simp] theorem termsVariables_eq_flatMap (terms : List Term) :
    termsVariables terms = terms.flatMap termVariables := by
  induction terms with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [termsVariables, inductionHypothesis]

/-- Coverage is stable when the same ordered occurrence prefix is retained on
both sides. -/
theorem List.Subset.append_same_left {X : Type} {left right : List X}
    (front : List X) (covered : List.Subset left right) :
    List.Subset (front ++ left) (front ++ right) := by
  intro item membership
  rw [List.mem_append] at membership ⊢
  exact membership.elim Or.inl (fun inTail => Or.inr (covered inTail))

/-- Independent coverage of two ordered regions composes over append. -/
theorem List.Subset.append_both {X : Type}
    {leftSource rightSource leftTarget rightTarget : List X}
    (leftCovered : List.Subset leftSource leftTarget)
    (rightCovered : List.Subset rightSource rightTarget) :
    List.Subset (leftSource ++ rightSource) (leftTarget ++ rightTarget) := by
  intro item membership
  rw [List.mem_append] at membership ⊢
  exact membership.elim (fun inLeft => Or.inl (leftCovered inLeft))
    (fun inRight => Or.inr (rightCovered inRight))

@[simp] theorem AlphaTermForest.referenceVariables_empty
    (alpha : List (LogicVar × String)) :
    (AlphaTermForest.empty alpha).referenceVariables = [] := rfl

@[simp] theorem AlphaTermForest.referenceVariables_singleton
    {alpha : List (LogicVar × String)} {reference : Term}
    {executable : Atom}
    (agreement : AlphaTermAgrees alpha reference executable) :
    (AlphaTermForest.singleton agreement).referenceVariables =
      termVariables reference := by
  simp [AlphaTermForest.referenceVariables, AlphaTermForest.singleton]

@[simp] theorem AlphaTermForest.referenceVariables_ofTerms
    {alpha : List (LogicVar × String)} {references : List Term}
    {executables : List Atom}
    (agreement : AlphaTermsAgree alpha references executables) :
    (AlphaTermForest.ofTerms agreement).referenceVariables =
      termsVariables references := by
  simp [AlphaTermForest.referenceVariables, AlphaTermForest.ofTerms]

@[simp] theorem AlphaTermForest.referenceVariables_append
    {alpha : List (LogicVar × String)}
    (left right : AlphaTermForest alpha) :
    (left.append right).referenceVariables =
      left.referenceVariables ++ right.referenceVariables := by
  simp [AlphaTermForest.referenceVariables, AlphaTermForest.append]

@[simp] theorem AlphaTermForest.executableVariables_empty
    (alpha : List (LogicVar × String)) :
    (AlphaTermForest.empty alpha).executableVariables = [] := rfl

@[simp] theorem AlphaTermForest.executableVariables_singleton
    {alpha : List (LogicVar × String)} {reference : Term}
    {executable : Atom}
    (agreement : AlphaTermAgrees alpha reference executable) :
    (AlphaTermForest.singleton agreement).executableVariables =
      executable.vars := by
  simp [AlphaTermForest.executableVariables, AlphaTermForest.singleton]

@[simp] theorem AlphaTermForest.executableVariables_ofTerms
    {alpha : List (LogicVar × String)} {references : List Term}
    {executables : List Atom}
    (agreement : AlphaTermsAgree alpha references executables) :
    (AlphaTermForest.ofTerms agreement).executableVariables =
      executables.flatMap Atom.vars := by
  simp [AlphaTermForest.executableVariables, AlphaTermForest.ofTerms]

@[simp] theorem AlphaTermForest.executableVariables_append
    {alpha : List (LogicVar × String)}
    (left right : AlphaTermForest alpha) :
    (left.append right).executableVariables =
      left.executableVariables ++ right.executableVariables := by
  simp [AlphaTermForest.executableVariables, AlphaTermForest.append]

/-- Literal `amb` branches have no nested bodies but still retain the hidden
enclosing output at every branch and in the empty case. -/
inductive AlphaLiteralTermForest
    (alpha : List (LogicVar × String))
    (referenceOutput : Term) (executableOutput : Atom) :
    {references : List PeTTaSpec.PrologCore.Goal} →
      {executables : List (Atom × List PLeaTTa.Goal)} →
      AlphaLiteralAmbBranchesAgree alpha referenceOutput executableOutput
        references executables → AlphaTermForest alpha → Prop where
  | nil (output : AlphaTermAgrees alpha referenceOutput executableOutput) :
      AlphaLiteralTermForest alpha referenceOutput executableOutput
        (.nil output) (AlphaTermForest.singleton output)
  | cons {referenceValue : Term} {executableValue : Atom}
      {referenceBranches : List PeTTaSpec.PrologCore.Goal}
      {executableBranches : List (Atom × List PLeaTTa.Goal)}
      (value : AlphaTermAgrees alpha referenceValue executableValue)
      (output : AlphaTermAgrees alpha referenceOutput executableOutput)
      (tail : AlphaLiteralAmbBranchesAgree alpha referenceOutput
        executableOutput referenceBranches executableBranches)
      {tailForest : AlphaTermForest alpha}
      (tailRel : AlphaLiteralTermForest alpha referenceOutput executableOutput
        tail tailForest) :
      AlphaLiteralTermForest alpha referenceOutput executableOutput
        (.cons value output tail)
        ((AlphaTermForest.singleton value).append
          ((AlphaTermForest.singleton output).append tailForest))

mutual

/-- Proof-relevant specification of the complete term forest for one goal. -/
inductive AlphaGoalTermForest
    (alpha : List (LogicVar × String)) (barrier : Nat) :
    {reference : PeTTaSpec.PrologCore.Goal} →
      {executable : PLeaTTa.Goal} →
      AlphaGoalAgrees alpha barrier reference executable →
      AlphaTermForest alpha → Prop where
  | unify {referenceLeft referenceRight : Term}
      {executableLeft executableRight : Atom}
      (left : AlphaTermAgrees alpha referenceLeft executableLeft)
      (right : AlphaTermAgrees alpha referenceRight executableRight) :
      AlphaGoalTermForest alpha barrier (.unify left right)
        ((AlphaTermForest.singleton left).append
          (AlphaTermForest.singleton right))
  | compileAlias {referenceLeft referenceRight : Term}
      {executableLeft executableRight : Atom}
      (left : AlphaTermAgrees alpha referenceLeft executableLeft)
      (right : AlphaTermAgrees alpha referenceRight executableRight) :
      AlphaGoalTermForest alpha barrier (.compileAlias left right)
        ((AlphaTermForest.singleton left).append
          (AlphaTermForest.singleton right))
  | cut : AlphaGoalTermForest alpha barrier .cut (.empty alpha)
  | builtin {predicate : String} {referenceArguments : List Term}
      {referenceResult : Term} {executableArguments : List Atom}
      {executableResult : Atom}
      (arguments : AlphaTermsAgree alpha referenceArguments executableArguments)
      (result : AlphaTermAgrees alpha referenceResult executableResult) :
      AlphaGoalTermForest alpha barrier (.builtin arguments result)
        ((AlphaTermForest.ofTerms arguments).append
          (AlphaTermForest.singleton result))
  | definedCall {predicate : String} {referenceArguments : List Term}
      {referenceResult : Term} {executableArguments : List Atom}
      {executableResult : Atom}
      (arguments : AlphaTermsAgree alpha referenceArguments executableArguments)
      (result : AlphaTermAgrees alpha referenceResult executableResult) :
      AlphaGoalTermForest alpha barrier (.definedCall arguments result)
        ((AlphaTermForest.ofTerms arguments).append
          (AlphaTermForest.singleton result))
  | assertaPredicate {referencePayload referenceResult : Term}
      {executablePayload executableResult : Atom}
      (payload : AlphaTermAgrees alpha referencePayload executablePayload)
      (result : AlphaTermAgrees alpha referenceResult executableResult) :
      AlphaGoalTermForest alpha barrier (.assertaPredicate payload result)
        ((AlphaTermForest.singleton payload).append
          (AlphaTermForest.singleton result))
  | assertzPredicate {referencePayload referenceResult : Term}
      {executablePayload executableResult : Atom}
      (payload : AlphaTermAgrees alpha referencePayload executablePayload)
      (result : AlphaTermAgrees alpha referenceResult executableResult) :
      AlphaGoalTermForest alpha barrier (.assertzPredicate payload result)
        ((AlphaTermForest.singleton payload).append
          (AlphaTermForest.singleton result))
  | softCutTruth {referenceCondition referenceElse}
      {executableCondition executableElse}
      (condition : AlphaGoalsAgree alpha barrier referenceCondition
        executableCondition)
      (otherwise : AlphaGoalsAgree alpha barrier referenceElse executableElse)
      {conditionForest otherwiseForest : AlphaTermForest alpha}
      (conditionRel : AlphaGoalsTermForest alpha barrier condition
        conditionForest)
      (otherwiseRel : AlphaGoalsTermForest alpha barrier otherwise
        otherwiseForest) :
      AlphaGoalTermForest alpha barrier (.softCutTruth condition otherwise)
        (conditionForest.append otherwiseForest)
  | typeCheckSoftCut {referenceValue referenceExpected referenceDirect
        referenceMeta : Term}
      {executableValue executableExpected executableDirect executableMeta
        executableTemplate : Atom}
      (value : AlphaTermAgrees alpha referenceValue executableValue)
      (expected : AlphaTypeCheckExpectedAgrees alpha referenceExpected
        executableExpected executableTemplate)
      (direct : AlphaTermAgrees alpha referenceDirect executableDirect)
      (metaTerm : AlphaTermAgrees alpha referenceMeta executableMeta) :
      AlphaGoalTermForest alpha barrier
        (.typeCheckSoftCut value expected direct metaTerm)
        ((AlphaTermForest.singleton value).append
          ((AlphaTermForest.singleton expected.term).append
            ((AlphaTermForest.singleton direct).append
              (AlphaTermForest.singleton metaTerm))))
  | shortCircuitAnd {referenceCondition referenceBody referenceOutput}
      {executableCondition executableBody executableOutput}
      {referenceBodyGoals executableBodyGoals}
      (condition : AlphaTermAgrees alpha referenceCondition executableCondition)
      (body : AlphaTermAgrees alpha referenceBody executableBody)
      (output : AlphaTermAgrees alpha referenceOutput executableOutput)
      (bodyGoals : AlphaGoalsAgree alpha barrier referenceBodyGoals
        executableBodyGoals)
      {bodyForest : AlphaTermForest alpha}
      (bodyRel : AlphaGoalsTermForest alpha barrier bodyGoals bodyForest) :
      AlphaGoalTermForest alpha barrier
        (.shortCircuitAnd condition body output bodyGoals)
        ((AlphaTermForest.singleton condition).append
          ((AlphaTermForest.singleton body).append
            ((AlphaTermForest.singleton output).append bodyForest)))
  | shortCircuitOr {referenceCondition referenceBody referenceOutput}
      {executableCondition executableBody executableOutput}
      {referenceBodyGoals executableBodyGoals}
      (condition : AlphaTermAgrees alpha referenceCondition executableCondition)
      (body : AlphaTermAgrees alpha referenceBody executableBody)
      (output : AlphaTermAgrees alpha referenceOutput executableOutput)
      (bodyGoals : AlphaGoalsAgree alpha barrier referenceBodyGoals
        executableBodyGoals)
      {bodyForest : AlphaTermForest alpha}
      (bodyRel : AlphaGoalsTermForest alpha barrier bodyGoals bodyForest) :
      AlphaGoalTermForest alpha barrier
        (.shortCircuitOr condition body output bodyGoals)
        ((AlphaTermForest.singleton condition).append
          ((AlphaTermForest.singleton body).append
            ((AlphaTermForest.singleton output).append bodyForest)))
  | findall {referenceTemplate referenceOutput : Term}
      {executableTemplate executableOutput : Atom}
      {referenceGoals executableGoals}
      (template : AlphaTermAgrees alpha referenceTemplate executableTemplate)
      (body : AlphaGoalsAgree alpha barrier referenceGoals executableGoals)
      (output : AlphaTermAgrees alpha referenceOutput executableOutput)
      {bodyForest : AlphaTermForest alpha}
      (bodyRel : AlphaGoalsTermForest alpha barrier body bodyForest) :
      AlphaGoalTermForest alpha barrier (.findall template body output)
        ((AlphaTermForest.singleton template).append
          (bodyForest.append (AlphaTermForest.singleton output)))
  | literalAmb {referenceOutput : Term} {executableOutput : Atom}
      {referenceBranches executableBranches}
      (branches : AlphaLiteralAmbBranchesAgree alpha referenceOutput
        executableOutput referenceBranches executableBranches)
      {forest : AlphaTermForest alpha}
      (rel : AlphaLiteralTermForest alpha referenceOutput executableOutput
        branches forest) :
      AlphaGoalTermForest alpha barrier (.literalAmb branches) forest
  | builtAmb {referenceOutput : Term} {executableOutput : Atom}
      {referenceBranches executableBranches}
      (branches : AlphaSuperposeBranchesAgree alpha barrier referenceOutput
        executableOutput referenceBranches executableBranches)
      {forest : AlphaTermForest alpha}
      (rel : AlphaSuperposeBranchesTermForest alpha barrier branches forest) :
      AlphaGoalTermForest alpha barrier (.builtAmb branches) forest
  | spread {referenceValue referenceOutput : Term}
      {executableValue executableOutput : Atom}
      (value : AlphaTermAgrees alpha referenceValue executableValue)
      (output : AlphaTermAgrees alpha referenceOutput executableOutput) :
      AlphaGoalTermForest alpha barrier (.spread value output)
        ((AlphaTermForest.singleton value).append
          (AlphaTermForest.singleton output))
  | conditional {referenceCondition referenceOutput : Term}
      {referenceThen referenceElse} {executableCondition executableOutput}
      {executableThen executableElse}
      (condition : AlphaTermAgrees alpha referenceCondition executableCondition)
      (output : AlphaTermAgrees alpha referenceOutput executableOutput)
      (thenBranch : AlphaIfBranchAgrees alpha barrier referenceOutput
        executableOutput referenceThen executableThen)
      (elseBranch : AlphaIfBranchAgrees alpha barrier referenceOutput
        executableOutput referenceElse executableElse)
      {thenForest elseForest : AlphaTermForest alpha}
      (thenRel : AlphaIfBranchTermForest alpha barrier thenBranch thenForest)
      (elseRel : AlphaIfBranchTermForest alpha barrier elseBranch elseForest) :
      AlphaGoalTermForest alpha barrier
        (.conditional condition output thenBranch elseBranch)
        ((AlphaTermForest.singleton condition).append
          ((AlphaTermForest.singleton output).append
            (thenForest.append elseForest)))

inductive AlphaIfBranchTermForest
    (alpha : List (LogicVar × String)) (barrier : Nat) :
    {referenceOutput : Term} → {executableOutput : Atom} →
      {reference : PeTTaSpec.PrologCore.Goal} →
      {executable : Atom × List PLeaTTa.Goal} →
      AlphaIfBranchAgrees alpha barrier referenceOutput executableOutput
        reference executable → AlphaTermForest alpha → Prop where
  | empty {referenceOutput referenceValue executableOutput executableValue}
      (value : AlphaTermAgrees alpha referenceValue executableValue)
      (output : AlphaTermAgrees alpha referenceOutput executableOutput) :
      AlphaIfBranchTermForest alpha barrier (.empty value output)
        ((AlphaTermForest.singleton value).append
          (AlphaTermForest.singleton output))
  | aliased {referenceOutput executableOutput referenceGoals executableGoals}
      (output : AlphaTermAgrees alpha referenceOutput executableOutput)
      (goals : AlphaGoalsAgree alpha barrier referenceGoals executableGoals)
      {forest : AlphaTermForest alpha}
      (rel : AlphaGoalsTermForest alpha barrier goals forest) :
      AlphaIfBranchTermForest alpha barrier (.aliased output goals)
        ((AlphaTermForest.singleton output).append forest)
  | nonvariable {referenceOutput referenceValue executableOutput
        executableValue referenceGoals executableGoals}
      (value : AlphaTermAgrees alpha referenceValue executableValue)
      (output : AlphaTermAgrees alpha referenceOutput executableOutput)
      (goals : AlphaGoalsAgree alpha barrier referenceGoals executableGoals)
      {forest : AlphaTermForest alpha}
      (rel : AlphaGoalsTermForest alpha barrier goals forest) :
      AlphaIfBranchTermForest alpha barrier (.nonvariable value output goals)
        ((AlphaTermForest.singleton value).append
          ((AlphaTermForest.singleton output).append forest))
  | failed {referenceOutput executableOutput}
      (output : AlphaTermAgrees alpha referenceOutput executableOutput) :
      AlphaIfBranchTermForest alpha barrier (.failed output)
        (AlphaTermForest.singleton output)

inductive AlphaSuperposeBranchTermForest
    (alpha : List (LogicVar × String)) (barrier : Nat) :
    {referenceOutput : Term} → {executableOutput : Atom} →
      {reference : PeTTaSpec.PrologCore.Goal} →
      {executable : Atom × List PLeaTTa.Goal} →
      AlphaSuperposeBranchAgrees alpha barrier referenceOutput
        executableOutput reference executable →
      AlphaTermForest alpha → Prop where
  | empty {referenceOutput referenceValue executableOutput executableValue}
      (value : AlphaTermAgrees alpha referenceValue executableValue)
      (output : AlphaTermAgrees alpha referenceOutput executableOutput) :
      AlphaSuperposeBranchTermForest alpha barrier (.empty value output)
        ((AlphaTermForest.singleton value).append
          (AlphaTermForest.singleton output))
  | aliased {referenceOutput executableOutput referenceGoals executableGoals}
      (output : AlphaTermAgrees alpha referenceOutput executableOutput)
      (goals : AlphaGoalsAgree alpha barrier referenceGoals executableGoals)
      (nonempty : executableGoals ≠ []) {forest : AlphaTermForest alpha}
      (rel : AlphaGoalsTermForest alpha barrier goals forest) :
      AlphaSuperposeBranchTermForest alpha barrier
        (.aliased output goals nonempty)
        ((AlphaTermForest.singleton output).append forest)
  | nonvariable {referenceOutput referenceValue executableOutput
        executableValue referenceGoals executableGoals}
      (value : AlphaTermAgrees alpha referenceValue executableValue)
      (output : AlphaTermAgrees alpha referenceOutput executableOutput)
      (goals : AlphaGoalsAgree alpha barrier referenceGoals executableGoals)
      {forest : AlphaTermForest alpha}
      (rel : AlphaGoalsTermForest alpha barrier goals forest) :
      AlphaSuperposeBranchTermForest alpha barrier
        (.nonvariable value output goals)
        ((AlphaTermForest.singleton value).append
          ((AlphaTermForest.singleton output).append forest))

inductive AlphaSuperposeBranchesTermForest
    (alpha : List (LogicVar × String)) (barrier : Nat) :
    {referenceOutput : Term} → {executableOutput : Atom} →
      {references : List PeTTaSpec.PrologCore.Goal} →
      {executables : List (Atom × List PLeaTTa.Goal)} →
      AlphaSuperposeBranchesAgree alpha barrier referenceOutput
        executableOutput references executables →
      AlphaTermForest alpha → Prop where
  | nil {referenceOutput executableOutput}
      (output : AlphaTermAgrees alpha referenceOutput executableOutput) :
      AlphaSuperposeBranchesTermForest alpha barrier (.nil output)
        (AlphaTermForest.singleton output)
  | cons {referenceOutput executableOutput referenceBranch executableBranch
        referenceBranches executableBranches}
      (head : AlphaSuperposeBranchAgrees alpha barrier referenceOutput
        executableOutput referenceBranch executableBranch)
      (tail : AlphaSuperposeBranchesAgree alpha barrier referenceOutput
        executableOutput referenceBranches executableBranches)
      {headForest tailForest : AlphaTermForest alpha}
      (headRel : AlphaSuperposeBranchTermForest alpha barrier head headForest)
      (tailRel : AlphaSuperposeBranchesTermForest alpha barrier tail tailForest) :
      AlphaSuperposeBranchesTermForest alpha barrier (.cons head tail)
        (headForest.append tailForest)

inductive AlphaGoalsTermForest
    (alpha : List (LogicVar × String)) (barrier : Nat) :
    {references : List PeTTaSpec.PrologCore.Goal} →
      {executables : List PLeaTTa.Goal} →
      AlphaGoalsAgree alpha barrier references executables →
      AlphaTermForest alpha → Prop where
  | nil : AlphaGoalsTermForest alpha barrier .nil (.empty alpha)
  | cons {reference executable references executables}
      (head : AlphaGoalAgrees alpha barrier reference executable)
      (tail : AlphaGoalsAgree alpha barrier references executables)
      {headForest tailForest : AlphaTermForest alpha}
      (headRel : AlphaGoalTermForest alpha barrier head headForest)
      (tailRel : AlphaGoalsTermForest alpha barrier tail tailForest) :
      AlphaGoalsTermForest alpha barrier (.cons head tail)
        (headForest.append tailForest)
  | conjunction {referenceBlock referenceTail executableBlock executableTail}
      (block : AlphaGoalsAgree alpha barrier referenceBlock executableBlock)
      (tail : AlphaGoalsAgree alpha barrier referenceTail executableTail)
      {blockForest tailForest : AlphaTermForest alpha}
      (blockRel : AlphaGoalsTermForest alpha barrier block blockForest)
      (tailRel : AlphaGoalsTermForest alpha barrier tail tailForest) :
      AlphaGoalsTermForest alpha barrier (.conjunction block tail)
        (blockForest.append tailForest)

end

/-- Every literal-branch agreement has its structurally fixed forest. -/
theorem alphaLiteralExistsTermForest
    {alpha : List (LogicVar × String)} {referenceOutput : Term}
    {executableOutput : Atom} {references} {executables}
    (agreement : AlphaLiteralAmbBranchesAgree alpha referenceOutput
      executableOutput references executables) :
    ∃ forest, AlphaLiteralTermForest alpha referenceOutput executableOutput
      agreement forest := by
  induction agreement with
  | nil output =>
      exact ⟨_, AlphaLiteralTermForest.nil output⟩
  | cons value output tail inductionHypothesis =>
      obtain ⟨tailForest, tailRel⟩ := inductionHypothesis
      exact ⟨_, AlphaLiteralTermForest.cons value output tail tailRel⟩

/-- Literal-branch extraction cannot omit a source variable.  Its empty case
may retain the executable-hidden output, hence coverage is intentionally a
subset statement rather than equality. -/
theorem alphaLiteralTermForest_covers
    {alpha : List (LogicVar × String)} {referenceOutput : Term}
    {executableOutput : Atom} {references} {executables}
    {agreement : AlphaLiteralAmbBranchesAgree alpha referenceOutput
      executableOutput references executables}
    {forest : AlphaTermForest alpha}
    (rel : AlphaLiteralTermForest alpha referenceOutput executableOutput
      agreement forest) :
    List.Subset (goalsVariables references) forest.referenceVariables := by
  induction rel with
  | nil output =>
      intro identity membership
      simp [goalsVariables] at membership
  | cons value output tail tailRel inductionHypothesis =>
      simpa [goalVariables, goalsVariables, AlphaTermForest.referenceVariables,
        AlphaTermForest.append, AlphaTermForest.singleton] using
        List.Subset.append_same_left _
          (List.Subset.append_same_left _ inductionHypothesis)

/-- Literal-branch extraction covers the full executable branch payload plus
the enclosing hidden result. -/
theorem alphaLiteralTermForestCoversExecutable
    {alpha : List (LogicVar × String)} {referenceOutput : Term}
    {executableOutput : Atom} {references} {executables}
    {agreement : AlphaLiteralAmbBranchesAgree alpha referenceOutput
      executableOutput references executables}
    {forest : AlphaTermForest alpha}
    (rel : AlphaLiteralTermForest alpha referenceOutput executableOutput
      agreement forest) :
    List.Subset
      (PLeaTTa.specializationBranchVars executables ++ executableOutput.vars)
      forest.executableVariables := by
  induction rel with
  | nil output =>
      intro name membership
      simpa [PLeaTTa.specializationBranchVars] using membership
  | cons value output tail tailRel inductionHypothesis =>
      intro name membership
      simp [PLeaTTa.specializationBranchVars,
        PLeaTTa.specializationGoalsVars] at membership ⊢
      aesop

/-- The literal relation determines its forest uniquely. -/
theorem alphaLiteralTermForestUnique
    {alpha : List (LogicVar × String)} {referenceOutput : Term}
    {executableOutput : Atom} {references} {executables}
    {agreement : AlphaLiteralAmbBranchesAgree alpha referenceOutput
      executableOutput references executables}
    {leftForest rightForest : AlphaTermForest alpha}
    (left : AlphaLiteralTermForest alpha referenceOutput executableOutput
      agreement leftForest)
    (right : AlphaLiteralTermForest alpha referenceOutput executableOutput
      agreement rightForest) :
    leftForest = rightForest := by
  induction left generalizing rightForest with
  | nil output =>
      cases right
      rfl
  | cons value output tail tailRel inductionHypothesis =>
      cases right with
      | cons _ _ _ rightTailRel =>
          rw [inductionHypothesis rightTailRel]

mutual

/-- Every goal agreement has one structurally certified complete forest. -/
theorem alphaGoalExistsTermForest
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {reference : PeTTaSpec.PrologCore.Goal} {executable : PLeaTTa.Goal}
    (agreement : AlphaGoalAgrees alpha barrier reference executable) :
    ∃ forest, AlphaGoalTermForest alpha barrier agreement forest := by
  cases agreement with
  | unify left right =>
      exact ⟨_, AlphaGoalTermForest.unify left right⟩
  | compileAlias left right =>
      exact ⟨_, AlphaGoalTermForest.compileAlias left right⟩
  | cut =>
      exact ⟨_, AlphaGoalTermForest.cut⟩
  | @builtin predicate referenceArguments referenceResult executableArguments
      executableResult arguments result =>
      exact ⟨_, AlphaGoalTermForest.builtin (predicate := predicate)
        arguments result⟩
  | @definedCall predicate referenceArguments referenceResult
      executableArguments executableResult arguments result =>
      exact ⟨_, AlphaGoalTermForest.definedCall (predicate := predicate)
        arguments result⟩
  | assertaPredicate payload result =>
      exact ⟨_, AlphaGoalTermForest.assertaPredicate payload result⟩
  | assertzPredicate payload result =>
      exact ⟨_, AlphaGoalTermForest.assertzPredicate payload result⟩
  | softCutTruth condition otherwise =>
      obtain ⟨conditionForest, conditionRel⟩ :=
        alphaGoalsExistsTermForest condition
      obtain ⟨otherwiseForest, otherwiseRel⟩ :=
        alphaGoalsExistsTermForest otherwise
      exact ⟨_, AlphaGoalTermForest.softCutTruth condition otherwise
        conditionRel otherwiseRel⟩
  | typeCheckSoftCut value expected direct metaTerm =>
      exact ⟨_, AlphaGoalTermForest.typeCheckSoftCut value expected direct
        metaTerm⟩
  | shortCircuitAnd condition body output bodyGoals =>
      obtain ⟨bodyForest, bodyRel⟩ :=
        alphaGoalsExistsTermForest bodyGoals
      exact ⟨_, AlphaGoalTermForest.shortCircuitAnd condition body output
        bodyGoals bodyRel⟩
  | shortCircuitOr condition body output bodyGoals =>
      obtain ⟨bodyForest, bodyRel⟩ :=
        alphaGoalsExistsTermForest bodyGoals
      exact ⟨_, AlphaGoalTermForest.shortCircuitOr condition body output
        bodyGoals bodyRel⟩
  | findall template body output =>
      obtain ⟨bodyForest, bodyRel⟩ := alphaGoalsExistsTermForest body
      exact ⟨_, AlphaGoalTermForest.findall template body output bodyRel⟩
  | literalAmb branches =>
      obtain ⟨forest, rel⟩ := alphaLiteralExistsTermForest branches
      exact ⟨forest, AlphaGoalTermForest.literalAmb branches rel⟩
  | builtAmb branches =>
      obtain ⟨forest, rel⟩ :=
        alphaSuperposeBranchesExistsTermForest branches
      exact ⟨forest, AlphaGoalTermForest.builtAmb branches rel⟩
  | spread value output =>
      exact ⟨_, AlphaGoalTermForest.spread value output⟩
  | conditional condition output thenBranch elseBranch =>
      obtain ⟨thenForest, thenRel⟩ :=
        alphaIfBranchExistsTermForest thenBranch
      obtain ⟨elseForest, elseRel⟩ :=
        alphaIfBranchExistsTermForest elseBranch
      exact ⟨_, AlphaGoalTermForest.conditional condition output thenBranch
        elseBranch thenRel elseRel⟩

/-- Every normalized branch agreement has its structurally fixed forest. -/
theorem alphaIfBranchExistsTermForest
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {referenceOutput : Term} {executableOutput : Atom}
    {reference : PeTTaSpec.PrologCore.Goal}
    {executable : Atom × List PLeaTTa.Goal}
    (agreement : AlphaIfBranchAgrees alpha barrier referenceOutput
      executableOutput reference executable) :
    ∃ forest, AlphaIfBranchTermForest alpha barrier agreement forest := by
  cases agreement with
  | empty value output =>
      exact ⟨_, AlphaIfBranchTermForest.empty value output⟩
  | aliased output goals =>
      obtain ⟨forest, rel⟩ := alphaGoalsExistsTermForest goals
      exact ⟨_, AlphaIfBranchTermForest.aliased output goals rel⟩
  | nonvariable value output goals =>
      obtain ⟨forest, rel⟩ := alphaGoalsExistsTermForest goals
      exact ⟨_, AlphaIfBranchTermForest.nonvariable value output goals rel⟩
  | failed output =>
      exact ⟨_, AlphaIfBranchTermForest.failed output⟩

/-- Every superpose branch agreement has its structurally fixed forest. -/
theorem alphaSuperposeBranchExistsTermForest
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {referenceOutput : Term} {executableOutput : Atom}
    {reference : PeTTaSpec.PrologCore.Goal}
    {executable : Atom × List PLeaTTa.Goal}
    (agreement : AlphaSuperposeBranchAgrees alpha barrier referenceOutput
      executableOutput reference executable) :
    ∃ forest, AlphaSuperposeBranchTermForest alpha barrier agreement forest := by
  cases agreement with
  | empty value output =>
      exact ⟨_, AlphaSuperposeBranchTermForest.empty value output⟩
  | aliased output goals nonempty =>
      obtain ⟨forest, rel⟩ := alphaGoalsExistsTermForest goals
      exact ⟨_, AlphaSuperposeBranchTermForest.aliased output goals nonempty rel⟩
  | nonvariable value output goals =>
      obtain ⟨forest, rel⟩ := alphaGoalsExistsTermForest goals
      exact ⟨_, AlphaSuperposeBranchTermForest.nonvariable value output goals rel⟩

/-- Every ordered superpose branch sequence has its certified forest. -/
theorem alphaSuperposeBranchesExistsTermForest
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {referenceOutput : Term} {executableOutput : Atom}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List (Atom × List PLeaTTa.Goal)}
    (agreement : AlphaSuperposeBranchesAgree alpha barrier referenceOutput
      executableOutput references executables) :
    ∃ forest, AlphaSuperposeBranchesTermForest alpha barrier agreement forest := by
  cases agreement with
  | nil output =>
      exact ⟨_, AlphaSuperposeBranchesTermForest.nil output⟩
  | cons head tail =>
      obtain ⟨headForest, headRel⟩ :=
        alphaSuperposeBranchExistsTermForest head
      obtain ⟨tailForest, tailRel⟩ :=
        alphaSuperposeBranchesExistsTermForest tail
      exact ⟨_, AlphaSuperposeBranchesTermForest.cons head tail headRel tailRel⟩

/-- Every ordered goal sequence has its structurally certified forest. -/
theorem alphaGoalsExistsTermForest
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement : AlphaGoalsAgree alpha barrier references executables) :
    ∃ forest, AlphaGoalsTermForest alpha barrier agreement forest := by
  cases agreement with
  | nil =>
      exact ⟨_, AlphaGoalsTermForest.nil⟩
  | cons head tail =>
      obtain ⟨headForest, headRel⟩ := alphaGoalExistsTermForest head
      obtain ⟨tailForest, tailRel⟩ := alphaGoalsExistsTermForest tail
      exact ⟨_, AlphaGoalsTermForest.cons head tail headRel tailRel⟩
  | conjunction block tail =>
      obtain ⟨blockForest, blockRel⟩ := alphaGoalsExistsTermForest block
      obtain ⟨tailForest, tailRel⟩ := alphaGoalsExistsTermForest tail
      exact ⟨_, AlphaGoalsTermForest.conjunction block tail blockRel tailRel⟩

end

mutual

/-- The structurally certified forest covers every source-variable occurrence
of its goal.  Extra hidden executable carry fields are permitted. -/
theorem alphaGoalTermForestCovers
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {reference : PeTTaSpec.PrologCore.Goal} {executable : PLeaTTa.Goal}
    {agreement : AlphaGoalAgrees alpha barrier reference executable}
    {forest : AlphaTermForest alpha}
    (rel : AlphaGoalTermForest alpha barrier agreement forest) :
    List.Subset (goalVariables reference) forest.referenceVariables := by
  cases rel with
  | unify left right =>
      intro identity membership
      simpa [goalVariables] using membership
  | compileAlias left right =>
      intro identity membership
      simpa [goalVariables] using membership
  | cut =>
      intro identity membership
      simp [goalVariables] at membership
  | builtin arguments result =>
      intro identity membership
      simpa [goalVariables] using membership
  | definedCall arguments result =>
      intro identity membership
      simpa [goalVariables] using membership
  | assertaPredicate payload result =>
      intro identity membership
      simpa [goalVariables, termsVariables] using membership
  | assertzPredicate payload result =>
      intro identity membership
      simpa [goalVariables, termsVariables] using membership
  | softCutTruth condition otherwise conditionRel otherwiseRel =>
      simpa [goalVariables, goalsVariables] using
        List.Subset.append_both
          (alphaGoalsTermForestCovers conditionRel)
          (alphaGoalsTermForestCovers otherwiseRel)
  | typeCheckSoftCut value expected direct metaTerm =>
      intro identity membership
      simp [goalVariables, goalsVariables] at membership ⊢
      aesop
  | shortCircuitAnd condition body output bodyGoals bodyRel =>
      have bodyCovered := alphaGoalsTermForestCovers bodyRel
      intro identity membership
      simp [goalVariables, goalsVariables, termVariables] at membership ⊢
      aesop
  | shortCircuitOr condition body output bodyGoals bodyRel =>
      have bodyCovered := alphaGoalsTermForestCovers bodyRel
      intro identity membership
      simp [goalVariables, goalsVariables, termVariables] at membership ⊢
      aesop
  | findall template body output bodyRel =>
      simpa [goalVariables, goalsVariables] using
        List.Subset.append_both
          (List.Subset.append_both (List.Subset.refl _)
            (alphaGoalsTermForestCovers bodyRel))
          (List.Subset.refl _)
  | literalAmb branches rel =>
      simpa [goalVariables] using alphaLiteralTermForest_covers rel
  | builtAmb branches rel =>
      simpa [goalVariables] using alphaSuperposeBranchesTermForestCovers rel
  | spread value output =>
      intro identity membership
      simpa [goalVariables, termsVariables] using membership
  | conditional condition output thenBranch elseBranch thenRel elseRel =>
      have thenCovered := alphaIfBranchTermForestCovers thenRel
      have elseCovered := alphaIfBranchTermForestCovers elseRel
      intro identity membership
      simp [goalVariables, termVariables] at membership ⊢
      aesop

/-- Branch forests cover the complete source branch, even when the executable
stores its output outside the visible body list. -/
theorem alphaIfBranchTermForestCovers
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {referenceOutput : Term} {executableOutput : Atom}
    {reference : PeTTaSpec.PrologCore.Goal}
    {executable : Atom × List PLeaTTa.Goal}
    {agreement : AlphaIfBranchAgrees alpha barrier referenceOutput
      executableOutput reference executable}
    {forest : AlphaTermForest alpha}
    (rel : AlphaIfBranchTermForest alpha barrier agreement forest) :
    List.Subset (goalVariables reference) forest.referenceVariables := by
  cases rel with
  | empty value output =>
      intro identity membership
      simpa [goalVariables] using membership
  | aliased output goals rel =>
      have covered := alphaGoalsTermForestCovers rel
      intro identity membership
      simp [goalVariables] at membership ⊢
      exact Or.inr (covered membership)
  | nonvariable value output goals rel =>
      have covered := alphaGoalsTermForestCovers rel
      intro identity membership
      simp [goalVariables, goalsVariables] at membership ⊢
      aesop
  | failed output =>
      intro identity membership
      simp [goalVariables] at membership

/-- One superpose branch retains every variable of its independent goal. -/
theorem alphaSuperposeBranchTermForestCovers
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {referenceOutput : Term} {executableOutput : Atom}
    {reference : PeTTaSpec.PrologCore.Goal}
    {executable : Atom × List PLeaTTa.Goal}
    {agreement : AlphaSuperposeBranchAgrees alpha barrier referenceOutput
      executableOutput reference executable}
    {forest : AlphaTermForest alpha}
    (rel : AlphaSuperposeBranchTermForest alpha barrier agreement forest) :
    List.Subset (goalVariables reference) forest.referenceVariables := by
  cases rel with
  | empty value output =>
      intro identity membership
      simpa [goalVariables] using membership
  | aliased output goals nonempty rel =>
      have covered := alphaGoalsTermForestCovers rel
      intro identity membership
      simp [goalVariables] at membership ⊢
      exact Or.inr (covered membership)
  | nonvariable value output goals rel =>
      have covered := alphaGoalsTermForestCovers rel
      intro identity membership
      simp [goalVariables, goalsVariables] at membership ⊢
      aesop

/-- Ordered superpose-branch forests cover every source branch. -/
theorem alphaSuperposeBranchesTermForestCovers
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {referenceOutput : Term} {executableOutput : Atom}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List (Atom × List PLeaTTa.Goal)}
    {agreement : AlphaSuperposeBranchesAgree alpha barrier referenceOutput
      executableOutput references executables}
    {forest : AlphaTermForest alpha}
    (rel : AlphaSuperposeBranchesTermForest alpha barrier agreement forest) :
    List.Subset (goalsVariables references) forest.referenceVariables := by
  cases rel with
  | nil output =>
      intro identity membership
      simp [goalsVariables] at membership
  | cons head tail headRel tailRel =>
      simpa [goalsVariables] using
        List.Subset.append_both
          (alphaSuperposeBranchTermForestCovers headRel)
          (alphaSuperposeBranchesTermForestCovers tailRel)

/-- Ordered goal forests cover every source goal occurrence, including nested
conjunction blocks. -/
theorem alphaGoalsTermForestCovers
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    {agreement : AlphaGoalsAgree alpha barrier references executables}
    {forest : AlphaTermForest alpha}
    (rel : AlphaGoalsTermForest alpha barrier agreement forest) :
    List.Subset (goalsVariables references) forest.referenceVariables := by
  cases rel with
  | nil =>
      exact List.Subset.refl []
  | cons head tail headRel tailRel =>
      simpa [goalsVariables] using
        List.Subset.append_both (alphaGoalTermForestCovers headRel)
          (alphaGoalsTermForestCovers tailRel)
  | conjunction block tail blockRel tailRel =>
      simpa [goalVariables, goalsVariables] using
        List.Subset.append_both (alphaGoalsTermForestCovers blockRel)
          (alphaGoalsTermForestCovers tailRel)

end


mutual

/-- Every variable in the full compiled goal is represented by the forest's
paired leaves.  Derived carry atoms may be covered through their certified
variable-support theorem rather than pretending they have a source term. -/
theorem alphaGoalTermForestCoversExecutable
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {reference : PeTTaSpec.PrologCore.Goal} {executable : PLeaTTa.Goal}
    {agreement : AlphaGoalAgrees alpha barrier reference executable}
    {forest : AlphaTermForest alpha}
    (rel : AlphaGoalTermForest alpha barrier agreement forest) :
    List.Subset (PLeaTTa.specializationGoalVars executable)
      forest.executableVariables := by
  cases rel with
  | unify left right =>
      intro name membership
      simpa [PLeaTTa.specializationGoalVars] using membership
  | compileAlias left right =>
      intro name membership
      simpa [PLeaTTa.specializationGoalVars] using membership
  | cut =>
      intro name membership
      simp [PLeaTTa.specializationGoalVars] at membership
  | builtin arguments result =>
      intro name membership
      simpa [PLeaTTa.specializationGoalVars] using membership
  | definedCall arguments result =>
      intro name membership
      simpa [PLeaTTa.specializationGoalVars] using membership
  | assertaPredicate payload result =>
      intro name membership
      simpa [PLeaTTa.specializationGoalVars] using membership
  | assertzPredicate payload result =>
      intro name membership
      simpa [PLeaTTa.specializationGoalVars] using membership
  | softCutTruth condition otherwise conditionRel otherwiseRel =>
      simpa [PLeaTTa.specializationGoalVars,
        PLeaTTa.specializationGoalsVars, Atom.vars] using
        List.Subset.append_both
          (alphaGoalsTermForestCoversExecutable conditionRel)
          (alphaGoalsTermForestCoversExecutable otherwiseRel)
  | @typeCheckSoftCut referenceValue referenceExpected referenceDirect
      referenceMeta executableValue executableExpected executableDirect
      executableMeta executableTemplate value expected direct metaTerm =>
      have templateCovered :
          List.Subset executableTemplate.vars
            (chainify executableExpected).vars := by
        intro name membership
        rw [expected.template_eq] at membership
        rw [CompilerSubstitutionAdequacy.chainify_vars]
        exact
          CompilerSubstitutionAdequacy.typeCheckBindingTemplate_vars_subset
            executableExpected membership
      intro name membership
      simp [PLeaTTa.specializationGoalVars,
        PLeaTTa.specializationGoalsVars] at membership ⊢
      aesop
  | shortCircuitAnd condition body output bodyGoals bodyRel =>
      have bodyCovered := alphaGoalsTermForestCoversExecutable bodyRel
      intro name membership
      simp [PLeaTTa.specializationGoalVars,
        PLeaTTa.specializationGoalsVars, Atom.vars] at membership ⊢
      aesop
  | shortCircuitOr condition body output bodyGoals bodyRel =>
      have bodyCovered := alphaGoalsTermForestCoversExecutable bodyRel
      intro name membership
      simp [PLeaTTa.specializationGoalVars,
        PLeaTTa.specializationGoalsVars, Atom.vars] at membership ⊢
      aesop
  | findall template body output bodyRel =>
      simpa [PLeaTTa.specializationGoalVars] using
        List.Subset.append_both
          (List.Subset.append_both (List.Subset.refl _)
            (alphaGoalsTermForestCoversExecutable bodyRel))
          (List.Subset.refl _)
  | literalAmb branches rel =>
      simpa [PLeaTTa.specializationGoalVars] using
        alphaLiteralTermForestCoversExecutable rel
  | builtAmb branches rel =>
      simpa [PLeaTTa.specializationGoalVars] using
        alphaSuperposeBranchesTermForestCoversExecutable rel
  | spread value output =>
      intro name membership
      simpa [PLeaTTa.specializationGoalVars] using membership
  | conditional condition output thenBranch elseBranch thenRel elseRel =>
      have thenCovered := alphaIfBranchTermForestCoversExecutable thenRel
      have elseCovered := alphaIfBranchTermForestCoversExecutable elseRel
      intro name membership
      simp [PLeaTTa.specializationGoalVars] at membership ⊢
      aesop

/-- Every executable variable in an `if` branch is covered, including branch
templates stored outside their nested goal lists. -/
theorem alphaIfBranchTermForestCoversExecutable
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {referenceOutput : Term} {executableOutput : Atom}
    {reference : PeTTaSpec.PrologCore.Goal}
    {executable : Atom × List PLeaTTa.Goal}
    {agreement : AlphaIfBranchAgrees alpha barrier referenceOutput
      executableOutput reference executable}
    {forest : AlphaTermForest alpha}
    (rel : AlphaIfBranchTermForest alpha barrier agreement forest) :
    List.Subset
      (executable.1.vars ++ PLeaTTa.specializationGoalsVars executable.2)
      forest.executableVariables := by
  cases rel with
  | empty value output =>
      intro name membership
      simp [PLeaTTa.specializationGoalsVars] at membership ⊢
      exact Or.inl membership
  | aliased output goals rel =>
      simpa using
        List.Subset.append_both (List.Subset.refl _)
          (alphaGoalsTermForestCoversExecutable rel)
  | nonvariable value output goals rel =>
      have covered := alphaGoalsTermForestCoversExecutable rel
      intro name membership
      simp at membership ⊢
      aesop
  | failed output =>
      intro name membership
      simpa [PLeaTTa.specializationGoalsVars,
        PLeaTTa.specializationGoalVars, Atom.vars] using membership

/-- Every executable variable in one superpose branch is covered. -/
theorem alphaSuperposeBranchTermForestCoversExecutable
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {referenceOutput : Term} {executableOutput : Atom}
    {reference : PeTTaSpec.PrologCore.Goal}
    {executable : Atom × List PLeaTTa.Goal}
    {agreement : AlphaSuperposeBranchAgrees alpha barrier referenceOutput
      executableOutput reference executable}
    {forest : AlphaTermForest alpha}
    (rel : AlphaSuperposeBranchTermForest alpha barrier agreement forest) :
    List.Subset
      (executable.1.vars ++ PLeaTTa.specializationGoalsVars executable.2)
      forest.executableVariables := by
  cases rel with
  | empty value output =>
      intro name membership
      simp [PLeaTTa.specializationGoalsVars] at membership ⊢
      exact Or.inl membership
  | aliased output goals nonempty rel =>
      simpa using
        List.Subset.append_both (List.Subset.refl _)
          (alphaGoalsTermForestCoversExecutable rel)
  | nonvariable value output goals rel =>
      have covered := alphaGoalsTermForestCoversExecutable rel
      intro name membership
      simp [PLeaTTa.specializationGoalsVars,
        PLeaTTa.specializationGoalVars] at membership ⊢
      aesop

/-- Ordered superpose forests cover branch templates, nested goals, and the
single enclosing result. -/
theorem alphaSuperposeBranchesTermForestCoversExecutable
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {referenceOutput : Term} {executableOutput : Atom}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List (Atom × List PLeaTTa.Goal)}
    {agreement : AlphaSuperposeBranchesAgree alpha barrier referenceOutput
      executableOutput references executables}
    {forest : AlphaTermForest alpha}
    (rel : AlphaSuperposeBranchesTermForest alpha barrier agreement forest) :
    List.Subset
      (PLeaTTa.specializationBranchVars executables ++ executableOutput.vars)
      forest.executableVariables := by
  cases rel with
  | nil output =>
      intro name membership
      simpa [PLeaTTa.specializationBranchVars] using membership
  | cons head tail headRel tailRel =>
      have headCovered := alphaSuperposeBranchTermForestCoversExecutable headRel
      have tailCovered :=
        alphaSuperposeBranchesTermForestCoversExecutable tailRel
      intro name membership
      simp [PLeaTTa.specializationBranchVars] at membership ⊢
      aesop

/-- Ordered goal forests cover the complete executable variable traversal. -/
theorem alphaGoalsTermForestCoversExecutable
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    {agreement : AlphaGoalsAgree alpha barrier references executables}
    {forest : AlphaTermForest alpha}
    (rel : AlphaGoalsTermForest alpha barrier agreement forest) :
    List.Subset (PLeaTTa.specializationGoalsVars executables)
      forest.executableVariables := by
  cases rel with
  | nil =>
      exact List.Subset.refl []
  | cons head tail headRel tailRel =>
      simpa [PLeaTTa.specializationGoalsVars] using
        List.Subset.append_both (alphaGoalTermForestCoversExecutable headRel)
          (alphaGoalsTermForestCoversExecutable tailRel)
  | conjunction block tail blockRel tailRel =>
      simpa [PLeaTTa.specializationGoalsVars] using
        List.Subset.append_both
          (alphaGoalsTermForestCoversExecutable blockRel)
          (alphaGoalsTermForestCoversExecutable tailRel)

end


/-- Administrative-normalized term-forest relation.  Erased truth has an
empty local forest; conjunction flattening remains ordered. -/
inductive NormalizedAlphaGoalsTermForest
    (alpha : List (LogicVar × String)) (barrier : Nat) :
    {references : List PeTTaSpec.PrologCore.Goal} →
      {executables : List PLeaTTa.Goal} →
      NormalizedAlphaGoalsAgree alpha barrier references executables →
      AlphaTermForest alpha → Prop where
  | nil : NormalizedAlphaGoalsTermForest alpha barrier .nil (.empty alpha)
  | truth {references executables}
      (tail : NormalizedAlphaGoalsAgree alpha barrier references executables)
      {forest : AlphaTermForest alpha}
      (rel : NormalizedAlphaGoalsTermForest alpha barrier tail forest) :
      NormalizedAlphaGoalsTermForest alpha barrier (.truth tail) forest
  | cons {reference executable references executables}
      (head : AlphaGoalAgrees alpha barrier reference executable)
      (tail : NormalizedAlphaGoalsAgree alpha barrier references executables)
      {headForest tailForest : AlphaTermForest alpha}
      (headRel : AlphaGoalTermForest alpha barrier head headForest)
      (tailRel : NormalizedAlphaGoalsTermForest alpha barrier tail tailForest) :
      NormalizedAlphaGoalsTermForest alpha barrier (.cons head tail)
        (headForest.append tailForest)
  | conjunction {referenceBlock referenceTail executableBlock executableTail}
      (block : NormalizedAlphaGoalsAgree alpha barrier referenceBlock
        executableBlock)
      (tail : NormalizedAlphaGoalsAgree alpha barrier referenceTail
        executableTail)
      {blockForest tailForest : AlphaTermForest alpha}
      (blockRel : NormalizedAlphaGoalsTermForest alpha barrier block blockForest)
      (tailRel : NormalizedAlphaGoalsTermForest alpha barrier tail tailForest) :
      NormalizedAlphaGoalsTermForest alpha barrier (.conjunction block tail)
        (blockForest.append tailForest)

/-- Every normalized alpha-agreement admits its exact structural forest.
This is propositional totality, not proof-to-data elimination: the relation's
constructors determine the forest while remaining within `Prop`. -/
theorem NormalizedAlphaGoalsAgree.exists_termForest
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      NormalizedAlphaGoalsAgree alpha barrier references executables) :
    ∃ forest, NormalizedAlphaGoalsTermForest alpha barrier agreement forest := by
  induction agreement with
  | nil =>
      exact ⟨_, NormalizedAlphaGoalsTermForest.nil⟩
  | truth tail inductionHypothesis =>
      obtain ⟨forest, rel⟩ := inductionHypothesis
      exact ⟨forest, NormalizedAlphaGoalsTermForest.truth tail rel⟩
  | cons head tail inductionHypothesis =>
      obtain ⟨headForest, headRel⟩ := alphaGoalExistsTermForest head
      obtain ⟨tailForest, tailRel⟩ := inductionHypothesis
      exact ⟨_, NormalizedAlphaGoalsTermForest.cons head tail headRel tailRel⟩
  | conjunction block tail blockIH tailIH =>
      obtain ⟨blockForest, blockRel⟩ := blockIH
      obtain ⟨tailForest, tailRel⟩ := tailIH
      exact ⟨_, NormalizedAlphaGoalsTermForest.conjunction block tail
        blockRel tailRel⟩

/-- Administrative normalization cannot hide a source variable: erased truth
has none, and conjunction flattening composes the two recursive coverage
facts. -/
theorem NormalizedAlphaGoalsTermForest.covers
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    {agreement :
      NormalizedAlphaGoalsAgree alpha barrier references executables}
    {forest : AlphaTermForest alpha}
    (rel : NormalizedAlphaGoalsTermForest alpha barrier agreement forest) :
    List.Subset (goalsVariables references) forest.referenceVariables := by
  induction rel with
  | nil =>
      exact List.Subset.refl []
  | truth tail rel inductionHypothesis =>
      simpa [goalVariables, goalsVariables] using inductionHypothesis
  | cons head tail headRel tailRel inductionHypothesis =>
      simpa [goalsVariables] using
        List.Subset.append_both (alphaGoalTermForestCovers headRel)
          inductionHypothesis
  | conjunction block tail blockRel tailRel blockIH tailIH =>
      simpa [goalVariables, goalsVariables] using
        List.Subset.append_both blockIH tailIH

/-- The normalized wrapper also covers every executable variable, including
variables in compiler-hidden carry templates and branch outputs. -/
theorem NormalizedAlphaGoalsTermForest.coversExecutable
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    {agreement :
      NormalizedAlphaGoalsAgree alpha barrier references executables}
    {forest : AlphaTermForest alpha}
    (rel : NormalizedAlphaGoalsTermForest alpha barrier agreement forest) :
    List.Subset (PLeaTTa.specializationGoalsVars executables)
      forest.executableVariables := by
  induction rel with
  | nil =>
      exact List.Subset.refl []
  | truth tail rel inductionHypothesis =>
      exact inductionHypothesis
  | cons head tail headRel tailRel inductionHypothesis =>
      simpa [PLeaTTa.specializationGoalsVars] using
        List.Subset.append_both
          (alphaGoalTermForestCoversExecutable headRel)
          inductionHypothesis
  | conjunction block tail blockRel tailRel blockIH tailIH =>
      simpa [PLeaTTa.specializationGoalsVars] using
        List.Subset.append_both blockIH tailIH

/-- Totality and completeness packaged together: every normalized agreement
has a structurally certified forest, and no source variable is omitted. -/
theorem NormalizedAlphaGoalsAgree.exists_complete_termForest
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      NormalizedAlphaGoalsAgree alpha barrier references executables) :
    ∃ forest,
      NormalizedAlphaGoalsTermForest alpha barrier agreement forest ∧
        List.Subset (goalsVariables references) forest.referenceVariables ∧
        List.Subset (PLeaTTa.specializationGoalsVars executables)
          forest.executableVariables := by
  obtain ⟨forest, rel⟩ :=
    PLeaTTa.PrologGoalTermForestBridge.NormalizedAlphaGoalsAgree.exists_termForest
      agreement
  exact ⟨forest, rel, rel.covers, rel.coversExecutable⟩

/-- Agreement-indexed support for one structurally certified forest. -/
def NormalizedAlphaGoalsAgree.ForestSupported
    {alpha : List (LogicVar × String)} (support : List (LogicVar × String))
    {barrier : Nat} {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      NormalizedAlphaGoalsAgree alpha barrier references executables) : Prop :=
  ∃ forest : AlphaTermForest alpha,
    NormalizedAlphaGoalsTermForest alpha barrier agreement forest ∧
      AlphaTermsSupported alpha support forest.references

/-- One supported continuation forest materializes under one shared residual
alpha.  The result retains both the structural no-omission certificate and
the concrete shared runtime supports; no leaf may select a private residual
orientation. -/
theorem TaskPayloadAgrees.materializeControlForest
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : PeTTaSpec.PrologCore.Canonical.TreeSubstitution}
    {referenceBase current :
      PeTTaSpec.PrologCore.OpenSubstitution.Substitution}
    {runtime : Metta.Subst}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (payload :
      TaskPayloadAgrees alpha support barrier canonical referenceBase current
        runtime references executables)
    (supported :
      PLeaTTa.PrologGoalTermForestBridge.NormalizedAlphaGoalsAgree.ForestSupported
        support payload.control) :
    ∃ forest referenceSupport executableSupport,
      NormalizedAlphaGoalsTermForest alpha barrier payload.control forest ∧
        List.Subset (goalsVariables references) forest.referenceVariables ∧
        List.Subset (PLeaTTa.specializationGoalsVars executables)
          forest.executableVariables ∧
        PrologFindallBagAlphaBridge.RuntimeTermsAgreesWith
          referenceSupport executableSupport
          (current.applyTerms forest.references)
          (forest.executables.map (PLeaTTa.subst runtime)) := by
  obtain ⟨forest, forestRel, forestSupported⟩ := supported
  obtain ⟨referenceSupport, executableSupport, materialized⟩ :=
    PLeaTTa.PrologResidualForestBridge.TaskDataAgrees.runtimeTermsAgreesWith
      payload.data forest.agreement forestSupported
  exact ⟨forest, referenceSupport, executableSupport, forestRel,
    forestRel.covers, forestRel.coversExecutable, materialized⟩

/-- Goal-level anti-vacuity witness.  The complete forest of one equality
whose operands share a source variable preserves that alias globally; the
same forest cannot be re-read with two distinct runtime names. -/
theorem shared_goal_forest_alias_is_preserved :
    let identity : LogicVar := .source "shared"
    let alpha : List (LogicVar × String) := [(identity, "same")]
    ∃ (agreement :
        NormalizedAlphaGoalsAgree alpha 0
          [.unify (.variable identity) (.variable identity)]
          [.eq (.var "same") (.var "same")])
      (forest : AlphaTermForest alpha),
      NormalizedAlphaGoalsTermForest alpha 0 agreement forest ∧
        forest.references =
          [.variable identity, .variable identity] ∧
        forest.executables = [.var "same", .var "same"] ∧
        PrologFindallBagAlphaBridge.RuntimeTermsAgrees
          forest.references [.var "same", .var "same"] ∧
        ¬ PrologFindallBagAlphaBridge.RuntimeTermsAgrees
          forest.references [.var "left", .var "right"] := by
  let identity : LogicVar := .source "shared"
  let alpha : List (LogicVar × String) := [(identity, "same")]
  have leaf : AlphaTermAgrees alpha (.variable identity) (.var "same") :=
    .variable (by simp [alpha, identity])
  let goalAgreement : AlphaGoalAgrees alpha 0
      (.unify (.variable identity) (.variable identity))
      (.eq (.var "same") (.var "same")) :=
    .unify leaf leaf
  let agreement : NormalizedAlphaGoalsAgree alpha 0
      [.unify (.variable identity) (.variable identity)]
      [.eq (.var "same") (.var "same")] :=
    .cons goalAgreement .nil
  let headForest : AlphaTermForest alpha :=
    (AlphaTermForest.singleton leaf).append
      (AlphaTermForest.singleton leaf)
  let forest : AlphaTermForest alpha :=
    headForest.append (AlphaTermForest.empty alpha)
  have forestRel :
      NormalizedAlphaGoalsTermForest alpha 0 agreement forest := by
    exact .cons goalAgreement .nil (.unify leaf leaf) .nil
  have aliases :=
    PLeaTTa.PrologResidualForestBridge.shared_forest_alias_is_preserved
  refine ⟨agreement, forest, forestRel, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · simpa [forest, headForest, AlphaTermForest.append,
      AlphaTermForest.singleton, AlphaTermForest.empty, identity] using aliases

end PLeaTTa.PrologGoalTermForestBridge
