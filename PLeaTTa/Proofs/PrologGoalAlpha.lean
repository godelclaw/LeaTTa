-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologGoalAlpha
Purpose: Transport compiler goal agreement through the two actual
  clause-standardization operations under an explicit runtime alpha graph.
Trusted boundary: none
Main exports: AlphaGoalAgrees, AlphaGoalsAgree,
  failedIfBranch_alpha_freshen,
  wrong_alpha_hidden_branch_output_is_rejected
-/
import PLeaTTa.Proofs.CompilerGoalSubstitutionAdequacy
import PLeaTTa.Proofs.PrologStateBridge

namespace PLeaTTa.PrologGoalAlpha

open Metta (Atom)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open CompilerAdequacy
open CompilerGoalSubstitutionAdequacy
open CompilerSubstitutionAdequacy
open OpenBindingAgreement
open PrologStateBridge

/-!
`GoalAgrees` describes compiler-time correspondence before a clause is
standardized apart.  The independent resolver then applies a finite
`Substitution`, while the executable applies `renameGoalSuffix`, including
turning a source `.cut` into a barrier-specific `.cutAt`.

The relations below mirror only the already-proved `CompilerAdequacy`
constructors.  Every term leaf is replaced by `AlphaTermAgrees`; no
constructor lets an oracle provide an answer or reinterpret goal structure.
Hidden executable branch fields remain explicit.
-/

/-- Alpha-facing type-check carry contract.  The expected value is observed
through the exact deep-chain representation used by the emitted equality,
and the hidden soft-cut template must be the compiler's exact carry for the
renamed expected atom. -/
structure AlphaTypeCheckExpectedAgrees
    (alpha : List (LogicVar × String))
    (reference : Term) (executable template : Atom) : Prop where
  term : AlphaTermAgrees alpha reference (chainify executable)
  template_eq : template = typeCheckBindingTemplate executable

/-- Ordered literal `amb` branches have no nested executable bodies, but the
enclosing output is still an explicit hidden field of every branch. -/
inductive AlphaLiteralAmbBranchesAgree
    (alpha : List (LogicVar × String))
    (referenceOutput : Term) (executableOutput : Atom) :
    List PeTTaSpec.PrologCore.Goal →
      List (Atom × List PLeaTTa.Goal) → Prop where
  | nil
      (output : AlphaTermAgrees alpha referenceOutput executableOutput) :
      AlphaLiteralAmbBranchesAgree alpha referenceOutput executableOutput
        [] []
  | cons {referenceValue : Term} {executableValue : Atom}
      {referenceBranches : List PeTTaSpec.PrologCore.Goal}
      {executableBranches : List (Atom × List PLeaTTa.Goal)}
      (value : AlphaTermAgrees alpha referenceValue executableValue)
      (output : AlphaTermAgrees alpha referenceOutput executableOutput)
      (tail : AlphaLiteralAmbBranchesAgree alpha referenceOutput
        executableOutput referenceBranches executableBranches) :
      AlphaLiteralAmbBranchesAgree alpha referenceOutput executableOutput
        (.unify referenceValue referenceOutput :: referenceBranches)
        ((executableValue, []) :: executableBranches)

mutual

/-- Cross-representation goal agreement after runtime standardization apart.
The barrier is present in the executable syntax, so a wrongly scoped cut is
not related merely because both sides contain a cut. -/
inductive AlphaGoalAgrees (alpha : List (LogicVar × String))
    (barrier : Nat) :
    PeTTaSpec.PrologCore.Goal → PLeaTTa.Goal → Prop where
  | unify {referenceLeft referenceRight : Term}
      {executableLeft executableRight : Atom}
      (left : AlphaTermAgrees alpha referenceLeft executableLeft)
      (right : AlphaTermAgrees alpha referenceRight executableRight) :
      AlphaGoalAgrees alpha barrier (.unify referenceLeft referenceRight)
        (.eq executableLeft executableRight)
  | compileAlias {referenceLeft referenceRight : Term}
      {executableLeft executableRight : Atom}
      (left : AlphaTermAgrees alpha referenceLeft executableLeft)
      (right : AlphaTermAgrees alpha referenceRight executableRight) :
      AlphaGoalAgrees alpha barrier (.unify referenceLeft referenceRight)
        (.compileAlias executableLeft executableRight)
  | cut :
      AlphaGoalAgrees alpha barrier .cut (.cutAt barrier)
  | builtin {predicate : String} {referenceArguments : List Term}
      {referenceResult : Term} {executableArguments : List Atom}
      {executableResult : Atom}
      (arguments :
        AlphaTermsAgree alpha referenceArguments executableArguments)
      (result : AlphaTermAgrees alpha referenceResult executableResult) :
      AlphaGoalAgrees alpha barrier
        (.call predicate (referenceArguments ++ [referenceResult]))
        (.bin predicate executableArguments executableResult)
  | definedCall {predicate : String} {referenceArguments : List Term}
      {referenceResult : Term} {executableArguments : List Atom}
      {executableResult : Atom}
      (arguments :
        AlphaTermsAgree alpha referenceArguments executableArguments)
      (result : AlphaTermAgrees alpha referenceResult executableResult) :
      AlphaGoalAgrees alpha barrier
        (.call predicate (referenceArguments ++ [referenceResult]))
        (.call predicate executableArguments executableResult)
  | softCutTruth {referenceCondition referenceElse :
        List PeTTaSpec.PrologCore.Goal}
      {executableCondition executableElse : List PLeaTTa.Goal}
      (condition :
        AlphaGoalsAgree alpha barrier referenceCondition executableCondition)
      (otherwise :
        AlphaGoalsAgree alpha barrier referenceElse executableElse) :
      AlphaGoalAgrees alpha barrier
        (.softCut (.conjunction referenceCondition) .truth
          (.conjunction referenceElse))
        (.softcut (.sym "#u") executableCondition [] executableElse)
  | typeCheckSoftCut {referenceValue referenceExpected referenceDirect
        referenceMeta : Term}
      {executableValue executableExpected executableDirect executableMeta
        executableTemplate : Atom}
      (value : AlphaTermAgrees alpha referenceValue executableValue)
      (expected : AlphaTypeCheckExpectedAgrees alpha referenceExpected
        executableExpected executableTemplate)
      (direct : AlphaTermAgrees alpha referenceDirect executableDirect)
      (metaTerm : AlphaTermAgrees alpha referenceMeta executableMeta) :
      AlphaGoalAgrees alpha barrier
        (.softCut
          (.conjunction
            [.call "get-type" [referenceValue, referenceDirect],
             .unify referenceDirect referenceExpected])
          .truth
          (.conjunction
            [.call "get-metatype" [referenceValue, referenceMeta],
             .unify referenceMeta referenceExpected]))
        (.softcut executableTemplate
          [.bin "get-type" [executableValue] executableDirect,
           .eq executableDirect (chainify executableExpected)]
          []
          [.bin "get-metatype" [executableValue] executableMeta,
           .eq executableMeta (chainify executableExpected)])
  | shortCircuitAnd {referenceCondition referenceBody referenceOutput : Term}
      {executableCondition executableBody executableOutput : Atom}
      {referenceBodyGoals : List PeTTaSpec.PrologCore.Goal}
      {executableBodyGoals : List PLeaTTa.Goal}
      (condition :
        AlphaTermAgrees alpha referenceCondition executableCondition)
      (body : AlphaTermAgrees alpha referenceBody executableBody)
      (output : AlphaTermAgrees alpha referenceOutput executableOutput)
      (bodyGoals :
        AlphaGoalsAgree alpha barrier referenceBodyGoals
          executableBodyGoals) :
      AlphaGoalAgrees alpha barrier
        (.ifThenElse (.identical referenceCondition (.atom "true"))
          (.conjunction
            [.conjunction referenceBodyGoals,
             .unify referenceOutput referenceBody])
          (.unify referenceOutput (.atom "false")))
        (.ite executableCondition
          (executableOutput,
            executableBodyGoals ++ [.eq executableOutput executableBody])
          (executableOutput, [.eq executableOutput (.sym "False")])
          executableOutput)
  | shortCircuitOr {referenceCondition referenceBody referenceOutput : Term}
      {executableCondition executableBody executableOutput : Atom}
      {referenceBodyGoals : List PeTTaSpec.PrologCore.Goal}
      {executableBodyGoals : List PLeaTTa.Goal}
      (condition :
        AlphaTermAgrees alpha referenceCondition executableCondition)
      (body : AlphaTermAgrees alpha referenceBody executableBody)
      (output : AlphaTermAgrees alpha referenceOutput executableOutput)
      (bodyGoals :
        AlphaGoalsAgree alpha barrier referenceBodyGoals
          executableBodyGoals) :
      AlphaGoalAgrees alpha barrier
        (.ifThenElse (.identical referenceCondition (.atom "true"))
          (.unify referenceOutput (.atom "true"))
          (.conjunction
            [.conjunction referenceBodyGoals,
             .unify referenceOutput referenceBody]))
        (.ite executableCondition
          (executableOutput, [.eq executableOutput (.sym "True")])
          (executableOutput,
            executableBodyGoals ++ [.eq executableOutput executableBody])
          executableOutput)
  | findall {referenceTemplate referenceOutput : Term}
      {executableTemplate executableOutput : Atom}
      {referenceGoals : List PeTTaSpec.PrologCore.Goal}
      {executableGoals : List PLeaTTa.Goal}
      (template :
        AlphaTermAgrees alpha referenceTemplate executableTemplate)
      (body :
        AlphaGoalsAgree alpha barrier referenceGoals executableGoals)
      (output : AlphaTermAgrees alpha referenceOutput executableOutput) :
      AlphaGoalAgrees alpha barrier
        (.findall referenceTemplate (.conjunction referenceGoals)
          referenceOutput)
        (.findall executableTemplate executableGoals executableOutput)
  | literalAmb {referenceOutput : Term} {executableOutput : Atom}
      {referenceBranches : List PeTTaSpec.PrologCore.Goal}
      {executableBranches : List (Atom × List PLeaTTa.Goal)}
      (branches : AlphaLiteralAmbBranchesAgree alpha referenceOutput
        executableOutput referenceBranches executableBranches) :
      AlphaGoalAgrees alpha barrier (.disjunction referenceBranches)
        (.amb executableBranches executableOutput)
  | builtAmb {referenceOutput : Term} {executableOutput : Atom}
      {referenceBranches : List PeTTaSpec.PrologCore.Goal}
      {executableBranches : List (Atom × List PLeaTTa.Goal)}
      (branches : AlphaSuperposeBranchesAgree alpha barrier referenceOutput
        executableOutput referenceBranches executableBranches) :
      AlphaGoalAgrees alpha barrier (.disjunction referenceBranches)
        (.amb executableBranches executableOutput)
  | spread {referenceValue referenceOutput : Term}
      {executableValue executableOutput : Atom}
      (value : AlphaTermAgrees alpha referenceValue executableValue)
      (output : AlphaTermAgrees alpha referenceOutput executableOutput) :
      AlphaGoalAgrees alpha barrier
        (.call "superpose" [referenceValue, referenceOutput])
        (.spread executableValue executableOutput)
  | conditional {referenceCondition referenceOutput : Term}
      {referenceThen referenceElse : PeTTaSpec.PrologCore.Goal}
      {executableCondition executableOutput : Atom}
      {executableThen executableElse : Atom × List PLeaTTa.Goal}
      (condition :
        AlphaTermAgrees alpha referenceCondition executableCondition)
      (output : AlphaTermAgrees alpha referenceOutput executableOutput)
      (thenBranch : AlphaIfBranchAgrees alpha barrier referenceOutput
        executableOutput referenceThen executableThen)
      (elseBranch : AlphaIfBranchAgrees alpha barrier referenceOutput
        executableOutput referenceElse executableElse) :
      AlphaGoalAgrees alpha barrier
        (.ifThenElse (.identical referenceCondition (.atom "true"))
          referenceThen referenceElse)
        (.ite executableCondition executableThen executableElse
          executableOutput)

/-- Alpha agreement for normalized `if` branches, including the executable
output hidden by a failing independent branch. -/
inductive AlphaIfBranchAgrees (alpha : List (LogicVar × String))
    (barrier : Nat) :
    Term → Atom → PeTTaSpec.PrologCore.Goal →
      Atom × List PLeaTTa.Goal → Prop where
  | empty {referenceOutput referenceValue : Term}
      {executableOutput executableValue : Atom}
      (value : AlphaTermAgrees alpha referenceValue executableValue)
      (output : AlphaTermAgrees alpha referenceOutput executableOutput) :
      AlphaIfBranchAgrees alpha barrier referenceOutput executableOutput
        (.unify referenceValue referenceOutput) (executableValue, [])
  | aliased {referenceOutput : Term} {executableOutput : Atom}
      {referenceGoals : List PeTTaSpec.PrologCore.Goal}
      {executableGoals : List PLeaTTa.Goal}
      (output : AlphaTermAgrees alpha referenceOutput executableOutput)
      (goals :
        AlphaGoalsAgree alpha barrier referenceGoals executableGoals) :
      AlphaIfBranchAgrees alpha barrier referenceOutput executableOutput
        (.conjunction referenceGoals) (executableOutput, executableGoals)
  | nonvariable {referenceOutput referenceValue : Term}
      {executableOutput executableValue : Atom}
      {referenceGoals : List PeTTaSpec.PrologCore.Goal}
      {executableGoals : List PLeaTTa.Goal}
      (value : AlphaTermAgrees alpha referenceValue executableValue)
      (output : AlphaTermAgrees alpha referenceOutput executableOutput)
      (goals :
        AlphaGoalsAgree alpha barrier referenceGoals executableGoals) :
      AlphaIfBranchAgrees alpha barrier referenceOutput executableOutput
        (.conjunction (.unify referenceValue referenceOutput ::
          referenceGoals))
        (executableValue, executableGoals)
  | failed {referenceOutput : Term} {executableOutput : Atom}
      (output : AlphaTermAgrees alpha referenceOutput executableOutput) :
      AlphaIfBranchAgrees alpha barrier referenceOutput executableOutput .fail
        (executableOutput,
          [PLeaTTa.Goal.eq (.sym "True") (.sym "False")])

/-- Alpha agreement for one normalized syntactic-superpose branch. -/
inductive AlphaSuperposeBranchAgrees
    (alpha : List (LogicVar × String)) (barrier : Nat) :
    Term → Atom → PeTTaSpec.PrologCore.Goal →
      Atom × List PLeaTTa.Goal → Prop where
  | empty {referenceOutput referenceValue : Term}
      {executableOutput executableValue : Atom}
      (value : AlphaTermAgrees alpha referenceValue executableValue)
      (output : AlphaTermAgrees alpha referenceOutput executableOutput) :
      AlphaSuperposeBranchAgrees alpha barrier referenceOutput executableOutput
        (.unify referenceValue referenceOutput) (executableValue, [])
  | aliased {referenceOutput : Term} {executableOutput : Atom}
      {referenceGoals : List PeTTaSpec.PrologCore.Goal}
      {executableGoals : List PLeaTTa.Goal}
      (output : AlphaTermAgrees alpha referenceOutput executableOutput)
      (goals :
        AlphaGoalsAgree alpha barrier referenceGoals executableGoals)
      (nonempty : executableGoals ≠ []) :
      AlphaSuperposeBranchAgrees alpha barrier referenceOutput executableOutput
        (.conjunction referenceGoals) (executableOutput, executableGoals)
  | nonvariable {referenceOutput referenceValue : Term}
      {executableOutput executableValue : Atom}
      {referenceGoals : List PeTTaSpec.PrologCore.Goal}
      {executableGoals : List PLeaTTa.Goal}
      (value : AlphaTermAgrees alpha referenceValue executableValue)
      (output : AlphaTermAgrees alpha referenceOutput executableOutput)
      (goals :
        AlphaGoalsAgree alpha barrier referenceGoals executableGoals) :
      AlphaSuperposeBranchAgrees alpha barrier referenceOutput executableOutput
        (.conjunction (.unify referenceValue referenceOutput ::
          referenceGoals))
        (executableOutput,
          PLeaTTa.Goal.eq executableValue executableOutput ::
            executableGoals)

/-- Ordered alpha agreement for the general-superpose branch collection. -/
inductive AlphaSuperposeBranchesAgree
    (alpha : List (LogicVar × String)) (barrier : Nat) :
    Term → Atom → List PeTTaSpec.PrologCore.Goal →
      List (Atom × List PLeaTTa.Goal) → Prop where
  | nil {referenceOutput : Term} {executableOutput : Atom}
      (output : AlphaTermAgrees alpha referenceOutput executableOutput) :
      AlphaSuperposeBranchesAgree alpha barrier referenceOutput
        executableOutput
        [] []
  | cons {referenceOutput : Term} {executableOutput : Atom}
      {referenceBranch : PeTTaSpec.PrologCore.Goal}
      {executableBranch : Atom × List PLeaTTa.Goal}
      {referenceBranches : List PeTTaSpec.PrologCore.Goal}
      {executableBranches : List (Atom × List PLeaTTa.Goal)}
      (head : AlphaSuperposeBranchAgrees alpha barrier referenceOutput
        executableOutput referenceBranch executableBranch)
      (tail : AlphaSuperposeBranchesAgree alpha barrier referenceOutput
        executableOutput referenceBranches executableBranches) :
      AlphaSuperposeBranchesAgree alpha barrier referenceOutput
        executableOutput
        (referenceBranch :: referenceBranches)
        (executableBranch :: executableBranches)

/-- Ordered pointwise alpha agreement for flattened goal lists. -/
inductive AlphaGoalsAgree (alpha : List (LogicVar × String))
    (barrier : Nat) :
    List PeTTaSpec.PrologCore.Goal → List PLeaTTa.Goal → Prop where
  | nil : AlphaGoalsAgree alpha barrier [] []
  | cons {reference : PeTTaSpec.PrologCore.Goal}
      {executable : PLeaTTa.Goal}
      {references : List PeTTaSpec.PrologCore.Goal}
      {executables : List PLeaTTa.Goal}
      (head : AlphaGoalAgrees alpha barrier reference executable)
      (tail : AlphaGoalsAgree alpha barrier references executables) :
      AlphaGoalsAgree alpha barrier (reference :: references)
        (executable :: executables)
  | conjunction {referenceBlock referenceTail :
        List PeTTaSpec.PrologCore.Goal}
      {executableBlock executableTail : List PLeaTTa.Goal}
      (block :
        AlphaGoalsAgree alpha barrier referenceBlock executableBlock)
      (tail : AlphaGoalsAgree alpha barrier referenceTail executableTail) :
      AlphaGoalsAgree alpha barrier
        (.conjunction referenceBlock :: referenceTail)
        (executableBlock ++ executableTail)

end

/-! ## Structural renaming laws for hidden type-check fields -/

/-- Deep chainification commutes with suffix renaming.  This is specific to
an injective variable renaming; it is deliberately not stated for arbitrary
executable substitution. -/
theorem renameAtomSuffix_chainify (suffix : String) (atom : Atom) :
    renameAtomSuffix suffix (chainify atom) =
      chainify (renameAtomSuffix suffix atom) := by
  induction atom with
  | sym name =>
      by_cases isTrue : name = "true"
      · subst name
        simp [chainify, canonBool, renameAtomSuffix_sym]
      · by_cases isFalse : name = "false"
        · subst name
          simp [chainify, canonBool, renameAtomSuffix_sym]
        · simp [chainify, canonBool, renameAtomSuffix_sym, isTrue, isFalse]
  | var name =>
      simp [chainify, canonBool, renameAtomSuffix_var]
  | gnd ground =>
      cases ground with
      | int value =>
          simp [chainify, canonBool, renameAtomSuffix_gnd]
      | float value =>
          simp [chainify, canonBool, renameAtomSuffix_gnd]
      | str value =>
          simp [chainify, canonBool, renameAtomSuffix_gnd]
      | bool value =>
          cases value <;>
            simp [chainify, canonBool, renameAtomSuffix_gnd,
              renameAtomSuffix_sym]
      | unit =>
          simp [chainify, canonBool, renameAtomSuffix_gnd]
      | error message =>
          simp [chainify, canonBool, renameAtomSuffix_gnd]
      | external tag payload =>
          simp [chainify, canonBool, renameAtomSuffix_gnd]
  | expr atoms inductionHypothesis =>
      rw [chainify_expr, renameAtomSuffix_chainOf,
        renameAtomSuffix_expr, chainify_expr]
      simp only [List.map_map]
      apply congrArg chainOf
      apply List.map_congr_left
      intro child member
      exact inductionHypothesis child member

/-- Appending one fixed suffix to a string is injective. -/
theorem string_append_suffix_injective (suffix : String) :
    Function.Injective fun name : String => name ++ suffix := by
  intro left right equality
  apply String.toList_inj.mp
  apply List.append_inj_left'
  · simpa only [String.toList_append] using
      congrArg String.toList equality
  · rfl

/-- Filtering out one source commutes with an injective map. -/
private theorem filter_map_not_beq_injective
    {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (function : α → β) (injective : Function.Injective function)
    (source : α) (values : List α) :
    (values.map function).filter (fun target => !target == function source) =
      (values.filter (fun value => !value == source)).map function := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      by_cases same : head = source
      · subst head
        simp [inductionHypothesis]
      · have mappedDifferent : function head ≠ function source := by
          intro equality
          exact same (injective equality)
        simp [same, mappedDifferent, inductionHypothesis]

/-- First-occurrence duplicate removal commutes with an injective map. -/
theorem eraseDups_map_injective
    {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (function : α → β) (injective : Function.Injective function)
    : ∀ values : List α,
    (values.map function).eraseDups =
      values.eraseDups.map function
  | [] => rfl
  | head :: tail => by
      rw [List.map_cons, List.eraseDups_cons, List.eraseDups_cons,
        filter_map_not_beq_injective function injective]
      congr 1
      exact eraseDups_map_injective function injective
        (tail.filter fun value => !value == head)
termination_by values => values.length
decreasing_by
  have bound :=
    List.length_filter_le (fun value : α => !value == head) tail
  simp only [List.length_cons]
  omega

/-- Type-check carry-template construction commutes with suffix renaming.
This is the specialized law needed by clause standardization; the analogous
statement is false for arbitrary substitutions because carry variables are
deduplicated before execution. -/
theorem renameAtomSuffix_typeCheckBindingTemplate
    (suffix : String) (expected : Atom) :
    renameAtomSuffix suffix (typeCheckBindingTemplate expected) =
      typeCheckBindingTemplate (renameAtomSuffix suffix expected) := by
  unfold typeCheckBindingTemplate bindingTemplate
  rw [renameAtomSuffix_vars_exact]
  by_cases empty : expected.vars.isEmpty
  · simp [empty, renameAtomSuffix_sym]
  · simp [empty, renameAtomSuffix_chainOf, renameAtomSuffix_sym]
    rw [renameAtomSuffix_vars_exact,
      eraseDups_map_injective
        (fun name : String => name ++ suffix)
        (string_append_suffix_injective suffix)]
    simp [List.map_map, Function.comp_def, renameAtomSuffix_var]

/-- Expected-type agreement transports through clause standardization using
the type-specific support domain.  The carry-template equation is proved
from the compiler's independent contract and the specialized commutation
law above, rather than assumed as an executable invariant. -/
theorem typeCheckExpectedAgrees_alpha_freshen
    {referenceSubstitution : Substitution} {suffix : String}
    {domain : List LogicVar} {alpha : List (LogicVar × String)}
    (variableAgreement :
      ∀ identity, identity ∈ domain →
        ∃ target,
          referenceSubstitution.applyTerm (.variable identity) =
            .variable target ∧
          (target, logicVarExecutableName identity ++ suffix) ∈ alpha)
    {reference : Term} {executable template : Atom}
    (agreement : TypeCheckExpectedAgrees reference executable template)
    (supported : TypeCheckExpectedAgreesSupported domain agreement) :
    AlphaTypeCheckExpectedAgrees alpha
      (referenceSubstitution.applyTerm reference)
      (renameAtomSuffix suffix executable)
      (renameAtomSuffix suffix template) := by
  constructor
  · have transported :=
      termAgrees_alpha_freshen variableAgreement agreement.term supported
    simpa [renameAtomSuffix_chainify] using transported
  · calc
      renameAtomSuffix suffix template =
          renameAtomSuffix suffix (typeCheckBindingTemplate executable) :=
        congrArg (renameAtomSuffix suffix) agreement.compilerTemplate_eq.symm
      _ = typeCheckBindingTemplate (renameAtomSuffix suffix executable) :=
        renameAtomSuffix_typeCheckBindingTemplate suffix executable

/-- Structural suffix renaming cannot erase a nonempty executable goal
sequence. -/
theorem renameGoalsSuffix_ne_nil
    {suffix : String} {barrier : Nat} {goals : List PLeaTTa.Goal}
    (nonempty : goals ≠ []) :
    renameGoalsSuffix suffix barrier goals ≠ [] := by
  cases goals with
  | nil => contradiction
  | cons goal goals => simp [renameGoalsSuffix]

/-! ## Agreement-indexed alpha transport -/

/-- Literal-only alternatives need no mutual recursion through nested goal
bodies.  Keeping this proof outside the structural mutual block also makes
its only recursive decrease—the tail branch list—explicit. -/
theorem literalAmbBranchesAgree_alpha_freshen_of_supported
    {referenceSubstitution : Substitution} {suffix : String}
    {termDomain typeDomain : List LogicVar}
    {alpha : List (LogicVar × String)}
    (termVariableAgreement :
      ∀ identity, identity ∈ termDomain →
        ∃ target,
          referenceSubstitution.applyTerm (.variable identity) =
            .variable target ∧
          (target, logicVarExecutableName identity ++ suffix) ∈ alpha)
    (barrier : Nat)
    {referenceOutput : Term} {executableOutput : Atom}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List (Atom × List PLeaTTa.Goal)}
    {agreement : LiteralAmbBranchesAgree referenceOutput executableOutput
      references executables}
    (supported : LiteralAmbBranchesAgreeSupported termDomain typeDomain
      agreement) :
    AlphaLiteralAmbBranchesAgree alpha
      (referenceSubstitution.applyTerm referenceOutput)
      (renameAtomSuffix suffix executableOutput)
      (referenceSubstitution.applyGoals references)
      (renameBranchesSuffix suffix barrier executables) := by
  induction agreement with
  | nil output =>
      cases supported with
      | nil outputSupport =>
          simpa [renameBranchesSuffix] using
            AlphaLiteralAmbBranchesAgree.nil
              (termAgrees_alpha_freshen termVariableAgreement output
                outputSupport)
  | cons value output tail tailInduction =>
      cases supported with
      | cons outputTermSupport valueSupport outputSupport tailSupport =>
          simpa [renameBranchesSuffix, renameGoalsSuffix] using
            AlphaLiteralAmbBranchesAgree.cons
              (termAgrees_alpha_freshen termVariableAgreement value
                valueSupport)
              (termAgrees_alpha_freshen termVariableAgreement output
                outputSupport)
              (tailInduction tailSupport)

mutual

/-- Every supported compiler goal agreement transports through the actual
independent finite freshening and executable suffix renamer.  Ordinary term
fields and type-check carry fields use their separately certified domains. -/
theorem GoalAgrees.alpha_freshen_of_supported
    {referenceSubstitution : Substitution} {suffix : String}
    {termDomain typeDomain : List LogicVar}
    {alpha : List (LogicVar × String)}
    (termVariableAgreement :
      ∀ identity, identity ∈ termDomain →
        ∃ target,
          referenceSubstitution.applyTerm (.variable identity) =
            .variable target ∧
          (target, logicVarExecutableName identity ++ suffix) ∈ alpha)
    (typeVariableAgreement :
      ∀ identity, identity ∈ typeDomain →
        ∃ target,
          referenceSubstitution.applyTerm (.variable identity) =
            .variable target ∧
          (target, logicVarExecutableName identity ++ suffix) ∈ alpha)
    (barrier : Nat)
    {reference : PeTTaSpec.PrologCore.Goal}
    {executable : PLeaTTa.Goal}
    {agreement : GoalAgrees reference executable}
    (supported : GoalAgreesSupported termDomain typeDomain agreement) :
    AlphaGoalAgrees alpha barrier
      (referenceSubstitution.applyGoal reference)
      (renameGoalSuffix suffix barrier executable) := by
  cases supported with
  | @unify referenceLeft referenceRight executableLeft executableRight
      left right leftSupport rightSupport =>
      simpa [renameGoalSuffix] using AlphaGoalAgrees.unify
        (termAgrees_alpha_freshen termVariableAgreement left leftSupport)
        (termAgrees_alpha_freshen termVariableAgreement right rightSupport)
  | @compileAlias referenceLeft referenceRight executableLeft executableRight
      left right leftSupport rightSupport =>
      simpa [renameGoalSuffix] using AlphaGoalAgrees.compileAlias
        (termAgrees_alpha_freshen termVariableAgreement left leftSupport)
        (termAgrees_alpha_freshen termVariableAgreement right rightSupport)
  | cut =>
      simpa [renameGoalSuffix] using
        (AlphaGoalAgrees.cut :
          AlphaGoalAgrees alpha barrier .cut (.cutAt barrier))
  | @builtin x predicate referenceArguments referenceResult
      executableArguments executableResult arguments result argumentsSupport
      resultSupport =>
      simpa [renameGoalSuffix] using AlphaGoalAgrees.builtin
        (termsAgree_alpha_freshen termVariableAgreement arguments
          argumentsSupport)
        (termAgrees_alpha_freshen termVariableAgreement result resultSupport)
  | @definedCall x predicate referenceArguments referenceResult
      executableArguments executableResult arguments result argumentsSupport
      resultSupport =>
      simpa [renameGoalSuffix] using AlphaGoalAgrees.definedCall
        (termsAgree_alpha_freshen termVariableAgreement arguments
          argumentsSupport)
        (termAgrees_alpha_freshen termVariableAgreement result resultSupport)
  | softCutTruth conditionSupport otherwiseSupport =>
      simpa [renameGoalSuffix, renameGoalsSuffix,
        renameAtomSuffix_sym] using
        AlphaGoalAgrees.softCutTruth
          (GoalsAgree.alpha_freshen_of_supported termVariableAgreement
            typeVariableAgreement barrier conditionSupport)
          (GoalsAgree.alpha_freshen_of_supported termVariableAgreement
            typeVariableAgreement barrier otherwiseSupport)
  | typeCheckSoftCut valueSupport expectedSupport directSupport metaSupport =>
      rename_i referenceValue referenceExpected referenceDirect referenceMeta
        executableValue executableExpected executableDirect executableMeta
        executableTemplate value expected direct metaTerm
      have expectedTransport :=
        typeCheckExpectedAgrees_alpha_freshen
          typeVariableAgreement expected expectedSupport
      have transported := AlphaGoalAgrees.typeCheckSoftCut
        (barrier := barrier)
        (termAgrees_alpha_freshen termVariableAgreement value valueSupport)
        expectedTransport
        (termAgrees_alpha_freshen termVariableAgreement direct directSupport)
        (termAgrees_alpha_freshen termVariableAgreement metaTerm metaSupport)
      simpa [renameGoalSuffix, renameGoalsSuffix,
        renameAtomSuffix_chainify] using transported
  | @shortCircuitAnd referenceCondition referenceBody referenceOutput
      executableCondition executableBody executableOutput referenceBodyGoals
      executableBodyGoals condition body output bodyGoals conditionSupport
      bodySupport outputSupport bodyGoalsSupport =>
      simpa [renameGoalSuffix, renameGoalsSuffix, renameAtomSuffix_sym] using
        AlphaGoalAgrees.shortCircuitAnd
          (termAgrees_alpha_freshen termVariableAgreement condition
            conditionSupport)
          (termAgrees_alpha_freshen termVariableAgreement body bodySupport)
          (termAgrees_alpha_freshen termVariableAgreement output outputSupport)
          (GoalsAgree.alpha_freshen_of_supported termVariableAgreement
            typeVariableAgreement barrier bodyGoalsSupport)
  | @shortCircuitOr referenceCondition referenceBody referenceOutput
      executableCondition executableBody executableOutput referenceBodyGoals
      executableBodyGoals condition body output bodyGoals conditionSupport
      bodySupport outputSupport bodyGoalsSupport =>
      simpa [renameGoalSuffix, renameGoalsSuffix, renameAtomSuffix_sym] using
        AlphaGoalAgrees.shortCircuitOr
          (termAgrees_alpha_freshen termVariableAgreement condition
            conditionSupport)
          (termAgrees_alpha_freshen termVariableAgreement body bodySupport)
          (termAgrees_alpha_freshen termVariableAgreement output outputSupport)
          (GoalsAgree.alpha_freshen_of_supported termVariableAgreement
            typeVariableAgreement barrier bodyGoalsSupport)
  | @findall referenceTemplate referenceOutput executableTemplate
      executableOutput referenceGoals executableGoals template body output
      templateSupport bodySupport outputSupport =>
      simpa [renameGoalSuffix] using AlphaGoalAgrees.findall
        (termAgrees_alpha_freshen termVariableAgreement template
          templateSupport)
        (GoalsAgree.alpha_freshen_of_supported termVariableAgreement
          typeVariableAgreement barrier bodySupport)
        (termAgrees_alpha_freshen termVariableAgreement output outputSupport)
  | literalAmb branchesSupport =>
      simpa [renameGoalSuffix] using AlphaGoalAgrees.literalAmb
        (literalAmbBranchesAgree_alpha_freshen_of_supported
          termVariableAgreement barrier branchesSupport)
  | builtAmb branchesSupport =>
      simpa [renameGoalSuffix] using AlphaGoalAgrees.builtAmb
        (SuperposeBranchesAgree.alpha_freshen_of_supported
          termVariableAgreement typeVariableAgreement barrier branchesSupport)
  | @spread referenceValue referenceOutput executableValue executableOutput
      value output valueSupport outputSupport =>
      simpa [renameGoalSuffix] using AlphaGoalAgrees.spread
        (termAgrees_alpha_freshen termVariableAgreement value valueSupport)
        (termAgrees_alpha_freshen termVariableAgreement output outputSupport)
  | @conditional referenceCondition referenceOutput referenceThen
      referenceElse executableCondition executableOutput executableThen
      executableElse condition output thenBranch elseBranch conditionSupport
      outputSupport thenSupport elseSupport =>
      simpa [renameGoalSuffix] using AlphaGoalAgrees.conditional
        (termAgrees_alpha_freshen termVariableAgreement condition
          conditionSupport)
        (termAgrees_alpha_freshen termVariableAgreement output outputSupport)
        (IfBranchAgrees.alpha_freshen_of_supported termVariableAgreement
          typeVariableAgreement barrier thenSupport)
        (IfBranchAgrees.alpha_freshen_of_supported termVariableAgreement
          typeVariableAgreement barrier elseSupport)

/-- Branch transport retains the enclosing output even when the independent
branch is visibly failing. -/
theorem IfBranchAgrees.alpha_freshen_of_supported
    {referenceSubstitution : Substitution} {suffix : String}
    {termDomain typeDomain : List LogicVar}
    {alpha : List (LogicVar × String)}
    (termVariableAgreement :
      ∀ identity, identity ∈ termDomain →
        ∃ target,
          referenceSubstitution.applyTerm (.variable identity) =
            .variable target ∧
          (target, logicVarExecutableName identity ++ suffix) ∈ alpha)
    (typeVariableAgreement :
      ∀ identity, identity ∈ typeDomain →
        ∃ target,
          referenceSubstitution.applyTerm (.variable identity) =
            .variable target ∧
          (target, logicVarExecutableName identity ++ suffix) ∈ alpha)
    (barrier : Nat)
    {referenceOutput : Term} {executableOutput : Atom}
    {reference : PeTTaSpec.PrologCore.Goal}
    {executable : Atom × List PLeaTTa.Goal}
    {agreement : IfBranchAgrees referenceOutput executableOutput reference
      executable}
    (supported : IfBranchAgreesSupported termDomain typeDomain agreement) :
    AlphaIfBranchAgrees alpha barrier
      (referenceSubstitution.applyTerm referenceOutput)
      (renameAtomSuffix suffix executableOutput)
      (referenceSubstitution.applyGoal reference)
      (renameAtomSuffix suffix executable.1,
        renameGoalsSuffix suffix barrier executable.2) := by
  cases supported with
  | @empty referenceOutput referenceValue executableOutput executableValue
      value output valueSupport outputSupport =>
      simpa [renameGoalsSuffix] using AlphaIfBranchAgrees.empty
        (termAgrees_alpha_freshen termVariableAgreement value valueSupport)
        (termAgrees_alpha_freshen termVariableAgreement output outputSupport)
  | @aliased referenceOutput executableOutput referenceGoals executableGoals
      output goals outputSupport goalsSupport =>
      simpa using AlphaIfBranchAgrees.aliased
        (termAgrees_alpha_freshen termVariableAgreement output outputSupport)
        (GoalsAgree.alpha_freshen_of_supported termVariableAgreement
          typeVariableAgreement barrier goalsSupport)
  | @nonvariable referenceOutput referenceValue executableOutput
      executableValue referenceGoals executableGoals value output goals
      valueSupport outputSupport goalsSupport =>
      simpa using AlphaIfBranchAgrees.nonvariable
        (termAgrees_alpha_freshen termVariableAgreement value valueSupport)
        (termAgrees_alpha_freshen termVariableAgreement output outputSupport)
        (GoalsAgree.alpha_freshen_of_supported termVariableAgreement
          typeVariableAgreement barrier goalsSupport)
  | @failed referenceOutput executableOutput output outputSupport =>
      simpa [renameGoalsSuffix, renameGoalSuffix, renameAtomSuffix_sym] using
        AlphaIfBranchAgrees.failed
          (termAgrees_alpha_freshen termVariableAgreement output outputSupport)

/-- One normalized general-superpose branch transports with its nested goals
and its nonemptiness certificate intact. -/
theorem SuperposeBranchAgrees.alpha_freshen_of_supported
    {referenceSubstitution : Substitution} {suffix : String}
    {termDomain typeDomain : List LogicVar}
    {alpha : List (LogicVar × String)}
    (termVariableAgreement :
      ∀ identity, identity ∈ termDomain →
        ∃ target,
          referenceSubstitution.applyTerm (.variable identity) =
            .variable target ∧
          (target, logicVarExecutableName identity ++ suffix) ∈ alpha)
    (typeVariableAgreement :
      ∀ identity, identity ∈ typeDomain →
        ∃ target,
          referenceSubstitution.applyTerm (.variable identity) =
            .variable target ∧
          (target, logicVarExecutableName identity ++ suffix) ∈ alpha)
    (barrier : Nat)
    {referenceOutput : Term} {executableOutput : Atom}
    {reference : PeTTaSpec.PrologCore.Goal}
    {executable : Atom × List PLeaTTa.Goal}
    {agreement : SuperposeBranchAgrees referenceOutput executableOutput
      reference executable}
    (supported : SuperposeBranchAgreesSupported termDomain typeDomain
      agreement) :
    AlphaSuperposeBranchAgrees alpha barrier
      (referenceSubstitution.applyTerm referenceOutput)
      (renameAtomSuffix suffix executableOutput)
      (referenceSubstitution.applyGoal reference)
      (renameAtomSuffix suffix executable.1,
        renameGoalsSuffix suffix barrier executable.2) := by
  cases supported with
  | @empty referenceOutput referenceValue executableOutput executableValue
      value output valueSupport outputSupport =>
      simpa [renameGoalsSuffix] using AlphaSuperposeBranchAgrees.empty
        (termAgrees_alpha_freshen termVariableAgreement value valueSupport)
        (termAgrees_alpha_freshen termVariableAgreement output outputSupport)
  | @aliased referenceOutput executableOutput referenceGoals executableGoals
      output goals nonempty outputSupport goalsSupport =>
      simpa using AlphaSuperposeBranchAgrees.aliased
        (termAgrees_alpha_freshen termVariableAgreement output outputSupport)
        (GoalsAgree.alpha_freshen_of_supported termVariableAgreement
          typeVariableAgreement barrier goalsSupport)
        (renameGoalsSuffix_ne_nil nonempty)
  | @nonvariable referenceOutput referenceValue executableOutput
      executableValue referenceGoals executableGoals value output goals
      valueSupport outputSupport goalsSupport =>
      simpa [renameGoalsSuffix, renameGoalSuffix] using
        AlphaSuperposeBranchAgrees.nonvariable
          (termAgrees_alpha_freshen termVariableAgreement value valueSupport)
          (termAgrees_alpha_freshen termVariableAgreement output outputSupport)
          (GoalsAgree.alpha_freshen_of_supported termVariableAgreement
            typeVariableAgreement barrier goalsSupport)

/-- Ordered general-superpose alternatives transport without permutation or
duplicate elimination, including explicit output evidence in the empty case. -/
theorem SuperposeBranchesAgree.alpha_freshen_of_supported
    {referenceSubstitution : Substitution} {suffix : String}
    {termDomain typeDomain : List LogicVar}
    {alpha : List (LogicVar × String)}
    (termVariableAgreement :
      ∀ identity, identity ∈ termDomain →
        ∃ target,
          referenceSubstitution.applyTerm (.variable identity) =
            .variable target ∧
          (target, logicVarExecutableName identity ++ suffix) ∈ alpha)
    (typeVariableAgreement :
      ∀ identity, identity ∈ typeDomain →
        ∃ target,
          referenceSubstitution.applyTerm (.variable identity) =
            .variable target ∧
          (target, logicVarExecutableName identity ++ suffix) ∈ alpha)
    (barrier : Nat)
    {referenceOutput : Term} {executableOutput : Atom}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List (Atom × List PLeaTTa.Goal)}
    {agreement : SuperposeBranchesAgree referenceOutput executableOutput
      references executables}
    (supported : SuperposeBranchesAgreeSupported termDomain typeDomain
      agreement) :
    AlphaSuperposeBranchesAgree alpha barrier
      (referenceSubstitution.applyTerm referenceOutput)
      (renameAtomSuffix suffix executableOutput)
      (referenceSubstitution.applyGoals references)
      (renameBranchesSuffix suffix barrier executables) := by
  cases supported with
  | @nil referenceOutput executableOutput output outputSupport =>
      simpa [renameBranchesSuffix] using
        AlphaSuperposeBranchesAgree.nil
          (termAgrees_alpha_freshen termVariableAgreement output outputSupport)
  | @cons referenceOutput executableOutput referenceBranch executableBranch
      referenceBranches executableBranches head tail outputSupport headSupport
      tailSupport =>
      simpa [renameBranchesSuffix] using AlphaSuperposeBranchesAgree.cons
        (SuperposeBranchAgrees.alpha_freshen_of_supported
          termVariableAgreement typeVariableAgreement barrier headSupport)
        (SuperposeBranchesAgree.alpha_freshen_of_supported
          termVariableAgreement typeVariableAgreement barrier tailSupport)

/-- Ordered flattened goal lists transport constructor by constructor. -/
theorem GoalsAgree.alpha_freshen_of_supported
    {referenceSubstitution : Substitution} {suffix : String}
    {termDomain typeDomain : List LogicVar}
    {alpha : List (LogicVar × String)}
    (termVariableAgreement :
      ∀ identity, identity ∈ termDomain →
        ∃ target,
          referenceSubstitution.applyTerm (.variable identity) =
            .variable target ∧
          (target, logicVarExecutableName identity ++ suffix) ∈ alpha)
    (typeVariableAgreement :
      ∀ identity, identity ∈ typeDomain →
        ∃ target,
          referenceSubstitution.applyTerm (.variable identity) =
            .variable target ∧
          (target, logicVarExecutableName identity ++ suffix) ∈ alpha)
    (barrier : Nat)
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    {agreement : GoalsAgree references executables}
    (supported : GoalsAgreeSupported termDomain typeDomain agreement) :
    AlphaGoalsAgree alpha barrier
      (referenceSubstitution.applyGoals references)
      (renameGoalsSuffix suffix barrier executables) := by
  cases supported with
  | nil =>
      simpa [renameGoalsSuffix] using
        (AlphaGoalsAgree.nil : AlphaGoalsAgree alpha barrier [] [])
  | cons headSupport tailSupport =>
      simpa [renameGoalsSuffix] using AlphaGoalsAgree.cons
        (GoalAgrees.alpha_freshen_of_supported termVariableAgreement
          typeVariableAgreement barrier headSupport)
        (GoalsAgree.alpha_freshen_of_supported termVariableAgreement
          typeVariableAgreement barrier tailSupport)
  | conjunction blockSupport tailSupport =>
      simpa [renameGoalsSuffix] using AlphaGoalsAgree.conjunction
        (GoalsAgree.alpha_freshen_of_supported termVariableAgreement
          typeVariableAgreement barrier blockSupport)
        (GoalsAgree.alpha_freshen_of_supported termVariableAgreement
          typeVariableAgreement barrier tailSupport)

end

/-- The two actual clause copiers transport every compiler-agreeing body goal
when the agreement-indexed support certificate covers the clause's complete
finite variable support.  This premise is explicit: `LocalClauseAgrees.body`
alone cannot reveal executable fields hidden by a failed branch. -/
theorem freshenClause_body_alpha_agrees
    {reference : LocalClause} {executablePredicate : String}
    {executable : PLeaTTa.Clause}
    (base : LocalClauseAgrees reference
      (executablePredicate, executable))
    (supported :
      GoalsAgreeSupported reference.variables reference.variables base.body)
    (freshSeed : Nat) (argsv args : List Atom) (result : Atom)
    (rest : List PLeaTTa.Goal) (binding : Metta.Subst)
    (query : Atom) (seed barrier : Nat) :
    AlphaGoalsAgree
      (RuntimeAlpha.graph
        (referenceFreshTargets
          (reference.freshCopy freshSeed).firstFresh reference.variables)
        (executableFreshTargets
          (resolutionFreshSuffix argsv result rest binding query seed)
          reference.variables))
      barrier
      (reference.freshCopy freshSeed).clause.body
      (freshenResolutionClause argsv args result rest binding query
        seed barrier executable).body := by
  let suffix :=
    resolutionFreshSuffix argsv result rest binding query seed
  let alpha :=
    RuntimeAlpha.graph
      (referenceFreshTargets
        (reference.freshCopy freshSeed).firstFresh reference.variables)
      (executableFreshTargets suffix reference.variables)
  have variableAgreement :
      ∀ identity, identity ∈ reference.variables →
        ∃ target,
          (reference.freshCopy freshSeed).freshSubstitution.applyTerm
              (.variable identity) =
            .variable target ∧
          (target, logicVarExecutableName identity ++ suffix) ∈ alpha := by
    intro identity member
    exact LocalClause.freshCopy_alpha_variable
      reference freshSeed suffix member
  have transported :=
    GoalsAgree.alpha_freshen_of_supported
      variableAgreement variableAgreement barrier supported
  simpa [LocalClause.freshCopy, freshenResolutionClause, suffix, alpha,
    renameGoalsSuffix_eq_map] using transported

/-- The hardest hidden-field case is transported first.  The independent
branch is visibly `.fail`, but the agreement-indexed support certificate
forces its executable output template into the alpha domain. -/
theorem failedIfBranch_alpha_freshen
    {referenceSubstitution : Substitution} {suffix : String}
    {domain typeDomain : List LogicVar}
    {alpha : List (LogicVar × String)}
    (variableAgreement :
      ∀ identity, identity ∈ domain →
        ∃ target,
          referenceSubstitution.applyTerm (.variable identity) =
            .variable target ∧
          (target, logicVarExecutableName identity ++ suffix) ∈ alpha)
    {referenceOutput : Term} {executableOutput : Atom}
    {output : TermAgrees referenceOutput executableOutput}
    (supported :
      IfBranchAgreesSupported domain typeDomain
        (IfBranchAgrees.failed output))
    (barrier : Nat) :
    AlphaIfBranchAgrees alpha barrier
      (referenceSubstitution.applyTerm referenceOutput)
      (renameAtomSuffix suffix executableOutput)
      (referenceSubstitution.applyGoal .fail)
      (renameAtomSuffix suffix executableOutput,
        renameGoalsSuffix suffix barrier
          [PLeaTTa.Goal.eq (.sym "True") (.sym "False")]) := by
  have outputSupported :
      termVariablesIn domain referenceOutput :=
    (failedIfBranch_support_requires_output output).mp supported
  have transported :=
    termAgrees_alpha_freshen variableAgreement output outputSupported
  simpa [renameGoalsSuffix, renameGoalSuffix, renameAtomSuffix_sym] using
    AlphaIfBranchAgrees.failed transported

/-- A one-variable failed branch cannot launder a wrong hidden output name.
The visible independent goal is `.fail` in both cases; only the explicit
hidden-field relation distinguishes the bad branch. -/
theorem wrong_alpha_hidden_branch_output_is_rejected :
    ¬ AlphaIfBranchAgrees [(.generated 0, "right#r0")] 7
      (.variable (.generated 0)) (.var "wrong#r0") .fail
      (.var "wrong#r0",
        [PLeaTTa.Goal.eq (.sym "True") (.sym "False")]) := by
  intro agreement
  cases agreement with
  | failed output =>
      cases output
      simp_all

/-- Empty literal-branch tails no longer erase their shared output
correspondence.  This rejects the exact mismatch accepted by the former
evidence-free `.nil` constructor. -/
theorem wrong_empty_literal_output_is_rejected :
    ¬ LiteralAmbBranchesAgree (.atom "left") (.var "right")
      [] [] := by
  intro agreement
  cases agreement with
  | nil output =>
      exact output.executable_not_variable (by intro; simp) "right" rfl

/-- The general-superpose tail has the same explicit empty-output guard. -/
theorem wrong_empty_superpose_output_is_rejected :
    ¬ SuperposeBranchesAgree (.atom "left") (.var "right")
      [] [] := by
  intro agreement
  cases agreement with
  | nil output =>
      exact output.executable_not_variable (by intro; simp) "right" rfl

/-- Runtime renaming tags a source cut with exactly the active predicate
barrier; alpha-renaming never invents or erases that control identity. -/
theorem cut_alpha_freshen
    (alpha : List (LogicVar × String)) (suffix : String) (barrier : Nat) :
    AlphaGoalAgrees alpha barrier
      (Substitution.applyGoal [] .cut)
      (renameGoalSuffix suffix barrier .cut) := by
  simpa [renameGoalSuffix] using
    (AlphaGoalAgrees.cut :
      AlphaGoalAgrees alpha barrier .cut (.cutAt barrier))

/-- A cut tagged for a different predicate barrier is rejected.  This is the
control-scope counterpart of the wrong-variable-name witnesses. -/
theorem wrong_alpha_cut_barrier_is_rejected
    (alpha : List (LogicVar × String)) {expected actual : Nat}
    (different : expected ≠ actual) :
    ¬ AlphaGoalAgrees alpha expected .cut (.cutAt actual) := by
  intro agreement
  cases agreement
  exact different rfl

end PLeaTTa.PrologGoalAlpha
