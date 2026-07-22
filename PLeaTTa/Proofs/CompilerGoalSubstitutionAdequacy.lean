-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.CompilerGoalSubstitutionAdequacy
Purpose: Transport compiler goal agreement through related finite alias
  substitutions, including branch fields hidden from independent goal syntax.
Trusted boundary: none
Main exports: GoalAgreesSupported, GoalsAgreeSupported,
  GoalAgrees.subst_of_supported, GoalsAgree.subst_of_supported,
  compileSuperposeBranches_alias_supported_finalization_sound,
  splitDomainBranch_supported, splitDomain_same_type_domain_rejected
-/
import PLeaTTa.Proofs.CompilerSubstitutionAdequacy

namespace PLeaTTa.CompilerGoalSubstitutionAdequacy

open Metta (Atom Subst)
open PLeaTTa
open PLeaTTa.CompilerAdequacy
open PLeaTTa.CompilerSubstitutionAdequacy
open PLeaTTa.OpenBindingAgreement
open PLeaTTa.PeTTaSpec.PrologCore
open PLeaTTa.PeTTaSpec.PrologCore.OpenSubstitution

/-! ## Agreement-indexed finite support

Support is indexed by the independent/executable agreement derivation rather
than recovered from the independent goal syntax alone.  This distinction is
necessary: a failed `if` branch has independent goal `.fail`, while its
executable branch still stores the enclosing output template.  The support
certificate therefore follows the actual relation constructor and includes
every hidden term without defining support from the desired substitution
conclusion.
-/

/-- Finite independent support of one agreeing term. -/
def TermAgreesSupported (domain : List LogicVar)
    {reference : Term} {executable : Atom}
    (_agreement : TermAgrees reference executable) : Prop :=
  termVariablesIn domain reference

/-- Finite independent support of an ordered agreeing term list. -/
def TermsAgreeSupported (domain : List LogicVar)
    {references : List Term} {executables : List Atom}
    (_agreement : TermsAgree references executables) : Prop :=
  termsVariablesIn domain references

/-- Finite support of an expected-type agreement, including the independent
identity that determines its executable carry template. -/
def TypeCheckExpectedAgreesSupported (domain : List LogicVar)
    {reference : Term} {executable template : Atom}
    (_agreement : TypeCheckExpectedAgrees reference executable template) :
    Prop :=
  termVariablesIn domain reference

mutual

/-- Constructor-sensitive support for one goal-agreement derivation.  Ordinary
terms and specialized type-check templates use separate domains: alias
sources may occur in continuation goals, while carry-template transport needs
the stricter alias-disjoint type domain. -/
inductive GoalAgreesSupported (termDomain typeDomain : List LogicVar) :
    {reference : PeTTaSpec.PrologCore.Goal} →
    {executable : PLeaTTa.Goal} →
    GoalAgrees reference executable → Prop where
  | unify {referenceLeft referenceRight executableLeft executableRight}
      {left : TermAgrees referenceLeft executableLeft}
      {right : TermAgrees referenceRight executableRight}
      (leftSupport : TermAgreesSupported termDomain left)
      (rightSupport : TermAgreesSupported termDomain right) :
      GoalAgreesSupported termDomain typeDomain
        (GoalAgrees.unify left right)
  | compileAlias
      {referenceLeft referenceRight executableLeft executableRight}
      {left : TermAgrees referenceLeft executableLeft}
      {right : TermAgrees referenceRight executableRight}
      (leftSupport : TermAgreesSupported termDomain left)
      (rightSupport : TermAgreesSupported termDomain right) :
      GoalAgreesSupported termDomain typeDomain
        (GoalAgrees.compileAlias left right)
  | cut : GoalAgreesSupported termDomain typeDomain GoalAgrees.cut
  | builtin {predicate : String} {referenceArguments : List Term}
      {referenceResult : Term} {executableArguments : List Atom}
      {executableResult : Atom}
      {arguments : TermsAgree referenceArguments executableArguments}
      {result : TermAgrees referenceResult executableResult}
      (argumentsSupport : TermsAgreeSupported termDomain arguments)
      (resultSupport : TermAgreesSupported termDomain result) :
      GoalAgreesSupported termDomain typeDomain
        (GoalAgrees.builtin arguments result)
  | definedCall {predicate : String} {referenceArguments : List Term}
      {referenceResult : Term} {executableArguments : List Atom}
      {executableResult : Atom}
      {arguments : TermsAgree referenceArguments executableArguments}
      {result : TermAgrees referenceResult executableResult}
      (argumentsSupport : TermsAgreeSupported termDomain arguments)
      (resultSupport : TermAgreesSupported termDomain result) :
      GoalAgreesSupported termDomain typeDomain
        (GoalAgrees.definedCall arguments result)
  | softCutTruth {referenceCondition referenceElse executableCondition
        executableElse}
      {condition : GoalsAgree referenceCondition executableCondition}
      {otherwise : GoalsAgree referenceElse executableElse}
      (conditionSupport : GoalsAgreeSupported termDomain typeDomain condition)
      (otherwiseSupport : GoalsAgreeSupported termDomain typeDomain otherwise) :
      GoalAgreesSupported termDomain typeDomain
        (GoalAgrees.softCutTruth condition otherwise)
  | typeCheckSoftCut {referenceValue referenceExpected referenceDirect
        referenceMeta executableValue executableExpected executableDirect
        executableMeta executableTemplate}
      {value : TermAgrees referenceValue executableValue}
      {expected : TypeCheckExpectedAgrees referenceExpected
        executableExpected executableTemplate}
      {direct : TermAgrees referenceDirect executableDirect}
      {metaTerm : TermAgrees referenceMeta executableMeta}
      (valueSupport : TermAgreesSupported termDomain value)
      (expectedSupport : TypeCheckExpectedAgreesSupported typeDomain expected)
      (directSupport : TermAgreesSupported termDomain direct)
      (metaSupport : TermAgreesSupported termDomain metaTerm) :
      GoalAgreesSupported termDomain typeDomain
        (GoalAgrees.typeCheckSoftCut value expected direct metaTerm)
  | shortCircuitAnd {referenceCondition referenceBody referenceOutput
        executableCondition executableBody executableOutput
        referenceBodyGoals executableBodyGoals}
      {condition : TermAgrees referenceCondition executableCondition}
      {body : TermAgrees referenceBody executableBody}
      {output : TermAgrees referenceOutput executableOutput}
      {bodyGoals : GoalsAgree referenceBodyGoals executableBodyGoals}
      (conditionSupport : TermAgreesSupported termDomain condition)
      (bodySupport : TermAgreesSupported termDomain body)
      (outputSupport : TermAgreesSupported termDomain output)
      (bodyGoalsSupport : GoalsAgreeSupported termDomain typeDomain bodyGoals) :
      GoalAgreesSupported termDomain typeDomain
        (GoalAgrees.shortCircuitAnd condition body output bodyGoals)
  | shortCircuitOr {referenceCondition referenceBody referenceOutput
        executableCondition executableBody executableOutput
        referenceBodyGoals executableBodyGoals}
      {condition : TermAgrees referenceCondition executableCondition}
      {body : TermAgrees referenceBody executableBody}
      {output : TermAgrees referenceOutput executableOutput}
      {bodyGoals : GoalsAgree referenceBodyGoals executableBodyGoals}
      (conditionSupport : TermAgreesSupported termDomain condition)
      (bodySupport : TermAgreesSupported termDomain body)
      (outputSupport : TermAgreesSupported termDomain output)
      (bodyGoalsSupport : GoalsAgreeSupported termDomain typeDomain bodyGoals) :
      GoalAgreesSupported termDomain typeDomain
        (GoalAgrees.shortCircuitOr condition body output bodyGoals)
  | findall {referenceTemplate referenceOutput executableTemplate
        executableOutput referenceGoals executableGoals}
      {template : TermAgrees referenceTemplate executableTemplate}
      {body : GoalsAgree referenceGoals executableGoals}
      {output : TermAgrees referenceOutput executableOutput}
      (templateSupport : TermAgreesSupported termDomain template)
      (bodySupport : GoalsAgreeSupported termDomain typeDomain body)
      (outputSupport : TermAgreesSupported termDomain output) :
      GoalAgreesSupported termDomain typeDomain
        (GoalAgrees.findall template body output)
  | literalAmb {referenceOutput executableOutput referenceBranches
        executableBranches}
      {branches : LiteralAmbBranchesAgree referenceOutput executableOutput
        referenceBranches executableBranches}
      (branchesSupport : LiteralAmbBranchesAgreeSupported termDomain
        typeDomain branches) :
      GoalAgreesSupported termDomain typeDomain
        (GoalAgrees.literalAmb branches)
  | builtAmb {referenceOutput executableOutput referenceBranches
        executableBranches}
      {branches : SuperposeBranchesAgree referenceOutput executableOutput
        referenceBranches executableBranches}
      (branchesSupport : SuperposeBranchesAgreeSupported termDomain
        typeDomain branches) :
      GoalAgreesSupported termDomain typeDomain
        (GoalAgrees.builtAmb branches)
  | spread {referenceValue referenceOutput executableValue executableOutput}
      {value : TermAgrees referenceValue executableValue}
      {output : TermAgrees referenceOutput executableOutput}
      (valueSupport : TermAgreesSupported termDomain value)
      (outputSupport : TermAgreesSupported termDomain output) :
      GoalAgreesSupported termDomain typeDomain
        (GoalAgrees.spread value output)
  | conditional {referenceCondition referenceOutput referenceThen
        referenceElse executableCondition executableOutput executableThen
        executableElse}
      {condition : TermAgrees referenceCondition executableCondition}
      {output : TermAgrees referenceOutput executableOutput}
      {thenBranch : IfBranchAgrees referenceOutput executableOutput
        referenceThen executableThen}
      {elseBranch : IfBranchAgrees referenceOutput executableOutput
        referenceElse executableElse}
      (conditionSupport : TermAgreesSupported termDomain condition)
      (outputSupport : TermAgreesSupported termDomain output)
      (thenSupport : IfBranchAgreesSupported termDomain typeDomain thenBranch)
      (elseSupport : IfBranchAgreesSupported termDomain typeDomain elseBranch) :
      GoalAgreesSupported termDomain typeDomain
        (GoalAgrees.conditional condition output thenBranch elseBranch)

/-- Support for a normalized `if` branch, including the enclosing output even
when the independent branch is `.fail`. -/
inductive IfBranchAgreesSupported (termDomain typeDomain : List LogicVar) :
    {referenceOutput : Term} → {executableOutput : Atom} →
    {reference : PeTTaSpec.PrologCore.Goal} →
    {executable : Atom × List PLeaTTa.Goal} →
    IfBranchAgrees referenceOutput executableOutput reference executable →
      Prop where
  | empty {referenceOutput referenceValue executableOutput executableValue}
      {value : TermAgrees referenceValue executableValue}
      {output : TermAgrees referenceOutput executableOutput}
      (valueSupport : TermAgreesSupported termDomain value)
      (outputSupport : TermAgreesSupported termDomain output) :
      IfBranchAgreesSupported termDomain typeDomain
        (IfBranchAgrees.empty value output)
  | aliased {referenceOutput executableOutput referenceGoals executableGoals}
      {output : TermAgrees referenceOutput executableOutput}
      {goals : GoalsAgree referenceGoals executableGoals}
      (outputSupport : TermAgreesSupported termDomain output)
      (goalsSupport : GoalsAgreeSupported termDomain typeDomain goals) :
      IfBranchAgreesSupported termDomain typeDomain
        (IfBranchAgrees.aliased output goals)
  | nonvariable {referenceOutput referenceValue executableOutput
        executableValue referenceGoals executableGoals}
      {value : TermAgrees referenceValue executableValue}
      {output : TermAgrees referenceOutput executableOutput}
      {goals : GoalsAgree referenceGoals executableGoals}
      (valueSupport : TermAgreesSupported termDomain value)
      (outputSupport : TermAgreesSupported termDomain output)
      (goalsSupport : GoalsAgreeSupported termDomain typeDomain goals) :
      IfBranchAgreesSupported termDomain typeDomain
        (IfBranchAgrees.nonvariable value output goals)
  | failed {referenceOutput executableOutput}
      {output : TermAgrees referenceOutput executableOutput}
      (outputSupport : TermAgreesSupported termDomain output) :
      IfBranchAgreesSupported termDomain typeDomain
        (IfBranchAgrees.failed output)

/-- Support for one normalized syntactic-superpose branch. -/
inductive SuperposeBranchAgreesSupported
    (termDomain typeDomain : List LogicVar) :
    {referenceOutput : Term} → {executableOutput : Atom} →
    {reference : PeTTaSpec.PrologCore.Goal} →
    {executable : Atom × List PLeaTTa.Goal} →
    SuperposeBranchAgrees referenceOutput executableOutput reference
      executable → Prop where
  | empty {referenceOutput referenceValue executableOutput executableValue}
      {value : TermAgrees referenceValue executableValue}
      {output : TermAgrees referenceOutput executableOutput}
      (valueSupport : TermAgreesSupported termDomain value)
      (outputSupport : TermAgreesSupported termDomain output) :
      SuperposeBranchAgreesSupported termDomain typeDomain
        (SuperposeBranchAgrees.empty value output)
  | aliased {referenceOutput executableOutput referenceGoals executableGoals}
      {output : TermAgrees referenceOutput executableOutput}
      {goals : GoalsAgree referenceGoals executableGoals}
      {nonempty : executableGoals ≠ []}
      (outputSupport : TermAgreesSupported termDomain output)
      (goalsSupport : GoalsAgreeSupported termDomain typeDomain goals) :
      SuperposeBranchAgreesSupported termDomain typeDomain
        (SuperposeBranchAgrees.aliased output goals nonempty)
  | nonvariable {referenceOutput referenceValue executableOutput
        executableValue referenceGoals executableGoals}
      {value : TermAgrees referenceValue executableValue}
      {output : TermAgrees referenceOutput executableOutput}
      {goals : GoalsAgree referenceGoals executableGoals}
      (valueSupport : TermAgreesSupported termDomain value)
      (outputSupport : TermAgreesSupported termDomain output)
      (goalsSupport : GoalsAgreeSupported termDomain typeDomain goals) :
      SuperposeBranchAgreesSupported termDomain typeDomain
        (SuperposeBranchAgrees.nonvariable value output goals)

/-- Ordered support for the general-superpose branch collection.  The output
is explicit here because the empty collection has no independent branch in
which that identity could appear. -/
inductive SuperposeBranchesAgreeSupported
    (termDomain typeDomain : List LogicVar) :
    {referenceOutput : Term} → {executableOutput : Atom} →
    {references : List PeTTaSpec.PrologCore.Goal} →
    {executables : List (Atom × List PLeaTTa.Goal)} →
    SuperposeBranchesAgree referenceOutput executableOutput references
      executables → Prop where
  | nil {referenceOutput executableOutput}
      (outputSupport : termVariablesIn termDomain referenceOutput) :
      SuperposeBranchesAgreeSupported termDomain typeDomain
        (SuperposeBranchesAgree.nil (referenceOutput := referenceOutput)
          (executableOutput := executableOutput))
  | cons {referenceOutput executableOutput referenceBranch executableBranch
        referenceBranches executableBranches}
      {head : SuperposeBranchAgrees referenceOutput executableOutput
        referenceBranch executableBranch}
      {tail : SuperposeBranchesAgree referenceOutput executableOutput
        referenceBranches executableBranches}
      (outputSupport : termVariablesIn termDomain referenceOutput)
      (headSupport : SuperposeBranchAgreesSupported termDomain typeDomain head)
      (tailSupport : SuperposeBranchesAgreeSupported termDomain typeDomain tail) :
      SuperposeBranchesAgreeSupported termDomain typeDomain
        (SuperposeBranchesAgree.cons head tail)

/-- Ordered support for the literal-only `amb` collection, again retaining
the enclosing output in the empty case. -/
inductive LiteralAmbBranchesAgreeSupported
    (termDomain typeDomain : List LogicVar) :
    {referenceOutput : Term} → {executableOutput : Atom} →
    {references : List PeTTaSpec.PrologCore.Goal} →
    {executables : List (Atom × List PLeaTTa.Goal)} →
    LiteralAmbBranchesAgree referenceOutput executableOutput references
      executables → Prop where
  | nil {referenceOutput executableOutput}
      (outputSupport : termVariablesIn termDomain referenceOutput) :
      LiteralAmbBranchesAgreeSupported termDomain typeDomain
        (LiteralAmbBranchesAgree.nil (referenceOutput := referenceOutput)
          (executableOutput := executableOutput))
  | cons {referenceOutput executableOutput referenceValue executableValue
        referenceBranches executableBranches}
      {value : TermAgrees referenceValue executableValue}
      {output : TermAgrees referenceOutput executableOutput}
      {tail : LiteralAmbBranchesAgree referenceOutput executableOutput
        referenceBranches executableBranches}
      (outputTermSupport : termVariablesIn termDomain referenceOutput)
      (valueSupport : TermAgreesSupported termDomain value)
      (outputSupport : TermAgreesSupported termDomain output)
      (tailSupport : LiteralAmbBranchesAgreeSupported termDomain typeDomain tail) :
      LiteralAmbBranchesAgreeSupported termDomain typeDomain
        (LiteralAmbBranchesAgree.cons value output tail)

/-- Ordered support for a flattened goal-list agreement. -/
inductive GoalsAgreeSupported (termDomain typeDomain : List LogicVar) :
    {references : List PeTTaSpec.PrologCore.Goal} →
    {executables : List PLeaTTa.Goal} →
    GoalsAgree references executables → Prop where
  | nil : GoalsAgreeSupported termDomain typeDomain GoalsAgree.nil
  | cons {reference executable references executables}
      {head : GoalAgrees reference executable}
      {tail : GoalsAgree references executables}
      (headSupport : GoalAgreesSupported termDomain typeDomain head)
      (tailSupport : GoalsAgreeSupported termDomain typeDomain tail) :
      GoalsAgreeSupported termDomain typeDomain (GoalsAgree.cons head tail)
  | conjunction {referenceBlock referenceTail executableBlock executableTail}
      {block : GoalsAgree referenceBlock executableBlock}
      {tail : GoalsAgree referenceTail executableTail}
      (blockSupport : GoalsAgreeSupported termDomain typeDomain block)
      (tailSupport : GoalsAgreeSupported termDomain typeDomain tail) :
      GoalsAgreeSupported termDomain typeDomain
        (GoalsAgree.conjunction block tail)

end

/-! ## Non-vacuity and the hidden-field boundary -/

/-- Empty ordered agreement has support on every finite domain pair. -/
theorem goalsAgreeSupported_nil (termDomain typeDomain : List LogicVar) :
    GoalsAgreeSupported termDomain typeDomain (GoalsAgree.nil) := by
  exact .nil

/-- The support relation sees the output retained by a failed executable
branch even though the independent branch itself is `.fail`. -/
theorem failedIfBranch_support_requires_output
    {termDomain typeDomain : List LogicVar} {referenceOutput : Term}
    {executableOutput : Atom}
    (output : TermAgrees referenceOutput executableOutput) :
    IfBranchAgreesSupported termDomain typeDomain
        (IfBranchAgrees.failed output) ↔
      termVariablesIn termDomain referenceOutput := by
  constructor
  · intro support
    cases support with
    | failed outputSupport => exact outputSupport
  · intro outputSupport
    exact @IfBranchAgreesSupported.failed termDomain typeDomain
      referenceOutput executableOutput output outputSupport

/-- Literal-branch support always retains the enclosing result identity. -/
theorem LiteralAmbBranchesAgreeSupported.output_variables
    {termDomain typeDomain : List LogicVar} {referenceOutput : Term}
    {executableOutput : Atom}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List (Atom × List PLeaTTa.Goal)}
    {agreement : LiteralAmbBranchesAgree referenceOutput executableOutput
      references executables}
    (supported : LiteralAmbBranchesAgreeSupported termDomain typeDomain
      agreement) :
    termVariablesIn termDomain referenceOutput := by
  cases supported with
  | nil outputSupport => exact outputSupport
  | cons outputTermSupport _ _ _ => exact outputTermSupport

/-- Literal-branch support projects to the syntax-only finite support used by
the earlier literal transport theorem.  This projection is sound here because
literal branches contain no hidden nested executable goals. -/
theorem LiteralAmbBranchesAgreeSupported.goal_variables
    {termDomain typeDomain : List LogicVar} {referenceOutput : Term}
    {executableOutput : Atom}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List (Atom × List PLeaTTa.Goal)}
    {agreement : LiteralAmbBranchesAgree referenceOutput executableOutput
      references executables}
    (supported : LiteralAmbBranchesAgreeSupported termDomain typeDomain
      agreement) :
    goalsVariablesIn termDomain references := by
  induction agreement with
  | nil =>
      cases supported
      trivial
  | cons value output tail induction =>
      cases supported with
      | cons outputTermSupport valueSupport outputSupport tailSupport =>
          exact ⟨⟨valueSupport, outputSupport⟩, induction tailSupport⟩

/-! ## Mutual substitution transport -/

/-- Term agreement transports using its agreement-indexed support wrapper. -/
theorem TermAgrees.subst_of_supported
    {referenceBinding : Substitution} {executableBinding : Subst}
    {domain : List LogicVar}
    (variableState :
      VariableStateAgreesOn referenceBinding executableBinding domain)
    {reference : Term} {executable : Atom}
    (agreement : TermAgrees reference executable)
    (supported : TermAgreesSupported domain agreement) :
    TermAgrees (referenceBinding.applyTerm reference)
      (subst executableBinding executable) :=
  PLeaTTa.CompilerSubstitutionAdequacy.TermAgrees.subst_of_variableStateOn
    variableState agreement supported

/-- Ordered term-list counterpart. -/
theorem TermsAgree.subst_of_supported
    {referenceBinding : Substitution} {executableBinding : Subst}
    {domain : List LogicVar}
    (variableState :
      VariableStateAgreesOn referenceBinding executableBinding domain)
    {references : List Term} {executables : List Atom}
    (agreement : TermsAgree references executables)
    (supported : TermsAgreeSupported domain agreement) :
    TermsAgree (referenceBinding.applyTerms references)
      (executables.map (subst executableBinding)) :=
  PLeaTTa.CompilerSubstitutionAdequacy.TermsAgree.subst_of_variableStateOn
    variableState agreement supported

mutual

/-- Every supported goal-agreement derivation transports through related
finite substitutions.  The type-check closure is explicit because carry
deduplication and chainification do not obey a generic substitution law. -/
theorem GoalAgrees.subst_of_supported
    {referenceBinding : Substitution} {executableBinding : Subst}
    {termDomain typeDomain : List LogicVar}
    (variableState :
      VariableStateAgreesOn referenceBinding executableBinding termDomain)
    (typeChecks :
      TypeCheckSubstitutionAgrees referenceBinding executableBinding
        typeDomain)
    {reference : PeTTaSpec.PrologCore.Goal} {executable : PLeaTTa.Goal}
    {agreement : GoalAgrees reference executable}
    (supported : GoalAgreesSupported termDomain typeDomain agreement) :
    GoalAgrees (referenceBinding.applyGoal reference)
      (substCompiledGoal executableBinding executable) := by
  cases supported with
  | unify leftSupport rightSupport =>
      simpa [substCompiledGoal] using GoalAgrees.unify
        (TermAgrees.subst_of_supported variableState _ leftSupport)
        (TermAgrees.subst_of_supported variableState _ rightSupport)
  | compileAlias leftSupport rightSupport =>
      simpa [substCompiledGoal] using GoalAgrees.compileAlias
        (TermAgrees.subst_of_supported variableState _ leftSupport)
        (TermAgrees.subst_of_supported variableState _ rightSupport)
  | cut => simpa [substCompiledGoal] using GoalAgrees.cut
  | builtin argumentsSupport resultSupport =>
      simpa [substCompiledGoal] using GoalAgrees.builtin
        (TermsAgree.subst_of_supported variableState _ argumentsSupport)
        (TermAgrees.subst_of_supported variableState _ resultSupport)
  | definedCall argumentsSupport resultSupport =>
      simpa [substCompiledGoal] using GoalAgrees.definedCall
        (TermsAgree.subst_of_supported variableState _ argumentsSupport)
        (TermAgrees.subst_of_supported variableState _ resultSupport)
  | softCutTruth conditionSupport otherwiseSupport =>
      simpa [substCompiledGoal, substCompiledGoals] using
        GoalAgrees.softCutTruth
        (GoalsAgree.subst_of_supported variableState typeChecks
          conditionSupport)
        (GoalsAgree.subst_of_supported variableState typeChecks
          otherwiseSupport)
  | typeCheckSoftCut valueSupport expectedSupport directSupport metaSupport =>
      rename_i referenceValue referenceExpected referenceDirect referenceMeta
        executableValue executableExpected executableDirect executableMeta
        executableTemplate value expected direct metaTerm
      have expectedTransport := typeChecks expected expectedSupport
      have transported := GoalAgrees.typeCheckSoftCut
        (TermAgrees.subst_of_supported variableState value valueSupport)
        expectedTransport.1
        (TermAgrees.subst_of_supported variableState direct directSupport)
        (TermAgrees.subst_of_supported variableState metaTerm metaSupport)
      simpa [substCompiledGoal, substCompiledGoals,
        expectedTransport.2] using transported
  | shortCircuitAnd conditionSupport bodySupport outputSupport
      bodyGoalsSupport =>
      simpa [substCompiledGoal, substCompiledGoals] using
        GoalAgrees.shortCircuitAnd
        (TermAgrees.subst_of_supported variableState _ conditionSupport)
        (TermAgrees.subst_of_supported variableState _ bodySupport)
        (TermAgrees.subst_of_supported variableState _ outputSupport)
        (GoalsAgree.subst_of_supported variableState typeChecks
          bodyGoalsSupport)
  | shortCircuitOr conditionSupport bodySupport outputSupport
      bodyGoalsSupport =>
      simpa [substCompiledGoal, substCompiledGoals] using
        GoalAgrees.shortCircuitOr
        (TermAgrees.subst_of_supported variableState _ conditionSupport)
        (TermAgrees.subst_of_supported variableState _ bodySupport)
        (TermAgrees.subst_of_supported variableState _ outputSupport)
        (GoalsAgree.subst_of_supported variableState typeChecks
          bodyGoalsSupport)
  | findall templateSupport bodySupport outputSupport =>
      simpa [substCompiledGoal] using GoalAgrees.findall
        (TermAgrees.subst_of_supported variableState _ templateSupport)
        (GoalsAgree.subst_of_supported variableState typeChecks bodySupport)
        (TermAgrees.subst_of_supported variableState _ outputSupport)
  | literalAmb branchesSupport =>
      have branches :=
        LiteralAmbBranchesAgree.subst_of_supported variableState typeChecks
          branchesSupport
      simpa [substCompiledGoal] using GoalAgrees.literalAmb branches
  | builtAmb branchesSupport =>
      have branches :=
        SuperposeBranchesAgree.subst_of_supported variableState typeChecks
          branchesSupport
      simpa [substCompiledGoal] using GoalAgrees.builtAmb branches
  | spread valueSupport outputSupport =>
      simpa [substCompiledGoal] using GoalAgrees.spread
        (TermAgrees.subst_of_supported variableState _ valueSupport)
        (TermAgrees.subst_of_supported variableState _ outputSupport)
  | conditional conditionSupport outputSupport thenSupport elseSupport =>
      simpa [substCompiledGoal] using GoalAgrees.conditional
        (TermAgrees.subst_of_supported variableState _ conditionSupport)
        (TermAgrees.subst_of_supported variableState _ outputSupport)
        (IfBranchAgrees.subst_of_supported variableState typeChecks
          thenSupport)
        (IfBranchAgrees.subst_of_supported variableState typeChecks
          elseSupport)

/-- Branch-template transport sees the enclosing output even in the failed
branch case. -/
theorem IfBranchAgrees.subst_of_supported
    {referenceBinding : Substitution} {executableBinding : Subst}
    {termDomain typeDomain : List LogicVar}
    (variableState :
      VariableStateAgreesOn referenceBinding executableBinding termDomain)
    (typeChecks :
      TypeCheckSubstitutionAgrees referenceBinding executableBinding
        typeDomain)
    {referenceOutput : Term} {executableOutput : Atom}
    {reference : PeTTaSpec.PrologCore.Goal}
    {executable : Atom × List PLeaTTa.Goal}
    {agreement : IfBranchAgrees referenceOutput executableOutput reference
      executable}
    (supported : IfBranchAgreesSupported termDomain typeDomain agreement) :
    IfBranchAgrees (referenceBinding.applyTerm referenceOutput)
      (subst executableBinding executableOutput)
      (referenceBinding.applyGoal reference)
      (subst executableBinding executable.1,
        substCompiledGoals executableBinding executable.2) := by
  cases supported with
  | empty valueSupport outputSupport =>
      simpa [substCompiledGoals] using IfBranchAgrees.empty
        (TermAgrees.subst_of_supported variableState _ valueSupport)
        (TermAgrees.subst_of_supported variableState _ outputSupport)
  | aliased outputSupport goalsSupport =>
      simpa using IfBranchAgrees.aliased
        (TermAgrees.subst_of_supported variableState _ outputSupport)
        (GoalsAgree.subst_of_supported variableState typeChecks goalsSupport)
  | nonvariable valueSupport outputSupport goalsSupport =>
      simpa using IfBranchAgrees.nonvariable
        (TermAgrees.subst_of_supported variableState _ valueSupport)
        (TermAgrees.subst_of_supported variableState _ outputSupport)
        (GoalsAgree.subst_of_supported variableState typeChecks goalsSupport)
  | failed outputSupport =>
      simpa [substCompiledGoals, substCompiledGoal] using IfBranchAgrees.failed
        (TermAgrees.subst_of_supported variableState _ outputSupport)

/-- One normalized general-superpose branch transports with its nested goal
support and retains non-emptiness. -/
theorem SuperposeBranchAgrees.subst_of_supported
    {referenceBinding : Substitution} {executableBinding : Subst}
    {termDomain typeDomain : List LogicVar}
    (variableState :
      VariableStateAgreesOn referenceBinding executableBinding termDomain)
    (typeChecks :
      TypeCheckSubstitutionAgrees referenceBinding executableBinding
        typeDomain)
    {referenceOutput : Term} {executableOutput : Atom}
    {reference : PeTTaSpec.PrologCore.Goal}
    {executable : Atom × List PLeaTTa.Goal}
    {agreement : SuperposeBranchAgrees referenceOutput executableOutput
      reference executable}
    (supported : SuperposeBranchAgreesSupported termDomain typeDomain
      agreement) :
    SuperposeBranchAgrees (referenceBinding.applyTerm referenceOutput)
      (subst executableBinding executableOutput)
      (referenceBinding.applyGoal reference)
      (subst executableBinding executable.1,
        substCompiledGoals executableBinding executable.2) := by
  cases supported with
  | empty valueSupport outputSupport =>
      simpa [substCompiledGoals] using SuperposeBranchAgrees.empty
        (TermAgrees.subst_of_supported variableState _ valueSupport)
        (TermAgrees.subst_of_supported variableState _ outputSupport)
  | @aliased referenceOutput executableOutput referenceGoals executableGoals
      output goals nonempty outputSupport goalsSupport =>
      simpa using SuperposeBranchAgrees.aliased
        (TermAgrees.subst_of_supported variableState output outputSupport)
        (GoalsAgree.subst_of_supported variableState typeChecks goalsSupport)
        (substCompiledGoals_ne_nil nonempty)
  | nonvariable valueSupport outputSupport goalsSupport =>
      simpa [substCompiledGoals, substCompiledGoal] using
        SuperposeBranchAgrees.nonvariable
          (TermAgrees.subst_of_supported variableState _ valueSupport)
          (TermAgrees.subst_of_supported variableState _ outputSupport)
          (GoalsAgree.subst_of_supported variableState typeChecks
            goalsSupport)

/-- Ordered general-superpose branches transport without permutation or
duplicate elimination. -/
theorem SuperposeBranchesAgree.subst_of_supported
    {referenceBinding : Substitution} {executableBinding : Subst}
    {termDomain typeDomain : List LogicVar}
    (variableState :
      VariableStateAgreesOn referenceBinding executableBinding termDomain)
    (typeChecks :
      TypeCheckSubstitutionAgrees referenceBinding executableBinding
        typeDomain)
    {referenceOutput : Term} {executableOutput : Atom}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List (Atom × List PLeaTTa.Goal)}
    {agreement : SuperposeBranchesAgree referenceOutput executableOutput
      references executables}
    (supported : SuperposeBranchesAgreeSupported termDomain typeDomain
      agreement) :
    SuperposeBranchesAgree (referenceBinding.applyTerm referenceOutput)
      (subst executableBinding executableOutput)
      (referenceBinding.applyGoals references)
      (substCompiledBranches executableBinding executables) := by
  cases supported with
  | nil outputSupport =>
      simpa [substCompiledBranches] using
        (SuperposeBranchesAgree.nil :
          SuperposeBranchesAgree
            (referenceBinding.applyTerm referenceOutput)
            (subst executableBinding executableOutput) [] [])
  | @cons referenceOutput executableOutput referenceBranch executableBranch
      referenceBranches executableBranches head tail outputSupport headSupport
      tailSupport =>
      simpa [substCompiledBranches] using SuperposeBranchesAgree.cons
        (SuperposeBranchAgrees.subst_of_supported variableState typeChecks
          headSupport)
        (SuperposeBranchesAgree.subst_of_supported variableState typeChecks
          tailSupport)

/-- Literal-only alternatives use the same indexed support discipline. -/
theorem LiteralAmbBranchesAgree.subst_of_supported
    {referenceBinding : Substitution} {executableBinding : Subst}
    {termDomain typeDomain : List LogicVar}
    (variableState :
      VariableStateAgreesOn referenceBinding executableBinding termDomain)
    (_typeChecks :
      TypeCheckSubstitutionAgrees referenceBinding executableBinding
        typeDomain)
    {referenceOutput : Term} {executableOutput : Atom}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List (Atom × List PLeaTTa.Goal)}
    {agreement : LiteralAmbBranchesAgree referenceOutput executableOutput
      references executables}
    (supported : LiteralAmbBranchesAgreeSupported termDomain typeDomain
      agreement) :
    LiteralAmbBranchesAgree (referenceBinding.applyTerm referenceOutput)
      (subst executableBinding executableOutput)
      (referenceBinding.applyGoals references)
      (substCompiledBranches executableBinding executables) := by
  exact
    PLeaTTa.CompilerSubstitutionAdequacy.LiteralAmbBranchesAgree.subst_of_variableStateOn
      variableState agreement supported.output_variables
        supported.goal_variables

/-- Ordered flattened goal lists transport constructor by constructor. -/
theorem GoalsAgree.subst_of_supported
    {referenceBinding : Substitution} {executableBinding : Subst}
    {termDomain typeDomain : List LogicVar}
    (variableState :
      VariableStateAgreesOn referenceBinding executableBinding termDomain)
    (typeChecks :
      TypeCheckSubstitutionAgrees referenceBinding executableBinding
        typeDomain)
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    {agreement : GoalsAgree references executables}
    (supported : GoalsAgreeSupported termDomain typeDomain agreement) :
    GoalsAgree (referenceBinding.applyGoals references)
      (substCompiledGoals executableBinding executables) := by
  cases supported with
  | nil => simpa [substCompiledGoals] using GoalsAgree.nil
  | cons headSupport tailSupport =>
      simpa [substCompiledGoals] using GoalsAgree.cons
        (GoalAgrees.subst_of_supported variableState typeChecks headSupport)
        (GoalsAgree.subst_of_supported variableState typeChecks tailSupport)
  | conjunction blockSupport tailSupport =>
      simpa [substCompiledGoals] using GoalsAgree.conjunction
        (GoalsAgree.subst_of_supported variableState typeChecks blockSupport)
        (GoalsAgree.subst_of_supported variableState typeChecks tailSupport)

end

/-! ## Ordered alias-finalization composition -/

/-- A supported ordered branch collection reconstructs the complete public
`amb` agreement after paired alias substitution.  Unlike the earlier
syntax-only theorem, this statement covers hidden executable fields and uses
a separate alias-disjoint domain for type-check carry templates. -/
theorem SuperposeBranchesAgree.finalizedGoalAgrees_of_supported
    {referenceBinding : Substitution} {executableBinding : Subst}
    {termDomain typeDomain : List LogicVar}
    (variableState :
      VariableStateAgreesOn referenceBinding executableBinding termDomain)
    (typeChecks :
      TypeCheckSubstitutionAgrees referenceBinding executableBinding
        typeDomain)
    {referenceOutput : Term} {executableOutput : Atom}
    {referenceBranches : List PeTTaSpec.PrologCore.Goal}
    {executableBranches : List (Atom × List PLeaTTa.Goal)}
    (agreement : SuperposeBranchesAgree referenceOutput executableOutput
      referenceBranches executableBranches)
    (supported : SuperposeBranchesAgreeSupported termDomain typeDomain
      agreement) :
    GoalAgrees
      (referenceBinding.applyGoal (.disjunction referenceBranches))
      (substCompiledGoal executableBinding
        (.amb executableBranches executableOutput)) := by
  have branches := SuperposeBranchesAgree.subst_of_supported variableState
    typeChecks supported
  simpa [substCompiledGoal] using GoalAgrees.builtAmb branches

/-- Restrict finite executable-name injectivity to a listed subdomain. -/
theorem encodingInjectiveOn_of_subset
    {smaller larger : List LogicVar}
    (subset : ∀ identity, identity ∈ smaller → identity ∈ larger)
    (injective : EncodingInjectiveOn larger) :
    EncodingInjectiveOn smaller := by
  intro left right leftMember rightMember sameName
  exact injective (subset left leftMember) (subset right rightMember) sameName

/-- Complete ordered superpose traversal through alias resolution and final
public `amb` reconstruction.  `termDomain` supports ordinary continuation
terms and may contain emitted alias sources.  `typeDomain` supports only the
specialized carry templates and must avoid those sources.  The theorem
returns the exact branch-agreement proof and its support certificate together
with the final substituted `GoalAgrees`, so neither order nor multiplicity is
hidden by the composition.

The remaining `branchSupport` premise is deliberately source-facing: later
compiler freshness/support lemmas must discharge it from the independent
translation derivation.  It is not defined by compiler success or by the
conclusion below.  Although it quantifies over agreeing executable branch
lists, every support leaf is a finite membership fact about the fixed
reference syntax; the executable list is only an agreement index. -/
theorem compileSuperposeBranches_alias_supported_finalization_sound
    {state : TranslatorState} (env : CEnv)
    (envAgreement : EnvAgrees state env)
    {outputIndex counter nextCounter : Nat} {sources : List Atom}
    {referenceAliases referenceBranches :
      List PeTTaSpec.PrologCore.Goal}
    {termDomain typeDomain : List LogicVar}
    (native : TranslatesSuperposeBranches state
      (.variable (.generated outputIndex)) counter sources referenceAliases
      referenceBranches nextCounter)
    (aliasSafety :
      ∀ {aliasSources aliasNames executableAliases},
        AliasLedgerAgrees (.generated outputIndex) s!"_q{outputIndex}"
          aliasSources aliasNames referenceAliases executableAliases →
        EncodingInjectiveOn
            (.generated outputIndex ::
              (aliasSources ++ (termDomain ++ typeDomain))) ∧
          AliasDomainAvoids (.generated outputIndex) aliasSources typeDomain)
    (branchSupport :
      ∀ {executableBranches}
        (agreement : SuperposeBranchesAgree
          (.variable (.generated outputIndex))
          (.var s!"_q{outputIndex}") referenceBranches executableBranches),
        SuperposeBranchesAgreeSupported termDomain typeDomain agreement) :
    ∃ baseFuel,
      0 < baseFuel ∧
      baseFuel < 8 * ((sources.map Atom.size).sum + 1) ∧
      ∀ extraFuel accumulator,
        ∃ rawBranches aliasSources aliasNames executableAliases
            executableBranches referenceBinding executableBinding
            referenceSeen executableSeen,
          ∃ branchesAgreement : SuperposeBranchesAgree
              (.variable (.generated outputIndex))
              (.var s!"_q{outputIndex}") referenceBranches
              executableBranches,
          List.foldlM
            (fun (acc : List (Atom × List PLeaTTa.Goal) × Nat)
                expression => do
              let (term, goals, next) ←
                compileExprFuel (baseFuel + extraFuel) env acc.2 expression
              .ok (acc.1 ++ [(term, goals)], next))
            (accumulator, counter) sources =
              .ok (accumulator ++ rawBranches, nextCounter) ∧
          compileSuperposeBranches (.var s!"_q{outputIndex}") rawBranches =
            (executableAliases, executableBranches) ∧
          ResolvedAliasStateOn (.generated outputIndex) s!"_q{outputIndex}"
            aliasSources aliasNames referenceAliases executableAliases
            termDomain referenceBinding executableBinding referenceSeen
            executableSeen ∧
          TypeCheckSubstitutionAgrees referenceBinding executableBinding
            typeDomain ∧
          SuperposeBranchesAgreeSupported termDomain typeDomain
            branchesAgreement ∧
          GoalAgrees
            (referenceBinding.applyGoal (.disjunction referenceBranches))
            (substCompiledGoal executableBinding
              (.amb executableBranches (.var s!"_q{outputIndex}"))) := by
  obtain ⟨baseFuel, positive, bounded, compiles⟩ :=
    compileSuperposeBranchesFuel_initial_sound env envAgreement native
  refine ⟨baseFuel, positive, bounded, ?_⟩
  intro extraFuel accumulator
  obtain ⟨rawBranches, aliasSources, aliasNames, executableAliases,
      executableBranches, compiled, normalized, aliasLedger,
      branchesAgreement⟩ := compiles extraFuel accumulator
  obtain ⟨combinedInjective, typeAvoids⟩ := aliasSafety aliasLedger
  have termSubset : ∀ identity,
      identity ∈ .generated outputIndex :: (aliasSources ++ termDomain) →
      identity ∈ .generated outputIndex ::
        (aliasSources ++ (termDomain ++ typeDomain)) := by
    intro identity member
    simp only [List.mem_cons, List.mem_append] at member ⊢
    aesop
  have typeSubset : ∀ identity,
      identity ∈ .generated outputIndex :: (aliasSources ++ typeDomain) →
      identity ∈ .generated outputIndex ::
        (aliasSources ++ (termDomain ++ typeDomain)) := by
    intro identity member
    simp only [List.mem_cons, List.mem_append] at member ⊢
    aesop
  have termInjective : EncodingInjectiveOn
      (.generated outputIndex :: (aliasSources ++ termDomain)) :=
    encodingInjectiveOn_of_subset termSubset combinedInjective
  have typeInjective : EncodingInjectiveOn
      (.generated outputIndex :: (aliasSources ++ typeDomain)) :=
    encodingInjectiveOn_of_subset typeSubset combinedInjective
  obtain ⟨referenceBinding, executableBinding, referenceSeen,
      executableSeen, resolved⟩ :=
    AliasLedgerAgrees.resolveStateOn aliasLedger
      (.generatedVariable outputIndex) termInjective
  have typeChecks : TypeCheckSubstitutionAgrees referenceBinding
      executableBinding typeDomain :=
    PLeaTTa.CompilerSubstitutionAdequacy.ResolvedAliasStateOn.typeCheckSubstitutionAgreesOn
      resolved typeInjective typeAvoids
  have supported := branchSupport branchesAgreement
  have finalized :=
    PLeaTTa.CompilerGoalSubstitutionAdequacy.SuperposeBranchesAgree.finalizedGoalAgrees_of_supported
      resolved.variableState typeChecks branchesAgreement supported
  exact ⟨rawBranches, aliasSources, aliasNames, executableAliases,
    executableBranches, referenceBinding, executableBinding, referenceSeen,
    executableSeen, branchesAgreement, compiled, normalized, resolved,
    typeChecks, supported, finalized⟩

/-- A domain containing an emitted alias source cannot satisfy the
type-template avoidance premise unless that source is the shared target.
This is the concrete reason ordinary continuation support and type-template
support may not be conflated. -/
theorem aliasDomainAvoids_rejects_distinct_source
    {target source : LogicVar} {sources domain : List LogicVar}
    (distinct : source ≠ target) (sourceMember : source ∈ sources)
    (domainMember : source ∈ domain) :
    ¬ AliasDomainAvoids target sources domain := by
  intro avoids
  rcases avoids source domainMember with same | absent
  · exact distinct same
  · exact absent sourceMember

/-! ## Split-domain witnesses -/

/-- A concrete nonempty variable-valued branch whose generated result occurs
in its continuation goal. -/
def splitDomainReferenceGoals : List PeTTaSpec.PrologCore.Goal :=
  [.unify (.variable (.generated 1)) (.integer 7)]

/-- Executable counterpart of `splitDomainReferenceGoals`. -/
def splitDomainExecutableGoals : List PLeaTTa.Goal :=
  [.eq (.var s!"_q{1}") (.gnd (.int 7))]

/-- The concrete continuation goals agree in their original order. -/
def splitDomainGoalsAgree :
    GoalsAgree splitDomainReferenceGoals splitDomainExecutableGoals :=
  .cons (.unify (.generatedVariable 1) (.integer 7)) .nil

/-- Concrete normalized aliased branch: `_q1` is shared with `_q0` at
translation time while remaining present in the branch continuation. -/
def splitDomainBranchAgrees :
    SuperposeBranchAgrees (.variable (.generated 0)) (.var s!"_q{0}")
      (.conjunction splitDomainReferenceGoals)
      (.var s!"_q{0}", splitDomainExecutableGoals) :=
  .aliased (.generatedVariable 0) splitDomainGoalsAgree (by
    simp [splitDomainExecutableGoals])

/-- The aliased continuation is genuinely supported when ordinary terms use
the continuation domain and the branch has no type-check carry templates. -/
theorem splitDomainBranch_supported :
    SuperposeBranchAgreesSupported [.generated 0, .generated 1] []
      splitDomainBranchAgrees := by
  let output : TermAgrees (.variable (.generated 0)) (.var s!"_q{0}") :=
    .generatedVariable 0
  let goals : GoalsAgree splitDomainReferenceGoals
      splitDomainExecutableGoals := splitDomainGoalsAgree
  have nonempty : splitDomainExecutableGoals ≠ [] := by
    simp [splitDomainExecutableGoals]
  have outputSupport :
      TermAgreesSupported [.generated 0, .generated 1] output := by
    simp [TermAgreesSupported, termVariablesIn]
  have leftSupport :
      TermAgreesSupported [.generated 0, .generated 1]
        (TermAgrees.generatedVariable 1) := by
    simp [TermAgreesSupported, termVariablesIn]
  have rightSupport :
      TermAgreesSupported [.generated 0, .generated 1]
        (TermAgrees.integer 7) := by
    simp [TermAgreesSupported, termVariablesIn]
  have goalsSupport :
      GoalsAgreeSupported [.generated 0, .generated 1] [] goals := by
    unfold goals splitDomainGoalsAgree
    exact .cons (.unify leftSupport rightSupport) .nil
  exact @SuperposeBranchAgreesSupported.aliased
    [.generated 0, .generated 1] []
    (.variable (.generated 0)) (.var s!"_q{0}")
    splitDomainReferenceGoals splitDomainExecutableGoals output goals
    nonempty outputSupport goalsSupport

/-- Reusing that continuation domain as the type-template domain is
impossible: it contains the distinct emitted alias source. -/
theorem splitDomain_same_type_domain_rejected :
    ¬ AliasDomainAvoids (.generated 0) [.generated 1]
      [.generated 0, .generated 1] := by
  exact aliasDomainAvoids_rejects_distinct_source
    (target := .generated 0) (source := .generated 1)
    (sources := [.generated 1])
    (domain := [.generated 0, .generated 1])
    (by decide) (by simp) (by simp)

end PLeaTTa.CompilerGoalSubstitutionAdequacy
