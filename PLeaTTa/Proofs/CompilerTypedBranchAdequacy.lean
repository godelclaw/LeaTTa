-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.CompilerTypedBranchAdequacy
Purpose: Relate branch-local typed dispatch to the independent pinned-PeTTa
  translation judgments.
Trusted boundary: none
Main exports: compileFreshTypedArgs_sound, compileFreshTypedArgs_complete,
  compileTypedDispatchBranches_sound, compileTypedDispatchBranches_complete
-/
import PLeaTTa.Proofs.CompilerAdequacy
import PLeaTTa.Proofs.CompilerTypeFreshening

namespace PLeaTTa.CompilerTypedBranchAdequacy

open Metta (Atom)
open PLeaTTa.PeTTaSpec.PrologCore
open PLeaTTa.CompilerAdequacy
open PLeaTTa.CompilerTypeFreshening

/-- Independent atomic type freshening agrees with executable substitution.
The variable case consumes the exact first-occurrence lookup law rather than
reopening `mapIdx` and counter arithmetic. -/
theorem freshensTypeAtom_sound {sourceChain : List Atom} {counter : Nat}
    {source : Atom} {reference : Term}
    (derivation : FreshensTypeAtom sourceChain counter source reference) :
    TermAgrees reference
      (Metta.Subst.apply (compilerTypeFresheningSubst counter sourceChain)
        source) := by
  cases derivation with
  | symbol name notTrue notFalse =>
      simpa [Metta.Subst.apply] using TermAgrees.atom notTrue notFalse
  | «variable» name member =>
      have executableMember : name ∈ compilerTypeVarNames sourceChain := by
        simpa [typeChainVariables, compilerTypeVarNames] using member
      have lookup := compilerTypeFresheningSubst_lookup_idxOf
        (counter := counter) executableMember
      simpa [Metta.Subst.apply, lookup, typeChainVariables,
        compilerTypeVarNames, compilerGeneratedName] using
        (TermAgrees.generatedVariable
          (counter + List.idxOf name (typeChainVariables sourceChain)))

/-- Ordered freshening agreement is pointwise. -/
theorem freshensTypeAtoms_sound {sourceChain : List Atom} {counter : Nat}
    {sources : List Atom} {references : List Term}
    (derivation : FreshensTypeAtoms sourceChain counter sources references) :
    TermsAgree references
      (sources.map (Metta.Subst.apply
        (compilerTypeFresheningSubst counter sourceChain))) := by
  induction derivation with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      exact .cons (freshensTypeAtom_sound head) inductionHypothesis

/-- One independent branch-local fresh copy agrees with the executable copy,
including its exact next counter. -/
theorem freshensTypeChain_sound {counter nextCounter : Nat}
    {sourceChain : List Atom} {referenceChain : List Term}
    (derivation : FreshensTypeChain counter sourceChain referenceChain
      nextCounter) :
    TermsAgree referenceChain (freshenTypeChain counter sourceChain).1 ∧
      nextCounter = (freshenTypeChain counter sourceChain).2 := by
  cases derivation with
  | freshened atoms =>
      exact ⟨freshensTypeAtoms_sound atoms, rfl⟩

/-- Freshened atomic types determine the exact executable soft-cut carry
template. Open type variables are carried; closed symbol types use `#u`. -/
theorem freshensTypeAtom_expected_agrees {sourceChain : List Atom}
    {counter : Nat} {source : Atom} {reference : Term}
    (derivation : FreshensTypeAtom sourceChain counter source reference) :
    let executable := Metta.Subst.apply
      (compilerTypeFresheningSubst counter sourceChain) source
    TypeCheckExpectedAgrees reference executable
      (typeCheckBindingTemplate executable) := by
  cases derivation with
  | symbol name notTrue notFalse =>
      simpa [Metta.Subst.apply] using
        (TypeCheckExpectedAgrees.atom notTrue notFalse)
  | «variable» name member =>
      have executableMember : name ∈ compilerTypeVarNames sourceChain := by
        simpa [typeChainVariables, compilerTypeVarNames] using member
      have lookup := compilerTypeFresheningSubst_lookup_idxOf
        (counter := counter) executableMember
      simpa [Metta.Subst.apply, lookup, typeChainVariables,
        compilerTypeVarNames, compilerGeneratedName,
        typeCheckBindingTemplate, bindingTemplate, Atom.vars,
        List.eraseDups_cons] using
        (TypeCheckExpectedAgrees.generated
          (counter + List.idxOf name (typeChainVariables sourceChain)))

/-- Pointwise agreement for a complete branch-local arrow chain.  This is
stronger than ordinary `TermsAgree`: every expected type also determines the
exact soft-cut carry template needed if that position is checked. -/
inductive TypedChainAgrees : List Term → List Atom → Prop where
  | nil : TypedChainAgrees [] []
  | cons {reference : Term} {executable : Atom}
      {references : List Term} {executables : List Atom}
      (head : TypeCheckExpectedAgrees reference executable
        (typeCheckBindingTemplate executable))
      (tail : TypedChainAgrees references executables) :
      TypedChainAgrees (reference :: references) (executable :: executables)

/-- Typed-chain agreement forgets to ordinary ordered term agreement. -/
theorem TypedChainAgrees.terms {references : List Term}
    {executables : List Atom}
    (agreement : TypedChainAgrees references executables) :
    TermsAgree references executables := by
  induction agreement with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      exact .cons head.term inductionHypothesis

/-- Splitting the independent final result type splits the executable chain
at the same position and retains the stronger expected-type relation. -/
theorem TypedChainAgrees.unsnoc {initial : List Term} {last : Term}
    {executables : List Atom}
    (agreement : TypedChainAgrees (initial ++ [last]) executables) :
    ∃ executableInitial executableLast,
      executables = executableInitial ++ [executableLast] ∧
      TypedChainAgrees initial executableInitial ∧
      TypeCheckExpectedAgrees last executableLast
        (typeCheckBindingTemplate executableLast) := by
  induction initial generalizing executables with
  | nil =>
      cases agreement with
      | cons head tail =>
          cases tail
          exact ⟨[], _, rfl, .nil, head⟩
  | cons _ _ inductionHypothesis =>
      cases agreement with
      | cons head tail =>
          obtain ⟨executableInitial, executableLast, equality,
            initialAgreement, lastAgreement⟩ := inductionHypothesis tail
          subst equality
          exact ⟨_ :: executableInitial, executableLast, rfl,
            .cons head initialAgreement, lastAgreement⟩

/-- An independently atomic expected type determines the same executable
symbol.  This inversion avoids dependent case-splitting on the carry template. -/
theorem typeCheckExpectedAtom_executable {name : String}
    {executable template : Atom}
    (agreement : TypeCheckExpectedAgrees (.atom name) executable template) :
    executable = .sym name := by
  cases agreement
  rfl

/-- The exact expected-type relation is inherited pointwise from independent
freshening; no second traversal or name calculation is required. -/
theorem freshensTypeAtoms_typedChain_sound {sourceChain : List Atom}
    {counter : Nat} {sources : List Atom} {references : List Term}
    (derivation : FreshensTypeAtoms sourceChain counter sources references) :
    TypedChainAgrees references
      (sources.map (Metta.Subst.apply
        (compilerTypeFresheningSubst counter sourceChain))) := by
  induction derivation with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      exact .cons (freshensTypeAtom_expected_agrees head) inductionHypothesis

/-- Strong fresh-chain soundness retaining each expected type's carry
template as well as the exact next counter. -/
theorem freshensTypeChain_typedChain_sound {counter nextCounter : Nat}
    {sourceChain : List Atom} {referenceChain : List Term}
    (derivation : FreshensTypeChain counter sourceChain referenceChain
      nextCounter) :
    TypedChainAgrees referenceChain (freshenTypeChain counter sourceChain).1 ∧
      nextCounter = (freshenTypeChain counter sourceChain).2 := by
  cases derivation with
  | freshened atoms =>
      exact ⟨freshensTypeAtoms_typedChain_sound atoms, rfl⟩

/-- Independent and executable arity decisions construct agreeing complete
calls or agreeing first-class partial values. -/
theorem buildsCallOrPartial_sound
    {registry : FunctionRegistry} {env : CEnv}
    (registryAgreement : FunctionRegistryAgrees registry env)
    {head : String} {referenceTerms : List Term}
    {executableTerms : List Atom} {referenceShared : Term}
    {executableShared : Atom} {referenceBranch : Term}
    {referenceGoals : List PeTTaSpec.PrologCore.Goal}
    (termsAgreement : TermsAgree referenceTerms executableTerms)
    (sharedAgreement : TermAgrees referenceShared executableShared)
    (derivation : BuildsCallOrPartial registry head referenceTerms
      referenceShared referenceBranch referenceGoals) :
    let executable := compileTypedCallOrPartial (env.arities head)
      executableShared head executableTerms
    TermAgrees referenceBranch executable.1 ∧
      GoalsAgree referenceGoals executable.2 := by
  cases derivation with
  | complete accepted =>
      have executableAccepted : executableTerms.length ∈ env.arities head := by
        have acceptedAtReference :=
          (registryAgreement.arity head referenceTerms.length).mp accepted
        simpa [termsAgreement.length_eq] using acceptedAtReference
      simp only [compileTypedCallOrPartial_complete _ _ _ _
        executableAccepted]
      exact ⟨sharedAgreement,
        .cons (.definedCall termsAgreement sharedAgreement) .nil⟩
  | incomplete rejected =>
      have executableRejected : executableTerms.length ∉ env.arities head := by
        intro executableAccepted
        apply rejected
        apply (registryAgreement.arity head referenceTerms.length).mpr
        simpa [termsAgreement.length_eq] using executableAccepted
      simp only [compileTypedCallOrPartial_partial _ _ _ _
        executableRejected]
      exact ⟨by
        simpa [partialValue] using
          (TermAgrees.partialValue termsAgreement.properList), .nil⟩

/-- A checked independent input type selects the executable checked branch. -/
theorem typeCheckExpectedAgrees_input_required
    {reference : Term} {executable template : Atom}
    (agreement : TypeCheckExpectedAgrees reference executable template)
    (checked : CheckedInputType reference) :
    typeRequiresCheck executable = true := by
  cases agreement with
  | atom _ _ =>
      rcases checked with ⟨notUndefined, notAtom, notExpression⟩
      have nameNotUndefined : _ := fun equal =>
        notUndefined (congrArg Term.atom equal)
      have nameNotAtom : _ := fun equal =>
        notAtom (congrArg Term.atom equal)
      have nameNotExpression : _ := fun equal =>
        notExpression (congrArg Term.atom equal)
      simp only [typeRequiresCheck, Bool.and_eq_true, bne_iff_ne]
      exact ⟨⟨nameNotUndefined, nameNotAtom⟩, nameNotExpression⟩
  | generated _ => rfl

/-- A checked input can never select the staged-`Expression` argument branch. -/
theorem typeCheckExpectedAgrees_not_expression
    {reference : Term} {executable template : Atom}
    (agreement : TypeCheckExpectedAgrees reference executable template)
    (checked : CheckedInputType reference) :
    (executable == (.sym "Expression" : Atom)) = false := by
  cases agreement with
  | atom _ _ =>
      rcases checked with ⟨_, _, notExpression⟩
      have nameNotExpression : _ := fun equal =>
        notExpression (congrArg Term.atom equal)
      change (_ == "Expression") = false
      exact beq_eq_false_iff_ne.mpr nameNotExpression
  | generated _ => rfl

/-- A checked independent result type selects the executable checked branch. -/
theorem typeCheckExpectedAgrees_result_required
    {reference : Term} {executable template : Atom}
    (agreement : TypeCheckExpectedAgrees reference executable template)
    (checked : CheckedResultType reference) :
    resultTypeRequiresCheck executable = true := by
  cases agreement with
  | atom _ _ =>
      rcases checked with ⟨notUndefined, notAtom⟩
      have nameNotUndefined : _ := fun equal =>
        notUndefined (congrArg Term.atom equal)
      have nameNotAtom : _ := fun equal =>
        notAtom (congrArg Term.atom equal)
      simp only [resultTypeRequiresCheck, Bool.and_eq_true, bne_iff_ne]
      exact ⟨nameNotUndefined, nameNotAtom⟩
  | generated _ => rfl

/-- The shared executable type-check constructor preserves the independent
soft-cut, including an open expected-type binding, and consumes two names. -/
theorem compileTypeCheckWhen_sound
    {referenceValue referenceExpected : Term}
    {executableValue executableExpected executableTemplate : Atom}
    (valueAgreement : TermAgrees referenceValue executableValue)
    (expectedAgreement : TypeCheckExpectedAgrees referenceExpected
      executableExpected executableTemplate)
    (templateEq : executableTemplate =
      typeCheckBindingTemplate executableExpected)
    (counter : Nat) :
    GoalsAgree (typedTypeCheckGoals referenceValue referenceExpected counter)
        (compileTypeCheckWhen true executableValue executableExpected counter).1 ∧
      (compileTypeCheckWhen true executableValue executableExpected counter).2 =
        counter + 2 := by
  subst executableTemplate
  let directReference := Term.variable (.generated counter)
  let directExecutable := Atom.var s!"_q{counter}"
  let metaReference := Term.variable (.generated (counter + 1))
  let metaExecutable := Atom.var s!"_q{counter + 1}"
  have directAgreement : TermAgrees directReference directExecutable := by
    exact .generatedVariable counter
  have metaAgreement : TermAgrees metaReference metaExecutable := by
    exact .generatedVariable (counter + 1)
  constructor
  · simpa [typedTypeCheckGoals, compileTypeCheckWhen, fresh,
      directReference, directExecutable, metaReference, metaExecutable] using
      GoalsAgree.cons
        (GoalAgrees.typeCheckSoftCut valueAgreement expectedAgreement
          directAgreement metaAgreement)
        GoalsAgree.nil
  · rfl

/-- General checked-input soundness, including branch-local type variables. -/
theorem compileTypeCheck_open_sound
    {referenceValue referenceExpected : Term}
    {executableValue executableExpected executableTemplate : Atom}
    (valueAgreement : TermAgrees referenceValue executableValue)
    (expectedAgreement : TypeCheckExpectedAgrees referenceExpected
      executableExpected executableTemplate)
    (templateEq : executableTemplate =
      typeCheckBindingTemplate executableExpected)
    (counter : Nat) (checked : CheckedInputType referenceExpected) :
    GoalsAgree (typedTypeCheckGoals referenceValue referenceExpected counter)
        (compileTypeCheck executableValue executableExpected counter).1 ∧
      (compileTypeCheck executableValue executableExpected counter).2 =
        counter + 2 := by
  rw [compileTypeCheck]
  rw [typeCheckExpectedAgrees_input_required expectedAgreement checked]
  exact compileTypeCheckWhen_sound valueAgreement expectedAgreement templateEq
    counter

/-- General checked-result soundness, including branch-local type variables. -/
theorem compileResultTypeCheck_open_sound
    {referenceValue referenceExpected : Term}
    {executableValue executableExpected executableTemplate : Atom}
    (valueAgreement : TermAgrees referenceValue executableValue)
    (expectedAgreement : TypeCheckExpectedAgrees referenceExpected
      executableExpected executableTemplate)
    (templateEq : executableTemplate =
      typeCheckBindingTemplate executableExpected)
    (counter : Nat) (checked : CheckedResultType referenceExpected) :
    GoalsAgree (typedTypeCheckGoals referenceValue referenceExpected counter)
        (compileResultTypeCheck executableValue executableExpected counter).1 ∧
      (compileResultTypeCheck executableValue executableExpected counter).2 =
        counter + 2 := by
  rw [compileResultTypeCheck]
  rw [typeCheckExpectedAgrees_result_required expectedAgreement checked]
  exact compileTypeCheckWhen_sound valueAgreement expectedAgreement templateEq
    counter

/-- A stable, fixed-result expression-compilation certificate.  Existing
soundness stated `∀ fuel, ∃ result`; fuel monotonicity strengthens it to one
canonical result reused at every larger budget. -/
def ExprFuelCertificate (env : CEnv) (counter : Nat) (source : Atom)
    (reference : Term) (referenceGoals : List PeTTaSpec.PrologCore.Goal)
    (nextCounter : Nat) : Prop :=
  ∃ baseFuel internal executableGoals,
    0 < baseFuel ∧ baseFuel < 8 * source.size ∧
    (∀ extraFuel,
      compileExprFuel (baseFuel + extraFuel) env counter source =
        .ok (internal, executableGoals, nextCounter)) ∧
    TermAgrees reference internal ∧
    GoalsAgree referenceGoals executableGoals

/-- Package an independent expression derivation into its stable certificate. -/
theorem exprFuelCertificate_of_translation {state : TranslatorState}
    (env : CEnv) (stateAgreement : EnvAgrees state env) {counter : Nat}
    {source : Atom} {reference : Term}
    {referenceGoals : List PeTTaSpec.PrologCore.Goal} {nextCounter : Nat}
    (translation : TranslatesExpr state counter source reference referenceGoals
      nextCounter) :
    ExprFuelCertificate env counter source reference referenceGoals
      nextCounter := by
  obtain ⟨baseFuel, positive, bounded, compiles⟩ :=
    compileExprFuel_initial_sound env stateAgreement translation
  obtain ⟨internal, executableGoals, compiled, termAgreement,
    goalsAgreement⟩ := compiles 0
  have baseCompiled : compileExprFuel baseFuel env counter source =
      .ok (internal, executableGoals, nextCounter) := by
    simpa using compiled
  exact ⟨baseFuel, internal, executableGoals, positive, bounded,
    fun extraFuel => compileExprFuel_mono baseFuel extraFuel env counter source
      internal executableGoals nextCounter baseCompiled,
    termAgreement, goalsAgreement⟩

/-- Stable exact typed-argument traversal certificate.  Besides removing
fuel bookkeeping from consumers, it preserves the ordered fixed output that
branch assembly needs. -/
def TypedArgsFuelCertificate (env : CEnv) (counter : Nat)
    (sources executableTypes : List Atom) (references : List Term)
    (referenceGoals : List PeTTaSpec.PrologCore.Goal)
    (nextCounter : Nat) : Prop :=
  ∃ baseFuel internals executableGoals,
    0 < baseFuel ∧
    baseFuel < 16 * ((sources.map Atom.size).sum + 1) ∧
    (∀ extraFuel,
      compileTypedArgsFuel (baseFuel + extraFuel) env counter sources
        executableTypes = .ok (internals, executableGoals, nextCounter)) ∧
    TermsAgree references internals ∧
    GoalsAgree referenceGoals executableGoals

/-- Empty source traversal ignores surplus declared parameter types. -/
theorem typedArgsFuelCertificate_nil (env : CEnv) (counter : Nat)
    (executableTypes : List Atom) :
    TypedArgsFuelCertificate env counter [] executableTypes [] [] counter := by
  refine ⟨1, [], [], by omega, by simp, ?_, .nil, .nil⟩
  intro extraFuel
  cases executableTypes with
  | nil =>
      simpa [Nat.add_comm] using
        compileTypedArgsFuel_nil_eq extraFuel env counter
  | cons ty types =>
      simpa [Nat.add_comm] using
        compileTypedArgsFuel_surplus_type_eq extraFuel env counter ty types

/-- Reusable expression-staging step for exact typed traversal.  Consumers
provide one stable tail computation; the lemma owns successor-fuel alignment
and the executable constructor equation. -/
theorem compileTypedArgsFuel_expression_compose
    (env : CEnv) {tailFuel counter : Nat}
    {source : Atom} {sources types : List Atom}
    {terms : List Atom} {tailGoals : List PLeaTTa.Goal}
    {nextCounter : Nat}
    (tailCompiles : ∀ extraFuel,
      compileTypedArgsFuel (tailFuel + extraFuel) env counter sources types =
        .ok (terms, tailGoals, nextCounter)) :
    ∀ extraFuel,
      compileTypedArgsFuel (tailFuel + 1 + extraFuel) env counter
          (source :: sources) (.sym "Expression" :: types) =
        .ok (chainify source :: terms, tailGoals, nextCounter) := by
  intro extraFuel
  rw [show tailFuel + 1 + extraFuel =
    (tailFuel + extraFuel) + 1 by omega]
  rw [compileTypedArgsFuel_expression_eq]
  rw [tailCompiles]
  rfl

/-- Reusable evaluated-argument step.  It aligns two independently sufficient
fuel thresholds, inserts one already-proved type check, threads the exact
counter, and preserves left-to-right goal concatenation.  Checked and
unchecked typed cases instantiate this same law. -/
theorem compileTypedArgsFuel_evaluated_compose
    (env : CEnv) {headFuel tailFuel counter : Nat}
    {source ty : Atom} {sources types : List Atom}
    {term : Atom} {headGoals checkGoals : List PLeaTTa.Goal}
    {middleCounter checkedCounter : Nat}
    {terms : List Atom} {tailGoals : List PLeaTTa.Goal}
    {nextCounter : Nat}
    (notExpression : (ty == .sym "Expression") = false)
    (headCompiles : ∀ extraFuel,
      compileExprFuel (headFuel + extraFuel) env counter source =
        .ok (term, headGoals, middleCounter))
    (checkEq : compileTypeCheck term ty middleCounter =
      (checkGoals, checkedCounter))
    (tailCompiles : ∀ extraFuel,
      compileTypedArgsFuel (tailFuel + extraFuel) env checkedCounter sources
        types = .ok (terms, tailGoals, nextCounter)) :
    ∀ extraFuel,
      compileTypedArgsFuel (max headFuel tailFuel + 1 + extraFuel) env counter
          (source :: sources) (ty :: types) =
        .ok (term :: terms, headGoals ++ checkGoals ++ tailGoals,
          nextCounter) := by
  intro extraFuel
  let childFuel := max headFuel tailFuel
  have headLe : headFuel ≤ childFuel := Nat.le_max_left _ _
  have tailLe : tailFuel ≤ childFuel := Nat.le_max_right _ _
  have headFuelEq :
      headFuel + (childFuel + extraFuel - headFuel) =
        childFuel + extraFuel := by omega
  have tailFuelEq :
      tailFuel + (childFuel + extraFuel - tailFuel) =
        childFuel + extraFuel := by omega
  have headCompiled := headCompiles (childFuel + extraFuel - headFuel)
  have tailCompiled := tailCompiles (childFuel + extraFuel - tailFuel)
  rw [headFuelEq] at headCompiled
  rw [tailFuelEq] at tailCompiled
  rw [show max headFuel tailFuel + 1 + extraFuel =
    (childFuel + extraFuel) + 1 by omega]
  rw [compileTypedArgsFuel_evaluated_eq _ _ _ _ _ _ _ notExpression]
  rw [headCompiled]
  dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind]
  rw [checkEq]
  dsimp only
  rw [tailCompiled]
  rfl

/-- Certificate constructor for one staged `Expression` argument. -/
theorem typedArgsFuelCertificate_expression (env : CEnv)
    {counter : Nat} {source : Atom} {sources executableTypes : List Atom}
    {reference : Term} {references : List Term}
    {referenceGoals : List PeTTaSpec.PrologCore.Goal} {nextCounter : Nat}
    (quoted : Quotes source reference)
    (tail : TypedArgsFuelCertificate env counter sources executableTypes
      references referenceGoals nextCounter) :
    TypedArgsFuelCertificate env counter (source :: sources)
      (.sym "Expression" :: executableTypes) (reference :: references)
      referenceGoals nextCounter := by
  rcases tail with ⟨tailFuel, tailInternals, tailExecutableGoals,
    tailPositive, tailBounded, tailCompiles, tailTerms, tailGoals⟩
  refine ⟨tailFuel + 1, chainify source :: tailInternals,
    tailExecutableGoals, by omega, ?_,
    compileTypedArgsFuel_expression_compose env tailCompiles,
    .cons (quotes_term_agrees quoted) tailTerms, tailGoals⟩
  have sourcePositive := atom_size_positive_for_compiler source
  simp only [List.map, List.sum_cons] at tailBounded ⊢
  omega

/-- Certificate constructor shared by `%Undefined%` and `Atom` inputs. -/
theorem typedArgsFuelCertificate_unchecked (env : CEnv)
    {counter middleCounter nextCounter : Nat} {source : Atom}
    {sources executableTypes : List Atom} {expected : String}
    {reference : Term} {references : List Term}
    {headReferenceGoals tailReferenceGoals :
      List PeTTaSpec.PrologCore.Goal}
    (unchecked : expected = "%Undefined%" ∨ expected = "Atom")
    (head : ExprFuelCertificate env counter source reference
      headReferenceGoals middleCounter)
    (tail : TypedArgsFuelCertificate env middleCounter sources executableTypes
      references tailReferenceGoals nextCounter) :
    TypedArgsFuelCertificate env counter (source :: sources)
      (.sym expected :: executableTypes) (reference :: references)
      (headReferenceGoals ++ tailReferenceGoals) nextCounter := by
  rcases head with ⟨headFuel, internal, headExecutableGoals,
    headPositive, headBounded, headCompiles, termAgreement, headGoals⟩
  rcases tail with ⟨tailFuel, internals, tailExecutableGoals,
    tailPositive, tailBounded, tailCompiles, termsAgreement, tailGoals⟩
  have uncheckedMember :
      expected ∈ ["%Undefined%", "Atom", "Expression"] := by
    rcases unchecked with rfl | rfl <;> simp
  have notExpression :
      ((.sym expected : Atom) == .sym "Expression") = false := by
    rcases unchecked with rfl | rfl <;> decide
  have checkEq : compileTypeCheck internal (.sym expected) middleCounter =
      ([], middleCounter) :=
    compileTypeCheck_unchecked_symbol_eq internal middleCounter expected
      uncheckedMember
  refine ⟨max headFuel tailFuel + 1, internal :: internals,
    headExecutableGoals ++ tailExecutableGoals, by omega, ?_, ?_,
    .cons termAgreement termsAgreement,
    GoalsAgree.append headGoals tailGoals⟩
  · have sourcePositive := atom_size_positive_for_compiler source
    simp only [List.map, List.sum_cons] at tailBounded ⊢
    omega
  · simpa using compileTypedArgsFuel_evaluated_compose env notExpression
      headCompiles checkEq tailCompiles

/-- Certificate constructor for a checked input type, including an open
branch-local expected type carried through soft-cut. -/
theorem typedArgsFuelCertificate_checked (env : CEnv)
    {counter middleCounter nextCounter : Nat}
    {source expectedExecutable : Atom}
    {sources executableTypes : List Atom}
    {expectedReference reference : Term} {references : List Term}
    {headReferenceGoals tailReferenceGoals :
      List PeTTaSpec.PrologCore.Goal}
    (checked : CheckedInputType expectedReference)
    (expectedAgreement : TypeCheckExpectedAgrees expectedReference
      expectedExecutable (typeCheckBindingTemplate expectedExecutable))
    (head : ExprFuelCertificate env counter source reference
      headReferenceGoals middleCounter)
    (tail : TypedArgsFuelCertificate env (middleCounter + 2) sources
      executableTypes references tailReferenceGoals nextCounter) :
    TypedArgsFuelCertificate env counter (source :: sources)
      (expectedExecutable :: executableTypes) (reference :: references)
      (headReferenceGoals ++
        typedTypeCheckGoals reference expectedReference middleCounter ++
        tailReferenceGoals) nextCounter := by
  rcases head with ⟨headFuel, internal, headExecutableGoals,
    headPositive, headBounded, headCompiles, termAgreement, headGoals⟩
  rcases tail with ⟨tailFuel, internals, tailExecutableGoals,
    tailPositive, tailBounded, tailCompiles, termsAgreement, tailGoals⟩
  have checkSound := compileTypeCheck_open_sound termAgreement
    expectedAgreement rfl middleCounter checked
  have checkEq : compileTypeCheck internal expectedExecutable middleCounter =
      ((compileTypeCheck internal expectedExecutable middleCounter).1,
        middleCounter + 2) := by
    apply Prod.ext
    · rfl
    · exact checkSound.2
  have notExpression :=
    typeCheckExpectedAgrees_not_expression expectedAgreement checked
  refine ⟨max headFuel tailFuel + 1, internal :: internals,
    headExecutableGoals ++
      (compileTypeCheck internal expectedExecutable middleCounter).1 ++
      tailExecutableGoals, by omega, ?_, ?_,
    .cons termAgreement termsAgreement, ?_⟩
  · have sourcePositive := atom_size_positive_for_compiler source
    simp only [List.map, List.sum_cons] at tailBounded ⊢
    omega
  · exact compileTypedArgsFuel_evaluated_compose env notExpression
      headCompiles checkEq tailCompiles
  · exact GoalsAgree.append (GoalsAgree.append headGoals checkSound.1)
      tailGoals

/-- Soundness of exact typed-argument traversal against the independent
fresh-type judgment.  The proof is now constructor-level: all fuel alignment,
counter threading, check insertion, and goal concatenation live in the
certificate combinators above. -/
theorem compileFreshTypedArgsFuel_sound {state : TranslatorState}
    (env : CEnv) (stateAgreement : EnvAgrees state env) {counter : Nat}
    {sources : List Atom} {referenceTypes references : List Term}
    {referenceGoals : List PeTTaSpec.PrologCore.Goal} {nextCounter : Nat}
    (translation : TranslatesFreshTypedArgs state counter sources
      referenceTypes references referenceGoals nextCounter) :
    ∀ {executableTypes : List Atom},
      TypedChainAgrees referenceTypes executableTypes →
      TypedArgsFuelCertificate env counter sources executableTypes references
        referenceGoals nextCounter := by
  induction translation with
  | nil =>
      intro executableTypes _
      exact typedArgsFuelCertificate_nil env _ executableTypes
  | expression quoted _ inductionHypothesis =>
      intro executableTypes typeAgreement
      cases typeAgreement with
      | cons expectedAgreement tailAgreement =>
          rw [typeCheckExpectedAtom_executable expectedAgreement]
          exact typedArgsFuelCertificate_expression env quoted
            (inductionHypothesis tailAgreement)
  | undefined head _ inductionHypothesis =>
      intro executableTypes typeAgreement
      cases typeAgreement with
      | cons expectedAgreement tailAgreement =>
          rw [typeCheckExpectedAtom_executable expectedAgreement]
          exact typedArgsFuelCertificate_unchecked env (Or.inl rfl)
            (exprFuelCertificate_of_translation env stateAgreement head)
            (inductionHypothesis tailAgreement)
  | atom head _ inductionHypothesis =>
      intro executableTypes typeAgreement
      cases typeAgreement with
      | cons expectedAgreement tailAgreement =>
          rw [typeCheckExpectedAtom_executable expectedAgreement]
          exact typedArgsFuelCertificate_unchecked env (Or.inr rfl)
            (exprFuelCertificate_of_translation env stateAgreement head)
            (inductionHypothesis tailAgreement)
  | checked checkedType head _ inductionHypothesis =>
      intro executableTypes typeAgreement
      cases typeAgreement with
      | cons expectedAgreement tailAgreement =>
          exact typedArgsFuelCertificate_checked env checkedType
            expectedAgreement
            (exprFuelCertificate_of_translation env stateAgreement head)
            (inductionHypothesis tailAgreement)

/-- Public soundness of fresh exact typed traversal at the source-derived
compiler budget. -/
theorem compileFreshTypedArgs_sound {state : TranslatorState}
    (env : CEnv) (stateAgreement : EnvAgrees state env) {counter : Nat}
    {sources executableTypes : List Atom}
    {referenceTypes references : List Term}
    {referenceGoals : List PeTTaSpec.PrologCore.Goal} {nextCounter : Nat}
    (typeAgreement : TypedChainAgrees referenceTypes executableTypes)
    (translation : TranslatesFreshTypedArgs state counter sources
      referenceTypes references referenceGoals nextCounter) :
    ∃ internals executableGoals,
      compileTypedArgs env counter sources executableTypes =
        .ok (internals, executableGoals, nextCounter) ∧
      TermsAgree references internals ∧
      GoalsAgree referenceGoals executableGoals := by
  rcases compileFreshTypedArgsFuel_sound env stateAgreement translation
      typeAgreement with
    ⟨baseFuel, internals, executableGoals, positive, bounded, compiles,
      termsAgreement, goalsAgreement⟩
  have baseLe : baseFuel ≤ compilerListFuel sources + 64 := by
    simp only [compilerListFuel]
    omega
  have baseCompiled :
      compileTypedArgsFuel baseFuel env counter sources executableTypes =
        .ok (internals, executableGoals, nextCounter) := by
    simpa using compiles 0
  exact ⟨internals, executableGoals,
    by simpa [compileTypedArgs] using
      compileTypedArgsFuel_mono_of_le env counter sources executableTypes
        internals executableGoals nextCounter baseLe baseCompiled,
    termsAgreement, goalsAgreement⟩

/-- Independent support for one exact fresh typed-argument traversal.  It is
defined only by the pinned translation judgment, never compiler success. -/
def SupportedFreshTypedArgs (state : TranslatorState) (counter : Nat)
    (sources : List Atom) (referenceTypes : List Term) : Prop :=
  ∃ references referenceGoals nextCounter,
    TranslatesFreshTypedArgs state counter sources referenceTypes references
      referenceGoals nextCounter

/-- Completeness on independently supported fresh typed arguments. -/
theorem compileFreshTypedArgs_complete {state : TranslatorState}
    (env : CEnv) (stateAgreement : EnvAgrees state env) {counter : Nat}
    {sources executableTypes : List Atom} {referenceTypes : List Term}
    {internals : List Atom} {executableGoals : List PLeaTTa.Goal}
    {nextCounter : Nat}
    (typeAgreement : TypedChainAgrees referenceTypes executableTypes)
    (supported : SupportedFreshTypedArgs state counter sources referenceTypes)
    (compiled : compileTypedArgs env counter sources executableTypes =
      .ok (internals, executableGoals, nextCounter)) :
    ∃ references referenceGoals,
      TranslatesFreshTypedArgs state counter sources referenceTypes references
        referenceGoals nextCounter ∧
      TermsAgree references internals ∧
      GoalsAgree referenceGoals executableGoals := by
  rcases supported with
    ⟨references, referenceGoals, referenceCounter, translation⟩
  obtain ⟨referenceInternals, referenceExecutableGoals,
      referenceCompiled, termsAgreement, goalsAgreement⟩ :=
    compileFreshTypedArgs_sound env stateAgreement typeAgreement translation
  have resultEquality :
      (internals, executableGoals, nextCounter) =
        (referenceInternals, referenceExecutableGoals, referenceCounter) :=
    Except.ok.inj (compiled.symm.trans referenceCompiled)
  cases resultEquality
  exact ⟨references, referenceGoals, translation, termsAgreement,
    goalsAgreement⟩

/-- Soundness of the result-type suffix for unchecked, closed checked, and
open checked expected types. -/
theorem translatesResultTypeCheck_sound
    {counter nextCounter : Nat} {referenceValue referenceExpected : Term}
    {executableValue executableExpected : Atom}
    (valueAgreement : TermAgrees referenceValue executableValue)
    (expectedAgreement : TypeCheckExpectedAgrees referenceExpected
      executableExpected (typeCheckBindingTemplate executableExpected))
    {referenceGoals : List PeTTaSpec.PrologCore.Goal}
    (translation : TranslatesResultTypeCheck counter referenceValue
      referenceExpected referenceGoals nextCounter) :
    GoalsAgree referenceGoals
        (compileResultTypeCheck executableValue executableExpected counter).1 ∧
      (compileResultTypeCheck executableValue executableExpected counter).2 =
        nextCounter := by
  cases translation with
  | undefined =>
      rw [typeCheckExpectedAtom_executable expectedAgreement]
      have checkEq := compileResultTypeCheck_unchecked_symbol_eq
        executableValue counter "%Undefined%" (by simp)
      rw [checkEq]
      exact ⟨.nil, rfl⟩
  | atom =>
      rw [typeCheckExpectedAtom_executable expectedAgreement]
      have checkEq := compileResultTypeCheck_unchecked_symbol_eq
        executableValue counter "Atom" (by simp)
      rw [checkEq]
      exact ⟨.nil, rfl⟩
  | checked checkedType =>
      exact compileResultTypeCheck_open_sound valueAgreement expectedAgreement
        rfl counter checkedType

set_option maxHeartbeats 4000000 in
/-- One independent typed branch compiles to the same branch result, ordered
argument/call/result-check goals, and exact next counter. -/
theorem compileTypedDispatchStep_sound
    {registry : FunctionRegistry} {state : TranslatorState} (env : CEnv)
    (stateAgreement : EnvAgrees state env)
    (registryAgreement : FunctionRegistryAgrees registry env)
    {counter nextCounter : Nat} {head : String}
    {sources sourceChain : List Atom}
    {referenceShared referenceBranch : Term}
    {executableShared : Atom}
    {referenceGoals : List PeTTaSpec.PrologCore.Goal}
    (sharedAgreement : TermAgrees referenceShared executableShared)
    (translation : TranslatesTypedBranch registry state counter head sources
      sourceChain referenceShared referenceBranch referenceGoals nextCounter) :
    ∃ executableBranch executableGoals,
      compileTypedDispatchStepWith
        (fun branchCounter parameterTypes =>
          compileTypedArgs env branchCounter sources parameterTypes)
        executableShared head (env.arities head) ([], counter) sourceChain =
          .ok ([(executableBranch, executableGoals)], nextCounter) ∧
      TermAgrees referenceBranch executableBranch ∧
      GoalsAgree referenceGoals executableGoals := by
  cases translation with
  | branch freshened split arguments callOrPartial resultCheck =>
      rename_i freshCounter argumentCounter freshChain parameterTypes resultType
        terms argumentGoals callGoals resultGoals
      have freshSound := freshensTypeChain_typedChain_sound freshened
      rw [split] at freshSound
      obtain ⟨executableParameterTypes, executableResultType, chainEquality,
          parameterTypeAgreement, resultTypeAgreement⟩ :=
        TypedChainAgrees.unsnoc freshSound.1
      obtain ⟨executableTerms, executableArgumentGoals, argumentsCompiled,
          termsAgreement, argumentGoalsAgreement⟩ :=
        compileFreshTypedArgs_sound env stateAgreement parameterTypeAgreement
          arguments
      let executableCall := compileTypedCallOrPartial (env.arities head)
        executableShared head executableTerms
      have callSound := buildsCallOrPartial_sound registryAgreement
        termsAgreement sharedAgreement callOrPartial
      change TermAgrees referenceBranch executableCall.1 ∧
        GoalsAgree callGoals executableCall.2 at callSound
      have resultSound := translatesResultTypeCheck_sound callSound.1
        resultTypeAgreement resultCheck
      change GoalsAgree resultGoals
          (compileResultTypeCheck executableCall.1 executableResultType
            argumentCounter).1 ∧
        (compileResultTypeCheck executableCall.1 executableResultType
          argumentCounter).2 = nextCounter at resultSound
      refine ⟨executableCall.1,
        executableArgumentGoals ++ executableCall.2 ++
          (compileResultTypeCheck executableCall.1 executableResultType
            argumentCounter).1, ?_, callSound.1, ?_⟩
      · unfold compileTypedDispatchStepWith
        dsimp only [Prod.fst, Prod.snd]
        rw [← freshSound.2]
        rw [chainEquality]
        simp only [List.dropLast_concat, List.getLast?_concat]
        rw [argumentsCompiled]
        dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind]
        change Except.ok _ = Except.ok _
        rw [resultSound.2]
        simp [executableCall]
      · exact GoalsAgree.append
          (GoalsAgree.append argumentGoalsAgreement callSound.2)
          resultSound.1

/-- Independent support for one complete typed branch.  Support is stated
solely by the pinned translation relation, never by compiler success. -/
def SupportedTypedBranch (registry : FunctionRegistry)
    (state : TranslatorState) (counter : Nat) (head : String)
    (sources sourceChain : List Atom) (referenceShared : Term) : Prop :=
  ∃ referenceBranch referenceGoals nextCounter,
    TranslatesTypedBranch registry state counter head sources sourceChain
      referenceShared referenceBranch referenceGoals nextCounter

set_option maxHeartbeats 4000000 in
/-- Completeness of one typed-dispatch branch on the independently supported
fragment.  Executable determinism transports the independent derivation's
result to the observed branch, goals, and next counter. -/
theorem compileTypedDispatchStep_complete
    {registry : FunctionRegistry} {state : TranslatorState} (env : CEnv)
    (stateAgreement : EnvAgrees state env)
    (registryAgreement : FunctionRegistryAgrees registry env)
    {counter nextCounter : Nat} {head : String}
    {sources sourceChain : List Atom}
    {referenceShared : Term} {executableShared executableBranch : Atom}
    {executableGoals : List PLeaTTa.Goal}
    (sharedAgreement : TermAgrees referenceShared executableShared)
    (supported : SupportedTypedBranch registry state counter head sources
      sourceChain referenceShared)
    (compiled :
      compileTypedDispatchStepWith
        (fun branchCounter parameterTypes =>
          compileTypedArgs env branchCounter sources parameterTypes)
        executableShared head (env.arities head) ([], counter) sourceChain =
          .ok ([(executableBranch, executableGoals)], nextCounter)) :
    ∃ referenceBranch referenceGoals,
      TranslatesTypedBranch registry state counter head sources sourceChain
        referenceShared referenceBranch referenceGoals nextCounter ∧
      TermAgrees referenceBranch executableBranch ∧
      GoalsAgree referenceGoals executableGoals := by
  rcases supported with
    ⟨referenceBranch, referenceGoals, referenceCounter, translation⟩
  obtain ⟨referenceExecutableBranch, referenceExecutableGoals,
      referenceCompiled, branchAgreement, goalsAgreement⟩ :=
    compileTypedDispatchStep_sound env stateAgreement registryAgreement
      sharedAgreement translation
  have resultEquality :
      ([(executableBranch, executableGoals)], nextCounter) =
        ([(referenceExecutableBranch, referenceExecutableGoals)],
          referenceCounter) :=
    Except.ok.inj (compiled.symm.trans referenceCompiled)
  cases resultEquality
  exact ⟨referenceBranch, referenceGoals, translation, branchAgreement,
    goalsAgreement⟩

set_option maxHeartbeats 4000000 in
/-- One typed step depends on the accumulator only by appending its new
branch.  This is the reusable fold law: existing ordered branches are neither
inspected nor reordered. -/
theorem compileTypedDispatchStepWith_append
    (compileTypedArgs : Nat → List Atom →
      CompileM (List Atom × List PLeaTTa.Goal × Nat))
    (result : Atom) (head : String) (arities : List Nat)
    (priorBranches : List (Atom × List PLeaTTa.Goal))
    {counter nextCounter : Nat} (chain : List Atom)
    {branch : Atom} {goals : List PLeaTTa.Goal}
    (compiled :
      compileTypedDispatchStepWith compileTypedArgs result head arities
        ([], counter) chain = .ok ([(branch, goals)], nextCounter)) :
    compileTypedDispatchStepWith compileTypedArgs result head arities
      (priorBranches, counter) chain =
        .ok (priorBranches ++ [(branch, goals)], nextCounter) := by
  unfold compileTypedDispatchStepWith at compiled ⊢
  rcases freshEq : freshenTypeChain counter chain with
    ⟨freshChain, freshCounter⟩
  simp only [freshEq] at compiled ⊢
  cases lastEq : freshChain.getLast? with
  | none => simp [lastEq] at compiled
  | some resultType =>
      simp only [lastEq, Bind.bind, Except.bind] at compiled ⊢
      cases typedEq : compileTypedArgs freshCounter freshChain.dropLast with
      | error message => simp [typedEq] at compiled
      | ok value =>
          simp only [typedEq] at compiled ⊢
          have outputEq := Except.ok.inj compiled
          simp only [List.nil_append] at outputEq
          cases outputEq
          rfl

/-- Exact pointwise agreement for an ordered typed-branch collection. -/
inductive TypedBranchesAgree :
    List (Term × List PeTTaSpec.PrologCore.Goal) →
      List (Atom × List PLeaTTa.Goal) → Prop where
  | nil : TypedBranchesAgree [] []
  | cons {referenceBranch : Term}
      {referenceGoals : List PeTTaSpec.PrologCore.Goal}
      {executableBranch : Atom} {executableGoals : List PLeaTTa.Goal}
      {referenceBranches : List (Term × List PeTTaSpec.PrologCore.Goal)}
      {executableBranches : List (Atom × List PLeaTTa.Goal)}
      (branch : TermAgrees referenceBranch executableBranch)
      (goals : GoalsAgree referenceGoals executableGoals)
      (tail : TypedBranchesAgree referenceBranches executableBranches) :
      TypedBranchesAgree
        ((referenceBranch, referenceGoals) :: referenceBranches)
        ((executableBranch, executableGoals) :: executableBranches)

set_option maxHeartbeats 4000000 in
/-- Fold-level soundness with an arbitrary pre-existing branch prefix.  The
proof composes the one-step theorem; it does not reopen fuel, counter, or
type-check internals. -/
theorem compileTypedDispatchBranches_append_sound
    {registry : FunctionRegistry} {state : TranslatorState} (env : CEnv)
    (stateAgreement : EnvAgrees state env)
    (registryAgreement : FunctionRegistryAgrees registry env)
    {counter nextCounter : Nat} {head : String}
    {sources : List Atom} {chains : List (List Atom)}
    {referenceShared : Term} {executableShared : Atom}
    {referenceBranches : List (Term × List PeTTaSpec.PrologCore.Goal)}
    (sharedAgreement : TermAgrees referenceShared executableShared)
    (translation : TranslatesTypedBranches registry state head sources
      referenceShared counter chains referenceBranches nextCounter) :
    ∀ priorBranches : List (Atom × List PLeaTTa.Goal),
      ∃ executableBranches,
        chains.foldlM
          (compileTypedDispatchStepWith
            (fun branchCounter parameterTypes =>
              compileTypedArgs env branchCounter sources parameterTypes)
            executableShared head (env.arities head))
          (priorBranches, counter) =
            .ok (priorBranches ++ executableBranches, nextCounter) ∧
        TypedBranchesAgree referenceBranches executableBranches := by
  induction translation with
  | nil =>
      intro priorBranches
      refine ⟨[], ?_, .nil⟩
      rw [List.foldlM_nil, List.append_nil]
      change Except.pure (priorBranches, _) = _
      rfl
  | @cons counter middleCounter nextCounter sourceChain sourceChains
      referenceBranch referenceGoals referenceBranches branch tail
      inductionHypothesis =>
      intro priorBranches
      obtain ⟨executableBranch, executableGoals, branchCompiled,
          branchAgreement, goalsAgreement⟩ :=
        compileTypedDispatchStep_sound env stateAgreement registryAgreement
          sharedAgreement branch
      obtain ⟨executableBranches, branchesCompiled, branchesAgreement⟩ :=
        inductionHypothesis
          (priorBranches ++ [(executableBranch, executableGoals)])
      refine ⟨(executableBranch, executableGoals) :: executableBranches,
        ?_, .cons branchAgreement goalsAgreement branchesAgreement⟩
      rw [List.foldlM_cons]
      simp only [Bind.bind, Except.bind]
      rw [compileTypedDispatchStepWith_append
        (fun branchCounter parameterTypes =>
          compileTypedArgs env branchCounter sources parameterTypes)
        executableShared head (env.arities head) priorBranches sourceChain
        branchCompiled]
      dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind]
      rw [branchesCompiled]
      simp [List.append_assoc]

/-- Public soundness of ordered typed-branch construction.  Source-chain
order and multiplicity are preserved pointwise. -/
theorem compileTypedDispatchBranches_sound
    {registry : FunctionRegistry} {state : TranslatorState} (env : CEnv)
    (stateAgreement : EnvAgrees state env)
    (registryAgreement : FunctionRegistryAgrees registry env)
    {counter nextCounter : Nat} {head : String}
    {sources : List Atom} {chains : List (List Atom)}
    {referenceShared : Term} {executableShared : Atom}
    {referenceBranches : List (Term × List PeTTaSpec.PrologCore.Goal)}
    (sharedAgreement : TermAgrees referenceShared executableShared)
    (translation : TranslatesTypedBranches registry state head sources
      referenceShared counter chains referenceBranches nextCounter) :
    ∃ executableBranches,
      chains.foldlM
        (compileTypedDispatchStepWith
          (fun branchCounter parameterTypes =>
            compileTypedArgs env branchCounter sources parameterTypes)
          executableShared head (env.arities head))
        ([], counter) = .ok (executableBranches, nextCounter) ∧
      TypedBranchesAgree referenceBranches executableBranches := by
  obtain ⟨executableBranches, compiled, agreement⟩ :=
    compileTypedDispatchBranches_append_sound env stateAgreement
      registryAgreement sharedAgreement translation []
  exact ⟨executableBranches, by simpa using compiled, agreement⟩

/-- Independent support for a complete ordered typed-branch collection in the
atom-headed, empty-prefix, symbol/variable-type fragment.  In particular,
this support premise is not inhabited yet for compound type atoms, so the
completeness theorem below makes no claim about executable successes on that
still-open class. -/
def SupportedTypedBranches (registry : FunctionRegistry)
    (state : TranslatorState) (counter : Nat) (head : String)
    (sources : List Atom) (chains : List (List Atom))
    (referenceShared : Term) : Prop :=
  ∃ referenceBranches nextCounter,
    TranslatesTypedBranches registry state head sources referenceShared
      counter chains referenceBranches nextCounter

set_option maxHeartbeats 4000000 in
/-- Completeness of ordered typed-branch construction relative to the
independently supported fragment.  It is intentionally silent on compound
type atoms until `FreshensTypeAtom` is extended independently. -/
theorem compileTypedDispatchBranches_complete
    {registry : FunctionRegistry} {state : TranslatorState} (env : CEnv)
    (stateAgreement : EnvAgrees state env)
    (registryAgreement : FunctionRegistryAgrees registry env)
    {counter nextCounter : Nat} {head : String}
    {sources : List Atom} {chains : List (List Atom)}
    {referenceShared : Term} {executableShared : Atom}
    {executableBranches : List (Atom × List PLeaTTa.Goal)}
    (sharedAgreement : TermAgrees referenceShared executableShared)
    (supported : SupportedTypedBranches registry state counter head sources
      chains referenceShared)
    (compiled :
      chains.foldlM
        (compileTypedDispatchStepWith
          (fun branchCounter parameterTypes =>
            compileTypedArgs env branchCounter sources parameterTypes)
          executableShared head (env.arities head))
        ([], counter) = .ok (executableBranches, nextCounter)) :
    ∃ referenceBranches,
      TranslatesTypedBranches registry state head sources referenceShared
        counter chains referenceBranches nextCounter ∧
      TypedBranchesAgree referenceBranches executableBranches := by
  rcases supported with
    ⟨referenceBranches, referenceCounter, translation⟩
  obtain ⟨referenceExecutableBranches, referenceCompiled,
      branchesAgreement⟩ :=
    compileTypedDispatchBranches_sound env stateAgreement registryAgreement
      sharedAgreement translation
  have resultEquality :
      (executableBranches, nextCounter) =
        (referenceExecutableBranches, referenceCounter) :=
    Except.ok.inj (compiled.symm.trans referenceCompiled)
  cases resultEquality
  exact ⟨referenceBranches, translation, branchesAgreement⟩

end PLeaTTa.CompilerTypedBranchAdequacy
