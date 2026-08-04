-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.CompilerTranslationSupportAdequacy
Purpose: Derive finite independent goal-support certificates from the source
  variables and generated-counter interval of a translation derivation.
Trusted boundary: none
Main exports: translationSupportDomain,
  Literal.termVariablesIn_of_sourceVars,
  Quotes.termVariablesIn_of_sourceVars,
  TranslatesExpr.variablesIn,
  hiddenOutputConditional_not_supported,
  compileSuperposeBranchesFuel_initial_supported_sound,
  compileSuperposeBranches_alias_supported_finalization_from_contract
-/
import PLeaTTa.Proofs.CompilerGoalSubstitutionAdequacy
import PLeaTTa.Proofs.CompilerGeneratedNames

namespace PLeaTTa.CompilerTranslationSupportAdequacy

open Metta (Atom)
open PLeaTTa.CompilerAdequacy
open PLeaTTa.CompilerGoalSubstitutionAdequacy
open PLeaTTa.CompilerSubstitutionAdequacy
open PLeaTTa.OpenBindingAgreement
open PLeaTTa.PeTTaSpec.PrologCore

/-! ## Canonical source-and-counter support -/

/-- Every source variable visible in an atom has its independent source
identity in `domain`. -/
def SourceVarsIn (domain : List LogicVar) (source : Atom) : Prop :=
  ∀ name, name ∈ source.vars → .source name ∈ domain

/-- Every source variable visible in an ordered atom list has its independent
source identity in `domain`. -/
def SourcesVarsIn (domain : List LogicVar) (sources : List Atom) : Prop :=
  ∀ name, name ∈ sources.flatMap Atom.vars → .source name ∈ domain

/-- Every generated identity in the compiler's half-open allocation interval
`[origin, limit)` belongs to `domain`.  This is the independent-identity
counterpart of executable `CompilerNameAllowed`. -/
def GeneratedVarsIn (domain : List LogicVar) (origin limit : Nat) : Prop :=
  ∀ index, origin ≤ index → index < limit → .generated index ∈ domain

/-- Canonical finite domain for a source list and one generated-counter
high-water mark.  Duplicates are harmless: support needs membership, while
encoding injectivity is stated independently. -/
def translationSupportDomain (sources : List Atom) (origin limit : Nat) :
    List LogicVar :=
  (sources.flatMap Atom.vars).map LogicVar.source ++
    (List.range (limit - origin)).map
      (fun offset => LogicVar.generated (origin + offset))

/-- The canonical domain contains every source identity from its source list. -/
theorem translationSupportDomain_sources (sources : List Atom)
    (origin limit : Nat) :
    SourcesVarsIn (translationSupportDomain sources origin limit) sources := by
  intro name member
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨name, member, rfl⟩

/-- The canonical domain contains every generated identity below its bound. -/
theorem translationSupportDomain_generated (sources : List Atom)
    (origin limit : Nat) :
    GeneratedVarsIn (translationSupportDomain sources origin limit)
      origin limit := by
  intro index lower upper
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨index - origin, List.mem_range.mpr ?_, ?_⟩
  · omega
  · congr 2
    omega

/-- Membership in the independent support domain induces the executable
compiler-name classification for the same source/counter slice.  This is a
one-way representation bridge: the domain itself remains defined from
`LogicVar`, source syntax, and the half-open counter interval. -/
theorem translationSupportDomain_nameAllowed
    {sources : List Atom} {origin limit : Nat} {identity : LogicVar}
    (member : identity ∈ translationSupportDomain sources origin limit) :
    CompilerNameAllowed (fun name => name ∈ sources.flatMap Atom.vars)
      origin limit (logicVarExecutableName identity) := by
  simp only [translationSupportDomain, List.mem_append] at member
  rcases member with sourceMember | generatedMember
  · rcases List.mem_map.mp sourceMember with ⟨name, nameMember, rfl⟩
    exact .external nameMember
  · rcases List.mem_map.mp generatedMember with
      ⟨offset, offsetMember, rfl⟩
    simp only [logicVarExecutableName, generatedExecutableName]
    exact .generated (by omega) (by
      have offsetBound := List.mem_range.mp offsetMember
      omega)

/-! ## Counter-interval discipline -/

mutual

/-- Independent expression translation never moves its allocation counter
backwards. -/
theorem TranslatesExpr.counter_le
    {state : TranslatorState} {counter nextCounter : Nat} {source : Atom}
    {term : Term} {goals : List PeTTaSpec.PrologCore.Goal}
    (translation : TranslatesExpr state counter source term goals nextCounter) :
    counter ≤ nextCounter := by
  cases translation with
  | literal => omega
  | quote => omega
  | cut => omega
  | eval => omega
  | assertaPredicate _ payload =>
      have bound := TranslatesExpr.counter_le payload
      omega
  | assertzPredicate _ payload =>
      have bound := TranslatesExpr.counter_le payload
      omega
  | retractPredicate _ payload =>
      have bound := TranslatesExpr.counter_le payload
      omega
  | collapse _ body =>
      have bound := TranslatesExpr.counter_le body
      omega
  | superposeLiterals => omega
  | superposeBranches _ branches =>
      have bound := TranslatesSuperposeBranches.counter_le branches
      omega
  | letBind _ pattern value body =>
      exact Nat.le_trans (TranslatesExpr.counter_le pattern)
        (Nat.le_trans (TranslatesExpr.counter_le value)
          (TranslatesExpr.counter_le body))
  | chainBind _ first second body =>
      exact Nat.le_trans (TranslatesExpr.counter_le first)
        (Nat.le_trans (TranslatesExpr.counter_le second)
          (TranslatesExpr.counter_le body))
  | andThen _ condition body =>
      have first := TranslatesExpr.counter_le condition
      have second := TranslatesExpr.counter_le body
      omega
  | orElse _ condition body =>
      have first := TranslatesExpr.counter_le condition
      have second := TranslatesExpr.counter_le body
      omega
  | ifThen _ condition thenTranslation _ =>
      have first := TranslatesExpr.counter_le condition
      have second := TranslatesExpr.counter_le thenTranslation
      omega
  | ifThenElse _ condition thenTranslation elseTranslation _ _ =>
      have first := TranslatesExpr.counter_le condition
      have second := TranslatesExpr.counter_le thenTranslation
      have third := TranslatesExpr.counter_le elseTranslation
      omega
  | progn _ arguments => exact TranslatesSeq.counter_le arguments
  | prog1 _ arguments => exact TranslatesSeq.counter_le arguments

/-- Ordered expression sequences inherit counter monotonicity from each
left-to-right translation step. -/
theorem TranslatesSeq.counter_le
    {state : TranslatorState} {counter nextCounter : Nat}
    {sources : List Atom} {first last : Term}
    {goals : List PeTTaSpec.PrologCore.Goal}
    (translation :
      TranslatesSeq state counter sources first last goals nextCounter) :
    counter ≤ nextCounter := by
  cases translation with
  | single head => exact TranslatesExpr.counter_le head
  | cons head tail =>
      exact Nat.le_trans (TranslatesExpr.counter_le head)
        (TranslatesSeq.counter_le tail)

/-- General-superpose traversal threads a monotone counter through every
branch in source order. -/
theorem TranslatesSuperposeBranches.counter_le
    {state : TranslatorState} {output : Term} {counter nextCounter : Nat}
    {sources : List Atom}
    {aliases branches : List PeTTaSpec.PrologCore.Goal}
    (translation : TranslatesSuperposeBranches state output counter sources
      aliases branches nextCounter) :
    counter ≤ nextCounter := by
  cases translation with
  | nil => rfl
  | cons head _ tail =>
      exact Nat.le_trans (TranslatesExpr.counter_le head)
        (TranslatesSuperposeBranches.counter_le tail)

end

/-! ## Independent target-syntax support -/

/-- Branch normalization allocates no variables.  Its alias prefix, retained
template, and executable branch syntax therefore use only variables already
present in the shared output, translated value, and translated body goals. -/
theorem BuildsBranchNormalized.variablesIn
    {domain : List LogicVar} {output value template : Term}
    {goals aliases : List PeTTaSpec.PrologCore.Goal}
    {branch : PeTTaSpec.PrologCore.Goal}
    (translation :
      BuildsBranchNormalized output value goals aliases template branch)
    (outputSupported : termVariablesIn domain output)
    (valueSupported : termVariablesIn domain value)
    (goalsSupported : goalsVariablesIn domain goals) :
    goalsVariablesIn domain aliases ∧
      termVariablesIn domain template ∧
      goalVariablesIn domain branch := by
  cases translation with
  | empty =>
      simpa [goalsVariablesIn, goalVariablesIn] using
        And.intro valueSupported outputSupported
  | aliasVariable =>
      exact ⟨by
          simpa [goalsVariablesIn, goalVariablesIn] using
            And.intro valueSupported outputSupported,
        outputSupported, by
          simpa [goalVariablesIn] using goalsSupported⟩
  | nonVariable =>
      exact ⟨by simp [goalsVariablesIn], valueSupported, by
        simpa [goalVariablesIn, goalsVariablesIn] using
          And.intro (And.intro valueSupported outputSupported)
            goalsSupported⟩

/-- `conditionThen` changes only conjunction wrappers, never variable
support. -/
theorem conditionThen_variablesIn {domain : List LogicVar}
    {conditionGoals : List PeTTaSpec.PrologCore.Goal}
    {decision : PeTTaSpec.PrologCore.Goal}
    (conditionSupported : goalsVariablesIn domain conditionGoals)
    (decisionSupported : goalVariablesIn domain decision) :
    goalsVariablesIn domain (conditionThen conditionGoals decision) := by
  simp only [conditionThen]
  split <;> simp [goalsVariablesIn, goalVariablesIn, conditionSupported,
    decisionSupported]

/-- The pinned `and-then` target introduces no variable beyond its two
translated subexpressions and fresh output. -/
theorem andThenGoal_variablesIn {domain : List LogicVar}
    {condition body output : Term}
    {conditionGoals bodyGoals : List PeTTaSpec.PrologCore.Goal}
    (conditionSupported : termVariablesIn domain condition)
    (bodySupported : termVariablesIn domain body)
    (outputSupported : termVariablesIn domain output)
    (conditionGoalsSupported : goalsVariablesIn domain conditionGoals)
    (bodyGoalsSupported : goalsVariablesIn domain bodyGoals) :
    goalVariablesIn domain
      (andThenGoal condition body output conditionGoals bodyGoals) := by
  simp [andThenGoal, goalVariablesIn, goalsVariablesIn, termVariablesIn,
    conditionSupported, bodySupported, outputSupported,
    conditionGoalsSupported, bodyGoalsSupported]

/-- The pinned `or-else` target obeys the same finite-support discipline. -/
theorem orElseGoal_variablesIn {domain : List LogicVar}
    {condition body output : Term}
    {conditionGoals bodyGoals : List PeTTaSpec.PrologCore.Goal}
    (conditionSupported : termVariablesIn domain condition)
    (bodySupported : termVariablesIn domain body)
    (outputSupported : termVariablesIn domain output)
    (conditionGoalsSupported : goalsVariablesIn domain conditionGoals)
    (bodyGoalsSupported : goalsVariablesIn domain bodyGoals) :
    goalVariablesIn domain
      (orElseGoal condition body output conditionGoals bodyGoals) := by
  simp [orElseGoal, goalVariablesIn, goalsVariablesIn, termVariablesIn,
    conditionSupported, bodySupported, outputSupported,
    conditionGoalsSupported, bodyGoalsSupported]

/-- A list-level source cover restricts to any member atom. -/
theorem SourcesVarsIn.atom {domain : List LogicVar} {sources : List Atom}
    (covered : SourcesVarsIn domain sources) {source : Atom}
    (member : source ∈ sources) : SourceVarsIn domain source := by
  intro name nameMember
  exact covered name (List.mem_flatMap.mpr
    ⟨source, member, nameMember⟩)

/-- Ordered source-list coverage restricts to its tail. -/
theorem SourcesVarsIn.tail {domain : List LogicVar} {head : Atom}
    {tail : List Atom} (covered : SourcesVarsIn domain (head :: tail)) :
    SourcesVarsIn domain tail := by
  intro name member
  exact covered name (by
    simp only [List.flatMap_cons, List.mem_append]
    exact Or.inr member)

/-- Source coverage is monotone in the variable-name set. -/
theorem SourceVarsIn.of_subset {domain : List LogicVar} {smaller larger : Atom}
    (covered : SourceVarsIn domain larger)
    (subset : ∀ name, name ∈ smaller.vars → name ∈ larger.vars) :
    SourceVarsIn domain smaller := by
  intro name member
  exact covered name (subset name member)

/-- Source coverage of an expression restricts to any syntactic child. -/
theorem SourceVarsIn.expression_member {domain : List LogicVar}
    {children : List Atom} (covered : SourceVarsIn domain (.expr children))
    {child : Atom} (member : child ∈ children) : SourceVarsIn domain child := by
  intro name nameMember
  have flatMember : name ∈ children.flatMap Atom.vars :=
    List.mem_flatMap.mpr ⟨child, member, nameMember⟩
  exact covered name (by
    simpa [Atom.vars, List.flatMap] using flatMember)

/-- Source coverage of an expression is precisely list-level coverage of its
ordered children. -/
theorem SourceVarsIn.expression {domain : List LogicVar}
    {children : List Atom} (covered : SourceVarsIn domain (.expr children)) :
    SourcesVarsIn domain children := by
  intro name member
  exact covered name (by simpa [Atom.vars] using member)

/-- Generated coverage restricts to a nested allocation interval. -/
theorem GeneratedVarsIn.nest {domain : List LogicVar}
    {outerOrigin innerOrigin innerLimit outerLimit : Nat}
    (covered : GeneratedVarsIn domain outerOrigin outerLimit)
    (lower : outerOrigin ≤ innerOrigin) (upper : innerLimit ≤ outerLimit) :
    GeneratedVarsIn domain innerOrigin innerLimit := by
  intro index innerLower innerUpper
  exact covered index (Nat.le_trans lower innerLower)
    (Nat.lt_of_lt_of_le innerUpper upper)

/-! ## Literal and quotation support -/

/-- Independent literal conversion introduces no variables except source
identities already present in the input atom. -/
theorem Literal.termVariablesIn_of_sourceVars
    {domain : List LogicVar} {source : Atom} {term : Term}
    (translation : Literal source term)
    (covered : SourceVarsIn domain source) :
    termVariablesIn domain term := by
  cases translation with
  | «variable» name => exact covered name (by simp [Atom.vars])
  | symbol | integer | float | string | trueGround | falseGround => trivial
  | emptyList => trivial

mutual

/-- Deep quotation introduces no variables except source identities already
present in the quoted atom. -/
theorem Quotes.termVariablesIn_of_sourceVars
    {domain : List LogicVar} {source : Atom} {term : Term}
    (translation : Quotes source term)
    (covered : SourceVarsIn domain source) :
    termVariablesIn domain term := by
  cases translation with
  | «variable» name => exact covered name (by simp [Atom.vars])
  | symbol => trivial
  | integer => trivial
  | float => trivial
  | string => trivial
  | trueGround => trivial
  | falseGround => trivial
  | @expression atoms terms items =>
      have itemsCovered : SourcesVarsIn domain atoms := by
        intro name member
        exact covered name (by
          simpa [Atom.vars, List.flatMap] using member)
      simpa [termVariablesIn] using
        QuotesList.termsVariablesIn_of_sourceVars items itemsCovered

/-- Pointwise quotation preserves the same source-variable cover. -/
theorem QuotesList.termsVariablesIn_of_sourceVars
    {domain : List LogicVar} {sources : List Atom} {terms : List Term}
    (translation : QuotesList sources terms)
    (covered : SourcesVarsIn domain sources) :
    termsVariablesIn domain terms := by
  cases translation with
  | nil => trivial
  | @cons source term sources terms head tail =>
      constructor
      · exact Quotes.termVariablesIn_of_sourceVars head
          (covered.atom (by simp))
      · exact QuotesList.termsVariablesIn_of_sourceVars tail
          (fun name member => covered name (by
            simp only [List.flatMap_cons, List.mem_append]
            exact Or.inr member))

end

/-- Literal-only `superpose` alternatives use only their source variables
and the explicitly supplied shared output. -/
theorem TranslatesLiteralAmbBranches.variablesIn
    {domain : List LogicVar} {output : Term} {sources : List Atom}
    {branches : List PeTTaSpec.PrologCore.Goal}
    (translation : TranslatesLiteralAmbBranches output sources branches)
    (sourcesSupported : SourcesVarsIn domain sources)
    (outputSupported : termVariablesIn domain output) :
    goalsVariablesIn domain branches := by
  cases translation with
  | nil => trivial
  | cons value tail =>
      constructor
      · exact ⟨Literal.termVariablesIn_of_sourceVars value
          (sourcesSupported.atom (by simp)), outputSupported⟩
      · exact TranslatesLiteralAmbBranches.variablesIn tail
          sourcesSupported.tail outputSupported

/-! ## Support derived from independent translation

The current core `TranslatesExpr` relation has no type-check constructor.
Consequently this mutual proof derives ordinary term/goal support only; the
later agreement-indexed certificate legitimately uses an empty type domain.
If a typed constructor is added to the core relation, Lean makes this proof
non-exhaustive and forces its specialized carry support to be supplied.
-/

mutual

/-- An independent expression translation mentions only variables from its
source syntax and generated identities in the counter interval it consumes. -/
theorem TranslatesExpr.variablesIn
    {domain : List LogicVar} {state : TranslatorState}
    {counter nextCounter : Nat} {source : Atom} {term : Term}
    {goals : List PeTTaSpec.PrologCore.Goal}
    (translation : TranslatesExpr state counter source term goals nextCounter)
    (sourceSupported : SourceVarsIn domain source)
    (generatedSupported : GeneratedVarsIn domain counter nextCounter) :
    termVariablesIn domain term ∧ goalsVariablesIn domain goals := by
  cases translation with
  | literal value =>
      exact ⟨Literal.termVariablesIn_of_sourceVars value sourceSupported,
        trivial⟩
  | quote _ value =>
      exact ⟨Quotes.termVariablesIn_of_sourceVars value
          (sourceSupported.expression_member (by simp)), trivial⟩
  | cut => exact ⟨trivial, by simp [goalsVariablesIn, goalVariablesIn]⟩
  | eval _ quotation =>
      have codeSupported := Quotes.termVariablesIn_of_sourceVars quotation
        (sourceSupported.expression_member (by simp))
      have resultSupported :
          termVariablesIn domain (.variable (.generated counter)) :=
        generatedSupported counter (by omega) (by omega)
      exact ⟨resultSupported, by
        simp only [goalsVariablesIn, goalVariablesIn, termsVariablesIn,
          and_true]
        exact ⟨codeSupported, resultSupported⟩⟩
  | @assertaPredicate _ payloadCounter _ payload _ _ payloadTranslation =>
      have payloadCounterBound :=
        TranslatesExpr.counter_le payloadTranslation
      have payloadSupported := TranslatesExpr.variablesIn payloadTranslation
        (sourceSupported.expression_member (by simp))
        (generatedSupported.nest (by omega) (by omega))
      have outputSupported :
          termVariablesIn domain (.variable (.generated payloadCounter)) :=
        generatedSupported payloadCounter (by omega) (by omega)
      have appendedSupported : goalsVariablesIn domain
          [.call "assertaPredicate"
            [payload, .variable (.generated payloadCounter)]] := by
        simp only [goalsVariablesIn, goalVariablesIn, termsVariablesIn,
          and_true]
        exact ⟨payloadSupported.1, outputSupported⟩
      exact ⟨outputSupported,
        (goalsVariablesIn_append _ _ _).2
          ⟨payloadSupported.2, appendedSupported⟩⟩
  | @assertzPredicate _ payloadCounter _ payload _ _ payloadTranslation =>
      have payloadCounterBound :=
        TranslatesExpr.counter_le payloadTranslation
      have payloadSupported := TranslatesExpr.variablesIn payloadTranslation
        (sourceSupported.expression_member (by simp))
        (generatedSupported.nest (by omega) (by omega))
      have outputSupported :
          termVariablesIn domain (.variable (.generated payloadCounter)) :=
        generatedSupported payloadCounter (by omega) (by omega)
      have appendedSupported : goalsVariablesIn domain
          [.call "assertzPredicate"
            [payload, .variable (.generated payloadCounter)]] := by
        simp only [goalsVariablesIn, goalVariablesIn, termsVariablesIn,
          and_true]
        exact ⟨payloadSupported.1, outputSupported⟩
      exact ⟨outputSupported,
        (goalsVariablesIn_append _ _ _).2
          ⟨payloadSupported.2, appendedSupported⟩⟩
  | @retractPredicate _ payloadCounter _ payload _ _ payloadTranslation =>
      have payloadCounterBound :=
        TranslatesExpr.counter_le payloadTranslation
      have payloadSupported := TranslatesExpr.variablesIn payloadTranslation
        (sourceSupported.expression_member (by simp))
        (generatedSupported.nest (by omega) (by omega))
      have outputSupported :
          termVariablesIn domain (.variable (.generated payloadCounter)) :=
        generatedSupported payloadCounter (by omega) (by omega)
      have appendedSupported : goalsVariablesIn domain
          [.call "retractPredicate"
            [payload, .variable (.generated payloadCounter)]] := by
        simp only [goalsVariablesIn, goalVariablesIn, termsVariablesIn,
          and_true]
        exact ⟨payloadSupported.1, outputSupported⟩
      exact ⟨outputSupported,
        (goalsVariablesIn_append _ _ _).2
          ⟨payloadSupported.2, appendedSupported⟩⟩
  | @collapse _ bodyCounter _ _ _ _ body =>
      have bodyCounterBound := TranslatesExpr.counter_le body
      have bodySupported := TranslatesExpr.variablesIn body
        (sourceSupported.expression_member (by simp))
        (generatedSupported.nest (by omega) (by omega))
      have outputSupported :
          termVariablesIn domain (.variable (.generated bodyCounter)) :=
        generatedSupported bodyCounter (by omega) (by omega)
      exact ⟨outputSupported, by
        simp [goalsVariablesIn, goalVariablesIn, bodySupported.1,
          bodySupported.2, outputSupported]⟩
  | @superposeLiterals _ first sources branches _ translated =>
      have outputSupported :
          termVariablesIn domain (.variable (.generated counter)) :=
        generatedSupported counter (by omega) (by omega)
      have innerSupported := sourceSupported.expression_member
        (child := .expr (first :: sources)) (by simp)
      have branchesSupported :=
        TranslatesLiteralAmbBranches.variablesIn translated
          innerSupported.expression outputSupported
      exact ⟨outputSupported, by
        simp [goalsVariablesIn, goalVariablesIn, branchesSupported]⟩
  | @superposeBranches _ branchCounter first sources aliases branches _
      translated =>
      have traversalBound := TranslatesSuperposeBranches.counter_le translated
      have outputSupported :
          termVariablesIn domain (.variable (.generated branchCounter)) :=
        generatedSupported branchCounter (by omega) (by omega)
      have innerSupported := sourceSupported.expression_member
        (child := .expr (first :: sources)) (by simp)
      have traversalSupported :=
        TranslatesSuperposeBranches.variablesIn translated
          innerSupported.expression
          (generatedSupported.nest (by omega) (by omega)) outputSupported
      exact ⟨outputSupported, by
        simp [goalsVariablesIn, goalVariablesIn, traversalSupported.1,
          traversalSupported.2]⟩
  | letBind _ patternTranslation valueTranslation bodyTranslation =>
      have patternBound := TranslatesExpr.counter_le patternTranslation
      have valueBound := TranslatesExpr.counter_le valueTranslation
      have bodyBound := TranslatesExpr.counter_le bodyTranslation
      have patternSupported := TranslatesExpr.variablesIn patternTranslation
        (sourceSupported.expression_member (by simp))
        (generatedSupported.nest (by omega) (by omega))
      have valueSupported := TranslatesExpr.variablesIn valueTranslation
        (sourceSupported.expression_member (by simp))
        (generatedSupported.nest (by omega) (by omega))
      have bodySupported := TranslatesExpr.variablesIn bodyTranslation
        (sourceSupported.expression_member (by simp))
        (generatedSupported.nest (by omega) (by omega))
      exact ⟨bodySupported.1, by
        simp [goalsVariablesIn, goalVariablesIn, patternSupported.1,
          patternSupported.2, valueSupported.1, valueSupported.2,
          bodySupported.2]⟩
  | chainBind _ firstTranslation secondTranslation bodyTranslation =>
      have firstBound := TranslatesExpr.counter_le firstTranslation
      have secondBound := TranslatesExpr.counter_le secondTranslation
      have bodyBound := TranslatesExpr.counter_le bodyTranslation
      have firstSupported := TranslatesExpr.variablesIn firstTranslation
        (sourceSupported.expression_member (by simp))
        (generatedSupported.nest (by omega) (by omega))
      have secondSupported := TranslatesExpr.variablesIn secondTranslation
        (sourceSupported.expression_member (by simp))
        (generatedSupported.nest (by omega) (by omega))
      have bodySupported := TranslatesExpr.variablesIn bodyTranslation
        (sourceSupported.expression_member (by simp))
        (generatedSupported.nest (by omega) (by omega))
      exact ⟨bodySupported.1, by
        simp [goalsVariablesIn, goalVariablesIn, firstSupported.1,
          firstSupported.2, secondSupported.1, secondSupported.2,
          bodySupported.2]⟩
  | @andThen _ conditionCounter bodyCounter conditionSource bodySource
      conditionTerm bodyTerm conditionGoals bodyGoals _
      conditionTranslation bodyTranslation =>
      have conditionBound := TranslatesExpr.counter_le conditionTranslation
      have bodyBound := TranslatesExpr.counter_le bodyTranslation
      have conditionSupported :=
        TranslatesExpr.variablesIn conditionTranslation
          (sourceSupported.expression_member (by simp))
          (generatedSupported.nest (by omega) (by omega))
      have bodySupported := TranslatesExpr.variablesIn bodyTranslation
        (sourceSupported.expression_member (by simp))
        (generatedSupported.nest (by omega) (by omega))
      have outputSupported :
          termVariablesIn domain (.variable (.generated bodyCounter)) :=
        generatedSupported bodyCounter (by omega) (by omega)
      exact ⟨outputSupported, ⟨andThenGoal_variablesIn
        conditionSupported.1 bodySupported.1 outputSupported
        conditionSupported.2 bodySupported.2, trivial⟩⟩
  | @orElse _ conditionCounter bodyCounter conditionSource bodySource
      conditionTerm bodyTerm conditionGoals bodyGoals _
      conditionTranslation bodyTranslation =>
      have conditionBound := TranslatesExpr.counter_le conditionTranslation
      have bodyBound := TranslatesExpr.counter_le bodyTranslation
      have conditionSupported :=
        TranslatesExpr.variablesIn conditionTranslation
          (sourceSupported.expression_member (by simp))
          (generatedSupported.nest (by omega) (by omega))
      have bodySupported := TranslatesExpr.variablesIn bodyTranslation
        (sourceSupported.expression_member (by simp))
        (generatedSupported.nest (by omega) (by omega))
      have outputSupported :
          termVariablesIn domain (.variable (.generated bodyCounter)) :=
        generatedSupported bodyCounter (by omega) (by omega)
      exact ⟨outputSupported, ⟨orElseGoal_variablesIn
        conditionSupported.1 bodySupported.1 outputSupported
        conditionSupported.2 bodySupported.2, trivial⟩⟩
  | @ifThen _ conditionCounter thenCounter conditionSource thenSource
      conditionTerm thenTerm branchTemplate conditionGoals thenGoals
      aliasGoals thenBranch _ conditionTranslation thenTranslation branch =>
      have conditionBound := TranslatesExpr.counter_le conditionTranslation
      have thenBound := TranslatesExpr.counter_le thenTranslation
      have conditionSupported :=
        TranslatesExpr.variablesIn conditionTranslation
          (sourceSupported.expression_member (by simp))
          (generatedSupported.nest (by omega) (by omega))
      have thenSupported := TranslatesExpr.variablesIn thenTranslation
        (sourceSupported.expression_member (by simp))
        (generatedSupported.nest (by omega) (by omega))
      have outputSupported :
          termVariablesIn domain (.variable (.generated thenCounter)) :=
        generatedSupported thenCounter (by omega) (by omega)
      obtain ⟨aliasesSupported, _templateSupported, branchSupported⟩ :=
        PLeaTTa.CompilerTranslationSupportAdequacy.BuildsBranchNormalized.variablesIn
          branch outputSupported thenSupported.1 thenSupported.2
      have decisionSupported : goalVariablesIn domain
          (.ifThenElse (.identical conditionTerm (.atom "true"))
            thenBranch .fail) := by
        exact ⟨⟨conditionSupported.1, trivial⟩, branchSupported, trivial⟩
      exact ⟨outputSupported,
        (goalsVariablesIn_append _ _ _).2
          ⟨aliasesSupported,
            conditionThen_variablesIn conditionSupported.2
              decisionSupported⟩⟩
  | @ifThenElse _ conditionCounter thenCounter elseCounter conditionSource
      thenSource elseSource conditionTerm thenTerm elseTerm thenTemplate
      elseTemplate conditionGoals thenGoals elseGoals thenAliasGoals
      elseAliasGoals thenBranch elseBranch _ conditionTranslation
      thenTranslation elseTranslation thenBuild elseBuild =>
      have conditionBound := TranslatesExpr.counter_le conditionTranslation
      have thenBound := TranslatesExpr.counter_le thenTranslation
      have elseBound := TranslatesExpr.counter_le elseTranslation
      have conditionSupported :=
        TranslatesExpr.variablesIn conditionTranslation
          (sourceSupported.expression_member (by simp))
          (generatedSupported.nest (by omega) (by omega))
      have thenSupported := TranslatesExpr.variablesIn thenTranslation
        (sourceSupported.expression_member (by simp))
        (generatedSupported.nest (by omega) (by omega))
      have elseSupported := TranslatesExpr.variablesIn elseTranslation
        (sourceSupported.expression_member (by simp))
        (generatedSupported.nest (by omega) (by omega))
      have outputSupported :
          termVariablesIn domain (.variable (.generated elseCounter)) :=
        generatedSupported elseCounter (by omega) (by omega)
      obtain ⟨thenAliasesSupported, _thenTemplateSupported,
          thenBranchSupported⟩ :=
        PLeaTTa.CompilerTranslationSupportAdequacy.BuildsBranchNormalized.variablesIn
          thenBuild outputSupported thenSupported.1 thenSupported.2
      obtain ⟨elseAliasesSupported, _elseTemplateSupported,
          elseBranchSupported⟩ :=
        PLeaTTa.CompilerTranslationSupportAdequacy.BuildsBranchNormalized.variablesIn
          elseBuild outputSupported elseSupported.1 elseSupported.2
      have decisionSupported : goalVariablesIn domain
          (.ifThenElse (.identical conditionTerm (.atom "true"))
            thenBranch elseBranch) := by
        exact ⟨⟨conditionSupported.1, trivial⟩, thenBranchSupported,
          elseBranchSupported⟩
      exact ⟨outputSupported, by
        rw [goalsVariablesIn_append]
        refine ⟨?_, conditionThen_variablesIn conditionSupported.2
          decisionSupported⟩
        rw [goalsVariablesIn_append]
        exact ⟨thenAliasesSupported, elseAliasesSupported⟩⟩
  | progn _ arguments =>
      have argumentSources := sourceSupported.expression.tail
      have argumentsSupported := TranslatesSeq.variablesIn arguments
        argumentSources generatedSupported
      exact ⟨argumentsSupported.2.1, argumentsSupported.2.2⟩
  | prog1 _ arguments =>
      have argumentSources := sourceSupported.expression.tail
      have argumentsSupported := TranslatesSeq.variablesIn arguments
        argumentSources generatedSupported
      exact ⟨argumentsSupported.1, argumentsSupported.2.2⟩

/-- A nonempty translation sequence has the same source/counter support for
its first result, last result, and concatenated goals. -/
theorem TranslatesSeq.variablesIn
    {domain : List LogicVar} {state : TranslatorState}
    {counter nextCounter : Nat} {sources : List Atom} {first last : Term}
    {goals : List PeTTaSpec.PrologCore.Goal}
    (translation : TranslatesSeq state counter sources first last goals
      nextCounter)
    (sourcesSupported : SourcesVarsIn domain sources)
    (generatedSupported : GeneratedVarsIn domain counter nextCounter) :
    termVariablesIn domain first ∧ termVariablesIn domain last ∧
      goalsVariablesIn domain goals := by
  cases translation with
  | single head =>
      have supported := TranslatesExpr.variablesIn head
        (sourcesSupported.atom (by simp)) generatedSupported
      exact ⟨supported.1, supported.1, supported.2⟩
  | cons head tail =>
      have headBound := TranslatesExpr.counter_le head
      have tailBound := TranslatesSeq.counter_le tail
      have headSupported := TranslatesExpr.variablesIn head
        (sourcesSupported.atom (by simp))
        (generatedSupported.nest (by omega) (by omega))
      have tailSupported := TranslatesSeq.variablesIn tail
        sourcesSupported.tail
        (generatedSupported.nest (by omega) (by omega))
      exact ⟨headSupported.1, tailSupported.2.1,
        (goalsVariablesIn_append _ _ _).2
          ⟨headSupported.2, tailSupported.2.2⟩⟩

/-- General-superpose traversal supports its exact source-ordered alias and
branch lists.  `outputSupported` is separate because the enclosing output is
allocated after the traversal, at its final counter. -/
theorem TranslatesSuperposeBranches.variablesIn
    {domain : List LogicVar} {state : TranslatorState} {output : Term}
    {counter nextCounter : Nat} {sources : List Atom}
    {aliases branches : List PeTTaSpec.PrologCore.Goal}
    (translation : TranslatesSuperposeBranches state output counter sources
      aliases branches nextCounter)
    (sourcesSupported : SourcesVarsIn domain sources)
    (generatedSupported : GeneratedVarsIn domain counter nextCounter) :
    termVariablesIn domain output →
      goalsVariablesIn domain aliases ∧
        goalsVariablesIn domain branches := by
  intro outputSupported
  cases translation with
  | nil => exact ⟨trivial, trivial⟩
  | cons head built tail =>
      have headBound := TranslatesExpr.counter_le head
      have tailBound := TranslatesSuperposeBranches.counter_le tail
      have headSupported := TranslatesExpr.variablesIn head
        (sourcesSupported.atom (by simp))
        (generatedSupported.nest (by omega) (by omega))
      obtain ⟨headAliasesSupported, _templateSupported,
          headBranchSupported⟩ :=
        PLeaTTa.CompilerTranslationSupportAdequacy.BuildsBranchNormalized.variablesIn
          built outputSupported headSupported.1 headSupported.2
      have tailSupported :=
        TranslatesSuperposeBranches.variablesIn (output := output)
          (nextCounter := nextCounter) tail sourcesSupported.tail
          (generatedSupported.nest (by omega) (by omega)) outputSupported
      exact ⟨(goalsVariablesIn_append _ _ _).2
          ⟨headAliasesSupported, tailSupported.1⟩,
        ⟨headBranchSupported, tailSupported.2⟩⟩

end

/-! ## Why support must stay coupled to compilation -/

/-- A variable atom whose spelling differs from the sole supported generated
identity cannot have any agreeing independent term supported by that domain. -/
private theorem termAgrees_var_not_supported
    {reference : Term} {name : String}
    (different : name ≠ compilerGeneratedName 0)
    (agreement : TermAgrees reference (.var name))
    (supported : termVariablesIn [.generated 0] reference) : False := by
  cases agreement with
  | sourceVariable source => simp [termVariablesIn] at supported
  | generatedVariable index =>
      simp [termVariablesIn] at supported
      subst index
      exact different rfl
  | properList elements => cases elements

/-- Visible independent conditional syntax that deliberately omits its
branch-output identity. -/
def hiddenOutputConditionalReference : PeTTaSpec.PrologCore.Goal :=
  .ifThenElse (.identical (.atom "true") (.atom "true")) .fail .fail

/-- Executable conditional carrying an out-of-domain hidden output. -/
def hiddenOutputConditionalExecutable : PLeaTTa.Goal :=
  .ite (.sym "True")
    (.var "outside", [.eq (.sym "True") (.sym "False")])
    (.var "outside", [.eq (.sym "True") (.sym "False")])
    (.var "outside")

/-- The visible reference conditional agrees with the executable one even
though its output identity occurs only in the agreement evidence. -/
def hiddenOutputConditionalAgrees :
    GoalAgrees hiddenOutputConditionalReference
      hiddenOutputConditionalExecutable := by
  let output : TermAgrees (.variable (.source "outside"))
      (.var "outside") := .sourceVariable "outside"
  exact .conditional .trueAtom output (.failed output) (.failed output)

/-- Concrete counterexample to recovering agreement-indexed support from
visible reference syntax alone.  The reference goal has no visible variable,
but the agreeing executable conditional retains an unsupported hidden output.
Therefore a sound compiler theorem must return support for the particular
agreement it constructs; it cannot quantify over arbitrary agreements. -/
theorem hiddenOutputConditional_not_supported :
    ¬ GoalAgreesSupported [.generated 0] []
      hiddenOutputConditionalAgrees := by
  intro supported
  change GoalAgreesSupported [.generated 0] []
    (GoalAgrees.conditional TermAgrees.trueAtom
      (TermAgrees.sourceVariable "outside")
      (IfBranchAgrees.failed (TermAgrees.sourceVariable "outside"))
      (IfBranchAgrees.failed (TermAgrees.sourceVariable "outside"))) at supported
  cases supported with
  | @conditional _ _ _ _ _ _ _ _ condition output _ _ _ outputSupport _ _ =>
      exact termAgrees_var_not_supported (by decide) output outputSupport

/-! ## Support-carrying compiler interface -/

/-- One compiler result packages the relation proofs together with finite
support for those exact proofs.  Keeping the four fields existentially
coupled prevents a caller from replacing the compiler-produced hidden branch
outputs by an arbitrary agreeing executable structure. -/
structure ExprCompilationSupported (termDomain typeDomain : List LogicVar)
    (referenceTerm : Term)
    (referenceGoals : List PeTTaSpec.PrologCore.Goal)
    (executableTerm : Atom) (executableGoals : List PLeaTTa.Goal) : Prop where
  termAgreement : TermAgrees referenceTerm executableTerm
  goalsAgreement : GoalsAgree referenceGoals executableGoals
  termSupport : TermAgreesSupported termDomain termAgreement
  goalsSupport : GoalsAgreeSupported termDomain typeDomain goalsAgreement

/-- Reusable strengthening target for expression-level compiler adequacy.
Unlike a universal post-hoc support premise, this contract returns support
for the exact term/goal agreements produced by the compiler run. -/
def CompileExprSupportContract (state : TranslatorState) (env : CEnv)
    (termDomain typeDomain : List LogicVar) : Prop :=
  ∀ {counter nextCounter : Nat} {source : Atom} {term : Term}
      {goals : List PeTTaSpec.PrologCore.Goal},
    TranslatesExpr state counter source term goals nextCounter →
    SourceVarsIn termDomain source →
    GeneratedVarsIn termDomain counter nextCounter →
    ∃ baseFuel,
      0 < baseFuel ∧
      baseFuel < 8 * source.size ∧
      ∀ extraFuel, ∃ internal executableGoals,
        compileExprFuel (baseFuel + extraFuel) env counter source =
            .ok (internal, executableGoals, nextCounter) ∧
          ExprCompilationSupported termDomain typeDomain term goals internal
            executableGoals

/-- Support-carrying counterpart of branch normalization.  The support proof
is built in the same priority case as the exact executable branch agreement,
so hidden outputs cannot be changed after normalization. -/
theorem compileSuperposeBranch_normalized_supported_sound
    {termDomain typeDomain : List LogicVar} {outputIndex : Nat}
    {referenceValue : Term}
    {referenceGoals referenceAliases : List PeTTaSpec.PrologCore.Goal}
    {referenceTemplate : Term}
    {referenceBranch : PeTTaSpec.PrologCore.Goal}
    {executableValue : Atom} {executableGoals : List PLeaTTa.Goal}
    (valueAgreement : TermAgrees referenceValue executableValue)
    (valueSupport : TermAgreesSupported termDomain valueAgreement)
    (goalsAgreement : GoalsAgree referenceGoals executableGoals)
    (goalsSupport :
      GoalsAgreeSupported termDomain typeDomain goalsAgreement)
    (native : BuildsBranchNormalized
      (.variable (.generated outputIndex)) referenceValue referenceGoals
      referenceAliases referenceTemplate referenceBranch)
    (outputSupport :
      termVariablesIn termDomain (.variable (.generated outputIndex))) :
    ∃ aliasSources aliasNames executableAliases executableBranch,
      ∃ branchAgreement : SuperposeBranchAgrees
          (.variable (.generated outputIndex))
          (.var s!"_q{outputIndex}") referenceBranch executableBranch,
        compileSuperposeBranch (.var s!"_q{outputIndex}")
            (executableValue, executableGoals) =
            (executableAliases, executableBranch) ∧
          AliasLedgerAgrees (.generated outputIndex) s!"_q{outputIndex}"
            aliasSources aliasNames referenceAliases executableAliases ∧
          SuperposeBranchAgreesSupported termDomain typeDomain
            branchAgreement := by
  let outputAgreement :
      TermAgrees (.variable (.generated outputIndex))
        (.var s!"_q{outputIndex}") := .generatedVariable outputIndex
  cases native with
  | empty _ _ empty =>
      have width := goalsAgreement.flatWidth
      have lengthZero : executableGoals.length = 0 := by omega
      have executableEmpty : executableGoals = [] :=
        List.eq_nil_of_length_eq_zero lengthZero
      subst executableGoals
      let branchAgreement : SuperposeBranchAgrees
          (.variable (.generated outputIndex))
          (.var s!"_q{outputIndex}")
          (.unify referenceValue (.variable (.generated outputIndex)))
          (executableValue, []) :=
        .empty valueAgreement outputAgreement
      refine ⟨[], [], [], (executableValue, []), branchAgreement, ?_, .nil,
        ?_⟩
      · simp [compileSuperposeBranch]
      · simpa [branchAgreement] using
          (@SuperposeBranchAgreesSupported.empty termDomain typeDomain
            (.variable (.generated outputIndex)) referenceValue
            (.var s!"_q{outputIndex}") executableValue valueAgreement
            outputAgreement valueSupport outputSupport)
  | aliasVariable identity goals nonempty =>
      have width := goalsAgreement.flatWidth
      have executableNonempty : executableGoals ≠ [] := by
        intro empty
        subst executableGoals
        simp at width
        omega
      obtain ⟨goal, goals, rfl⟩ :=
        List.exists_cons_of_ne_nil executableNonempty
      cases valueAgreement with
      | sourceVariable name =>
          let branchAgreement : SuperposeBranchAgrees
              (.variable (.generated outputIndex))
              (.var s!"_q{outputIndex}")
              (.conjunction referenceGoals)
              (.var s!"_q{outputIndex}", goal :: goals) :=
            .aliased outputAgreement goalsAgreement (by simp)
          refine ⟨[.source name], [name],
            [PLeaTTa.Goal.compileAlias (.var name)
              (.var s!"_q{outputIndex}")],
            (.var s!"_q{outputIndex}", goal :: goals), branchAgreement,
            ?_, .cons (.sourceVariable name) .nil, ?_⟩
          · simp [compileSuperposeBranch, compileBranch, BEq.beq, Atom.beq]
          · simpa [branchAgreement] using
              (@SuperposeBranchAgreesSupported.aliased termDomain typeDomain
                (.variable (.generated outputIndex))
                (.var s!"_q{outputIndex}") referenceGoals (goal :: goals)
                outputAgreement goalsAgreement (by simp) outputSupport
                goalsSupport)
      | generatedVariable index =>
          let branchAgreement : SuperposeBranchAgrees
              (.variable (.generated outputIndex))
              (.var s!"_q{outputIndex}")
              (.conjunction referenceGoals)
              (.var s!"_q{outputIndex}", goal :: goals) :=
            .aliased outputAgreement goalsAgreement (by simp)
          refine ⟨[.generated index], [s!"_q{index}"],
            [PLeaTTa.Goal.compileAlias (.var s!"_q{index}")
              (.var s!"_q{outputIndex}")],
            (.var s!"_q{outputIndex}", goal :: goals), branchAgreement,
            ?_, .cons (.generatedVariable index) .nil, ?_⟩
          · simp [compileSuperposeBranch, compileBranch, BEq.beq, Atom.beq]
          · simpa [branchAgreement] using
              (@SuperposeBranchAgreesSupported.aliased termDomain typeDomain
                (.variable (.generated outputIndex))
                (.var s!"_q{outputIndex}") referenceGoals (goal :: goals)
                outputAgreement goalsAgreement (by simp) outputSupport
                goalsSupport)
  | nonVariable value goals nonempty notVariable =>
      have executableNotVariable :=
        valueAgreement.executable_not_variable notVariable
      have width := goalsAgreement.flatWidth
      have executableNonempty : executableGoals ≠ [] := by
        intro empty
        subst executableGoals
        simp at width
        omega
      let branchAgreement : SuperposeBranchAgrees
          (.variable (.generated outputIndex))
          (.var s!"_q{outputIndex}")
          (.conjunction
            (.unify referenceValue (.variable (.generated outputIndex)) ::
              referenceGoals))
          (.var s!"_q{outputIndex}",
            PLeaTTa.Goal.eq executableValue (.var s!"_q{outputIndex}") ::
              executableGoals) :=
        .nonvariable valueAgreement outputAgreement goalsAgreement
      refine ⟨[], [], [],
        (.var s!"_q{outputIndex}",
          PLeaTTa.Goal.eq executableValue (.var s!"_q{outputIndex}") ::
            executableGoals), branchAgreement, ?_, .nil, ?_⟩
      · cases executableValue with
        | var name => exact False.elim (executableNotVariable name rfl)
        | sym name =>
            simp [compileSuperposeBranch, compileBranch, executableNonempty,
              BEq.beq, Atom.beq]
        | gnd value =>
            simp [compileSuperposeBranch, compileBranch, executableNonempty,
              BEq.beq, Atom.beq]
        | expr values =>
            simp [compileSuperposeBranch, compileBranch, executableNonempty,
              BEq.beq, Atom.beq]
      · simpa [branchAgreement] using
          (@SuperposeBranchAgreesSupported.nonvariable termDomain typeDomain
            (.variable (.generated outputIndex)) referenceValue
            (.var s!"_q{outputIndex}") executableValue referenceGoals
            executableGoals valueAgreement outputAgreement goalsAgreement
            valueSupport outputSupport goalsSupport)

/-- Support-carrying general-superpose traversal.  The exact compiler fold,
normalizer output, independent branch agreement, and finite support
certificate are returned in one existential package.  This is the usable
replacement for the false rule that attempted to support every arbitrary
agreement with the same visible reference branches. -/
theorem compileSuperposeBranchesFuel_initial_supported_sound
    {termDomain typeDomain : List LogicVar} {state : TranslatorState}
    (env : CEnv)
    (expressionSupport :
      CompileExprSupportContract state env termDomain typeDomain)
    {outputIndex counter nextCounter : Nat} {sources : List Atom}
    {referenceAliases referenceBranches :
      List PeTTaSpec.PrologCore.Goal}
    (sourcesSupported : SourcesVarsIn termDomain sources)
    (outputSupported :
      termVariablesIn termDomain (.variable (.generated outputIndex)))
    (generatedSupported :
      GeneratedVarsIn termDomain counter nextCounter)
    (native : TranslatesSuperposeBranches state
      (.variable (.generated outputIndex)) counter sources referenceAliases
      referenceBranches nextCounter) :
    ∃ baseFuel,
      0 < baseFuel ∧
      baseFuel < 8 * ((sources.map Atom.size).sum + 1) ∧
      ∀ extraFuel accumulator,
        ∃ rawBranches aliasSources aliasNames executableAliases
            executableBranches,
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
            AliasLedgerAgrees (.generated outputIndex) s!"_q{outputIndex}"
              aliasSources aliasNames referenceAliases executableAliases ∧
            SuperposeBranchesAgreeSupported termDomain typeDomain
              branchesAgreement := by
  cases native with
  | nil =>
      refine ⟨1, by omega, by simp, ?_⟩
      intro extraFuel accumulator
      let outputAgreement :
          TermAgrees (.variable (.generated outputIndex))
            (.var s!"_q{outputIndex}") :=
        .generatedVariable outputIndex
      let branchesAgreement : SuperposeBranchesAgree
          (.variable (.generated outputIndex))
          (.var s!"_q{outputIndex}") [] [] := .nil outputAgreement
      refine ⟨[], [], [], [], [], branchesAgreement, ?_, rfl, .nil, ?_⟩
      · simp only [List.foldlM_nil, List.append_nil, Pure.pure, Except.pure]
      · simpa [branchesAgreement] using
          (@SuperposeBranchesAgreeSupported.nil termDomain typeDomain
            (.variable (.generated outputIndex))
            (.var s!"_q{outputIndex}") outputAgreement outputSupported)
  | cons head built tail =>
      rename_i middleCounter source sources value template sourceGoals
        headAliases tailAliases branch branches
      have headCounterBound := TranslatesExpr.counter_le head
      have tailCounterBound := TranslatesSuperposeBranches.counter_le tail
      obtain ⟨headFuel, headPositive, headBound, headCompiles⟩ :=
        expressionSupport head (sourcesSupported.atom (by simp))
          (generatedSupported.nest (by omega) (by omega))
      obtain ⟨tailFuel, tailPositive, tailBound, tailCompiles⟩ :=
        compileSuperposeBranchesFuel_initial_supported_sound env
          expressionSupport sourcesSupported.tail outputSupported
          (generatedSupported.nest (by omega) (by omega)) tail
      let jointFuel := Nat.max headFuel tailFuel
      have headLeJoint : headFuel ≤ jointFuel := Nat.le_max_left _ _
      have tailLeJoint : tailFuel ≤ jointFuel := Nat.le_max_right _ _
      refine ⟨jointFuel, by omega, ?_, ?_⟩
      · simp only [List.map, List.sum_cons] at tailBound ⊢
        have headLe : headFuel <
            8 * (source.size + (sources.map Atom.size).sum + 1) := by
          omega
        have tailLe : tailFuel <
            8 * (source.size + (sources.map Atom.size).sum + 1) := by
          omega
        exact (Nat.max_lt).2 ⟨headLe, tailLe⟩
      · intro extraFuel accumulator
        obtain ⟨headExtra, headFuelEq⟩ :
            ∃ headExtra, jointFuel + extraFuel = headFuel + headExtra := by
          exact ⟨jointFuel + extraFuel - headFuel, by omega⟩
        obtain ⟨tailExtra, tailFuelEq⟩ :
            ∃ tailExtra, jointFuel + extraFuel = tailFuel + tailExtra := by
          exact ⟨jointFuel + extraFuel - tailFuel, by omega⟩
        obtain ⟨headInternal, headExecutableGoals, headCompiled,
            headResult⟩ := headCompiles headExtra
        obtain ⟨tailRawBranches, tailAliasSources, tailAliasNames,
            tailExecutableAliases, tailExecutableBranches,
            tailBranchesAgreement, tailCompiled, tailNormalized,
            tailAliasesAgreement, tailBranchesSupported⟩ :=
          tailCompiles tailExtra
            (accumulator ++ [(headInternal, headExecutableGoals)])
        obtain ⟨headAliasSources, headAliasNames, headExecutableAliases,
            headExecutableBranch, headBranchAgreement, headNormalized,
            headAliasesAgreement, headBranchSupported⟩ :=
          compileSuperposeBranch_normalized_supported_sound
            headResult.termAgreement headResult.termSupport
            headResult.goalsAgreement headResult.goalsSupport built
            outputSupported
        have headCompiledAt :
            compileExprFuel (jointFuel + extraFuel) env counter source =
              .ok (headInternal, headExecutableGoals, middleCounter) := by
          simpa [headFuelEq] using headCompiled
        have tailCompiledAt :
            List.foldlM
              (fun (acc : List (Atom × List PLeaTTa.Goal) × Nat)
                  expression => do
                let (term, goals, next) ←
                  compileExprFuel (jointFuel + extraFuel) env acc.2 expression
                .ok (acc.1 ++ [(term, goals)], next))
              (accumulator ++ [(headInternal, headExecutableGoals)],
                middleCounter) sources =
              .ok
                ((accumulator ++ [(headInternal, headExecutableGoals)]) ++
                  tailRawBranches, nextCounter) := by
          simpa [tailFuelEq] using tailCompiled
        let branchesAgreement : SuperposeBranchesAgree
            (.variable (.generated outputIndex))
            (.var s!"_q{outputIndex}") (branch :: branches)
            (headExecutableBranch :: tailExecutableBranches) :=
          .cons headBranchAgreement tailBranchesAgreement
        refine ⟨(headInternal, headExecutableGoals) :: tailRawBranches,
          headAliasSources ++ tailAliasSources,
          headAliasNames ++ tailAliasNames,
          headExecutableAliases ++ tailExecutableAliases,
          headExecutableBranch :: tailExecutableBranches,
          branchesAgreement, ?_, ?_,
          headAliasesAgreement.append tailAliasesAgreement, ?_⟩
        · rw [List.foldlM_cons]
          simp only [headCompiledAt, Bind.bind, Except.bind]
          dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind]
            at tailCompiledAt ⊢
          simpa [List.append_assoc] using tailCompiledAt
        · simp only [compileSuperposeBranches]
          rw [headNormalized, tailNormalized]
        · simpa [branchesAgreement] using
            (@SuperposeBranchesAgreeSupported.cons termDomain typeDomain
              (.variable (.generated outputIndex))
              (.var s!"_q{outputIndex}") branch headExecutableBranch branches
              tailExecutableBranches headBranchAgreement
              tailBranchesAgreement outputSupported headBranchSupported
              tailBranchesSupported)
termination_by sources.length
decreasing_by simp_all

/-- Complete alias resolution and public `amb` reconstruction from the
support-carrying traversal contract.  Unlike the older interface, this
theorem has no premise quantifying over arbitrary agreements: the compiler
run, normalized branch list, agreement, and support certificate are obtained
from one source-derived traversal witness. -/
theorem compileSuperposeBranches_alias_supported_finalization_from_contract
    {termDomain typeDomain : List LogicVar} {state : TranslatorState}
    (env : CEnv)
    (expressionSupport :
      CompileExprSupportContract state env termDomain typeDomain)
    {outputIndex counter nextCounter : Nat} {sources : List Atom}
    {referenceAliases referenceBranches :
      List PeTTaSpec.PrologCore.Goal}
    (sourcesSupported : SourcesVarsIn termDomain sources)
    (outputSupported :
      termVariablesIn termDomain (.variable (.generated outputIndex)))
    (generatedSupported :
      GeneratedVarsIn termDomain counter nextCounter)
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
          AliasDomainAvoids (.generated outputIndex) aliasSources
            typeDomain) :
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
    compileSuperposeBranchesFuel_initial_supported_sound env
      expressionSupport sourcesSupported outputSupported generatedSupported
      native
  refine ⟨baseFuel, positive, bounded, ?_⟩
  intro extraFuel accumulator
  obtain ⟨rawBranches, aliasSources, aliasNames, executableAliases,
      executableBranches, branchesAgreement, compiled, normalized,
      aliasLedger, supported⟩ := compiles extraFuel accumulator
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
  have finalized :=
    PLeaTTa.CompilerGoalSubstitutionAdequacy.SuperposeBranchesAgree.finalizedGoalAgrees_of_supported
      resolved.variableState typeChecks branchesAgreement supported
  exact ⟨rawBranches, aliasSources, aliasNames, executableAliases,
    executableBranches, referenceBinding, executableBinding, referenceSeen,
    executableSeen, branchesAgreement, compiled, normalized, resolved,
    typeChecks, supported, finalized⟩

end PLeaTTa.CompilerTranslationSupportAdequacy
