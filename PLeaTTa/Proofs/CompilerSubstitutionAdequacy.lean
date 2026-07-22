-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.CompilerSubstitutionAdequacy
Purpose: Transport independent/executable representation agreement through
  finite substitutions on an explicit logical-variable domain.
Trusted boundary: none
Main exports: VariableStateAgreesOn,
  TermAgrees.subst_of_variableStateOn,
  ResolvedAliasStateOn.typeCheckSubstitutionAgreesOn,
  AliasLedgerAgrees.resolveVariableStateAndTypeCheckOn,
  compileSuperposeBranches_alias_continuation_sound (restricted same-domain
    compatibility result)
-/
import PLeaTTa.Proofs.CompilerAliasFinalizationAdequacy

namespace PLeaTTa.CompilerSubstitutionAdequacy

open Metta (Atom Subst)
open PLeaTTa
open PLeaTTa.CompilerAdequacy
open PLeaTTa.CompilerAliasFinalizationAdequacy
open PLeaTTa.OpenBindingAgreement
open PLeaTTa.PeTTaSpec.PrologCore
open PLeaTTa.PeTTaSpec.PrologCore.OpenSubstitution

/-! ## Finite independent support

The executable variable namespace is not globally injective: a source name
can equal a compiler-generated spelling.  Substitution transport is therefore
stated on the finite independent identities occurring in the syntax being
transported, never on all possible source variables.
-/

mutual

/-- Every independent variable occurring in one term belongs to `domain`. -/
def termVariablesIn (domain : List LogicVar) : Term → Prop
  | .variable identity => identity ∈ domain
  | .atom _ | .integer _ | .float _ | .string _ => True
  | .compound _ arguments => termsVariablesIn domain arguments
  | .list items none => termsVariablesIn domain items
  | .list items (some tail) =>
      termsVariablesIn domain items ∧ termVariablesIn domain tail

/-- Pointwise finite-support predicate for an ordered term sequence. -/
def termsVariablesIn (domain : List LogicVar) : List Term → Prop
  | [] => True
  | term :: terms =>
      termVariablesIn domain term ∧ termsVariablesIn domain terms

end

@[simp] theorem termsVariablesIn_append (domain : List LogicVar)
    (left right : List Term) :
    termsVariablesIn domain (left ++ right) ↔
      termsVariablesIn domain left ∧ termsVariablesIn domain right := by
  induction left with
  | nil => simp [termsVariablesIn]
  | cons head tail induction =>
      simp [termsVariablesIn, induction, and_assoc]

/-! ## Independent substitution equations

These equations make structural transport visible without exposing the
implementation of the independent substitution fold in every later proof.
-/

@[simp] theorem applyTerm_atom (bindings : Substitution) (name : String) :
    bindings.applyTerm (.atom name) = .atom name := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      rcases binding with ⟨source, replacement⟩
      simp [Substitution.applyTerm, induction, Term.instantiateOne]

@[simp] theorem applyTerm_integer (bindings : Substitution) (value : Int) :
    bindings.applyTerm (.integer value) = .integer value := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      rcases binding with ⟨source, replacement⟩
      simp [Substitution.applyTerm, induction, Term.instantiateOne]

@[simp] theorem applyTerm_float (bindings : Substitution) (value : Float) :
    bindings.applyTerm (.float value) = .float value := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      rcases binding with ⟨source, replacement⟩
      simp [Substitution.applyTerm, induction, Term.instantiateOne]

@[simp] theorem applyTerm_string (bindings : Substitution) (value : String) :
    bindings.applyTerm (.string value) = .string value := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      rcases binding with ⟨source, replacement⟩
      simp [Substitution.applyTerm, induction, Term.instantiateOne]

@[simp] theorem applyTerm_compound (bindings : Substitution) (head : String)
    (arguments : List Term) :
    bindings.applyTerm (.compound head arguments) =
      .compound head (bindings.applyTerms arguments) := by
  induction bindings with
  | nil => rfl
  | cons binding bindings induction =>
      rcases binding with ⟨source, replacement⟩
      simp only [Substitution.applyTerm, Substitution.applyTerms, induction,
        Term.instantiateOne]

@[simp] theorem applyTerm_list (bindings : Substitution) (items : List Term)
    (tail : Option Term) :
    bindings.applyTerm (.list items tail) =
      .list (bindings.applyTerms items) (tail.map bindings.applyTerm) := by
  induction bindings with
  | nil => cases tail <;> rfl
  | cons binding bindings induction =>
      rcases binding with ⟨source, replacement⟩
      cases tail <;>
        simp [Substitution.applyTerm, Substitution.applyTerms, induction,
          Term.instantiateOne]

/-! ## Cross-representation substitution transport -/

/-- Pointwise agreement of the independent and executable substitution
states on a finite identity domain.  Source and generated namespaces remain
separate in the premise even when their executable spellings could collide
outside the domain. -/
structure VariableStateAgreesOn (reference : Substitution)
    (executable : Subst) (domain : List LogicVar) : Prop where
  source (name : String) (member : .source name ∈ domain) :
    TermStateAgrees reference executable (.variable (.source name))
      (.var name)
  generated (index : Nat) (member : .generated index ∈ domain) :
    TermStateAgrees reference executable (.variable (.generated index))
      (.var (generatedExecutableName index))

/-- Structural transport theorem for the complete currently supported term
encoding.  The proof recurses over the independent representation relation;
it is not a second executable substitution algorithm. -/
theorem TermAgrees.subst_of_variableStateOn
    {reference : Substitution} {executable : Subst}
    {domain : List LogicVar}
    (variableAgreement :
      VariableStateAgreesOn reference executable domain)
    {term : Term} {atom : Atom} (agreement : TermAgrees term atom)
    (supported : termVariablesIn domain term) :
    TermAgrees (reference.applyTerm term)
      (PLeaTTa.subst executable atom) := by
  apply TermAgrees.rec
    (motive_1 := fun term atom _ =>
      termVariablesIn domain term →
        TermAgrees (reference.applyTerm term)
          (PLeaTTa.subst executable atom))
    (motive_2 := fun terms atom _ =>
      termsVariablesIn domain terms →
        ProperListAgrees (reference.applyTerms terms)
          (PLeaTTa.subst executable atom))
  · intro name member
    exact variableAgreement.source name member
  · intro index member
    exact variableAgreement.generated index member
  · intro name notTrue notFalse _supported
    simpa using TermAgrees.atom notTrue notFalse
  · intro _supported
    simpa using TermAgrees.trueAtom
  · intro _supported
    simpa using TermAgrees.falseAtom
  · intro value _supported
    simpa using TermAgrees.integer value
  · intro value _supported
    simpa using TermAgrees.float value
  · intro value _supported
    simpa using TermAgrees.string value
  · intro head terms encoded arguments induction termSupport
    have termsSupport : termsVariablesIn domain terms := by
      simpa [termVariablesIn, termsVariablesIn] using termSupport
    simpa [chainOf, consC, nilA] using
      TermAgrees.partialValue (induction termsSupport)
  · intro items encoded elements induction termSupport
    have itemsSupport : termsVariablesIn domain items := by
      simpa [termVariablesIn] using termSupport
    simpa using TermAgrees.properList (induction itemsSupport)
  · intro _supported
    simpa [nilA] using ProperListAgrees.nil
  · intro term atom terms tail head rest headInduction restInduction support
    simpa [consC] using
      ProperListAgrees.cons (headInduction support.1)
        (restInduction support.2)
  · exact agreement
  · exact supported

/-- Ordered term-list agreement transports pointwise through related finite
substitutions without re-proving the proper-list encoding. -/
theorem TermsAgree.subst_of_variableStateOn
    {reference : Substitution} {executable : Subst}
    {domain : List LogicVar}
    (variableAgreement :
      VariableStateAgreesOn reference executable domain)
    {terms : List Term} {atoms : List Atom}
    (agreement : TermsAgree terms atoms)
    (supported : termsVariablesIn domain terms) :
    TermsAgree (reference.applyTerms terms)
      (atoms.map (PLeaTTa.subst executable)) := by
  induction agreement with
  | nil => simpa using TermsAgree.nil
  | cons head tail induction =>
      simpa using TermsAgree.cons
        (PLeaTTa.CompilerSubstitutionAdequacy.TermAgrees.subst_of_variableStateOn
          variableAgreement head supported.1)
        (induction supported.2)

/-- A finite independent substitution fixes every supported term once it
fixes each variable identity in the declared domain.  This is the reusable
freshness bridge needed to turn alias-domain disjointness into structural
type-template stability. -/
theorem Substitution.applyTerm_eq_self_of_fixedOn
    {binding : Substitution} {domain : List LogicVar}
    (fixed : ∀ identity, identity ∈ domain →
      binding.applyTerm (.variable identity) = .variable identity)
    {term : Term} (supported : termVariablesIn domain term) :
    binding.applyTerm term = term := by
  apply Term.rec
    (motive_1 := fun term => termVariablesIn domain term →
      binding.applyTerm term = term)
    (motive_2 := fun terms => termsVariablesIn domain terms →
      binding.applyTerms terms = terms)
    (motive_3 := fun tail =>
      match tail with
      | none => True
      | some term => termVariablesIn domain term →
          binding.applyTerm term = term)
  · intro identity member
    exact fixed identity member
  · intro name _supported
    simp
  · intro value _supported
    simp
  · intro value _supported
    simp
  · intro value _supported
    simp
  · intro functor arguments induction support
    simp [induction support]
  · intro items tail itemsInduction tailInduction support
    cases tail with
    | none => simp [itemsInduction support]
    | some tail =>
        simp only [termVariablesIn] at support
        simp [itemsInduction support.1, tailInduction support.2]
  · intro _support
    simp
  · intro head tail headInduction tailInduction support
    simp only [termsVariablesIn] at support
    simp [headInduction support.1, tailInduction support.2]
  · trivial
  · intro term induction
    exact induction
  · exact supported

/-- Ordered-list counterpart of
`Substitution.applyTerm_eq_self_of_fixedOn`. -/
theorem Substitution.applyTerms_eq_self_of_fixedOn
    {binding : Substitution} {domain : List LogicVar}
    (fixed : ∀ identity, identity ∈ domain →
      binding.applyTerm (.variable identity) = .variable identity)
    {terms : List Term} (supported : termsVariablesIn domain terms) :
    binding.applyTerms terms = terms := by
  induction terms with
  | nil => simp
  | cons head tail induction =>
      simp only [termsVariablesIn] at supported
      simp [Substitution.applyTerm_eq_self_of_fixedOn fixed supported.1,
        induction supported.2]

/-! ## Alias-domain freshness factorization -/

/-- Every identity in a continuation domain is either the shared target
(which alias resolution fixes) or lies outside the canonical alias domain. -/
def AliasDomainAvoids (target : LogicVar) (sources domain : List LogicVar) :
    Prop :=
  ∀ identity, identity ∈ domain → identity = target ∨ identity ∉ sources

/-- Exact independent alias states fix every term supported by a domain that
avoids their actual source keys. -/
theorem aliasStateExactly_applyTerm_eq_self_of_domainAvoids
    {target : LogicVar} {sources : List LogicVar}
    {binding : Substitution}
    (state : AliasStateExactly target sources binding)
    {domain : List LogicVar}
    (avoids : AliasDomainAvoids target sources domain)
    {term : Term} (supported : termVariablesIn domain term) :
    binding.applyTerm term = term := by
  apply Substitution.applyTerm_eq_self_of_fixedOn
    (binding := binding) (domain := domain)
  · intro identity member
    rcases avoids identity member with same | absent
    · subst identity
      exact state.targetFixed
    · by_cases same : identity = target
      · subst identity
        exact state.targetFixed
      · exact state.outsideFixed identity same absent
  · exact supported

/-- Executable alias bindings fix atoms whose variables avoid the canonical
source-name domain. -/
theorem subst_aliasBinding_eq_self_of_namesOutside
    {target : String} {sources : List String} {atom : Atom}
    (outside : ∀ name, name ∈ atom.vars → name ∉ sources) :
    subst (aliasBinding target sources) atom = atom := by
  apply subst_eq_self_of_domain_free
  intro name member
  exact lookup_aliasBinding_of_not_mem (outside name member)

/-- Proper-list encoding introduces no variables of its own. -/
theorem chainOf_vars (atoms : List Atom) :
    (chainOf atoms).vars = atoms.flatMap Atom.vars := by
  induction atoms with
  | nil => simp [chainOf, nilA, Atom.vars]
  | cons head tail induction =>
      change (consC head (chainOf tail)).vars =
        head.vars ++ tail.flatMap Atom.vars
      simp [consC, Atom.vars, induction]

/-- Deep chainification preserves the exact ordered variable-occurrence
list.  It changes only structural constructors and boolean spellings. -/
theorem chainify_vars (atom : Atom) :
    (chainify atom).vars = atom.vars := by
  apply Atom.rec
    (motive_1 := fun atom => (chainify atom).vars = atom.vars)
    (motive_2 := fun atoms =>
      (atoms.map chainify).flatMap Atom.vars = atoms.flatMap Atom.vars)
  · intro name
    by_cases isTrue : name = "true"
    · subst name
      simp [chainify, canonBool, Atom.vars]
    · by_cases isFalse : name = "false"
      · subst name
        simp [chainify, canonBool, Atom.vars]
      · simp [chainify, canonBool, Atom.vars, isTrue, isFalse]
  · intro name
    simp [chainify, canonBool, Atom.vars]
  · intro ground
    cases ground with
    | bool value =>
        cases value <;> simp [chainify, canonBool, Atom.vars]
    | _ => simp [chainify, canonBool, Atom.vars]
  · intro atoms induction
    rw [chainify_expr, chainOf_vars]
    simp only [Atom.vars]
    simpa [List.flatMap] using induction
  · rfl
  · intro head tail headInduction tailInduction
    simp [headInduction, tailInduction]

/-- Compiler-generated identities retain an injective executable spelling on
every finite index list.  Possible collisions arise only when source names
enter the same string namespace. -/
theorem generatedEncodingInjectiveOn (indices : List Nat) :
    EncodingInjectiveOn (indices.map LogicVar.generated) := by
  intro left right leftMember rightMember sameName
  rcases List.mem_map.mp leftMember with ⟨leftIndex, _leftIndexMember, rfl⟩
  rcases List.mem_map.mp rightMember with
    ⟨rightIndex, _rightIndexMember, rfl⟩
  congr
  simp only [logicVarExecutableName, generatedExecutableName] at sameName
  have decoded := congrArg compilerGeneratedIndex? sameName
  rw [PLeaTTa.CompilerFreshness.compilerGeneratedIndex?_name,
    PLeaTTa.CompilerFreshness.compilerGeneratedIndex?_name] at decoded
  exact Option.some.inj decoded

/-- A type-check carry template contains only first occurrences of variables
already present in its raw expected type. -/
theorem typeCheckBindingTemplate_vars_subset (expected : Atom)
    {name : String}
    (member : name ∈ (typeCheckBindingTemplate expected).vars) :
    name ∈ expected.vars := by
  unfold typeCheckBindingTemplate at member
  split at member
  · simp [Atom.vars] at member
  · unfold bindingTemplate at member
    rw [chainOf_vars] at member
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      Atom.vars, List.nil_append, List.mem_flatMap] at member
    rcases member with ⟨varAtom, variableMember, nameMember⟩
    simp only [List.mem_map] at variableMember
    rcases variableMember with ⟨sourceName, sourceMember, rfl⟩
    simp [Atom.vars] at nameMember
    subst name
    exact List.mem_eraseDups.mp sourceMember

mutual

/-- Every executable variable in an agreeing expected type comes from one
generated independent identity in the declared finite support. -/
theorem typeCheckExpectedAgrees_executableVar_mem_domain
    {domain : List LogicVar}
    {reference : Term} {executable template : Atom}
    (agreement : TypeCheckExpectedAgrees reference executable template)
    (supported : termVariablesIn domain reference)
    {name : String} (member : name ∈ executable.vars) :
    ∃ index, .generated index ∈ domain ∧
      name = generatedExecutableName index := by
  cases agreement with
  | atom atomName => simp [Atom.vars] at member
  | generated index =>
      simp only [termVariablesIn] at supported
      simp only [Atom.vars, List.mem_singleton] at member
      subst name
      exact ⟨index, supported, rfl⟩
  | expression items =>
      simp only [termVariablesIn] at supported
      apply typeCheckExpectedListAgrees_executableVar_mem_domain items
        supported
      simpa [Atom.vars] using member

/-- Ordered-child counterpart of
`TypeCheckExpectedAgrees.executableVar_mem_domain`. -/
theorem typeCheckExpectedListAgrees_executableVar_mem_domain
    {domain : List LogicVar}
    {references : List Term} {executables : List Atom}
    (agreement : TypeCheckExpectedListAgrees references executables)
    (supported : termsVariablesIn domain references)
    {name : String}
    (member : name ∈ (executables.map Atom.vars).flatten) :
    ∃ index, .generated index ∈ domain ∧
      name = generatedExecutableName index := by
  cases agreement with
  | nil => simp at member
  | cons head tail =>
      simp only [termsVariablesIn] at supported
      simp only [List.map_cons, List.flatten_cons, List.mem_append] at member
      rcases member with headMember | tailMember
      · exact typeCheckExpectedAgrees_executableVar_mem_domain head
          supported.1 headMember
      · exact typeCheckExpectedListAgrees_executableVar_mem_domain tail
          supported.2 tailMember

end

/-- Executable half of the type-check freshness obligation.  The three
fields are deliberately syntactic name-disjointness facts: expected type,
deduplicated carry template, and already-chainified equality operand.  They
are the exact facts compiler counter proofs must establish. -/
structure TypeCheckExecutableNamesDisjoint (sources : List String)
    (domain : List LogicVar) : Prop where
  expected {referenceExpected executableExpected executableTemplate}
      (agreement : TypeCheckExpectedAgrees referenceExpected
        executableExpected executableTemplate)
      (supported : termVariablesIn domain referenceExpected) :
      ∀ name, name ∈ executableExpected.vars → name ∉ sources
  template {referenceExpected executableExpected executableTemplate}
      (agreement : TypeCheckExpectedAgrees referenceExpected
        executableExpected executableTemplate)
      (supported : termVariablesIn domain referenceExpected) :
      ∀ name, name ∈ executableTemplate.vars → name ∉ sources
  chainified {referenceExpected executableExpected executableTemplate}
      (agreement : TypeCheckExpectedAgrees referenceExpected
        executableExpected executableTemplate)
      (supported : termVariablesIn domain referenceExpected) :
      ∀ name, name ∈ (chainify executableExpected).vars → name ∉ sources

/-- Finite encoding injectivity transfers independent alias-domain
disjointness to every executable type-check representation.  The generated
type variables are obtained from the independent agreement, not guessed from
their `_q` spelling. -/
theorem typeCheckExecutableNamesDisjoint_of_encoding
    {target : LogicVar} {referenceSources domain : List LogicVar}
    {executableSources : List String}
    (sourceNames : executableSources =
      referenceSources.map logicVarExecutableName)
    (targetFresh : target ∉ referenceSources)
    (injective :
      EncodingInjectiveOn (target :: (referenceSources ++ domain)))
    (avoids : AliasDomainAvoids target referenceSources domain) :
    TypeCheckExecutableNamesDisjoint executableSources domain := by
  have expectedOutside :
      ∀ {referenceExpected executableExpected executableTemplate},
        TypeCheckExpectedAgrees referenceExpected executableExpected
          executableTemplate →
        termVariablesIn domain referenceExpected →
        ∀ name, name ∈ executableExpected.vars → name ∉ executableSources := by
    intro referenceExpected executableExpected executableTemplate agreement
      supported name member executableMember
    obtain ⟨index, domainMember, nameEq⟩ :=
      typeCheckExpectedAgrees_executableVar_mem_domain agreement supported
        member
    rw [sourceNames] at executableMember
    rcases List.mem_map.mp executableMember with
      ⟨source, sourceMember, sourceNameEq⟩
    have sameIdentity : source = .generated index := by
      apply injective
      · simp [List.mem_append, sourceMember]
      · simp [List.mem_append, domainMember]
      · exact sourceNameEq.trans nameEq
    rcases avoids (.generated index) domainMember with sameTarget | absent
    · apply targetFresh
      rw [sameIdentity, sameTarget] at sourceMember
      exact sourceMember
    · exact absent (sameIdentity ▸ sourceMember)
  refine
    { expected := ?_
      template := ?_
      chainified := ?_ }
  · intro referenceExpected executableExpected executableTemplate agreement
      supported name member
    exact expectedOutside agreement supported name member
  · intro referenceExpected executableExpected executableTemplate agreement
      supported name member
    apply expectedOutside agreement supported name
    rw [← agreement.compilerTemplate_eq] at member
    exact typeCheckBindingTemplate_vars_subset executableExpected member
  · intro referenceExpected executableExpected executableTemplate agreement
      supported name member
    apply expectedOutside agreement supported name
    rw [chainify_vars] at member
    exact member

@[simp] theorem applyTerms_append (bindings : Substitution)
    (left right : List Term) :
    bindings.applyTerms (left ++ right) =
      bindings.applyTerms left ++ bindings.applyTerms right := by
  induction left with
  | nil => simp
  | cons head tail induction => simp [induction]

@[simp] theorem applyGoals_append (bindings : Substitution)
    (left right : List PeTTaSpec.PrologCore.Goal) :
    bindings.applyGoals (left ++ right) =
      bindings.applyGoals left ++ bindings.applyGoals right := by
  induction left with
  | nil => simp
  | cons head tail induction => simp [induction]

@[simp] theorem substCompiledGoals_append (binding : Subst)
    (left right : List PLeaTTa.Goal) :
    substCompiledGoals binding (left ++ right) =
      substCompiledGoals binding left ++
        substCompiledGoals binding right := by
  induction left with
  | nil => rfl
  | cons head tail induction =>
      simp [substCompiledGoals, induction]

/-! ## Finite support and transport for continuation goals -/

mutual

/-- Every independent variable occurring in one goal belongs to `domain`. -/
def goalVariablesIn (domain : List LogicVar) :
    PeTTaSpec.PrologCore.Goal → Prop
  | .truth | .fail | .cut => True
  | .unify left right | .identical left right =>
      termVariablesIn domain left ∧ termVariablesIn domain right
  | .call _ arguments => termsVariablesIn domain arguments
  | .conjunction goals | .disjunction goals =>
      goalsVariablesIn domain goals
  | .ifThenElse condition thenBranch elseBranch
  | .softCut condition thenBranch elseBranch =>
      goalVariablesIn domain condition ∧
        goalVariablesIn domain thenBranch ∧
        goalVariablesIn domain elseBranch
  | .negation goal | .once goal | .transaction goal =>
      goalVariablesIn domain goal
  | .findall template goal output =>
      termVariablesIn domain template ∧
        goalVariablesIn domain goal ∧
        termVariablesIn domain output
  | .catch goal exception handler =>
      goalVariablesIn domain goal ∧
        termVariablesIn domain exception ∧
        goalVariablesIn domain handler
  | .withMutex mutex goal =>
      termVariablesIn domain mutex ∧ goalVariablesIn domain goal
  | .forall generator test =>
      goalVariablesIn domain generator ∧ goalVariablesIn domain test

/-- Pointwise finite-support predicate for an ordered goal sequence. -/
def goalsVariablesIn (domain : List LogicVar) :
    List PeTTaSpec.PrologCore.Goal → Prop
  | [] => True
  | goal :: goals =>
      goalVariablesIn domain goal ∧ goalsVariablesIn domain goals

end

@[simp] theorem goalsVariablesIn_append (domain : List LogicVar)
    (left right : List PeTTaSpec.PrologCore.Goal) :
    goalsVariablesIn domain (left ++ right) ↔
      goalsVariablesIn domain left ∧ goalsVariablesIn domain right := by
  induction left with
  | nil => simp [goalsVariablesIn]
  | cons head tail induction =>
      simp [goalsVariablesIn, induction, and_assoc]

/-- Closure contract needed to transport the nested goal lists stored by
branch constructors.  It is separated from alias resolution so each compiler
goal constructor can discharge it once and every enclosing construct can
reuse the result. -/
def GoalsSubstitutionAgrees (reference : Substitution)
    (executable : Subst) (domain : List LogicVar) : Prop :=
  ∀ {referenceGoals executableGoals},
    GoalsAgree referenceGoals executableGoals →
    goalsVariablesIn domain referenceGoals →
    GoalsAgree (reference.applyGoals referenceGoals)
      (substCompiledGoals executable executableGoals)

/-- The one specialized closure obligation not implied by ordinary term
agreement. Type-check carry templates erase duplicate generated names before
execution, and deep chainification does not commute with an arbitrary
variable-to-compound substitution.  A caller must therefore prove both the
transported expected/template relation and the exact emitted chainified
value, rather than assuming either representation law. -/
def TypeCheckSubstitutionAgrees (reference : Substitution)
    (executable : Subst) (domain : List LogicVar) : Prop :=
  ∀ {referenceExpected executableExpected executableTemplate},
    TypeCheckExpectedAgrees referenceExpected executableExpected
      executableTemplate →
    termVariablesIn domain referenceExpected →
    TypeCheckExpectedAgrees (reference.applyTerm referenceExpected)
        (subst executable executableExpected)
        (subst executable executableTemplate) ∧
      subst executable (chainify executableExpected) =
        chainify (subst executable executableExpected)

/-- Freshness-facing form of the specialized type-check obligation.  It asks
only that the independent expected type and the three already-emitted
executable representations are fixed.  This is strictly easier for compiler
counter/disjointness proofs to establish than reconstructing the dependent
agreement relation directly. -/
def TypeCheckStateFixedOn (reference : Substitution)
    (executable : Subst) (domain : List LogicVar) : Prop :=
  ∀ {referenceExpected executableExpected executableTemplate},
    TypeCheckExpectedAgrees referenceExpected executableExpected
      executableTemplate →
    termVariablesIn domain referenceExpected →
    reference.applyTerm referenceExpected = referenceExpected ∧
      subst executable executableExpected = executableExpected ∧
      subst executable executableTemplate = executableTemplate ∧
      subst executable (chainify executableExpected) =
        chainify executableExpected

/-- Independent alias-state exactness plus executable name-disjointness
jointly establish the freshness-facing type-check certificate. -/
theorem typeCheckStateFixedOn_of_aliasDisjoint
    {target : LogicVar} {referenceSources : List LogicVar}
    {referenceBinding : Substitution}
    (referenceState :
      AliasStateExactly target referenceSources referenceBinding)
    {targetName : String} {executableSources : List String}
    {domain : List LogicVar}
    (referenceDisjoint :
      AliasDomainAvoids target referenceSources domain)
    (executableDisjoint :
      TypeCheckExecutableNamesDisjoint executableSources domain) :
    TypeCheckStateFixedOn referenceBinding
      (aliasBinding targetName executableSources) domain := by
  intro referenceExpected executableExpected executableTemplate agreement
    supported
  refine ⟨aliasStateExactly_applyTerm_eq_self_of_domainAvoids
      referenceState referenceDisjoint supported, ?_, ?_, ?_⟩
  · exact subst_aliasBinding_eq_self_of_namesOutside
      (executableDisjoint.expected agreement supported)
  · exact subst_aliasBinding_eq_self_of_namesOutside
      (executableDisjoint.template agreement supported)
  · exact subst_aliasBinding_eq_self_of_namesOutside
      (executableDisjoint.chainified agreement supported)

/-- A fixed-state certificate discharges the exact type-check transport
contract without any commutation or deduplication assumption. -/
theorem typeCheckSubstitutionAgrees_of_fixed
    {reference : Substitution} {executable : Subst}
    {domain : List LogicVar}
    (fixed : TypeCheckStateFixedOn reference executable domain) :
    TypeCheckSubstitutionAgrees reference executable domain := by
  intro referenceExpected executableExpected executableTemplate agreement
    supported
  obtain ⟨referenceFixed, expectedFixed, templateFixed, chainifiedFixed⟩ :=
    fixed agreement supported
  constructor
  · simpa [referenceFixed, expectedFixed, templateFixed] using agreement
  · rw [chainifiedFixed, expectedFixed]

/-! ## Identity witnesses and sharp negative boundaries -/

@[simp] theorem map_subst_nil (atoms : List Atom) :
    atoms.map (PLeaTTa.subst []) = atoms := by
  induction atoms <;> simp_all

mutual

/-- Deep executable goal substitution is the identity for the empty state. -/
theorem substCompiledGoal_nil (goal : PLeaTTa.Goal) :
    substCompiledGoal [] goal = goal := by
  cases goal <;>
    simp [substCompiledGoal, substCompiledGoals_nil,
      substCompiledBranches_nil]

/-- Ordered executable goal substitution is the identity for the empty
state. -/
theorem substCompiledGoals_nil (goals : List PLeaTTa.Goal) :
    substCompiledGoals [] goals = goals := by
  cases goals with
  | nil => rfl
  | cons goal goals =>
      simp [substCompiledGoals, substCompiledGoal_nil,
        substCompiledGoals_nil]

/-- Branch-template substitution is the identity for the empty state. -/
theorem substCompiledBranches_nil
    (branches : List (Atom × List PLeaTTa.Goal)) :
    substCompiledBranches [] branches = branches := by
  cases branches with
  | nil => rfl
  | cons branch branches =>
      rcases branch with ⟨template, goals⟩
      simp [substCompiledBranches, substCompiledGoals_nil,
        substCompiledBranches_nil]

end

/-- The specialized type-check closure contract is inhabited: no
substitution transports every supported expected type exactly. -/
theorem typeCheckSubstitutionAgrees_nil (domain : List LogicVar) :
    TypeCheckSubstitutionAgrees [] [] domain := by
  intro referenceExpected executableExpected executableTemplate agreement
    _supported
  exact ⟨by simpa using agreement, by simp⟩

/-- The ordinary goal-list closure contract is likewise non-vacuous. -/
theorem goalsSubstitutionAgrees_nil (domain : List LogicVar) :
    GoalsSubstitutionAgrees [] [] domain := by
  intro referenceGoals executableGoals agreement _supported
  simpa [substCompiledGoals_nil] using agreement

/-- A genuinely nonempty alias state satisfies the type-check transport when
its source is disjoint from the continuation's generated variables.  This
positive witness complements the collision counterexample below. -/
theorem typeCheckSubstitution_aliasDisjoint_example :
    TypeCheckSubstitutionAgrees
      [(.generated 1, .variable (.generated 0))]
      [("_q1", .var "_q0")]
      [.generated 0, .generated 2] := by
  have referenceState :
      AliasStateExactly (.generated 0) [.generated 1]
        [(.generated 1, .variable (.generated 0))] := by
    refine
      { targetFixed := ?_
        sourceAliases := ?_
        outsideFixed := ?_ }
    · simp [Substitution.applyTerm, Term.instantiateOne]
    · intro source member
      simp only [List.mem_singleton] at member
      subst source
      simp [Substitution.applyTerm, Term.instantiateOne]
    · intro identity notTarget notSource
      have different : identity ≠ .generated 1 := by simpa using notSource
      simp [Substitution.applyTerm, Term.instantiateOne, different]
  have referenceDisjoint :
      AliasDomainAvoids (.generated 0) [.generated 1]
        [.generated 0, .generated 2] := by
    intro identity member
    simp at member
    rcases member with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by simp)
  have finiteInjective :
      EncodingInjectiveOn
        [.generated 0, .generated 1, .generated 0, .generated 2] := by
    change EncodingInjectiveOn
      ([0, 1, 0, 2].map LogicVar.generated)
    exact generatedEncodingInjectiveOn [0, 1, 0, 2]
  have executableDisjoint :
      TypeCheckExecutableNamesDisjoint ["_q1"]
        [.generated 0, .generated 2] :=
    typeCheckExecutableNamesDisjoint_of_encoding
      (target := .generated 0) (referenceSources := [.generated 1])
      (domain := [.generated 0, .generated 2])
      (executableSources := ["_q1"]) rfl (by simp) finiteInjective
        referenceDisjoint
  have fixed :
      TypeCheckStateFixedOn
        [(.generated 1, .variable (.generated 0))]
        [("_q1", .var "_q0")] [.generated 0, .generated 2] := by
    intro referenceExpected executableExpected executableTemplate agreement
      supported
    have canonical :
        TypeCheckStateFixedOn
          [(.generated 1, .variable (.generated 0))]
          (aliasBinding "_q0" ["_q1"])
          [.generated 0, .generated 2] :=
      typeCheckStateFixedOn_of_aliasDisjoint
        (targetName := "_q0") referenceState referenceDisjoint
          executableDisjoint
    unfold TypeCheckStateFixedOn at canonical
    simpa [aliasBinding] using
      (@canonical referenceExpected executableExpected executableTemplate
        agreement supported)
  intro referenceExpected executableExpected executableTemplate agreement
    supported
  obtain ⟨referenceFixed, expectedFixed, templateFixed, chainifiedFixed⟩ :=
    fixed (referenceExpected := referenceExpected)
      (executableExpected := executableExpected)
      (executableTemplate := executableTemplate) agreement supported
  constructor
  · simpa [referenceFixed, expectedFixed, templateFixed] using agreement
  · rw [chainifiedFixed, expectedFixed]

/-- Arbitrary substitution cannot be moved through deep chainification.
This concrete variable-to-compound witness prevents the specialized
type-check premise above from being weakened to a false generic lemma. -/
theorem subst_chainify_counterexample :
    subst [("_q0", .expr [.sym "a"])] (chainify (.var "_q0")) ≠
      chainify (subst [("_q0", .expr [.sym "a"])] (.var "_q0")) := by
  have lookup :
      Metta.Subst.lookup [("_q0", Atom.expr [Atom.sym "a"])] "_q0" =
        some (Atom.expr [Atom.sym "a"]) := by
    rfl
  have closed : (Atom.expr [Atom.sym "a"]).vars = [] := by
    simp [Atom.vars]
  rw [show chainify (Atom.var "_q0") = Atom.var "_q0" by
    simp [chainify, canonBool]]
  rw [subst_var_of_lookup_closed _ _ _ lookup closed]
  simp [chainify, chainOf, consC, nilA]

/-- Even a variable-to-variable alias can invalidate a type-check carry:
merging two distinct generated expected-type variables happens after the
template's first-occurrence deduplication.  The compiler must therefore
derive disjointness of branch-result aliases from freshened type variables;
it may not assume generic closure. -/
theorem typeCheckSubstitution_aliasMerge_counterexample :
    ¬ TypeCheckSubstitutionAgrees
      [(.generated 0, .variable (.generated 1))]
      [("_q0", .var "_q1")]
      [.generated 0, .generated 1] := by
  intro transport
  let expected : Term := .list
    [.variable (.generated 0), .variable (.generated 1)] none
  have agreement : TypeCheckExpectedAgrees expected
      (.expr [.var "_q0", .var "_q1"])
      (referenceTypeCheckTemplate expected) := by
    exact .expression (.cons (.generated 0) (.cons (.generated 1) .nil))
  have supported :
      termVariablesIn [.generated 0, .generated 1] expected := by
    simp [expected, termVariablesIn, termsVariablesIn]
  have transported := (transport agreement supported).1
  have q0 : toString "_q" ++ Nat.repr 0 = "_q0" := by decide
  have q1 : toString "_q" ++ Nat.repr 1 = "_q1" := by decide
  simp [expected, Substitution.applyTerm,
    Term.instantiateOne, Terms.instantiateOne,
    referenceTypeCheckTemplate, referenceTypeVariableNames,
    referenceTypeVariableNamesList, List.eraseDups_cons,
    subst, substN, Metta.Subst.lookup, q0, q1,
    chainOf, consC, nilA] at transported
  cases transported

/-- Pointwise deep substitution cannot turn a nonempty goal list into the
empty list. -/
theorem substCompiledGoals_ne_nil {binding : Subst}
    {goals : List PLeaTTa.Goal} (nonempty : goals ≠ []) :
    substCompiledGoals binding goals ≠ [] := by
  cases goals with
  | nil => contradiction
  | cons goal goals => simp [substCompiledGoals]

/-- Literal-only nondeterministic branches transport without a nested-goal
premise. Their empty bodies remain empty, while order and multiplicity are
retained by the relation induction. -/
theorem LiteralAmbBranchesAgree.subst_of_variableStateOn
    {reference : Substitution} {executable : Subst}
    {domain : List LogicVar}
    (variableAgreement :
      VariableStateAgreesOn reference executable domain)
    {referenceOutput : Term} {executableOutput : Atom}
    {referenceBranches : List PeTTaSpec.PrologCore.Goal}
    {executableBranches : List (Atom × List PLeaTTa.Goal)}
    (agreement : LiteralAmbBranchesAgree referenceOutput executableOutput
      referenceBranches executableBranches)
    (outputSupported : termVariablesIn domain referenceOutput)
    (branchesSupported : goalsVariablesIn domain referenceBranches) :
    LiteralAmbBranchesAgree (reference.applyTerm referenceOutput)
      (subst executable executableOutput)
      (reference.applyGoals referenceBranches)
      (substCompiledBranches executable executableBranches) := by
  induction agreement with
  | nil =>
      simpa [substCompiledBranches] using
        (LiteralAmbBranchesAgree.nil :
          LiteralAmbBranchesAgree (reference.applyTerm referenceOutput)
            (subst executable executableOutput) [] [])
  | cons value output tail induction =>
      have value' :=
        PLeaTTa.CompilerSubstitutionAdequacy.TermAgrees.subst_of_variableStateOn
          variableAgreement value branchesSupported.1.1
      have output' :=
        PLeaTTa.CompilerSubstitutionAdequacy.TermAgrees.subst_of_variableStateOn
          variableAgreement output outputSupported
      have tail' := induction branchesSupported.2
      simpa [substCompiledBranches, substCompiledGoals] using
        LiteralAmbBranchesAgree.cons value' output' tail'

/-- A normalized superpose branch transports through any related finite
variable state once nested goal-list transport is available. -/
theorem SuperposeBranchAgrees.subst_of_variableStateOn
    {reference : Substitution} {executable : Subst}
    {domain : List LogicVar}
    (variableAgreement :
      VariableStateAgreesOn reference executable domain)
    (goalTransport :
      GoalsSubstitutionAgrees reference executable domain)
    {referenceOutput : Term} {executableOutput : Atom}
    {referenceBranch : PeTTaSpec.PrologCore.Goal}
    {executableBranch : Atom × List PLeaTTa.Goal}
    (agreement : SuperposeBranchAgrees referenceOutput executableOutput
      referenceBranch executableBranch)
    (outputSupported : termVariablesIn domain referenceOutput)
    (branchSupported : goalVariablesIn domain referenceBranch) :
    SuperposeBranchAgrees (reference.applyTerm referenceOutput)
      (subst executable executableOutput)
      (reference.applyGoal referenceBranch)
      (subst executable executableBranch.1,
        substCompiledGoals executable executableBranch.2) := by
  cases agreement with
  | empty value output =>
      simpa [substCompiledGoals] using SuperposeBranchAgrees.empty
        (PLeaTTa.CompilerSubstitutionAdequacy.TermAgrees.subst_of_variableStateOn
          variableAgreement value branchSupported.1)
        (PLeaTTa.CompilerSubstitutionAdequacy.TermAgrees.subst_of_variableStateOn
          variableAgreement output outputSupported)
  | aliased output goals nonempty =>
      simpa using SuperposeBranchAgrees.aliased
        (PLeaTTa.CompilerSubstitutionAdequacy.TermAgrees.subst_of_variableStateOn
          variableAgreement output outputSupported)
        (goalTransport goals branchSupported)
        (substCompiledGoals_ne_nil nonempty)
  | nonvariable value output goals =>
      simpa [substCompiledGoals, substCompiledGoal] using
        SuperposeBranchAgrees.nonvariable
          (PLeaTTa.CompilerSubstitutionAdequacy.TermAgrees.subst_of_variableStateOn
            variableAgreement value branchSupported.1.1)
          (PLeaTTa.CompilerSubstitutionAdequacy.TermAgrees.subst_of_variableStateOn
            variableAgreement output outputSupported)
          (goalTransport goals branchSupported.2)

/-- Ordered superpose branch collections transport pointwise; the list
induction preserves alternative order and duplicate occurrences exactly. -/
theorem SuperposeBranchesAgree.subst_of_variableStateOn
    {reference : Substitution} {executable : Subst}
    {domain : List LogicVar}
    (variableAgreement :
      VariableStateAgreesOn reference executable domain)
    (goalTransport :
      GoalsSubstitutionAgrees reference executable domain)
    {referenceOutput : Term} {executableOutput : Atom}
    {referenceBranches : List PeTTaSpec.PrologCore.Goal}
    {executableBranches : List (Atom × List PLeaTTa.Goal)}
    (agreement : SuperposeBranchesAgree referenceOutput executableOutput
      referenceBranches executableBranches)
    (outputSupported : termVariablesIn domain referenceOutput)
    (branchesSupported :
      goalsVariablesIn domain referenceBranches) :
    SuperposeBranchesAgree (reference.applyTerm referenceOutput)
      (subst executable executableOutput)
      (reference.applyGoals referenceBranches)
      (substCompiledBranches executable executableBranches) := by
  induction referenceBranches generalizing executableBranches with
  | nil =>
      cases agreement
      simpa [substCompiledBranches] using
        (SuperposeBranchesAgree.nil :
          SuperposeBranchesAgree (reference.applyTerm referenceOutput)
            (subst executable executableOutput) [] [])
  | cons referenceBranch referenceBranches induction =>
      cases agreement with
      | cons head tail =>
          have head' :=
            PLeaTTa.CompilerSubstitutionAdequacy.SuperposeBranchAgrees.subst_of_variableStateOn
              variableAgreement goalTransport head outputSupported
              branchesSupported.1
          have tail' := induction tail branchesSupported.2
          simpa [substCompiledBranches] using
            SuperposeBranchesAgree.cons head' tail'

/-- The transported branch collection reconstructs the complete public
`amb` goal agreement after finalization. -/
theorem SuperposeBranchesAgree.finalizedGoalAgrees
    {reference : Substitution} {executable : Subst}
    {domain : List LogicVar}
    (variableAgreement :
      VariableStateAgreesOn reference executable domain)
    (goalTransport :
      GoalsSubstitutionAgrees reference executable domain)
    {referenceOutput : Term} {executableOutput : Atom}
    {referenceBranches : List PeTTaSpec.PrologCore.Goal}
    {executableBranches : List (Atom × List PLeaTTa.Goal)}
    (agreement : SuperposeBranchesAgree referenceOutput executableOutput
      referenceBranches executableBranches)
    (outputSupported : termVariablesIn domain referenceOutput)
    (branchesSupported :
      goalsVariablesIn domain referenceBranches) :
    GoalAgrees
      (reference.applyGoal (.disjunction referenceBranches))
      (substCompiledGoal executable
        (.amb executableBranches executableOutput)) := by
  have branches :=
    PLeaTTa.CompilerSubstitutionAdequacy.SuperposeBranchesAgree.subst_of_variableStateOn
      variableAgreement goalTransport agreement outputSupported
      branchesSupported
  simpa [substCompiledGoal] using GoalAgrees.builtAmb branches

/-! ## Alias-ledger instantiation -/

/-- Reusable certificate produced by resolving one related compiler-alias
ledger.  It retains the two resolver results, their canonical source domains,
the exact independent alias state, and finite cross-representation state
agreement.  Keeping these facts together avoids re-running the resolver proof
for each continuation invariant (type checks, ordinary goals, and later
observation transport). -/
structure ResolvedAliasStateOn
    (target : LogicVar) (targetName : String)
    (sources : List LogicVar) (sourceNames : List String)
    (referenceGoals : List PeTTaSpec.PrologCore.Goal)
    (executableGoals : List PLeaTTa.Goal)
    (domain : List LogicVar)
    (reference : Substitution) (executable : Subst)
    (referenceSeen : List LogicVar) (executableSeen : List String) : Prop where
  referenceSeen_eq :
    referenceSeen = sources.foldl
      (fun seen source => insertAliasSource target source seen) []
  executableSeen_eq :
    executableSeen = sourceNames.foldl
      (fun seen source => insertAliasSource targetName source seen) []
  referenceResolution :
    ResolvesAliasGoals [] referenceGoals reference
  executableResolution :
    resolveCompileAliases (collectCompileAliasesGoals executableGoals) =
      .ok executable
  referenceState : AliasStateExactly target referenceSeen reference
  executableBinding : executable = aliasBinding targetName executableSeen
  seenNames : executableSeen = referenceSeen.map logicVarExecutableName
  seenWithinSources :
    ∀ identity, identity ∈ referenceSeen → identity ∈ sources
  variableState : VariableStateAgreesOn reference executable domain

/-- The independent canonical source domain is duplicate-free and excludes
its shared target. -/
theorem ResolvedAliasStateOn.referenceWellFormed
    {target : LogicVar} {targetName : String}
    {sources : List LogicVar} {sourceNames : List String}
    {referenceGoals : List PeTTaSpec.PrologCore.Goal}
    {executableGoals : List PLeaTTa.Goal} {domain : List LogicVar}
    {reference : Substitution} {executable : Subst}
    {referenceSeen : List LogicVar} {executableSeen : List String}
    (resolved : ResolvedAliasStateOn target targetName sources sourceNames
      referenceGoals executableGoals domain reference executable
        referenceSeen executableSeen) :
    referenceSeen.Nodup ∧ target ∉ referenceSeen := by
  rw [resolved.referenceSeen_eq]
  exact foldInsert_wellFormed target sources [] (by simp) (by simp)

/-- Resolve both representations while retaining the exact canonical state
needed by downstream continuation proofs. -/
theorem AliasLedgerAgrees.resolveStateOn
    {target : LogicVar} {targetName : String}
    {sources : List LogicVar} {sourceNames : List String}
    {referenceGoals : List PeTTaSpec.PrologCore.Goal}
    {executableGoals : List PLeaTTa.Goal} {domain : List LogicVar}
    (agreement : AliasLedgerAgrees target targetName sources sourceNames
      referenceGoals executableGoals)
    (targetAgreement :
      TermAgrees (.variable target) (.var targetName))
    (injective :
      EncodingInjectiveOn (target :: (sources ++ domain))) :
    ∃ reference executable referenceSeen executableSeen,
      ResolvedAliasStateOn target targetName sources sourceNames
        referenceGoals executableGoals domain reference executable
          referenceSeen executableSeen := by
  let referenceSeen := sources.foldl
    (fun seen source => insertAliasSource target source seen) []
  let executableSeen := sourceNames.foldl
    (fun seen source => insertAliasSource targetName source seen) []
  obtain ⟨referenceBinding, referenceResolution, referenceState⟩ :=
    PLeaTTa.CompilerAliasFinalizationAdequacy.AliasLedgerAgrees.resolveReference
      agreement
  have targetNameEq : logicVarExecutableName target = targetName :=
    variable_name_eq targetAgreement
  have sourceNamesEq :=
    PLeaTTa.CompilerAliasFinalizationAdequacy.AliasLedgerAgrees.sourceNames_eq
      agreement
  have aliasInjective : EncodingInjectiveOn (target :: sources) := by
    intro left right leftMember rightMember sameName
    apply injective
    · simp only [List.mem_cons, List.mem_append] at leftMember ⊢
      exact leftMember.elim Or.inl
        (fun member => Or.inr (Or.inl member))
    · simp only [List.mem_cons, List.mem_append] at rightMember ⊢
      exact rightMember.elim Or.inl
        (fun member => Or.inr (Or.inl member))
    · exact sameName
  have seenNamesEq : executableSeen =
      referenceSeen.map logicVarExecutableName := by
    unfold executableSeen referenceSeen
    rw [sourceNamesEq, ← targetNameEq]
    exact foldInsert_names_eq target sources aliasInjective
  have executableWellFormed : executableSeen.Nodup ∧
      targetName ∉ executableSeen := by
    exact foldInsert_wellFormed targetName sourceNames [] (by simp) (by simp)
  let executableBinding := aliasBinding targetName executableSeen
  have executableTarget :
      subst executableBinding (.var targetName) = .var targetName :=
    subst_aliasBinding_target executableWellFormed.2
  have seenWithinSources : ∀ identity, identity ∈ referenceSeen →
      identity ∈ sources := by
    intro identity member
    have characterized :=
      (mem_foldInsert_iff target identity sources []).1 member
    have characterized' : identity ∈ sources ∧ identity ≠ target := by
      simpa using characterized
    exact characterized'.1
  have identityAgreement : ∀ identity, identity ∈ domain →
      TermAgrees (.variable identity)
        (.var (logicVarExecutableName identity)) →
      TermStateAgrees referenceBinding executableBinding
        (.variable identity)
        (.var (logicVarExecutableName identity)) := by
    intro identity domainMember originalAgreement
    unfold TermStateAgrees
    by_cases sameTarget : identity = target
    · subst identity
      rw [referenceState.targetFixed, targetNameEq, executableTarget]
      exact targetAgreement
    · by_cases seenMember : identity ∈ referenceSeen
      · have executableMember :
            logicVarExecutableName identity ∈ executableSeen := by
          rw [seenNamesEq]
          exact List.mem_map.mpr ⟨identity, seenMember, rfl⟩
        rw [referenceState.sourceAliases identity seenMember,
          subst_aliasBinding_of_mem executableWellFormed.1
            executableWellFormed.2 executableMember]
        exact targetAgreement
      · have executableAbsent :
            logicVarExecutableName identity ∉ executableSeen := by
          intro executableMember
          rw [seenNamesEq] at executableMember
          rcases List.mem_map.mp executableMember with
            ⟨seenIdentity, seenIdentityMember, sameName⟩
          have seenSource : seenIdentity ∈ sources :=
            seenWithinSources seenIdentity seenIdentityMember
          have sameIdentity : seenIdentity = identity := by
            apply injective
            · simp [List.mem_append, seenSource]
            · simp [List.mem_append, domainMember]
            · exact sameName
          subst seenIdentity
          exact seenMember seenIdentityMember
        rw [referenceState.outsideFixed identity sameTarget seenMember,
          subst_aliasBinding_of_not_mem executableAbsent]
        exact originalAgreement
  refine ⟨referenceBinding, executableBinding, referenceSeen,
    executableSeen, ?_⟩
  refine
    { referenceSeen_eq := rfl
      executableSeen_eq := rfl
      referenceResolution := referenceResolution
      executableResolution := ?_
      referenceState := referenceState
      executableBinding := rfl
      seenNames := seenNamesEq
      seenWithinSources := seenWithinSources
      variableState := ?_ }
  · simpa [executableBinding, executableSeen] using
      PLeaTTa.CompilerAliasFinalizationAdequacy.AliasLedgerAgrees.resolveCompileAliases
        agreement
  · refine
      { source := ?_
        generated := ?_ }
    · intro name member
      exact identityAgreement (.source name) member (.sourceVariable name)
    · intro index member
      exact identityAgreement (.generated index) member
        (.generatedVariable index)

/-- Resolving a related alias ledger induces pointwise substitution agreement
on any finite continuation domain whose encoding is injective together with
the shared target and alias sources.  This is the scoped replacement for the
false global claim that executable variable spellings are always fresh. -/
theorem AliasLedgerAgrees.resolveVariableStateOn
    {target : LogicVar} {targetName : String}
    {sources : List LogicVar} {sourceNames : List String}
    {referenceGoals : List PeTTaSpec.PrologCore.Goal}
    {executableGoals : List PLeaTTa.Goal} {domain : List LogicVar}
    (agreement : AliasLedgerAgrees target targetName sources sourceNames
      referenceGoals executableGoals)
    (targetAgreement :
      TermAgrees (.variable target) (.var targetName))
    (injective :
      EncodingInjectiveOn (target :: (sources ++ domain))) :
    ∃ reference executable,
      ResolvesAliasGoals [] referenceGoals reference ∧
      resolveCompileAliases (collectCompileAliasesGoals executableGoals) =
        .ok executable ∧
      VariableStateAgreesOn reference executable domain := by
  obtain ⟨reference, executable, _referenceSeen, _executableSeen,
      resolved⟩ :=
    PLeaTTa.CompilerSubstitutionAdequacy.AliasLedgerAgrees.resolveStateOn
      agreement targetAgreement injective
  exact ⟨reference, executable, resolved.referenceResolution,
    resolved.executableResolution, resolved.variableState⟩

/-- A resolved alias certificate can discharge type-check transport on a
domain distinct from the ordinary continuation domain stored in the
certificate.  This separation is essential: an alias source may occur in an
ordinary continuation goal, while carry-template stability requires the
type-template domain to avoid every alias source. -/
theorem ResolvedAliasStateOn.typeCheckSubstitutionAgreesOn
    {target : LogicVar} {targetName : String}
    {sources : List LogicVar} {sourceNames : List String}
    {referenceGoals : List PeTTaSpec.PrologCore.Goal}
    {executableGoals : List PLeaTTa.Goal} {stateDomain typeDomain : List LogicVar}
    {reference : Substitution} {executable : Subst}
    {referenceSeen : List LogicVar} {executableSeen : List String}
    (resolved : ResolvedAliasStateOn target targetName sources sourceNames
      referenceGoals executableGoals stateDomain reference executable
        referenceSeen executableSeen)
    (injective : EncodingInjectiveOn (target :: (sources ++ typeDomain)))
    (avoids : AliasDomainAvoids target sources typeDomain) :
    TypeCheckSubstitutionAgrees reference executable typeDomain := by
  have referenceDisjoint :
      AliasDomainAvoids target referenceSeen typeDomain := by
    intro identity member
    rcases avoids identity member with same | absent
    · exact Or.inl same
    · exact Or.inr (fun seenMember =>
        absent (resolved.seenWithinSources identity seenMember))
  have memberOriginal : ∀ identity,
      identity ∈ target :: (referenceSeen ++ typeDomain) →
      identity ∈ target :: (sources ++ typeDomain) := by
    intro identity member
    simp only [List.mem_cons, List.mem_append] at member ⊢
    rcases member with same | seen | continuation
    · exact Or.inl same
    · exact Or.inr (Or.inl
        (resolved.seenWithinSources identity seen))
    · exact Or.inr (Or.inr continuation)
  have restrictedInjective :
      EncodingInjectiveOn
        (target :: (referenceSeen ++ typeDomain)) := by
    intro left right leftMember rightMember sameName
    exact injective (memberOriginal left leftMember)
      (memberOriginal right rightMember) sameName
  have executableDisjoint :
      TypeCheckExecutableNamesDisjoint executableSeen typeDomain :=
    typeCheckExecutableNamesDisjoint_of_encoding resolved.seenNames
      resolved.referenceWellFormed.2 restrictedInjective referenceDisjoint
  have fixedCanonical :
      TypeCheckStateFixedOn reference
        (aliasBinding targetName executableSeen) typeDomain :=
    typeCheckStateFixedOn_of_aliasDisjoint resolved.referenceState
      referenceDisjoint executableDisjoint
  rw [resolved.executableBinding]
  intro referenceExpected executableExpected executableTemplate agreement
    supported
  obtain ⟨referenceFixed, expectedFixed, templateFixed, chainifiedFixed⟩ :=
    fixedCanonical agreement supported
  constructor
  · simpa [referenceFixed, expectedFixed, templateFixed] using agreement
  · rw [chainifiedFixed, expectedFixed]

/-- Same-domain compatibility wrapper retained for existing callers.  New
goal-transport composition should use `typeCheckSubstitutionAgreesOn` with a
separate type-template domain. -/
theorem ResolvedAliasStateOn.typeCheckSubstitutionAgrees
    {target : LogicVar} {targetName : String}
    {sources : List LogicVar} {sourceNames : List String}
    {referenceGoals : List PeTTaSpec.PrologCore.Goal}
    {executableGoals : List PLeaTTa.Goal} {domain : List LogicVar}
    {reference : Substitution} {executable : Subst}
    {referenceSeen : List LogicVar} {executableSeen : List String}
    (resolved : ResolvedAliasStateOn target targetName sources sourceNames
      referenceGoals executableGoals domain reference executable
        referenceSeen executableSeen)
    (injective : EncodingInjectiveOn (target :: (sources ++ domain)))
    (avoids : AliasDomainAvoids target sources domain) :
    TypeCheckSubstitutionAgrees reference executable domain :=
  resolved.typeCheckSubstitutionAgreesOn injective avoids

/-- Public package combining both resolver equations, finite variable-state
agreement, and the non-generic type-check closure needed by later goal
transport. -/
theorem AliasLedgerAgrees.resolveVariableStateAndTypeCheckOn
    {target : LogicVar} {targetName : String}
    {sources : List LogicVar} {sourceNames : List String}
    {referenceGoals : List PeTTaSpec.PrologCore.Goal}
    {executableGoals : List PLeaTTa.Goal} {domain : List LogicVar}
    (agreement : AliasLedgerAgrees target targetName sources sourceNames
      referenceGoals executableGoals)
    (targetAgreement :
      TermAgrees (.variable target) (.var targetName))
    (injective : EncodingInjectiveOn (target :: (sources ++ domain)))
    (avoids : AliasDomainAvoids target sources domain) :
    ∃ reference executable,
      ResolvesAliasGoals [] referenceGoals reference ∧
      resolveCompileAliases (collectCompileAliasesGoals executableGoals) =
        .ok executable ∧
      VariableStateAgreesOn reference executable domain ∧
      TypeCheckSubstitutionAgrees reference executable domain := by
  obtain ⟨reference, executable, _referenceSeen, _executableSeen,
      resolved⟩ :=
    PLeaTTa.CompilerSubstitutionAdequacy.AliasLedgerAgrees.resolveStateOn
      agreement targetAgreement injective
  exact ⟨reference, executable, resolved.referenceResolution,
    resolved.executableResolution, resolved.variableState,
    resolved.typeCheckSubstitutionAgrees injective avoids⟩

/-! ## Restricted same-domain superpose package -/

/-- The complete ordered `build_superpose_branches/3` traversal produces a
canonical alias-resolution certificate whose resulting substitutions agree
on an explicit continuation domain and preserve every supported type-check
carry.  Branch order and duplicate occurrences remain exposed through
`SuperposeBranchesAgree`; no bag normalization is admitted.

The `aliasSafety` premise is intentionally finite and semantic: executable
spellings must be injective on the emitted aliases plus the continuation, and
the continuation may contain the shared result but no emitted alias source.
The known source/generated spelling collision is therefore rejected rather
than hidden behind a global freshness assertion.

This theorem is a compatibility package, not the general final-goal
transport: ordinary variable-valued branches normally retain an emitted
alias source in their continuation while type-check carry templates must
exclude it.  The split-domain composition in
`CompilerGoalSubstitutionAdequacy` handles that case. -/
theorem compileSuperposeBranches_alias_continuation_sound
    {state : TranslatorState} (env : CEnv)
    (envAgreement : EnvAgrees state env)
    {outputIndex counter nextCounter : Nat} {sources : List Atom}
    {referenceAliases referenceBranches :
      List PeTTaSpec.PrologCore.Goal}
    {domain : List LogicVar}
    (native : TranslatesSuperposeBranches state
      (.variable (.generated outputIndex)) counter sources referenceAliases
      referenceBranches nextCounter)
    (aliasSafety :
      ∀ {aliasSources aliasNames executableAliases},
        AliasLedgerAgrees (.generated outputIndex) s!"_q{outputIndex}"
          aliasSources aliasNames referenceAliases executableAliases →
        EncodingInjectiveOn
            (.generated outputIndex :: (aliasSources ++ domain)) ∧
          AliasDomainAvoids (.generated outputIndex) aliasSources domain) :
    ∃ baseFuel,
      0 < baseFuel ∧
      baseFuel < 8 * ((sources.map Atom.size).sum + 1) ∧
      ∀ extraFuel accumulator,
        ∃ rawBranches aliasSources aliasNames executableAliases
            executableBranches referenceBinding executableBinding
            referenceSeen executableSeen,
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
            domain referenceBinding executableBinding referenceSeen
            executableSeen ∧
          TypeCheckSubstitutionAgrees referenceBinding executableBinding
            domain ∧
          SuperposeBranchesAgree (.variable (.generated outputIndex))
            (.var s!"_q{outputIndex}") referenceBranches
            executableBranches := by
  obtain ⟨baseFuel, positive, bounded, compiles⟩ :=
    compileSuperposeBranchesFuel_initial_sound env envAgreement native
  refine ⟨baseFuel, positive, bounded, ?_⟩
  intro extraFuel accumulator
  obtain ⟨rawBranches, aliasSources, aliasNames, executableAliases,
      executableBranches, compiled, normalized, aliasLedger,
      branchesAgreement⟩ := compiles extraFuel accumulator
  obtain ⟨injective, avoids⟩ := aliasSafety aliasLedger
  obtain ⟨referenceBinding, executableBinding, referenceSeen,
      executableSeen, resolved⟩ :=
    PLeaTTa.CompilerSubstitutionAdequacy.AliasLedgerAgrees.resolveStateOn
      aliasLedger (.generatedVariable outputIndex) injective
  refine ⟨rawBranches, aliasSources, aliasNames, executableAliases,
    executableBranches, referenceBinding, executableBinding,
    referenceSeen, executableSeen, compiled, normalized, resolved, ?_,
    branchesAgreement⟩
  exact resolved.typeCheckSubstitutionAgrees injective avoids

end PLeaTTa.CompilerSubstitutionAdequacy
