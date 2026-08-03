-- SPDX-License-Identifier: Apache-2.0

import PLeaTTa.Proofs.CompilerAdequacy
import Mathlib.Data.List.Induction

/-!
# Program-level binder desugaring

Pinned PeTTa's reader represents `!query` as one runnable.  PLeaTTa's reader
represents the same source as two adjacent atoms: the marker `!`, followed by
the query.  Binder translation may synthesize clauses before the query runs,
but those clauses must not separate the marker from the query it owns.

This file specifies that ownership independently of `desugarProgramAtoms`,
proves the executable pass sound and complete for the specification, relates
the batch and sequential source-form passes, and pins the tagged partial
closure value that exposed the original bug.

[SPEC filereader.pl:13-24, translator.pl:59-61,244-261]
-/

namespace PLeaTTa.CompilerProgramDesugaring

open Metta (Atom)
open PLeaTTa.CompilerAdequacy
open PLeaTTa.PeTTaSpec.PrologCore

def bangAtom : Atom := .sym "!"

/-- Declarative ownership and ordering specification for program-level binder
desugaring.

The relation treats one invocation of `desugarBinders` as an abstract
source-to-source expansion and independently specifies how those expansions
compose across program forms.  The split-runnable constructor is the
load-bearing case: synthesized definitions precede the marker/query pair,
while the marker remains adjacent to the transformed query.
-/
inductive DesugarsProgram : List Atom → Nat → List Atom → Nat → Prop where
  | nil (counter : Nat) :
      DesugarsProgram [] counter [] counter
  | loneBang (counter : Nat) :
      DesugarsProgram [bangAtom] counter [bangAtom] counter
  | splitBang {counter nextCounter finalCounter : Nat}
      {query query' : Atom} {definitions rest rest' : List Atom}
      (queryExpansion :
        desugarBinders query counter = (query', definitions, nextCounter))
      (tail : DesugarsProgram rest nextCounter rest' finalCounter) :
      DesugarsProgram (bangAtom :: query :: rest) counter
        (definitions ++ [bangAtom, query'] ++ rest') finalCounter
  | atom {counter nextCounter finalCounter : Nat}
      {source transformed : Atom} {definitions rest rest' : List Atom}
      (notBang : source ≠ bangAtom)
      (sourceExpansion :
        desugarBinders source counter =
          (transformed, definitions, nextCounter))
      (tail : DesugarsProgram rest nextCounter rest' finalCounter) :
      DesugarsProgram (source :: rest) counter
        (definitions ++ [transformed] ++ rest') finalCounter

/-- The declarative program relation determines the executable pass exactly.
This is the completeness direction: no declarative ordering can denote a
different executable result. -/
theorem DesugarsProgram.to_desugarProgramAtoms
    {source : List Atom} {counter : Nat} {output : List Atom}
    {nextCounter : Nat}
    (derivation : DesugarsProgram source counter output nextCounter) :
    desugarProgramAtoms source counter = (output, nextCounter) := by
  induction derivation with
  | nil => rfl
  | loneBang =>
      rw [desugarProgramAtoms.eq_3 (x_2 := by simp)]
      simp [bangAtom, desugarBinders, desugarProgramAtoms]
  | splitBang queryExpansion _ tailIH =>
      simp [desugarProgramAtoms, bangAtom, queryExpansion, tailIH]
  | atom notBang sourceExpansion _ tailIH =>
      rw [desugarProgramAtoms.eq_3 (x_2 := by
        intro _ _ sourceEq _
        exact notBang (sourceEq.trans rfl))]
      simp [sourceExpansion, tailIH]

/-- Every executable program desugaring has a declarative derivation.  The
two-step induction is essential: an ordinary form consumes one source atom,
whereas a split runnable consumes the marker and its query together. -/
theorem desugarProgramAtoms_sound (source : List Atom) (counter : Nat) :
    DesugarsProgram source counter
      (desugarProgramAtoms source counter).1
      (desugarProgramAtoms source counter).2 := by
  induction source using List.twoStepInduction generalizing counter with
  | nil =>
      exact DesugarsProgram.nil counter
  | singleton source =>
      by_cases isBang : source = bangAtom
      · subst source
        simpa [desugarProgramAtoms, bangAtom, desugarBinders,
          desugarBinderList] using
          (DesugarsProgram.loneBang counter)
      · generalize expansion :
          desugarBinders source counter = result
        obtain ⟨transformed, definitions, nextCounter⟩ := result
        simpa [desugarProgramAtoms, bangAtom, isBang, expansion] using
          (DesugarsProgram.atom isBang expansion
            (DesugarsProgram.nil nextCounter))
  | cons_cons first second rest restIH secondRestIH =>
      by_cases isBang : first = bangAtom
      · subst first
        generalize expansion :
          desugarBinders second counter = result
        obtain ⟨transformed, definitions, nextCounter⟩ := result
        have tail := restIH nextCounter
        simpa [desugarProgramAtoms, bangAtom, expansion] using
          (DesugarsProgram.splitBang expansion tail)
      · generalize expansion :
          desugarBinders first counter = result
        obtain ⟨transformed, definitions, nextCounter⟩ := result
        have tail := secondRestIH second nextCounter
        rw [desugarProgramAtoms.eq_3 (x_2 := by
          intro _ _ firstEq _
          exact isBang (firstEq.trans rfl))]
        simpa [desugarProgramAtoms, bangAtom, isBang, expansion] using
          (DesugarsProgram.atom isBang expansion tail)

/-- Soundness and completeness of the executable program pass with respect to
the independent marker-ownership relation. -/
theorem desugarProgramAtoms_iff
    {source : List Atom} {counter : Nat} {output : List Atom}
    {nextCounter : Nat} :
    desugarProgramAtoms source counter = (output, nextCounter) ↔
      DesugarsProgram source counter output nextCounter := by
  constructor
  · intro equality
    have derivation := desugarProgramAtoms_sound source counter
    rw [equality] at derivation
    exact derivation
  · exact DesugarsProgram.to_desugarProgramAtoms

/-- On ordinary reader atoms with one visibility bit, the sequential and
batch passes are the same transformation.  This prevents the two live compiler
entry points from drifting on split-runnable ownership. -/
theorem desugarSourceForms_atoms_map (source : List Atom) (observable : Bool)
    (counter : Nat) :
    desugarSourceForms (source.map (SourceForm.atom · observable)) counter =
      let result := desugarProgramAtoms source counter
      (result.1.map (SourceForm.atom · observable), result.2) := by
  induction source using List.twoStepInduction generalizing counter with
  | nil => rfl
  | singleton source =>
      simp only [List.map_cons, List.map_nil]
      by_cases isBang : source = bangAtom
      · subst source
        simp [bangAtom, desugarSourceForms, desugarProgramAtoms,
          desugarBinders]
      · generalize expansion :
          desugarBinders source counter = result
        obtain ⟨transformed, definitions, nextCounter⟩ := result
        simp [desugarSourceForms, desugarProgramAtoms, expansion]
  | cons_cons first second rest restIH secondRestIH =>
      by_cases isBang : first = bangAtom
      · subst first
        generalize expansion :
          desugarBinders second counter = result
        obtain ⟨transformed, definitions, nextCounter⟩ := result
        simp [desugarSourceForms, desugarProgramAtoms, bangAtom, expansion,
          restIH nextCounter, List.map_append]
      · generalize expansion :
          desugarBinders first counter = result
        obtain ⟨transformed, definitions, nextCounter⟩ := result
        simp only [List.map_cons]
        rw [desugarSourceForms.eq_3 (x_2 := by
          intro _ _ _ _ firstEq
          exact isBang (firstEq.trans rfl))]
        rw [desugarProgramAtoms.eq_3 (x_2 := by
          intro _ _ firstEq _
          exact isBang (firstEq.trans rfl))]
        rw [expansion]
        have tailEquality := secondRestIH second nextCounter
        simp only [List.map_cons] at tailEquality
        simp only
        rw [tailEquality]
        simp [List.map_append]

/-- A tagged partial closure is already a runtime value, not source syntax.
Its ordinary Prolog-compound representation is shared with `Predicate/2`.
Compiling it preserves both its independent reading and its counter and emits
no goals. -/
theorem compileExprFuel_partial_value_data
    (fuel counter : Nat) (env : CEnv) (head : String)
    {terms : List PeTTaSpec.PrologCore.Term} {encodedArguments : Atom}
    (arguments : ProperListAgrees terms encodedArguments) :
    compileExprFuel (fuel + 1) env counter
        (partialC head encodedArguments) =
        .ok (partialC head encodedArguments, [], counter) ∧
      TermAgrees
        (.compound "partial" [.atom head, .list terms none])
        (partialC head encodedArguments) := by
  constructor
  · exact compileExprFuel_partialC fuel env counter head encodedArguments
  · exact TermAgrees.partialValue arguments

/-- Applying an already-created partial value emits exactly one dynamic call
after compiling the newly supplied arguments.  The closure payload is
preserved byte-for-byte; the runtime reducer is therefore responsible for
appending those arguments after the bound list.
-/
theorem compileExprFuel_partial_application
    (fuel counter nextCounter : Nat) (env : CEnv) (head : String)
    (encodedArguments : Atom) (sources terms : List Atom)
    (goals : List Goal)
    (arguments :
      compileListFuel fuel env counter sources =
        .ok (terms, goals, nextCounter)) :
    compileExprFuel (fuel + 1) env counter
        (.expr (partialC head encodedArguments :: sources)) =
      .ok
        (Atom.var (compilerGeneratedName nextCounter),
          goals ++
            [Goal.callDyn (partialC head encodedArguments) terms
              (Atom.var (compilerGeneratedName nextCounter))],
          nextCounter + 1) := by
  cases fuel with
  | zero =>
      simp [compileListFuel] at arguments
  | succ fuel =>
      rw [show fuel.succ + 1 = fuel.succ.succ by omega]
      rw [compileExprFuel.eq_10
        (x_4 := by
          simp [partialC, prologCompoundC, prologCompoundTagA])
        (x_5 := by
          simp [partialC, prologCompoundC, prologCompoundTagA])
        (x_6 := by
          simp [partialC, prologCompoundC, prologCompoundTagA])
        (x_7 := by
          simp [partialC, prologCompoundC, prologCompoundTagA])]
      rw [staticDataHead_partialC_false]
      rw [compileExprFuel_partialC]
      simp only [Bind.bind, Except.bind]
      rw [arguments]
      simp [fresh, compilerGeneratedName]

/-- Narrow cross-language agreement for pinned partial smart dispatch.
Pinned emits a direct output-last call with bound arguments first; the
executable emits `callDyn` carrying the tagged partial value.  The sealed
machine's `callDyn_partial` step performs exactly that redispatch.
[SPEC translator.pl:59-61,302-346] -/
inductive PartialCallAgrees :
    PeTTaSpec.PrologCore.Goal → PLeaTTa.Goal → Prop where
  | call {head : String} {referenceBound referenceArguments : List Term}
      {referenceResult : Term} {encodedBound : Atom}
      {executableArguments : List Atom} {executableResult : Atom}
      (bound : ProperListAgrees referenceBound encodedBound)
      (arguments : TermsAgree referenceArguments executableArguments)
      (result : TermAgrees referenceResult executableResult) :
      PartialCallAgrees
        (.call head
          (referenceBound ++ referenceArguments ++ [referenceResult]))
        (.callDyn (partialC head encodedBound) executableArguments
          executableResult)

/-- Prefix compiler goals agree normally; the final partial smart-dispatch
goal agrees through `PartialCallAgrees`. -/
inductive PartialApplicationGoalsAgree :
    List PeTTaSpec.PrologCore.Goal → List PLeaTTa.Goal → Prop where
  | apply {referencePrefix : List PeTTaSpec.PrologCore.Goal}
      {executablePrefix : List PLeaTTa.Goal}
      {referenceCall : PeTTaSpec.PrologCore.Goal}
      {executableCall : PLeaTTa.Goal}
      (prefixAgreement : GoalsAgree referencePrefix executablePrefix)
      (call : PartialCallAgrees referenceCall executableCall) :
      PartialApplicationGoalsAgree
        (referencePrefix ++ [referenceCall])
        (executablePrefix ++ [executableCall])

/-- Fuel-indexed soundness of applying an independently specified pinned
partial closure.  This composes the existing ordered argument-translation
theorem with the exact executable `partialC` dynamic-call equation. -/
theorem compileExprFuel_partial_application_sound
    {registry : PartialApplicationRegistry}
    {state : TranslatorState} (env : CEnv)
    (stateAgreement : EnvAgrees state env)
    {counter : Nat} {head : String} {referenceBound : List Term}
    {encodedBound : Atom} {sources : List Atom} {referenceResult : Term}
    {referenceGoals : List PeTTaSpec.PrologCore.Goal}
    {nextCounter : Nat}
    (boundAgreement :
      ProperListAgrees referenceBound encodedBound)
    (native :
      TranslatesPartialApplication registry state counter head referenceBound
        sources referenceResult referenceGoals nextCounter) :
    ∃ baseFuel,
      0 < baseFuel ∧
      baseFuel < 16 * ((sources.map Atom.size).sum + 1) + 1 ∧
      ∀ extraFuel, ∃ internal executableGoals,
        compileExprFuel (baseFuel + extraFuel) env counter
            (.expr (partialC head encodedBound :: sources)) =
          .ok (internal, executableGoals, nextCounter) ∧
        TermAgrees referenceResult internal ∧
        PartialApplicationGoalsAgree referenceGoals executableGoals := by
  cases native with
  | @apply argumentCounter _ _ _ terms argumentGoals _ arguments =>
      obtain ⟨argumentFuel, argumentPositive, argumentBound,
          argumentCompiles⟩ :=
        compileListFuel_initial_sound env stateAgreement arguments
      refine ⟨argumentFuel + 1, by omega, by omega, ?_⟩
      intro extraFuel
      obtain ⟨executableArguments, executableArgumentGoals,
          compiledArguments, argumentsAgreement, goalsAgreement⟩ :=
        argumentCompiles extraFuel
      let executableResult : Atom :=
        .var (compilerGeneratedName argumentCounter)
      refine ⟨executableResult,
        executableArgumentGoals ++
          [.callDyn (partialC head encodedBound) executableArguments
            executableResult],
        ?_, TermAgrees.generatedVariable argumentCounter,
        PartialApplicationGoalsAgree.apply goalsAgreement
          (PartialCallAgrees.call boundAgreement argumentsAgreement
            (TermAgrees.generatedVariable argumentCounter))⟩
      rw [show (argumentFuel + 1) + extraFuel =
        (argumentFuel + extraFuel) + 1 by omega]
      exact compileExprFuel_partial_application
        (argumentFuel + extraFuel) counter argumentCounter env head
        encodedBound sources executableArguments executableArgumentGoals
        compiledArguments

/-- Public compiler soundness for the same independently specified partial
application fragment. -/
theorem compileExpr_partial_application_sound
    {registry : PartialApplicationRegistry}
    {state : TranslatorState} (env : CEnv)
    (stateAgreement : EnvAgrees state env)
    {counter : Nat} {head : String} {referenceBound : List Term}
    {encodedBound : Atom} {sources : List Atom} {referenceResult : Term}
    {referenceGoals : List PeTTaSpec.PrologCore.Goal}
    {nextCounter : Nat}
    (boundAgreement :
      ProperListAgrees referenceBound encodedBound)
    (native :
      TranslatesPartialApplication registry state counter head referenceBound
        sources referenceResult referenceGoals nextCounter) :
    ∃ internal executableGoals,
      compileExpr env counter
          (.expr (partialC head encodedBound :: sources)) =
        .ok (internal, executableGoals, nextCounter) ∧
      TermAgrees referenceResult internal ∧
      PartialApplicationGoalsAgree referenceGoals executableGoals := by
  obtain ⟨baseFuel, _basePositive, baseBound, compiles⟩ :=
    compileExprFuel_partial_application_sound env stateAgreement
      boundAgreement native
  have baseLe :
      baseFuel ≤
        compilerFuel (.expr (partialC head encodedBound :: sources)) + 64 := by
    simp only [compilerFuel, Atom.size, List.map, List.sum_cons]
    omega
  obtain ⟨extraFuel, publicFuelEq⟩ :
      ∃ extraFuel,
        compilerFuel (.expr (partialC head encodedBound :: sources)) + 64 =
          baseFuel + extraFuel :=
    ⟨compilerFuel (.expr (partialC head encodedBound :: sources)) + 64 -
      baseFuel, by omega⟩
  obtain ⟨internal, executableGoals, compiled, termAgreement,
      goalsAgreement⟩ := compiles extraFuel
  exact ⟨internal, executableGoals,
    by simpa [compileExpr, publicFuelEq] using compiled,
    termAgreement, goalsAgreement⟩

/-- Supported partial applications are those with at least one derivation in
the independent pinned relation. -/
def SupportedPartialApplication (registry : PartialApplicationRegistry)
    (state : TranslatorState) (counter : Nat) (head : String)
    (referenceBound : List Term) (sources : List Atom) : Prop :=
  ∃ result goals nextCounter,
    TranslatesPartialApplication registry state counter head referenceBound
      sources result goals nextCounter

/-- Completeness of the executable compiler on the supported partial
application fragment. -/
theorem compileExpr_partial_application_complete
    {registry : PartialApplicationRegistry}
    {state : TranslatorState} (env : CEnv)
    (stateAgreement : EnvAgrees state env)
    {counter : Nat} {head : String} {referenceBound : List Term}
    {encodedBound : Atom} {sources : List Atom} {internal : Atom}
    {executableGoals : List PLeaTTa.Goal} {nextCounter : Nat}
    (boundAgreement :
      ProperListAgrees referenceBound encodedBound)
    (supported :
      SupportedPartialApplication registry state counter head referenceBound
        sources)
    (compiled :
      compileExpr env counter
          (.expr (partialC head encodedBound :: sources)) =
        .ok (internal, executableGoals, nextCounter)) :
    ∃ referenceResult referenceGoals,
      TranslatesPartialApplication registry state counter head referenceBound
        sources referenceResult referenceGoals nextCounter ∧
      TermAgrees referenceResult internal ∧
      PartialApplicationGoalsAgree referenceGoals executableGoals := by
  obtain ⟨referenceResult, referenceGoals, referenceCounter, native⟩ :=
    supported
  obtain ⟨referenceInternal, referenceExecutableGoals, referenceCompiled,
      termAgreement, goalsAgreement⟩ :=
    compileExpr_partial_application_sound env stateAgreement
      boundAgreement native
  have resultEquality :
      (internal, executableGoals, nextCounter) =
        (referenceInternal, referenceExecutableGoals, referenceCounter) :=
    Except.ok.inj (compiled.symm.trans referenceCompiled)
  cases resultEquality
  exact ⟨referenceResult, referenceGoals, native, termAgreement,
    goalsAgreement⟩

/-- Minimal captured-lambda source used by the exact ownership witnesses:
`(|-> ($x) ($f $x))` captures `$f`, creates `#lam0`, and returns
`partial(#lam0, [$f])`. -/
theorem lambda_variable_parameter_eq_singleton
    (parameter : String) (body : Atom) (counter : Nat) :
    desugarBinders
        (.expr [.sym "|->", .var parameter, body]) counter =
      desugarBinders
        (.expr [.sym "|->", .expr [.var parameter], body]) counter := by
  simp [desugarBinders]

/-- Source syntax headed by the ordinary symbol `partial` cannot manufacture
the compiler-private external tag.  Therefore applying source-written
`(partial ...)` remains data rather than entering `callDyn_partial`. -/
theorem source_written_partial_ne_private (head : String)
    (encodedArguments : Atom) :
    .expr [.sym "partial", .sym head, encodedArguments] ≠
      partialC head encodedArguments := by
  simp [partialC, prologCompoundC, prologCompoundTagA]

def capturedLambda : Atom :=
  .expr [.sym "|->", .expr [.var "x"], .expr [.var "f", .var "x"]]

def capturedLambdaName : String := s!"#lam{0}"

def capturedLambdaRule : Atom :=
  .expr [.sym "=", .expr [.sym capturedLambdaName, .var "f", .var "x"],
    .expr [.var "f", .var "x"]]

def capturedLambdaValue : Atom :=
  partialValue capturedLambdaName [.var "f"]

/-- Binder conversion itself creates one definition and one tagged partial
value for the captured source. -/
theorem capturedLambda_desugars_exact :
    desugarBinders capturedLambda 0 =
      (capturedLambdaValue, [capturedLambdaRule], 1) := by
  simp [capturedLambda, capturedLambdaValue, capturedLambdaRule,
    capturedLambdaName, desugarBinders, desugarBinderList,
    finishLambdaDesugaring,
    surfaceVars, surfaceVarsList, partialValue]

/-- The actual reader-shaped split runnable keeps its marker adjacent to the
transformed query and hoists the generated clause before both. -/
theorem capturedLambda_split_bang_exact :
    desugarProgramAtoms [bangAtom, capturedLambda] 0 =
      ([capturedLambdaRule, bangAtom, capturedLambdaValue], 1) := by
  simp [bangAtom, desugarProgramAtoms, capturedLambda_desugars_exact]

/-- Anti-vacuity: the former ordering, which inserted a generated definition
between the marker and its query, is observably different from the specified
result. -/
theorem capturedLambda_wrong_order_rejected :
    desugarProgramAtoms [bangAtom, capturedLambda] 0 ≠
      ([bangAtom, capturedLambdaRule, capturedLambdaValue], 1) := by
  rw [capturedLambda_split_bang_exact]
  simp [bangAtom, capturedLambdaRule]

/-- A lone trailing marker remains a lone marker and consumes no generated
name.  This preserves the downstream compiler's explicit malformed-input
diagnostic rather than silently dropping it. -/
theorem lone_bang_preserves_counter (counter : Nat) :
    desugarProgramAtoms [bangAtom] counter = ([bangAtom], counter) := by
  rw [desugarProgramAtoms.eq_3 (x_2 := by simp)]
  simp [bangAtom, desugarBinders, desugarProgramAtoms]

/-- Generated definitions inherit query visibility, while the marker retains
its own visibility. -/
theorem capturedLambda_source_visibility_exact :
    desugarSourceForms
        [.atom bangAtom false, .atom capturedLambda true] 0 =
      ([.atom capturedLambdaRule true, .atom bangAtom false,
        .atom capturedLambdaValue true], 1) := by
  simp [bangAtom, desugarSourceForms, capturedLambda_desugars_exact]

end PLeaTTa.CompilerProgramDesugaring
