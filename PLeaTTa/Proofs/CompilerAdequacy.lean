/-
Module: PLeaTTa.Proofs.CompilerAdequacy
Purpose: Construct-by-construct adequacy of PLeaTTa's executable compiler to
  the independent pinned-PeTTa target relation.
Trusted boundary: none
-/
import PLeaTTa.Compile
import PLeaTTa.PeTTaSpec.PrologSemantics

namespace PLeaTTa.CompilerAdequacy

open Metta (Atom Ground)
open PLeaTTa.PeTTaSpec.PrologCore

mutual

/-- Cross-representation relation between independent Prolog terms and
PLeaTTa's internal chain representation.  This relation is not a compiler. -/
inductive TermAgrees : Term → Atom → Prop where
  | sourceVariable (name : String) :
      TermAgrees (.variable (.source name)) (.var name)
  | generatedVariable (index : Nat) :
      TermAgrees (.variable (.generated index)) (.var s!"_q{index}")
  | atom {name : String} (notTrue : name ≠ "true")
      (notFalse : name ≠ "false") : TermAgrees (.atom name) (.sym name)
  | trueAtom : TermAgrees (.atom "true") (.sym "True")
  | falseAtom : TermAgrees (.atom "false") (.sym "False")
  | integer (value : Int) : TermAgrees (.integer value) (.gnd (.int value))
  | float (value : Float) : TermAgrees (.float value) (.gnd (.float value))
  | string (value : String) : TermAgrees (.string value) (.gnd (.str value))
  | properList {items : List Term} {encoded : Atom}
      (elements : ProperListAgrees items encoded) :
      TermAgrees (.list items none) encoded

/-- Proper Prolog lists correspond to PLeaTTa's `#c`/`#nil` chains. -/
inductive ProperListAgrees : List Term → Atom → Prop where
  | nil : ProperListAgrees [] nilA
  | cons {term : Term} {atom : Atom} {terms : List Term} {tail : Atom}
      (head : TermAgrees term atom) (rest : ProperListAgrees terms tail) :
      ProperListAgrees (term :: terms) (consC atom tail)

end

/-- Pointwise ordered agreement between independent Prolog terms and the
executable atoms produced by compiler traversals. -/
inductive TermsAgree : List Term → List Atom → Prop where
  | nil : TermsAgree [] []
  | cons {term : Term} {atom : Atom} {terms : List Term} {atoms : List Atom}
      (head : TermAgrees term atom) (tail : TermsAgree terms atoms) :
      TermsAgree (term :: terms) (atom :: atoms)

/-- Representation agreement for recursive source patterns.  Unlike the
observation-level `TermAgrees`, this relation includes Prolog dotted list
cells; its denotational bridge remains an explicit later obligation. -/
inductive PatternTermAgrees : Term → Atom → Prop where
  | atomic {term : Term} {atom : Atom} (value : TermAgrees term atom) :
      PatternTermAgrees term atom
  | listCell {headTerm tailTerm : Term} {headAtom tailAtom : Atom}
      (head : PatternTermAgrees headTerm headAtom)
      (tail : PatternTermAgrees tailTerm tailAtom) :
      PatternTermAgrees (Term.prepend headTerm tailTerm)
        (consC headAtom tailAtom)

/-- Ordered pointwise agreement for recursively constrained pattern lists. -/
inductive PatternTermsAgree : List Term → List Atom → Prop where
  | nil : PatternTermsAgree [] []
  | cons {term : Term} {atom : Atom} {terms : List Term} {atoms : List Atom}
      (head : PatternTermAgrees term atom)
      (tail : PatternTermsAgree terms atoms) :
      PatternTermsAgree (term :: terms) (atom :: atoms)

/-- Agreement between the independent translator-rule predicate and the
executable compiler environment. -/
structure EnvAgrees (state : TranslatorState) (env : CEnv) : Prop where
  translatorRules (name : String) :
    state.hasRule name ↔ env.translatorRules.contains name = true

/-- Absence from the independent translator-rule set is reflected by the
executable list representation. -/
theorem EnvAgrees.notContains {state : TranslatorState} {env : CEnv}
    (agreement : EnvAgrees state env) {name : String}
    (absent : ¬ state.hasRule name) :
    env.translatorRules.contains name = false := by
  cases executableRule : env.translatorRules.contains name with
  | false => rfl
  | true =>
      exact False.elim
        (absent ((agreement.translatorRules name).mpr executableRule))

mutual

/-- Cross-representation agreement for the independent and executable goal
languages.  Constructors are added only when their compiler clauses are
proved. -/
inductive GoalAgrees : PeTTaSpec.PrologCore.Goal → PLeaTTa.Goal → Prop where
  | unify {referenceLeft referenceRight : Term}
      {executableLeft executableRight : Atom}
      (left : TermAgrees referenceLeft executableLeft)
      (right : TermAgrees referenceRight executableRight) :
      GoalAgrees (.unify referenceLeft referenceRight)
        (.eq executableLeft executableRight)
  | cut : GoalAgrees .cut .cut
  | findall {referenceTemplate referenceOutput : Term}
      {executableTemplate executableOutput : Atom}
      {referenceGoals : List PeTTaSpec.PrologCore.Goal}
      {executableGoals : List PLeaTTa.Goal}
      (template : TermAgrees referenceTemplate executableTemplate)
      (body : GoalsAgree referenceGoals executableGoals)
      (output : TermAgrees referenceOutput executableOutput) :
      GoalAgrees
        (.findall referenceTemplate (.conjunction referenceGoals)
          referenceOutput)
        (.findall executableTemplate executableGoals executableOutput)

/-- Ordered pointwise goal-list agreement. -/
inductive GoalsAgree : List PeTTaSpec.PrologCore.Goal → List PLeaTTa.Goal →
    Prop where
  | nil : GoalsAgree [] []
  | cons {reference : PeTTaSpec.PrologCore.Goal} {executable : PLeaTTa.Goal}
      {references : List PeTTaSpec.PrologCore.Goal}
      {executables : List PLeaTTa.Goal}
      (head : GoalAgrees reference executable)
      (tail : GoalsAgree references executables) :
      GoalsAgree (reference :: references) (executable :: executables)

end

/-- Ordered agreement is preserved by concatenating two agreeing goal
sequences. -/
theorem GoalsAgree.append {leftReference rightReference :
    List PeTTaSpec.PrologCore.Goal} {leftExecutable rightExecutable :
    List PLeaTTa.Goal}
    (left : GoalsAgree leftReference leftExecutable)
    (right : GoalsAgree rightReference rightExecutable) :
    GoalsAgree (leftReference ++ rightReference)
      (leftExecutable ++ rightExecutable) := by
  cases left with
  | nil => simpa using right
  | cons head tail =>
      exact .cons head (GoalsAgree.append tail right)

/-- Behavioral agreement for optimized executable targets. `normalized` is an
independent reference goal list that still agrees structurally with the
executable IR; the first field proves that normalization preserves every
ordered sequential observation. -/
def SequentialGoalsAgree
    (reference : List PeTTaSpec.PrologCore.Goal)
    (executable : List PLeaTTa.Goal) : Prop :=
  ∃ normalized : List PeTTaSpec.PrologCore.Goal,
    (∀ calls,
      PeTTaSpec.PrologCore.Declarative.Ordered.AllEquivalent calls reference
        normalized) ∧
    GoalsAgree normalized executable

/-- Structural agreement is the reflexive special case of behavioral
agreement. -/
def SequentialGoalsAgree.ofStructural
    {reference : List PeTTaSpec.PrologCore.Goal}
    {executable : List PLeaTTa.Goal}
    (agreement : GoalsAgree reference executable) :
    SequentialGoalsAgree reference executable :=
  ⟨reference, fun _ _ _ => Iff.rfl, agreement⟩

/-- Deep chainification of a surface expression is pointwise chainification
followed by the internal proper-list encoding. -/
theorem chainify_expr (atoms : List Atom) :
    chainify (.expr atoms) = chainOf (atoms.map chainify) := by
  simp [chainify]

/-- Every pinned `let*` expansion contains at least one well-formed binding. -/
theorem letStarExpands_bindings_nonempty {bindings : List Atom}
    {body nested : Atom} (expansion : LetStarExpands bindings body nested) :
    bindings ≠ [] := by
  cases expansion <;> simp

/-- The independent pinned `let*` expansion is accepted by the executable
expander and produces exactly the independently related nested source. -/
theorem letStarExpands_desugar {bindings : List Atom} {body nested : Atom}
    (expansion : LetStarExpands bindings body nested) :
    desugarLetStar? bindings body = some nested := by
  induction expansion with
  | single => rfl
  | @cons pattern value bindings body nested tail inductionHypothesis =>
      have bindingsNonempty : bindings ≠ [] :=
        letStarExpands_bindings_nonempty tail
      obtain ⟨binding, remaining, rfl⟩ :=
        List.exists_cons_of_ne_nil bindingsNonempty
      simp only [desugarLetStar?]
      rw [inductionHypothesis]
      rfl

/-- Expanding a well-formed `let*` grows syntax by less than a factor of two.
This source-side bound is independent of compiler fuel and is enough to show
that the public source-sized budget covers compilation of the nested form. -/
theorem letStarExpands_nested_size_le_twice_source
    {bindings : List Atom} {body nested : Atom}
    (expansion : LetStarExpands bindings body nested) :
    nested.size ≤
      2 * (Atom.expr [.sym "let*", .expr bindings, body]).size := by
  induction expansion with
  | single =>
      simp only [Atom.size, List.map, List.sum_cons, List.sum_nil, Nat.add_zero]
      omega
  | @cons pattern value bindings body nested tail inductionHypothesis =>
      simp only [Atom.size, List.map, List.sum_cons, List.sum_nil,
        Nat.add_zero] at inductionHypothesis ⊢
      omega

/-- Independent native quotation agrees with PLeaTTa's deep chain encoding. -/
theorem quotes_term_agrees {source : Atom} {term : Term}
    (quotation : Quotes source term) : TermAgrees term (chainify source) := by
  refine Quotes.rec
    (motive_1 := fun source term _ => TermAgrees term (chainify source))
    (motive_2 := fun sources terms _ =>
      ProperListAgrees terms (chainOf (sources.map chainify)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ quotation
  · intro name
    simpa [chainify, canonBool] using TermAgrees.sourceVariable name
  · intro name
    by_cases trueName : name = "true"
    · subst name
      simpa [chainify, canonBool] using TermAgrees.trueAtom
    · by_cases falseName : name = "false"
      · subst name
        simpa [chainify, canonBool] using TermAgrees.falseAtom
      · simpa [chainify, canonBool, trueName, falseName] using
          TermAgrees.atom trueName falseName
  · intro value
    simpa [chainify, canonBool] using TermAgrees.integer value
  · intro value
    simpa [chainify, canonBool] using TermAgrees.float value
  · intro value
    simpa [chainify, canonBool] using TermAgrees.string value
  · simpa [chainify, canonBool] using TermAgrees.trueAtom
  · simpa [chainify, canonBool] using TermAgrees.falseAtom
  · intro atoms terms items itemsAgreement
    rw [chainify_expr]
    exact .properList itemsAgreement
  · exact .nil
  · intro atom term atoms terms head tail headAgreement tailAgreement
    simpa [chainOf] using ProperListAgrees.cons headAgreement tailAgreement

/-- Every native literal translation is compiled to a related internal value,
with no emitted goals and an unchanged fresh-variable counter. -/
theorem compileExprFuel_literal_adequate {source : Atom} {term : Term}
    (fuel : Nat) (env : CEnv) (counter : Nat) (literal : Literal source term) :
    ∃ internal : Atom,
      compileExprFuel (fuel + 1) env counter source =
        .ok (internal, [], counter) ∧
      TermAgrees term internal := by
  cases literal with
  | «variable» name =>
      exact ⟨.var name, by rw [compileExprFuel.eq_2], .sourceVariable name⟩
  | symbol name =>
      by_cases trueName : name = "true"
      · subst name
        exact ⟨.sym "True", by rw [compileExprFuel.eq_3]; rfl, .trueAtom⟩
      · by_cases falseName : name = "false"
        · subst name
          exact ⟨.sym "False", by rw [compileExprFuel.eq_3]; rfl, .falseAtom⟩
        · exact ⟨.sym name,
            by rw [compileExprFuel.eq_3]; simp [canonBool, trueName, falseName],
            .atom trueName falseName⟩
  | integer value =>
      exact ⟨.gnd (.int value), by rw [compileExprFuel.eq_4]; rfl,
        .integer value⟩
  | float value =>
      exact ⟨.gnd (.float value), by rw [compileExprFuel.eq_4]; rfl,
        .float value⟩
  | string value =>
      exact ⟨.gnd (.str value), by rw [compileExprFuel.eq_4]; rfl,
        .string value⟩
  | trueGround =>
      exact ⟨.sym "True", by rw [compileExprFuel.eq_4]; rfl, .trueAtom⟩
  | falseGround =>
      exact ⟨.sym "False", by rw [compileExprFuel.eq_4]; rfl, .falseAtom⟩
  | emptyList =>
      exact ⟨nilA, by rw [compileExprFuel.eq_5], .properList .nil⟩

/-- The public compiler wrapper preserves the literal adequacy result. -/
theorem compileExpr_literal_adequate {source : Atom} {term : Term}
    (env : CEnv) (counter : Nat) (literal : Literal source term) :
    ∃ internal : Atom,
      compileExpr env counter source = .ok (internal, [], counter) ∧
      TermAgrees term internal := by
  simpa only [compileExpr, Nat.add_assoc, Nat.reduceAdd] using
    compileExprFuel_literal_adequate (compilerFuel source + 63) env counter
      literal

/-- Soundness of the executable atomic `constrain_args/3` branches.  The
independent source relation is `ConstrainsAtomicPattern`; executable pattern
compilation preserves the value, emits no goals, and leaves the fresh counter
unchanged.  [SPEC translator.pl:2] -/
theorem compilePatternFuel_atomic_sound {source : Atom} {term : Term}
    (fuel : Nat) (env : CEnv) (counter : Nat)
    (native : ConstrainsAtomicPattern source term) :
    ∃ internal : Atom,
      compilePatternFuel (fuel + 1) env counter source =
        .ok (internal, [], counter) ∧
      TermAgrees term internal := by
  cases native with
  | literal literal =>
      cases literal with
      | «variable» name =>
          exact ⟨.var name, compilePatternFuel_var_eq fuel env counter name,
            .sourceVariable name⟩
      | symbol name =>
          by_cases trueName : name = "true"
          · subst name
            exact ⟨.sym "True", by
                simpa [canonBool] using
                  compilePatternFuel_sym_eq fuel env counter "true",
              .trueAtom⟩
          · by_cases falseName : name = "false"
            · subst name
              exact ⟨.sym "False", by
                  simpa [canonBool] using
                    compilePatternFuel_sym_eq fuel env counter "false",
                .falseAtom⟩
            · exact ⟨.sym name,
                by
                  simpa [canonBool, trueName, falseName] using
                    compilePatternFuel_sym_eq fuel env counter name,
                .atom trueName falseName⟩
      | integer value =>
          exact ⟨.gnd (.int value), by
              simpa [canonBool] using
                compilePatternFuel_gnd_eq fuel env counter (.int value),
            .integer value⟩
      | float value =>
          exact ⟨.gnd (.float value), by
              simpa [canonBool] using
                compilePatternFuel_gnd_eq fuel env counter (.float value),
            .float value⟩
      | string value =>
          exact ⟨.gnd (.str value), by
              simpa [canonBool] using
                compilePatternFuel_gnd_eq fuel env counter (.str value),
            .string value⟩
      | trueGround =>
          exact ⟨.sym "True", by
              simpa [canonBool] using
                compilePatternFuel_gnd_eq fuel env counter (.bool true),
            .trueAtom⟩
      | falseGround =>
          exact ⟨.sym "False", by
              simpa [canonBool] using
                compilePatternFuel_gnd_eq fuel env counter (.bool false),
            .falseAtom⟩
      | emptyList =>
          exact ⟨nilA, compilePatternFuel_nil_eq fuel env counter,
            .properList .nil⟩

/-- Public atomic-pattern compiler soundness at the source-derived budget. -/
theorem compilePattern_atomic_sound {source : Atom} {term : Term}
    (env : CEnv) (counter : Nat)
    (native : ConstrainsAtomicPattern source term) :
    ∃ internal : Atom,
      compilePattern env counter source = .ok (internal, [], counter) ∧
      TermAgrees term internal := by
  simpa only [compilePattern, Nat.add_assoc, Nat.reduceAdd] using
    compilePatternFuel_atomic_sound (compilerFuel source + 63) env counter
      native

/-- Completeness on the independently supported atomic pattern fragment:
every successful executable result is represented by the pinned
`constrain_args/3` clause, with exactly the same output, empty goal list, and
counter. -/
theorem compilePattern_atomic_complete {source internal : Atom}
    (env : CEnv) (counter : Nat) {executableGoals : List PLeaTTa.Goal}
    {nextCounter : Nat} (supported : SupportedAtomicPattern source)
    (compiled : compilePattern env counter source =
      .ok (internal, executableGoals, nextCounter)) :
    ∃ term,
      ConstrainsAtomicPattern source term ∧
      TermAgrees term internal ∧ executableGoals = [] ∧ nextCounter = counter := by
  obtain ⟨term, native⟩ := supported
  obtain ⟨referenceInternal, referenceCompiled, termAgreement⟩ :=
    compilePattern_atomic_sound env counter native
  have resultEquality :
      (internal, executableGoals, nextCounter) =
        (referenceInternal, [], counter) :=
    Except.ok.inj (compiled.symm.trans referenceCompiled)
  cases resultEquality
  exact ⟨term, native, termAgreement, rfl, rfl⟩

/-- Structural atom size is always positive. -/
theorem atom_size_positive_for_compiler (source : Atom) : 0 < source.size := by
  cases source <;> simp [Atom.size] <;> omega

/-- A source list's length is bounded by the sum of its members' structural
sizes.  This connects the independent traversal depth to the public compiler's
syntax-derived fuel budget. -/
theorem source_length_le_size_sum (sources : List Atom) :
    sources.length ≤ (sources.map Atom.size).sum := by
  induction sources with
  | nil => simp
  | cons source sources inductionHypothesis =>
      simp only [List.length_cons, List.map, List.sum_cons]
      have positive := atom_size_positive_for_compiler source
      omega

/-- Fuel-parametric soundness of left-to-right atomic pattern traversal.  The
base `sources.length + 1` pays for one list node per member plus the terminal
empty list; extra fuel cannot change the result.  [SPEC translator.pl:20-22] -/
theorem compilePatternListFuel_atomic_sound (env : CEnv) (counter : Nat)
    {sources : List Atom} {terms : List Term}
    (native : ConstrainsAtomicPatternSeq sources terms) (extraFuel : Nat) :
    ∃ internals,
      compilePatternListFuel (sources.length + 1 + extraFuel) env counter
          sources = .ok (internals, [], counter) ∧
      TermsAgree terms internals := by
  induction native with
  | nil =>
      refine ⟨[], ?_, .nil⟩
      simpa [Nat.add_comm] using
        compilePatternListFuel_nil_eq extraFuel env counter
  | @cons source term sources terms head tail inductionHypothesis =>
      obtain ⟨headInternal, headCompiled, headAgreement⟩ :=
        compilePatternFuel_atomic_sound (sources.length + extraFuel) env
          counter head
      obtain ⟨tailInternals, tailCompiled, tailAgreement⟩ :=
        inductionHypothesis
      have childFuelEq :
          (sources.length + extraFuel) + 1 =
            sources.length + 1 + extraFuel := by
        omega
      rw [childFuelEq] at headCompiled
      refine ⟨headInternal :: tailInternals, ?_,
        .cons headAgreement tailAgreement⟩
      rw [show (source :: sources).length + 1 + extraFuel =
          (sources.length + 1 + extraFuel) + 1 by simp; omega]
      rw [compilePatternListFuel_cons_eq, headCompiled]
      dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind]
      rw [tailCompiled]
      rfl

/-- Public soundness of atomic `maplist(constrain_args, ...)` traversal.  The
public source-sized budget is proved sufficient rather than assumed. -/
theorem compilePatternList_atomic_sound (env : CEnv) (counter : Nat)
    {sources : List Atom} {terms : List Term}
    (native : ConstrainsAtomicPatternSeq sources terms) :
    ∃ internals,
      compilePatternList env counter sources = .ok (internals, [], counter) ∧
      TermsAgree terms internals := by
  have lengthBound := source_length_le_size_sum sources
  have fuelBound :
      sources.length + 1 ≤ compilerListFuel sources + 64 := by
    simp only [compilerListFuel]
    omega
  obtain ⟨extraFuel, fuelEquality⟩ :
      ∃ extraFuel,
        compilerListFuel sources + 64 =
          sources.length + 1 + extraFuel := by
    exact ⟨compilerListFuel sources + 64 - (sources.length + 1), by omega⟩
  obtain ⟨internals, compiled, termsAgreement⟩ :=
    compilePatternListFuel_atomic_sound env counter native extraFuel
  exact ⟨internals, by simpa [compilePatternList, fuelEquality] using compiled,
    termsAgreement⟩

/-- Completeness on independently supported atomic pattern sequences: every
successful executable result has the same ordered terms, empty flattened goal
list, and unchanged fresh counter as pinned `translate_clause/3`. -/
theorem compilePatternList_atomic_complete (env : CEnv) (counter : Nat)
    {sources internals : List Atom} {executableGoals : List PLeaTTa.Goal}
    {nextCounter : Nat} (supported : SupportedAtomicPatternSeq sources)
    (compiled : compilePatternList env counter sources =
      .ok (internals, executableGoals, nextCounter)) :
    ∃ terms,
      ConstrainsAtomicPatternSeq sources terms ∧
      TermsAgree terms internals ∧ executableGoals = [] ∧ nextCounter = counter := by
  obtain ⟨terms, native⟩ := supported
  obtain ⟨referenceInternals, referenceCompiled, termsAgreement⟩ :=
    compilePatternList_atomic_sound env counter native
  have resultEquality :
      (internals, executableGoals, nextCounter) =
        (referenceInternals, [], counter) :=
    Except.ok.inj (compiled.symm.trans referenceCompiled)
  cases resultEquality
  exact ⟨terms, native, termsAgreement, rfl, rfl⟩

/-- Concrete positive witness for ordered two-member pattern traversal. -/
theorem compilePatternList_atomic_pair_sound (env : CEnv) (counter : Nat)
    (name : String) (value : Int) :
    ∃ internals,
      compilePatternList env counter [.var name, .gnd (.int value)] =
        .ok (internals, [], counter) ∧
      TermsAgree [.variable (.source name), .integer value] internals := by
  exact compilePatternList_atomic_sound env counter
    (translates_atomic_pattern_pair name value)

/-- Every independently constrained atomic/`cons` pattern has a positive,
syntax-bounded compiler budget.  Additional fuel preserves the same native
term, ordered goal sequence, and fresh-counter result. -/
theorem compilePatternFuel_initial_sound {state : TranslatorState}
    (env : CEnv) {counter : Nat} {source : Atom} {term : Term}
    {goals : List PeTTaSpec.PrologCore.Goal} {nextCounter : Nat}
    (native : ConstrainsPattern state counter source term goals nextCounter) :
    ∃ baseFuel,
      0 < baseFuel ∧
      baseFuel < 2 * source.size ∧
      ∀ extraFuel, ∃ internal executableGoals,
        compilePatternFuel (baseFuel + extraFuel) env counter source =
          .ok (internal, executableGoals, nextCounter) ∧
        PatternTermAgrees term internal ∧
          GoalsAgree goals executableGoals := by
  induction native with
  | @atomic atomicCounter atomicSource atomicTerm value =>
      refine ⟨1, by omega, ?_, ?_⟩
      · cases value with
        | literal literal => cases literal <;> simp [Atom.size]
      · intro extraFuel
        obtain ⟨internal, compiled, termAgreement⟩ :=
          compilePatternFuel_atomic_sound extraFuel env atomicCounter value
        exact ⟨internal, [], by simpa [Nat.add_comm] using compiled,
          .atomic termAgreement, .nil⟩
  | @cons patternCounter headCounter nextCounter headSource tailSource _ _ _ _
      head tail
      headInduction tailInduction =>
      obtain ⟨headFuel, headPositive, headBound, headCompiles⟩ :=
        headInduction
      obtain ⟨tailFuel, tailPositive, tailBound, tailCompiles⟩ :=
        tailInduction
      let childFuel := max headFuel tailFuel
      have headLe : headFuel ≤ childFuel := Nat.le_max_left _ _
      have tailLe : tailFuel ≤ childFuel := Nat.le_max_right _ _
      refine ⟨childFuel + 1, by omega, ?_, ?_⟩
      · have headSizePositive := atom_size_positive_for_compiler headSource
        have tailSizePositive := atom_size_positive_for_compiler tailSource
        simp only [Atom.size, List.map, List.sum_cons, List.sum_nil]
        omega
      · intro extraFuel
        obtain ⟨headInternal, headExecutableGoals, headCompiled,
            headAgreement, headGoalsAgreement⟩ :=
          headCompiles (childFuel + extraFuel - headFuel)
        obtain ⟨tailInternal, tailExecutableGoals, tailCompiled,
            tailAgreement, tailGoalsAgreement⟩ :=
          tailCompiles (childFuel + extraFuel - tailFuel)
        have headFuelEq :
            headFuel + (childFuel + extraFuel - headFuel) =
              childFuel + extraFuel := by
          omega
        have tailFuelEq :
            tailFuel + (childFuel + extraFuel - tailFuel) =
              childFuel + extraFuel := by
          omega
        rw [headFuelEq] at headCompiled
        rw [tailFuelEq] at tailCompiled
        refine ⟨consC headInternal tailInternal,
          headExecutableGoals ++ tailExecutableGoals, ?_,
          .listCell headAgreement tailAgreement,
          GoalsAgree.append headGoalsAgreement tailGoalsAgreement⟩
        rw [show (childFuel + 1) + extraFuel =
            (childFuel + extraFuel) + 1 by omega]
        rw [compilePatternFuel_cons_eq, headCompiled]
        dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind]
        rw [tailCompiled]
        rfl

/-- Public soundness of the recursive atomic/`cons` pattern fragment.  The
source-derived compiler budget is proved sufficient rather than assumed. -/
theorem compilePattern_sound {state : TranslatorState} (env : CEnv)
    {counter : Nat} {source : Atom} {term : Term}
    {goals : List PeTTaSpec.PrologCore.Goal} {nextCounter : Nat}
    (native : ConstrainsPattern state counter source term goals nextCounter) :
    ∃ internal executableGoals,
      compilePattern env counter source =
        .ok (internal, executableGoals, nextCounter) ∧
      PatternTermAgrees term internal ∧ GoalsAgree goals executableGoals := by
  obtain ⟨baseFuel, basePositive, baseBound, compiles⟩ :=
    compilePatternFuel_initial_sound env native
  have sourcePositive := atom_size_positive_for_compiler source
  have baseLe : baseFuel ≤ compilerFuel source + 64 := by
    simp only [compilerFuel]
    omega
  obtain ⟨extraFuel, fuelEquality⟩ :
      ∃ extraFuel, compilerFuel source + 64 = baseFuel + extraFuel :=
    ⟨compilerFuel source + 64 - baseFuel, by omega⟩
  obtain ⟨internal, executableGoals, compiled, termAgreement,
      goalsAgreement⟩ := compiles extraFuel
  exact ⟨internal, executableGoals,
    by simpa [compilePattern, fuelEquality] using compiled,
    termAgreement, goalsAgreement⟩

/-- Completeness on the independently supported atomic/`cons` fragment:
every successful executable result agrees with the source relation, including
ordered goals and the final fresh counter. -/
theorem compilePattern_complete {state : TranslatorState} (env : CEnv)
    {counter : Nat} {source internal : Atom}
    {executableGoals : List PLeaTTa.Goal} {nextCounter : Nat}
    (supported : SupportedPattern state counter source)
    (compiled : compilePattern env counter source =
      .ok (internal, executableGoals, nextCounter)) :
    ∃ term goals,
      ConstrainsPattern state counter source term goals nextCounter ∧
      PatternTermAgrees term internal ∧ GoalsAgree goals executableGoals := by
  obtain ⟨term, goals, referenceCounter, native⟩ := supported
  obtain ⟨referenceInternal, referenceGoals, referenceCompiled,
      termAgreement, goalsAgreement⟩ := compilePattern_sound env native
  have resultEquality :
      (internal, executableGoals, nextCounter) =
        (referenceInternal, referenceGoals, referenceCounter) :=
    Except.ok.inj (compiled.symm.trans referenceCompiled)
  cases resultEquality
  exact ⟨term, goals, native, termAgreement, goalsAgreement⟩

/-- Every independently specified ordered pattern traversal has a positive,
syntax-bounded shared budget.  Member counters and flattened constraint goals
are threaded left-to-right exactly as in `translator.pl:20-22`. -/
theorem compilePatternListFuel_initial_sound {state : TranslatorState}
    (env : CEnv) {counter : Nat} {sources : List Atom} {terms : List Term}
    {goals : List PeTTaSpec.PrologCore.Goal} {nextCounter : Nat}
    (native :
      ConstrainsPatternSeq state counter sources terms goals nextCounter) :
    ∃ baseFuel,
      0 < baseFuel ∧
      baseFuel < 8 * ((sources.map Atom.size).sum + 1) ∧
      ∀ extraFuel, ∃ internals executableGoals,
        compilePatternListFuel (baseFuel + extraFuel) env counter sources =
          .ok (internals, executableGoals, nextCounter) ∧
        PatternTermsAgree terms internals ∧
          GoalsAgree goals executableGoals := by
  induction native with
  | @nil nilCounter =>
      refine ⟨1, by omega, by simp, ?_⟩
      intro extraFuel
      exact ⟨[], [], by
          simpa [Nat.add_comm] using
            compilePatternListFuel_nil_eq extraFuel env nilCounter,
        .nil, .nil⟩
  | @cons patternCounter headCounter nextCounter source term sources terms
      headGoals tailGoals head tail tailInduction =>
      obtain ⟨headFuel, headPositive, headBound, headCompiles⟩ :=
        compilePatternFuel_initial_sound env head
      obtain ⟨tailFuel, tailPositive, tailBound, tailCompiles⟩ :=
        tailInduction
      let childFuel := max headFuel tailFuel
      have headLe : headFuel ≤ childFuel := Nat.le_max_left _ _
      have tailLe : tailFuel ≤ childFuel := Nat.le_max_right _ _
      refine ⟨childFuel + 1, by omega, ?_, ?_⟩
      · have sourcePositive := atom_size_positive_for_compiler source
        simp only [List.map, List.sum_cons]
        omega
      · intro extraFuel
        obtain ⟨headInternal, headExecutableGoals, headCompiled,
            headAgreement, headGoalsAgreement⟩ :=
          headCompiles (childFuel + extraFuel - headFuel)
        obtain ⟨tailInternals, tailExecutableGoals, tailCompiled,
            tailAgreement, tailGoalsAgreement⟩ :=
          tailCompiles (childFuel + extraFuel - tailFuel)
        have headFuelEq :
            headFuel + (childFuel + extraFuel - headFuel) =
              childFuel + extraFuel := by
          omega
        have tailFuelEq :
            tailFuel + (childFuel + extraFuel - tailFuel) =
              childFuel + extraFuel := by
          omega
        rw [headFuelEq] at headCompiled
        rw [tailFuelEq] at tailCompiled
        refine ⟨headInternal :: tailInternals,
          headExecutableGoals ++ tailExecutableGoals, ?_,
          .cons headAgreement tailAgreement,
          GoalsAgree.append headGoalsAgreement tailGoalsAgreement⟩
        rw [show (childFuel + 1) + extraFuel =
            (childFuel + extraFuel) + 1 by omega]
        rw [compilePatternListFuel_cons_eq, headCompiled]
        dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind]
        rw [tailCompiled]
        rfl

/-- Public soundness of recursive pattern-list traversal at the source-derived
shared budget. -/
theorem compilePatternList_sound {state : TranslatorState} (env : CEnv)
    {counter : Nat} {sources : List Atom} {terms : List Term}
    {goals : List PeTTaSpec.PrologCore.Goal} {nextCounter : Nat}
    (native :
      ConstrainsPatternSeq state counter sources terms goals nextCounter) :
    ∃ internals executableGoals,
      compilePatternList env counter sources =
        .ok (internals, executableGoals, nextCounter) ∧
      PatternTermsAgree terms internals ∧ GoalsAgree goals executableGoals := by
  obtain ⟨baseFuel, basePositive, baseBound, compiles⟩ :=
    compilePatternListFuel_initial_sound env native
  have baseLe : baseFuel ≤ compilerListFuel sources + 64 := by
    simp only [compilerListFuel]
    omega
  obtain ⟨extraFuel, fuelEquality⟩ :
      ∃ extraFuel,
        compilerListFuel sources + 64 = baseFuel + extraFuel :=
    ⟨compilerListFuel sources + 64 - baseFuel, by omega⟩
  obtain ⟨internals, executableGoals, compiled, termsAgreement,
      goalsAgreement⟩ := compiles extraFuel
  exact ⟨internals, executableGoals,
    by simpa [compilePatternList, fuelEquality] using compiled,
    termsAgreement, goalsAgreement⟩

/-- Completeness on independently supported recursive pattern sequences. -/
theorem compilePatternList_complete {state : TranslatorState} (env : CEnv)
    {counter : Nat} {sources internals : List Atom}
    {executableGoals : List PLeaTTa.Goal} {nextCounter : Nat}
    (supported : SupportedPatternSeq state counter sources)
    (compiled : compilePatternList env counter sources =
      .ok (internals, executableGoals, nextCounter)) :
    ∃ terms goals,
      ConstrainsPatternSeq state counter sources terms goals nextCounter ∧
      PatternTermsAgree terms internals ∧ GoalsAgree goals executableGoals := by
  obtain ⟨terms, goals, referenceCounter, native⟩ := supported
  obtain ⟨referenceInternals, referenceGoals, referenceCompiled,
      termsAgreement, goalsAgreement⟩ := compilePatternList_sound env native
  have resultEquality :
      (internals, executableGoals, nextCounter) =
        (referenceInternals, referenceGoals, referenceCounter) :=
    Except.ok.inj (compiled.symm.trans referenceCompiled)
  cases resultEquality
  exact ⟨terms, goals, native, termsAgreement, goalsAgreement⟩

/-- Executable witness for the independent two-element proper-list pattern. -/
theorem compilePattern_cons_pair_sound (state : TranslatorState) (env : CEnv)
    (counter : Nat) (name : String) (value : Int) :
    ∃ internal executableGoals,
      compilePattern env counter
        (.expr [.sym "cons", .var name,
          .expr [.sym "cons", .gnd (.int value), .expr []]]) =
        .ok (internal, executableGoals, counter) ∧
      PatternTermAgrees
        (.list [.variable (.source name), .integer value] none) internal ∧
      GoalsAgree [] executableGoals := by
  exact compilePattern_sound env
    (constrains_cons_pair state counter name value)

/-- Executable witness for the independent dotted-list pattern. -/
theorem compilePattern_dotted_cons_sound (state : TranslatorState)
    (env : CEnv) (counter : Nat) (headName tailName : String) :
    ∃ internal executableGoals,
      compilePattern env counter
        (.expr [.sym "cons", .var headName, .var tailName]) =
        .ok (internal, executableGoals, counter) ∧
      PatternTermAgrees
        (.list [.variable (.source headName)]
          (some (.variable (.source tailName)))) internal ∧
      GoalsAgree [] executableGoals := by
  exact compilePattern_sound env
    (constrains_dotted_cons state counter headName tailName)

/-- Syntactic quotation compiles to the deep chain encoding related to the
independent native quotation term. -/
theorem compileExprFuel_quote_adequate {source : Atom} {term : Term}
    (fuel : Nat) (env : CEnv) (counter : Nat)
    (noHook : env.translatorRules.contains "quote" = false)
    (quotation : Quotes source term) :
    compileExprFuel (fuel + 3) env counter (.expr [.sym "quote", source]) =
        .ok (chainify source, [], counter) ∧
      TermAgrees term (chainify source) ∧ GoalsAgree [] [] := by
  exact ⟨compileExprFuel_quote_eq fuel counter env source noHook,
    quotes_term_agrees quotation, .nil⟩

/-- The public compiler wrapper preserves quotation adequacy. -/
theorem compileExpr_quote_adequate {source : Atom} {term : Term}
    (env : CEnv) (counter : Nat)
    (noHook : env.translatorRules.contains "quote" = false)
    (quotation : Quotes source term) :
    compileExpr env counter (.expr [.sym "quote", source]) =
        .ok (chainify source, [], counter) ∧
      TermAgrees term (chainify source) ∧ GoalsAgree [] [] := by
  simpa only [compileExpr, Nat.add_assoc, Nat.reduceAdd] using
    compileExprFuel_quote_adequate
      (compilerFuel (.expr [.sym "quote", source]) + 61) env counter noHook
      quotation

/-- Adequacy of the independent quotation rule, including native hook
priority. -/
theorem translatesExpr_quote_adequate {state : TranslatorState} (env : CEnv)
    (agreement : EnvAgrees state env) (counter : Nat) {source : Atom}
    {term : Term} (notShadowed : ¬ state.hasRule "quote")
    (quotation : Quotes source term) :
    TranslatesExpr state counter (.expr [.sym "quote", source]) term []
        counter ∧
      compileExpr env counter (.expr [.sym "quote", source]) =
        .ok (chainify source, [], counter) ∧
      TermAgrees term (chainify source) ∧ GoalsAgree [] [] := by
  refine ⟨.quote notShadowed quotation, ?_⟩
  exact compileExpr_quote_adequate env counter
    (agreement.notContains notShadowed) quotation

/-- The pinned zero-argument `cut` translation is represented by exactly one
cut goal and leaves the compiler counter unchanged. -/
theorem compileExprFuel_cut_adequate (fuel : Nat) (env : CEnv) (counter : Nat)
    (noHook : env.translatorRules.contains "cut" = false) :
    compileExprFuel (fuel + 3) env counter (.expr [.sym "cut"]) =
      .ok (.sym "True", [PLeaTTa.Goal.cut], counter) ∧
    TermAgrees (.atom "true") (.sym "True") ∧
    GoalsAgree [.cut] [PLeaTTa.Goal.cut] := by
  constructor
  · exact compileExprFuel_cut_eq fuel counter env noHook
  · exact ⟨.trueAtom, .cons .cut .nil⟩

/-- The public compiler wrapper preserves the unshadowed `cut` translation. -/
theorem compileExpr_cut_adequate (env : CEnv) (counter : Nat)
    (noHook : env.translatorRules.contains "cut" = false) :
    compileExpr env counter (.expr [.sym "cut"]) =
      .ok (.sym "True", [PLeaTTa.Goal.cut], counter) ∧
    TermAgrees (.atom "true") (.sym "True") ∧
    GoalsAgree [.cut] [PLeaTTa.Goal.cut] := by
  simpa only [compileExpr, Nat.add_assoc, Nat.reduceAdd] using
    compileExprFuel_cut_adequate (compilerFuel (.expr [.sym "cut"]) + 61)
      env counter noHook

/-- Adequacy of the independent `cut` rule, including the translator-state
side condition dictated by pinned branch priority.  The theorem constructs
the independent derivation and the agreeing executable result together. -/
theorem translatesExpr_cut_adequate {state : TranslatorState} (env : CEnv)
    (agreement : EnvAgrees state env) (counter : Nat)
    (notShadowed : ¬ state.hasRule "cut") :
    TranslatesExpr state counter (.expr [.sym "cut"])
        (.atom "true") [.cut] counter ∧
      compileExpr env counter (.expr [.sym "cut"]) =
        .ok (.sym "True", [PLeaTTa.Goal.cut], counter) ∧
      TermAgrees (.atom "true") (.sym "True") ∧
      GoalsAgree [.cut] [PLeaTTa.Goal.cut] := by
  refine ⟨.cut notShadowed, ?_⟩
  exact compileExpr_cut_adequate env counter
    (agreement.notContains notShadowed)

mutual

/-- Every independent translation derivation has a positive, syntax-bounded
base budget.  Any additional fuel preserves compilation into a value and
ordered goal list related to the same independent result. -/
theorem compileExprFuel_initial_sound {state : TranslatorState} (env : CEnv)
    (agreement : EnvAgrees state env) {counter : Nat} {source : Atom}
    {term : Term} {goals : List PeTTaSpec.PrologCore.Goal}
    {nextCounter : Nat}
    (native : TranslatesExpr state counter source term goals nextCounter) :
    ∃ baseFuel,
      0 < baseFuel ∧
      baseFuel < 8 * source.size ∧
      ∀ extraFuel, ∃ internal executableGoals,
        compileExprFuel (baseFuel + extraFuel) env counter source =
          .ok (internal, executableGoals, nextCounter) ∧
        TermAgrees term internal ∧ GoalsAgree goals executableGoals := by
  cases native with
  | literal literal =>
      refine ⟨1, by omega, ?_, ?_⟩
      · cases literal <;> simp [Atom.size]
      · intro extraFuel
        obtain ⟨internal, compiled, termAgreement⟩ :=
          compileExprFuel_literal_adequate extraFuel env counter literal
        exact ⟨internal, [], by simpa [Nat.add_comm] using compiled,
          termAgreement, .nil⟩
  | quote notShadowed quotation =>
      refine ⟨3, by omega, ?_, ?_⟩
      · simp [Atom.size]
        omega
      · intro extraFuel
        exact ⟨chainify _, [], by
          simpa [Nat.add_comm] using
            compileExprFuel_quote_adequate extraFuel env counter
              (agreement.notContains notShadowed) quotation⟩
  | cut notShadowed =>
      refine ⟨3, by omega, ?_, ?_⟩
      · simp [Atom.size]
      · intro extraFuel
        exact ⟨.sym "True", [PLeaTTa.Goal.cut], by
          simpa [Nat.add_comm] using
            compileExprFuel_cut_adequate extraFuel env counter
              (agreement.notContains notShadowed)⟩
  | @collapse _ bodyCounter _ _ _ notShadowed body =>
      obtain ⟨bodyFuel, bodyPositive, bodyBound, bodyCompiles⟩ :=
        compileExprFuel_initial_sound env agreement body
      refine ⟨bodyFuel + 3, by omega, ?_, ?_⟩
      · simp [Atom.size]
        omega
      · intro extraFuel
        obtain ⟨internal, executableGoals, compiled, termAgreement,
            goalsAgreement⟩ := bodyCompiles extraFuel
        let output := Atom.var s!"_q{bodyCounter}"
        refine ⟨output, [PLeaTTa.Goal.findall internal executableGoals output],
          ?_, .generatedVariable bodyCounter, ?_⟩
        · rw [show (bodyFuel + 3) + extraFuel =
            (bodyFuel + extraFuel) + 3 by omega]
          exact compileExprFuel_collapse_eq (bodyFuel + extraFuel) env counter
            _ internal executableGoals bodyCounter
            (agreement.notContains notShadowed) compiled
        · exact .cons
            (.findall termAgreement goalsAgreement
              (.generatedVariable bodyCounter))
            .nil
  | letBind notShadowed patternTranslation valueTranslation bodyTranslation =>
      obtain ⟨patternFuel, patternPositive, patternBound, patternCompiles⟩ :=
        compileExprFuel_initial_sound env agreement patternTranslation
      obtain ⟨valueFuel, valuePositive, valueBound, valueCompiles⟩ :=
        compileExprFuel_initial_sound env agreement valueTranslation
      obtain ⟨bodyFuel, bodyPositive, bodyBound, bodyCompiles⟩ :=
        compileExprFuel_initial_sound env agreement bodyTranslation
      let childFuel := max patternFuel (max valueFuel bodyFuel)
      have patternLe : patternFuel ≤ childFuel := by
        exact Nat.le_max_left _ _
      have valueLe : valueFuel ≤ childFuel := by
        exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      have bodyLe : bodyFuel ≤ childFuel := by
        exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
      have childFuelBound : childFuel ≤ patternFuel + valueFuel + bodyFuel := by
        omega
      refine ⟨childFuel + 3, by omega, ?_, ?_⟩
      · simp [Atom.size]
        omega
      · intro extraFuel
        have patternAt : patternFuel ≤ childFuel + extraFuel := by omega
        have valueAt : valueFuel ≤ childFuel + extraFuel := by omega
        have bodyAt : bodyFuel ≤ childFuel + extraFuel := by omega
        obtain ⟨patternInternal, patternExecutableGoals, patternCompiled,
            patternAgreement, patternGoalsAgreement⟩ :=
          patternCompiles (childFuel + extraFuel - patternFuel)
        obtain ⟨valueInternal, valueExecutableGoals, valueCompiled,
            valueAgreement, valueGoalsAgreement⟩ :=
          valueCompiles (childFuel + extraFuel - valueFuel)
        obtain ⟨bodyInternal, bodyExecutableGoals, bodyCompiled,
            bodyAgreement, bodyGoalsAgreement⟩ :=
          bodyCompiles (childFuel + extraFuel - bodyFuel)
        have patternFuelEq :
            patternFuel + (childFuel + extraFuel - patternFuel) =
              childFuel + extraFuel := by
          omega
        have valueFuelEq :
            valueFuel + (childFuel + extraFuel - valueFuel) =
              childFuel + extraFuel := by
          omega
        have bodyFuelEq :
            bodyFuel + (childFuel + extraFuel - bodyFuel) =
              childFuel + extraFuel := by
          omega
        rw [patternFuelEq] at patternCompiled
        rw [valueFuelEq] at valueCompiled
        rw [bodyFuelEq] at bodyCompiled
        refine ⟨bodyInternal,
          [PLeaTTa.Goal.eq patternInternal valueInternal] ++
            patternExecutableGoals ++ valueExecutableGoals ++
            bodyExecutableGoals,
          ?_, bodyAgreement, ?_⟩
        · rw [show (childFuel + 3) + extraFuel =
            (childFuel + extraFuel) + 3 by omega]
          exact compileExprFuel_let_eq (childFuel + extraFuel) env counter
            _ _ _ patternInternal valueInternal bodyInternal
            patternExecutableGoals valueExecutableGoals bodyExecutableGoals
            _ _ _ (agreement.notContains notShadowed)
            patternCompiled valueCompiled bodyCompiled
        · exact GoalsAgree.append
            (GoalsAgree.append
              (.cons (.unify patternAgreement valueAgreement)
                patternGoalsAgreement)
              valueGoalsAgreement)
            bodyGoalsAgreement
  | chainBind notShadowed firstTranslation secondTranslation
      bodyTranslation =>
      obtain ⟨firstFuel, firstPositive, firstBound, firstCompiles⟩ :=
        compileExprFuel_initial_sound env agreement firstTranslation
      obtain ⟨secondFuel, secondPositive, secondBound, secondCompiles⟩ :=
        compileExprFuel_initial_sound env agreement secondTranslation
      obtain ⟨bodyFuel, bodyPositive, bodyBound, bodyCompiles⟩ :=
        compileExprFuel_initial_sound env agreement bodyTranslation
      let childFuel := max firstFuel (max secondFuel bodyFuel)
      have firstLe : firstFuel ≤ childFuel := by
        exact Nat.le_max_left _ _
      have secondLe : secondFuel ≤ childFuel := by
        exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      have bodyLe : bodyFuel ≤ childFuel := by
        exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
      have childFuelBound : childFuel ≤ firstFuel + secondFuel + bodyFuel := by
        omega
      refine ⟨childFuel + 3, by omega, ?_, ?_⟩
      · simp [Atom.size]
        omega
      · intro extraFuel
        have firstAt : firstFuel ≤ childFuel + extraFuel := by omega
        have secondAt : secondFuel ≤ childFuel + extraFuel := by omega
        have bodyAt : bodyFuel ≤ childFuel + extraFuel := by omega
        obtain ⟨firstInternal, firstExecutableGoals, firstCompiled,
            firstAgreement, firstGoalsAgreement⟩ :=
          firstCompiles (childFuel + extraFuel - firstFuel)
        obtain ⟨secondInternal, secondExecutableGoals, secondCompiled,
            secondAgreement, secondGoalsAgreement⟩ :=
          secondCompiles (childFuel + extraFuel - secondFuel)
        obtain ⟨bodyInternal, bodyExecutableGoals, bodyCompiled,
            bodyAgreement, bodyGoalsAgreement⟩ :=
          bodyCompiles (childFuel + extraFuel - bodyFuel)
        have firstFuelEq :
            firstFuel + (childFuel + extraFuel - firstFuel) =
              childFuel + extraFuel := by
          omega
        have secondFuelEq :
            secondFuel + (childFuel + extraFuel - secondFuel) =
              childFuel + extraFuel := by
          omega
        have bodyFuelEq :
            bodyFuel + (childFuel + extraFuel - bodyFuel) =
              childFuel + extraFuel := by
          omega
        rw [firstFuelEq] at firstCompiled
        rw [secondFuelEq] at secondCompiled
        rw [bodyFuelEq] at bodyCompiled
        refine ⟨bodyInternal,
          [PLeaTTa.Goal.eq firstInternal secondInternal] ++
            firstExecutableGoals ++ secondExecutableGoals ++
            bodyExecutableGoals,
          ?_, bodyAgreement, ?_⟩
        · rw [show (childFuel + 3) + extraFuel =
            (childFuel + extraFuel) + 3 by omega]
          exact compileExprFuel_chain_eq (childFuel + extraFuel) env counter
            _ _ _ firstInternal secondInternal bodyInternal
            firstExecutableGoals secondExecutableGoals bodyExecutableGoals
            _ _ _ (agreement.notContains notShadowed)
            firstCompiled secondCompiled bodyCompiled
        · exact GoalsAgree.append
            (GoalsAgree.append
              (.cons (.unify firstAgreement secondAgreement)
                firstGoalsAgreement)
              secondGoalsAgreement)
            bodyGoalsAgreement
  | progn notShadowed arguments =>
      obtain ⟨listFuel, listPositive, listBound, listCompiles⟩ :=
        compileSeqFuel_initial_sound env agreement arguments
      have sourcesNonempty : _ := TranslatesSeq.sources_nonempty arguments
      obtain ⟨source, sources, rfl⟩ := List.exists_cons_of_ne_nil sourcesNonempty
      refine ⟨listFuel + 3, by omega, ?_, ?_⟩
      · simp only [List.map, List.sum_cons] at listBound
        simp only [Atom.size, List.map, List.sum_cons]
        omega
      · intro extraFuel
        obtain ⟨internals, executableGoals, compiled, _internalsNonempty,
            _firstAgreement, lastAgreement, goalsAgreement⟩ :=
          listCompiles extraFuel
        refine ⟨internals.getLast!, executableGoals, ?_, lastAgreement,
          goalsAgreement⟩
        rw [show (listFuel + 3) + extraFuel =
          (listFuel + extraFuel) + 3 by omega]
        exact compileExprFuel_progn_eq (listFuel + extraFuel) env counter
          source sources internals executableGoals _
          (agreement.notContains notShadowed) compiled
  | prog1 notShadowed arguments =>
      obtain ⟨listFuel, listPositive, listBound, listCompiles⟩ :=
        compileSeqFuel_initial_sound env agreement arguments
      have sourcesNonempty : _ := TranslatesSeq.sources_nonempty arguments
      obtain ⟨source, sources, rfl⟩ := List.exists_cons_of_ne_nil sourcesNonempty
      refine ⟨listFuel + 3, by omega, ?_, ?_⟩
      · simp only [List.map, List.sum_cons] at listBound
        simp only [Atom.size, List.map, List.sum_cons]
        omega
      · intro extraFuel
        obtain ⟨internals, executableGoals, compiled, _internalsNonempty,
            firstAgreement, _lastAgreement, goalsAgreement⟩ :=
          listCompiles extraFuel
        refine ⟨internals.head!, executableGoals, ?_, firstAgreement,
          goalsAgreement⟩
        rw [show (listFuel + 3) + extraFuel =
          (listFuel + extraFuel) + 3 by omega]
        exact compileExprFuel_prog1_eq (listFuel + extraFuel) env counter
          source sources internals executableGoals _
          (agreement.notContains notShadowed) compiled

/-- Every nonempty independent argument sequence compiles left-to-right with
the same first and last values, ordered goals, and final counter. -/
theorem compileSeqFuel_initial_sound {state : TranslatorState} (env : CEnv)
    (agreement : EnvAgrees state env) {counter : Nat} {sources : List Atom}
    {first last : Term} {goals : List PeTTaSpec.PrologCore.Goal}
    {nextCounter : Nat}
    (native :
      TranslatesSeq state counter sources first last goals nextCounter) :
    ∃ baseFuel,
      0 < baseFuel ∧
      baseFuel ≤ 8 * (sources.map Atom.size).sum ∧
      ∀ extraFuel, ∃ internals executableGoals,
        compileListFuel (baseFuel + extraFuel) env counter sources =
          .ok (internals, executableGoals, nextCounter) ∧
        internals ≠ [] ∧
        TermAgrees first internals.head! ∧
        TermAgrees last internals.getLast! ∧
        GoalsAgree goals executableGoals := by
  cases native with
  | single head =>
      obtain ⟨headFuel, headPositive, headBound, headCompiles⟩ :=
        compileExprFuel_initial_sound env agreement head
      refine ⟨headFuel + 1, by omega, ?_, ?_⟩
      · simp only [List.map, List.sum_cons, List.sum_nil, Nat.add_zero]
        omega
      · intro extraFuel
        obtain ⟨internal, executableGoals, compiled, termAgreement,
            goalsAgreement⟩ := headCompiles extraFuel
        refine ⟨[internal], executableGoals, ?_, by simp,
          by simpa [List.head!] using termAgreement,
          by simpa [List.getLast!] using termAgreement, goalsAgreement⟩
        ·
          rw [show (headFuel + 1) + extraFuel =
            (headFuel + extraFuel) + 1 by omega]
          rw [compileListFuel_cons_eq, compiled]
          dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind]
          obtain ⟨tailFuel, tailFuelEq⟩ :
              ∃ tailFuel, headFuel + extraFuel = tailFuel + 1 := by
            exact ⟨headFuel + extraFuel - 1, by omega⟩
          rw [tailFuelEq, compileListFuel_nil_eq]
          dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind,
            Pure.pure, Applicative.toPure, Monad.toApplicative, Except.pure]
          simp
  | cons head tail =>
      obtain ⟨headFuel, headPositive, headBound, headCompiles⟩ :=
        compileExprFuel_initial_sound env agreement head
      obtain ⟨tailFuel, tailPositive, tailBound, tailCompiles⟩ :=
        compileSeqFuel_initial_sound env agreement tail
      let jointFuel := Nat.max headFuel tailFuel
      have headLeJoint : headFuel ≤ jointFuel := Nat.le_max_left _ _
      have tailLeJoint : tailFuel ≤ jointFuel := Nat.le_max_right _ _
      refine ⟨jointFuel + 1, by omega, ?_, ?_⟩
      · simp only [List.map, List.sum_cons]
        by_cases order : headFuel ≤ tailFuel
        · have jointEq : jointFuel = tailFuel := by
            simp [jointFuel, Nat.max_eq_right order]
          rw [jointEq]
          omega
        · have reverseOrder : tailFuel ≤ headFuel :=
            Nat.le_of_lt (Nat.lt_of_not_ge order)
          have jointEq : jointFuel = headFuel := by
            simp [jointFuel, Nat.max_eq_left reverseOrder]
          rw [jointEq]
          omega
      · intro extraFuel
        obtain ⟨headExtra, headFuelEq⟩ :
            ∃ headExtra, jointFuel + extraFuel = headFuel + headExtra := by
          exact ⟨jointFuel + extraFuel - headFuel, by omega⟩
        obtain ⟨tailExtra, tailFuelEq⟩ :
            ∃ tailExtra, jointFuel + extraFuel = tailFuel + tailExtra := by
          exact ⟨jointFuel + extraFuel - tailFuel, by omega⟩
        obtain ⟨headInternal, headExecutableGoals, headCompiled,
            headAgreement, headGoalsAgreement⟩ := headCompiles headExtra
        obtain ⟨tailInternals, tailExecutableGoals, tailCompiled,
            tailInternalsNonempty, _tailFirstAgreement, tailLastAgreement,
            tailGoalsAgreement⟩ := tailCompiles tailExtra
        refine ⟨headInternal :: tailInternals,
          headExecutableGoals ++ tailExecutableGoals, ?_, by simp,
          by simpa [List.head!] using headAgreement, ?_,
          headGoalsAgreement.append tailGoalsAgreement⟩
        ·
          rw [show (jointFuel + 1) + extraFuel =
            (jointFuel + extraFuel) + 1 by omega]
          rw [compileListFuel_cons_eq, headFuelEq, headCompiled]
          dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind]
          rw [← headFuelEq, tailFuelEq, tailCompiled]
          dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind,
            Pure.pure, Applicative.toPure, Monad.toApplicative, Except.pure]
        · obtain ⟨tailHead, tailRest, rfl⟩ :=
            List.exists_cons_of_ne_nil tailInternalsNonempty
          simpa [List.getLast!] using tailLastAgreement

end

/-- Every independent pinned `translate_args/3` derivation has a positive,
syntax-bounded shared compiler budget.  All source terms, generated goals,
and counter changes are preserved in left-to-right order. -/
theorem compileListFuel_initial_sound {state : TranslatorState} (env : CEnv)
    (agreement : EnvAgrees state env) {counter : Nat}
    {sources : List Atom} {terms : List Term}
    {goals : List PeTTaSpec.PrologCore.Goal} {nextCounter : Nat}
    (native : TranslatesArgs state counter sources terms goals nextCounter) :
    ∃ baseFuel,
      0 < baseFuel ∧
      baseFuel < 16 * ((sources.map Atom.size).sum + 1) ∧
      ∀ extraFuel, ∃ internals executableGoals,
        compileListFuel (baseFuel + extraFuel) env counter sources =
          .ok (internals, executableGoals, nextCounter) ∧
        TermsAgree terms internals ∧ GoalsAgree goals executableGoals := by
  induction native with
  | @nil nilCounter =>
      refine ⟨1, by omega, by simp, ?_⟩
      intro extraFuel
      exact ⟨[], [], by
          simpa [Nat.add_comm] using
            compileListFuel_nil_eq extraFuel env nilCounter,
        .nil, .nil⟩
  | @cons listCounter middleCounter listNextCounter source sources term terms
      headGoals tailGoals head tail tailInduction =>
      obtain ⟨headFuel, headPositive, headBound, headCompiles⟩ :=
        compileExprFuel_initial_sound env agreement head
      obtain ⟨tailFuel, tailPositive, tailBound, tailCompiles⟩ :=
        tailInduction
      let childFuel := max headFuel tailFuel
      have headLe : headFuel ≤ childFuel := Nat.le_max_left _ _
      have tailLe : tailFuel ≤ childFuel := Nat.le_max_right _ _
      refine ⟨childFuel + 1, by omega, ?_, ?_⟩
      · have sourcePositive := atom_size_positive_for_compiler source
        simp only [List.map, List.sum_cons]
        omega
      · intro extraFuel
        obtain ⟨headInternal, headExecutableGoals, headCompiled,
            headAgreement, headGoalsAgreement⟩ :=
          headCompiles (childFuel + extraFuel - headFuel)
        obtain ⟨tailInternals, tailExecutableGoals, tailCompiled,
            tailAgreement, tailGoalsAgreement⟩ :=
          tailCompiles (childFuel + extraFuel - tailFuel)
        have headFuelEq :
            headFuel + (childFuel + extraFuel - headFuel) =
              childFuel + extraFuel := by
          omega
        have tailFuelEq :
            tailFuel + (childFuel + extraFuel - tailFuel) =
              childFuel + extraFuel := by
          omega
        rw [headFuelEq] at headCompiled
        rw [tailFuelEq] at tailCompiled
        refine ⟨headInternal :: tailInternals,
          headExecutableGoals ++ tailExecutableGoals, ?_,
          .cons headAgreement tailAgreement,
          GoalsAgree.append headGoalsAgreement tailGoalsAgreement⟩
        rw [show (childFuel + 1) + extraFuel =
            (childFuel + extraFuel) + 1 by omega]
        rw [compileListFuel_cons_eq, headCompiled]
        dsimp only [Bind.bind, Monad.toBind, Except.instMonad, Except.bind]
        rw [tailCompiled]
        rfl

/-- Public soundness of executable argument-list traversal at the
source-derived shared budget. -/
theorem compileList_sound {state : TranslatorState} (env : CEnv)
    (agreement : EnvAgrees state env) {counter : Nat}
    {sources : List Atom} {terms : List Term}
    {goals : List PeTTaSpec.PrologCore.Goal} {nextCounter : Nat}
    (native : TranslatesArgs state counter sources terms goals nextCounter) :
    ∃ internals executableGoals,
      compileList env counter sources =
        .ok (internals, executableGoals, nextCounter) ∧
      TermsAgree terms internals ∧ GoalsAgree goals executableGoals := by
  obtain ⟨baseFuel, basePositive, baseBound, compiles⟩ :=
    compileListFuel_initial_sound env agreement native
  have baseLe : baseFuel ≤ compilerListFuel sources + 64 := by
    simp only [compilerListFuel]
    omega
  obtain ⟨extraFuel, fuelEquality⟩ :
      ∃ extraFuel,
        compilerListFuel sources + 64 = baseFuel + extraFuel :=
    ⟨compilerListFuel sources + 64 - baseFuel, by omega⟩
  obtain ⟨internals, executableGoals, compiled, termsAgreement,
      goalsAgreement⟩ := compiles extraFuel
  exact ⟨internals, executableGoals,
    by simpa [compileList, fuelEquality] using compiled,
    termsAgreement, goalsAgreement⟩

/-- Completeness on independently supported ordered argument lists. -/
theorem compileList_complete {state : TranslatorState} (env : CEnv)
    (agreement : EnvAgrees state env) {counter : Nat}
    {sources internals : List Atom} {executableGoals : List PLeaTTa.Goal}
    {nextCounter : Nat} (supported : SupportedArgs state counter sources)
    (compiled : compileList env counter sources =
      .ok (internals, executableGoals, nextCounter)) :
    ∃ terms goals,
      TranslatesArgs state counter sources terms goals nextCounter ∧
      TermsAgree terms internals ∧ GoalsAgree goals executableGoals := by
  obtain ⟨terms, goals, referenceCounter, native⟩ := supported
  obtain ⟨referenceInternals, referenceGoals, referenceCompiled,
      termsAgreement, goalsAgreement⟩ :=
    compileList_sound env agreement native
  have resultEquality :
      (internals, executableGoals, nextCounter) =
        (referenceInternals, referenceGoals, referenceCounter) :=
    Except.ok.inj (compiled.symm.trans referenceCompiled)
  cases resultEquality
  exact ⟨terms, goals, native, termsAgreement, goalsAgreement⟩

/-- Executable witness for the independent empty argument traversal. -/
theorem compileList_empty_sound (state : TranslatorState) (env : CEnv)
    (agreement : EnvAgrees state env) (counter : Nat) :
    ∃ internals executableGoals,
      compileList env counter [] = .ok (internals, executableGoals, counter) ∧
      TermsAgree [] internals ∧ GoalsAgree [] executableGoals := by
  exact compileList_sound env agreement (translates_empty_args state counter)

/-- Executable witness for ordered translation of two literal arguments. -/
theorem compileList_two_literal_sound (state : TranslatorState) (env : CEnv)
    (agreement : EnvAgrees state env) (counter : Nat) (first second : Int) :
    ∃ internals executableGoals,
      compileList env counter [.gnd (.int first), .gnd (.int second)] =
        .ok (internals, executableGoals, counter) ∧
      TermsAgree [.integer first, .integer second] internals ∧
      GoalsAgree [] executableGoals := by
  exact compileList_sound env agreement
    (translates_two_literal_args state counter first second)

/-- Soundness of the executable compiler for independently specified,
well-formed pinned `let*` forms.  The nested expansion may be syntactically
larger than the source form, so the proof uses the independent expansion-size
bound to show that the public source-derived fuel still covers it. -/
theorem compileExpr_letStar_sound {state : TranslatorState} (env : CEnv)
    (agreement : EnvAgrees state env) {counter : Nat} {source : Atom}
    {term : Term} {goals : List PeTTaSpec.PrologCore.Goal}
    {nextCounter : Nat}
    (native :
      TranslatesLetStar state counter source term goals nextCounter) :
    ∃ internal executableGoals,
      compileExpr env counter source =
        .ok (internal, executableGoals, nextCounter) ∧
      TermAgrees term internal ∧ GoalsAgree goals executableGoals := by
  cases native with
  | expand notShadowed expansion nested =>
      rename_i bindings bodySource nestedSource
      obtain ⟨baseFuel, _basePositive, baseBound, compiles⟩ :=
        compileExprFuel_initial_sound env agreement nested
      have nestedSizeBound :=
        letStarExpands_nested_size_le_twice_source expansion
      let source := Atom.expr [.sym "let*", .expr bindings, bodySource]
      have baseLe : baseFuel ≤ compilerFuel source + 61 := by
        simp only [source, compilerFuel]
        omega
      obtain ⟨extraFuel, childFuelEq⟩ :
          ∃ extraFuel, compilerFuel source + 61 = baseFuel + extraFuel := by
        exact ⟨compilerFuel source + 61 - baseFuel, by omega⟩
      obtain ⟨internal, executableGoals, nestedCompiled, termAgreement,
          goalsAgreement⟩ := compiles extraFuel
      rw [← childFuelEq] at nestedCompiled
      refine ⟨internal, executableGoals, ?_, termAgreement, goalsAgreement⟩
      rw [compileExpr]
      change compileExprFuel (compilerFuel source + 64) env counter source =
        .ok (internal, executableGoals, nextCounter)
      rw [show compilerFuel source + 64 =
        (compilerFuel source + 61) + 3 by omega]
      exact compileExprFuel_letStar_eq (compilerFuel source + 61) env counter
        bindings bodySource nestedSource internal executableGoals nextCounter
        (agreement.notContains notShadowed)
        (letStarExpands_desugar expansion) nestedCompiled

/-- Completeness on the independently supported `let*` fragment: every
successful executable result is represented by the pinned expansion and
translation relation, with the same ordered goals and fresh counter. -/
theorem compileExpr_letStar_complete {state : TranslatorState} (env : CEnv)
    (agreement : EnvAgrees state env) {counter : Nat} {source internal : Atom}
    {executableGoals : List PLeaTTa.Goal} {nextCounter : Nat}
    (supported : SupportedLetStar state counter source)
    (compiled : compileExpr env counter source =
      .ok (internal, executableGoals, nextCounter)) :
    ∃ term goals,
      TranslatesLetStar state counter source term goals nextCounter ∧
      TermAgrees term internal ∧ GoalsAgree goals executableGoals := by
  obtain ⟨term, goals, referenceCounter, native⟩ := supported
  obtain ⟨referenceInternal, referenceGoals, referenceCompiled,
      termAgreement, goalsAgreement⟩ :=
    compileExpr_letStar_sound env agreement native
  have resultEquality :
      (internal, executableGoals, nextCounter) =
        (referenceInternal, referenceGoals, referenceCounter) :=
    Except.ok.inj (compiled.symm.trans referenceCompiled)
  cases resultEquality
  exact ⟨term, goals, native, termAgreement, goalsAgreement⟩

/-- Soundness for native `with_mutex` translation. The executable erases the
wrapper only in the explicitly sequential observation model; body goals retain
ordinary structural agreement. -/
theorem compileExprFuel_withMutex_sound {state : TranslatorState} (env : CEnv)
    (agreement : EnvAgrees state env) {counter : Nat} {source : Atom}
    {term : Term} {goals : List PeTTaSpec.PrologCore.Goal}
    {nextCounter : Nat}
    (native :
      TranslatesWithMutex state counter source term goals nextCounter) :
    ∃ baseFuel,
      0 < baseFuel ∧
      baseFuel < 8 * source.size ∧
      ∀ extraFuel, ∃ internal executableGoals,
        compileExprFuel (baseFuel + extraFuel) env counter source =
          .ok (internal, executableGoals, nextCounter) ∧
        TermAgrees term internal ∧
        SequentialGoalsAgree goals executableGoals := by
  cases native with
  | wrap notShadowed mutexValue body =>
      obtain ⟨bodyFuel, bodyPositive, bodyBound, bodyCompiles⟩ :=
        compileExprFuel_initial_sound env agreement body
      refine ⟨bodyFuel + 3, by omega, ?_, ?_⟩
      · simp [Atom.size]
        omega
      · intro extraFuel
        obtain ⟨internal, executableGoals, compiled, termAgreement,
            goalsAgreement⟩ := bodyCompiles extraFuel
        refine ⟨internal, executableGoals, ?_, termAgreement, ?_⟩
        · rw [show (bodyFuel + 3) + extraFuel =
            (bodyFuel + extraFuel) + 3 by omega]
          exact compileExprFuel_withMutex_eq (bodyFuel + extraFuel) env counter
            _ _ internal executableGoals nextCounter
            (agreement.notContains notShadowed) compiled
        · refine ⟨_, ?_, goalsAgreement⟩
          intro calls
          exact
            PeTTaSpec.PrologCore.Declarative.Ordered.withMutex_conjunction_all_equivalent
              calls _ _

/-- Public compiler soundness for the behaviorally normalized mutex fragment. -/
theorem compileExpr_withMutex_sound {state : TranslatorState} (env : CEnv)
    (agreement : EnvAgrees state env) {counter : Nat} {source : Atom}
    {term : Term} {goals : List PeTTaSpec.PrologCore.Goal}
    {nextCounter : Nat}
    (native :
      TranslatesWithMutex state counter source term goals nextCounter) :
    ∃ internal executableGoals,
      compileExpr env counter source =
        .ok (internal, executableGoals, nextCounter) ∧
      TermAgrees term internal ∧
      SequentialGoalsAgree goals executableGoals := by
  obtain ⟨baseFuel, _basePositive, baseBound, compiles⟩ :=
    compileExprFuel_withMutex_sound env agreement native
  have publicBound : baseFuel ≤ compilerFuel source + 64 := by
    simp [compilerFuel]
    omega
  obtain ⟨extraFuel, publicFuelEq⟩ :
      ∃ extraFuel, compilerFuel source + 64 = baseFuel + extraFuel := by
    exact ⟨compilerFuel source + 64 - baseFuel, by omega⟩
  obtain ⟨internal, executableGoals, compiled, termAgreement,
      goalsAgreement⟩ := compiles extraFuel
  refine ⟨internal, executableGoals, ?_, termAgreement, goalsAgreement⟩
  rw [compileExpr, publicFuelEq]
  exact compiled

/-- Completeness for the independently supported mutex fragment. -/
theorem compileExpr_withMutex_complete {state : TranslatorState} (env : CEnv)
    (agreement : EnvAgrees state env) {counter : Nat} {source internal : Atom}
    {executableGoals : List PLeaTTa.Goal} {nextCounter : Nat}
    (supported : SupportedWithMutex state counter source)
    (compiled : compileExpr env counter source =
      .ok (internal, executableGoals, nextCounter)) :
    ∃ term goals,
      TranslatesWithMutex state counter source term goals nextCounter ∧
      TermAgrees term internal ∧
      SequentialGoalsAgree goals executableGoals := by
  obtain ⟨term, goals, referenceCounter, native⟩ := supported
  obtain ⟨referenceInternal, referenceGoals, referenceCompiled,
      termAgreement, goalsAgreement⟩ :=
    compileExpr_withMutex_sound env agreement native
  have resultEquality :
      (internal, executableGoals, nextCounter) =
        (referenceInternal, referenceGoals, referenceCounter) :=
    Except.ok.inj (compiled.symm.trans referenceCompiled)
  cases resultEquality
  exact ⟨term, goals, native, termAgreement, goalsAgreement⟩

/-- Honest compiler-shape theorem for native `once`. It proves body
translation agreement, fresh-result allocation, and the exact `onceg` target.
It deliberately stops short of calling the result adequate: that requires the
later theorem that fresh-result unification observes the native body term. -/
theorem compileExprFuel_once_shape_sound {state : TranslatorState} (env : CEnv)
    (agreement : EnvAgrees state env) {counter : Nat} {source : Atom}
    {term : Term} {nativeGoals : List PeTTaSpec.PrologCore.Goal}
    {bodyCounter : Nat}
    (native :
      TranslatesOnce state counter source term nativeGoals bodyCounter) :
    ∃ baseFuel,
      0 < baseFuel ∧
      baseFuel < 8 * source.size ∧
      ∀ extraFuel, ∃ bodyGoals template executableBodyGoals,
        nativeGoals = [.once (.conjunction bodyGoals)] ∧
        compileExprFuel (baseFuel + extraFuel) env counter source =
          .ok (.var s!"_q{bodyCounter}",
            [PLeaTTa.Goal.onceg template executableBodyGoals
              (.var s!"_q{bodyCounter}")],
            bodyCounter + 1) ∧
        TermAgrees term template ∧
        TermAgrees (.variable (.generated bodyCounter))
          (.var s!"_q{bodyCounter}") ∧
        GoalsAgree bodyGoals executableBodyGoals := by
  cases native with
  | wrap notShadowed body =>
      obtain ⟨bodyFuel, bodyPositive, bodyBound, bodyCompiles⟩ :=
        compileExprFuel_initial_sound env agreement body
      refine ⟨bodyFuel + 3, by omega, ?_, ?_⟩
      · simp [Atom.size]
        omega
      · intro extraFuel
        obtain ⟨template, executableBodyGoals, compiled, termAgreement,
            goalsAgreement⟩ := bodyCompiles extraFuel
        refine ⟨_, template, executableBodyGoals, rfl, ?_, termAgreement,
          .generatedVariable _, ?_⟩
        · rw [show (bodyFuel + 3) + extraFuel =
            (bodyFuel + extraFuel) + 3 by omega]
          exact compileExprFuel_once_eq (bodyFuel + extraFuel) env counter _
            template executableBodyGoals bodyCounter
            (agreement.notContains notShadowed) compiled
        · exact goalsAgreement

/-- Public compiler shape for independently translated `once`. -/
theorem compileExpr_once_shape_sound {state : TranslatorState} (env : CEnv)
    (agreement : EnvAgrees state env) {counter : Nat} {source : Atom}
    {term : Term} {nativeGoals : List PeTTaSpec.PrologCore.Goal}
    {bodyCounter : Nat}
    (native :
      TranslatesOnce state counter source term nativeGoals bodyCounter) :
    ∃ bodyGoals template executableBodyGoals,
      nativeGoals = [.once (.conjunction bodyGoals)] ∧
      compileExpr env counter source =
        .ok (.var s!"_q{bodyCounter}",
          [PLeaTTa.Goal.onceg template executableBodyGoals
            (.var s!"_q{bodyCounter}")],
          bodyCounter + 1) ∧
      TermAgrees term template ∧
      TermAgrees (.variable (.generated bodyCounter))
        (.var s!"_q{bodyCounter}") ∧
      GoalsAgree bodyGoals executableBodyGoals := by
  obtain ⟨baseFuel, _basePositive, baseBound, compiles⟩ :=
    compileExprFuel_once_shape_sound env agreement native
  have publicBound : baseFuel ≤ compilerFuel source + 64 := by
    simp [compilerFuel]
    omega
  obtain ⟨extraFuel, publicFuelEq⟩ :
      ∃ extraFuel, compilerFuel source + 64 = baseFuel + extraFuel := by
    exact ⟨compilerFuel source + 64 - baseFuel, by omega⟩
  obtain ⟨bodyGoals, template, executableBodyGoals, nativeGoalsShape,
      compiled, termAgreement, outputAgreement, goalsAgreement⟩ :=
    compiles extraFuel
  refine ⟨bodyGoals, template, executableBodyGoals, nativeGoalsShape, ?_,
    termAgreement, outputAgreement, goalsAgreement⟩
  rw [compileExpr, publicFuelEq]
  exact compiled

/-- Soundness of the executable compiler for every derivation in the current
independent pinned-translation fragment. -/
theorem compileExpr_initial_sound {state : TranslatorState} (env : CEnv)
    (agreement : EnvAgrees state env) {counter : Nat} {source : Atom}
    {term : Term} {goals : List PeTTaSpec.PrologCore.Goal}
    {nextCounter : Nat}
    (native : TranslatesExpr state counter source term goals nextCounter) :
    ∃ internal executableGoals,
      compileExpr env counter source =
        .ok (internal, executableGoals, nextCounter) ∧
      TermAgrees term internal ∧ GoalsAgree goals executableGoals := by
  obtain ⟨baseFuel, _basePositive, baseBound, compiles⟩ :=
    compileExprFuel_initial_sound env agreement native
  have publicBound : baseFuel ≤ compilerFuel source + 64 := by
    simp [compilerFuel]
    omega
  obtain ⟨extraFuel, publicFuelEq⟩ :
      ∃ extraFuel, compilerFuel source + 64 = baseFuel + extraFuel := by
    exact ⟨compilerFuel source + 64 - baseFuel, by omega⟩
  obtain ⟨internal, executableGoals, compiled, termAgreement,
      goalsAgreement⟩ := compiles extraFuel
  refine ⟨internal, executableGoals, ?_, termAgreement, goalsAgreement⟩
  rw [compileExpr, publicFuelEq]
  exact compiled

/-- Completeness on the independently defined supported fragment: every
successful executable result is represented by a pinned-translation
derivation with agreeing ordered goals and value. -/
theorem compileExpr_initial_complete {state : TranslatorState} (env : CEnv)
    (agreement : EnvAgrees state env) {counter : Nat} {source internal : Atom}
    {executableGoals : List PLeaTTa.Goal} {nextCounter : Nat}
    (supported : SupportedExpr state counter source)
    (compiled : compileExpr env counter source =
      .ok (internal, executableGoals, nextCounter)) :
    ∃ term goals,
      TranslatesExpr state counter source term goals nextCounter ∧
      TermAgrees term internal ∧ GoalsAgree goals executableGoals := by
  obtain ⟨term, goals, referenceCounter, native⟩ := supported
  obtain ⟨referenceInternal, referenceGoals, referenceCompiled,
      termAgreement, goalsAgreement⟩ :=
    compileExpr_initial_sound env agreement native
  have resultEquality :
      (internal, executableGoals, nextCounter) =
        (referenceInternal, referenceGoals, referenceCounter) :=
    Except.ok.inj (compiled.symm.trans referenceCompiled)
  cases resultEquality
  exact ⟨term, goals, native, termAgreement, goalsAgreement⟩

/-- A host external value cannot masquerade as any certified Prolog term. -/
theorem external_not_term_agreement (tag payload : String) (term : Term) :
    ¬ TermAgrees term (.gnd (.external tag payload)) := by
  intro agreement
  cases agreement with
  | properList elements => cases elements

end PLeaTTa.CompilerAdequacy
