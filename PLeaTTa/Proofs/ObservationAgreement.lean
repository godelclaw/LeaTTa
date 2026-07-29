/-
Module: PLeaTTa.Proofs.ObservationAgreement
Purpose: Relate independent Prolog-term denotation to executable Atom values
  without identifying their representations by definition.
Trusted boundary: none
-/
import PLeaTTa.Proofs.CompilerAdequacy
import PLeaTTa.Semantics

namespace PLeaTTa.ObservationAgreement

open Metta (Atom)
open PLeaTTa.CompilerAdequacy
open PLeaTTa.PeTTaSpec.PrologCore
open PLeaTTa.PeTTaSpec.PrologCore.Declarative

/-- A total assignment for executable variable names. This is a semantic
environment, not the machine's finite substitution representation. -/
abbrev ExecutableValuation := String → GroundTerm

mutual

/-- Agreement of the independent and executable assignments on exactly the
variables occurring in one independent term. Anonymous variables remain
unsupported until the reader adequacy layer supplies their concrete encoding. -/
def VariablesAgreeOnTerm (reference : Valuation)
    (executable : ExecutableValuation) : Term → Prop
  | .variable (.source name) => executable name = reference (.source name)
  | .variable (.generated index) =>
      executable s!"_q{index}" = reference (.generated index)
  | .variable (.anonymous _) => False
  | .compound _ arguments =>
      VariablesAgreeOnTerms reference executable arguments
  | .list items none => VariablesAgreeOnTerms reference executable items
  | .list items (some tail) =>
      VariablesAgreeOnTerms reference executable items ∧
        VariablesAgreeOnTerm reference executable tail
  | _ => True

/-- Pointwise assignment agreement for a term list. -/
def VariablesAgreeOnTerms (reference : Valuation)
    (executable : ExecutableValuation) : List Term → Prop
  | [] => True
  | term :: terms =>
      VariablesAgreeOnTerm reference executable term ∧
        VariablesAgreeOnTerms reference executable terms

end

mutual

/-- Ground observations for which PLeaTTa's current executable encoding has
one source reading. Literal uses of the reserved executable spellings are
excluded; improper lists and compounds remain outside the proved bridge until
their executable encodings are added. -/
def CanonicalGroundTerm : GroundTerm → Prop
  | .atom name => name ≠ "True" ∧ name ≠ "False" ∧ name ≠ "#nil"
  | .integer _ | .float _ | .string _ => True
  | .compound _ _ => False
  | .list items none => CanonicalGroundTerms items
  | .list _ (some _) => False

/-- Pointwise canonicality for an ordered ground-term list. -/
def CanonicalGroundTerms : List GroundTerm → Prop
  | [] => True
  | term :: terms =>
      CanonicalGroundTerm term ∧ CanonicalGroundTerms terms

end

mutual

/-- Relational denotation of executable atoms in the supported independent
ground-term universe. It is intentionally relational: reserved executable
encodings can otherwise have multiple source readings, exposed below. -/
inductive AtomDenotes (valuation : ExecutableValuation) :
    Atom → GroundTerm → Prop where
  | variable (name : String) :
      AtomDenotes valuation (.var name) (valuation name)
  | symbol (name : String) :
      AtomDenotes valuation (.sym name) (.atom name)
  | trueAtom : AtomDenotes valuation (.sym "True") (.atom "true")
  | falseAtom : AtomDenotes valuation (.sym "False") (.atom "false")
  | integer (value : Int) :
      AtomDenotes valuation (.gnd (.int value)) (.integer value)
  | float (value : Float) :
      AtomDenotes valuation (.gnd (.float value))
        (.float (PLeaTTa.PrologFloatIdentity.ofFloat value))
  | string (value : String) :
      AtomDenotes valuation (.gnd (.str value)) (.string value)
  | properList {items : List GroundTerm} {encoded : Atom}
      (elements : ChainDenotes valuation items encoded) :
      AtomDenotes valuation encoded (.list items none)
  | partialValue {head : String} {items : List GroundTerm} {encoded : Atom}
      (arguments : ChainDenotes valuation items encoded) :
      AtomDenotes valuation
        (chainOf [.sym "partial", .sym head, encoded])
        (.compound "partial" [.atom head, .list items none])

/-- Denotation of PLeaTTa's internal `#c`/`#nil` proper-list encoding. -/
inductive ChainDenotes (valuation : ExecutableValuation) :
    List GroundTerm → Atom → Prop where
  | nil : ChainDenotes valuation [] nilA
  | cons {value : GroundTerm} {atom : Atom}
      {values : List GroundTerm} {tail : Atom}
      (head : AtomDenotes valuation atom value)
      (rest : ChainDenotes valuation values tail) :
      ChainDenotes valuation (value :: values) (consC atom tail)

end

private theorem chainDenotes_symbol {valuation : ExecutableValuation}
    {items : List GroundTerm} {name : String}
    (denotes : ChainDenotes valuation items (.sym name)) :
    name = "#nil" ∧ items = [] := by
  generalize encodedEq : Atom.sym name = encoded at denotes
  cases denotes with
  | nil => simpa [nilA] using encodedEq
  | cons head rest => simp [consC] at encodedEq

private theorem chainDenotes_variable_false
    {valuation : ExecutableValuation} {items : List GroundTerm}
    {name : String} (denotes : ChainDenotes valuation items (.var name)) :
    False := by
  generalize encodedEq : Atom.var name = encoded at denotes
  cases denotes <;> simp [nilA, consC] at encodedEq

private theorem chainDenotes_ground_false
    {valuation : ExecutableValuation} {items : List GroundTerm}
    {ground : Metta.Ground}
    (denotes : ChainDenotes valuation items (.gnd ground)) : False := by
  generalize encodedEq : Atom.gnd ground = encoded at denotes
  cases denotes <;> simp [nilA, consC] at encodedEq

private theorem chainDenotes_cons {valuation : ExecutableValuation}
    {items : List GroundTerm} {atom tail : Atom}
    (denotes : ChainDenotes valuation items (consC atom tail)) :
    ∃ value values, items = value :: values ∧
      AtomDenotes valuation atom value ∧
      ChainDenotes valuation values tail := by
  generalize encodedEq : consC atom tail = encoded at denotes
  cases denotes with
  | nil => simp [nilA, consC] at encodedEq
  | cons head rest =>
      simp [consC] at encodedEq
      rcases encodedEq with ⟨rfl, rfl⟩
      exact ⟨_, _, rfl, head, rest⟩

private theorem atomDenotes_variable {valuation : ExecutableValuation}
    {name : String} {value : GroundTerm}
    (denotes : AtomDenotes valuation (.var name) value) :
    value = valuation name := by
  generalize encodedEq : Atom.var name = encoded at denotes
  cases denotes with
  | «variable» other =>
      simp at encodedEq
      subst other
      rfl
  | symbol => simp at encodedEq
  | trueAtom => simp at encodedEq
  | falseAtom => simp at encodedEq
  | integer => simp at encodedEq
  | float => simp at encodedEq
  | string => simp at encodedEq
  | properList elements =>
      rw [← encodedEq] at elements
      exact False.elim (chainDenotes_variable_false elements)
  | partialValue arguments => simp [chainOf, consC] at encodedEq

private theorem atomDenotes_symbol {valuation : ExecutableValuation}
    {name : String} {value : GroundTerm}
    (denotes : AtomDenotes valuation (.sym name) value) :
    value = .atom name ∨
      (name = "True" ∧ value = .atom "true") ∨
      (name = "False" ∧ value = .atom "false") ∨
      (name = "#nil" ∧ value = .list [] none) := by
  generalize encodedEq : Atom.sym name = encoded at denotes
  cases denotes with
  | «variable» => simp at encodedEq
  | symbol other =>
      simp at encodedEq
      subst other
      exact Or.inl rfl
  | trueAtom =>
      simp at encodedEq
      exact Or.inr (Or.inl ⟨encodedEq, rfl⟩)
  | falseAtom =>
      simp at encodedEq
      exact Or.inr (Or.inr (Or.inl ⟨encodedEq, rfl⟩))
  | integer => simp at encodedEq
  | float => simp at encodedEq
  | string => simp at encodedEq
  | properList elements =>
      rw [← encodedEq] at elements
      obtain ⟨nameEq, itemsEq⟩ := chainDenotes_symbol elements
      exact Or.inr (Or.inr (Or.inr ⟨nameEq,
        congrArg (fun items => GroundTerm.list items none) itemsEq⟩))
  | partialValue arguments => simp [chainOf, consC] at encodedEq

private theorem atomDenotes_ground {valuation : ExecutableValuation}
    {ground : Metta.Ground} {value : GroundTerm}
    (denotes : AtomDenotes valuation (.gnd ground) value) :
    (∃ integer, ground = .int integer ∧ value = .integer integer) ∨
      (∃ float, ground = .float float ∧
        value = .float (PLeaTTa.PrologFloatIdentity.ofFloat float)) ∨
      (∃ string, ground = .str string ∧ value = .string string) := by
  generalize encodedEq : Atom.gnd ground = encoded at denotes
  cases denotes with
  | «variable» => simp at encodedEq
  | symbol => simp at encodedEq
  | trueAtom => simp at encodedEq
  | falseAtom => simp at encodedEq
  | integer integer =>
      simp at encodedEq
      exact Or.inl ⟨integer, encodedEq, rfl⟩
  | float float =>
      simp at encodedEq
      exact Or.inr (Or.inl ⟨float, encodedEq, rfl⟩)
  | string string =>
      simp at encodedEq
      exact Or.inr (Or.inr ⟨string, encodedEq, rfl⟩)
  | properList elements =>
      rw [← encodedEq] at elements
      exact False.elim (chainDenotes_ground_false elements)
  | partialValue arguments => simp [chainOf, consC] at encodedEq

private theorem atomDenotes_expression {valuation : ExecutableValuation}
    {atoms : List Atom} {value : GroundTerm}
    (denotes : AtomDenotes valuation (.expr atoms) value)
    (canonical : CanonicalGroundTerm value) :
    ∃ items, value = .list items none ∧
      ChainDenotes valuation items (.expr atoms) := by
  generalize encodedEq : Atom.expr atoms = encoded at denotes
  cases denotes with
  | «variable» => simp at encodedEq
  | symbol => simp at encodedEq
  | trueAtom => simp at encodedEq
  | falseAtom => simp at encodedEq
  | integer => simp at encodedEq
  | float => simp at encodedEq
  | string => simp at encodedEq
  | properList elements => exact ⟨_, rfl, elements⟩
  | partialValue arguments => simp [CanonicalGroundTerm] at canonical

private theorem atomDenotes_canonical_functional_aux
    {valuation : ExecutableValuation} {atom : Atom} {left : GroundTerm}
    (leftDenotes : AtomDenotes valuation atom left) : ∀ {right},
      CanonicalGroundTerm left → CanonicalGroundTerm right →
      AtomDenotes valuation atom right → left = right := by
  refine AtomDenotes.rec
    (motive_1 := fun atom left _ => ∀ {right},
      CanonicalGroundTerm left → CanonicalGroundTerm right →
      AtomDenotes valuation atom right → left = right)
    (motive_2 := fun left encoded _ => ∀ {right},
      CanonicalGroundTerms left → CanonicalGroundTerms right →
      ChainDenotes valuation right encoded → left = right)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ leftDenotes
  · intro name right _ _ rightDenotes
    exact (atomDenotes_variable rightDenotes).symm
  · intro name right leftCanonical _ rightDenotes
    rcases atomDenotes_symbol rightDenotes with
      same | trueReading | falseReading | nilReading
    · exact same.symm
    · exact False.elim (leftCanonical.1 trueReading.1)
    · exact False.elim (leftCanonical.2.1 falseReading.1)
    · exact False.elim (leftCanonical.2.2 nilReading.1)
  · intro right _ rightCanonical rightDenotes
    rcases atomDenotes_symbol rightDenotes with
      same | trueReading | falseReading | nilReading
    · rw [same] at rightCanonical
      simp [CanonicalGroundTerm] at rightCanonical
    · exact trueReading.2.symm
    · simp at falseReading
    · simp at nilReading
  · intro right _ rightCanonical rightDenotes
    rcases atomDenotes_symbol rightDenotes with
      same | trueReading | falseReading | nilReading
    · rw [same] at rightCanonical
      simp [CanonicalGroundTerm] at rightCanonical
    · simp at trueReading
    · exact falseReading.2.symm
    · simp at nilReading
  · intro value right _ _ rightDenotes
    rcases atomDenotes_ground rightDenotes with
      intReading | floatReading | stringReading
    · obtain ⟨other, groundEq, valueEq⟩ := intReading
      cases groundEq
      exact valueEq.symm
    · obtain ⟨other, groundEq, valueEq⟩ := floatReading
      cases groundEq
    · obtain ⟨other, groundEq, valueEq⟩ := stringReading
      cases groundEq
  · intro value right _ _ rightDenotes
    rcases atomDenotes_ground rightDenotes with
      intReading | floatReading | stringReading
    · obtain ⟨other, groundEq, valueEq⟩ := intReading
      cases groundEq
    · obtain ⟨other, groundEq, valueEq⟩ := floatReading
      cases groundEq
      exact valueEq.symm
    · obtain ⟨other, groundEq, valueEq⟩ := stringReading
      cases groundEq
  · intro value right _ _ rightDenotes
    rcases atomDenotes_ground rightDenotes with
      intReading | floatReading | stringReading
    · obtain ⟨other, groundEq, valueEq⟩ := intReading
      cases groundEq
    · obtain ⟨other, groundEq, valueEq⟩ := floatReading
      cases groundEq
    · obtain ⟨other, groundEq, valueEq⟩ := stringReading
      cases groundEq
      exact valueEq.symm
  · intro items encoded elements elementsIH right leftCanonical
      rightCanonical rightDenotes
    cases elements with
    | nil =>
        rcases atomDenotes_symbol rightDenotes with
          same | trueReading | falseReading | nilReading
        · rw [same] at rightCanonical
          simp [CanonicalGroundTerm] at rightCanonical
        · simp at trueReading
        · simp at falseReading
        · exact nilReading.2.symm
    | cons head rest =>
        obtain ⟨rightItems, rightEq, rightElements⟩ :=
          atomDenotes_expression rightDenotes rightCanonical
        rw [rightEq] at rightCanonical ⊢
        simp only [CanonicalGroundTerm] at rightCanonical
        exact congrArg (fun items => GroundTerm.list items none)
          (elementsIH leftCanonical rightCanonical rightElements)
  · intro _head _items _encoded _arguments _argumentsIH _right leftCanonical
      _rightCanonical _rightDenotes
    simp [CanonicalGroundTerm] at leftCanonical
  · intro right _ _ rightDenotes
    exact (chainDenotes_symbol rightDenotes).2.symm
  · intro value atom values tail head rest headIH restIH right
      leftCanonical rightCanonical rightDenotes
    obtain ⟨rightValue, rightValues, rightEq, rightHead, rightRest⟩ :=
      chainDenotes_cons rightDenotes
    subst right
    simp only [CanonicalGroundTerms] at leftCanonical rightCanonical
    rw [headIH leftCanonical.1 rightCanonical.1 rightHead,
      restIH leftCanonical.2 rightCanonical.2 rightRest]

/-- The relational executable denotation is a function on canonical source
observations. The premises are necessary: the executable symbols `True`,
`False`, and `#nil` each permit a second noncanonical source reading. -/
theorem AtomDenotes.canonical_functional {valuation : ExecutableValuation}
    {atom : Atom} {left right : GroundTerm}
    (leftCanonical : CanonicalGroundTerm left)
    (rightCanonical : CanonicalGroundTerm right)
    (leftDenotes : AtomDenotes valuation atom left)
    (rightDenotes : AtomDenotes valuation atom right) : left = right :=
  atomDenotes_canonical_functional_aux leftDenotes leftCanonical
    rightCanonical rightDenotes

/-- Canonical list-chain denotation preserves the complete ordered element
list uniquely. -/
theorem ChainDenotes.canonical_functional
    {valuation : ExecutableValuation} {encoded : Atom}
    {left right : List GroundTerm}
    (leftCanonical : CanonicalGroundTerms left)
    (rightCanonical : CanonicalGroundTerms right)
    (leftDenotes : ChainDenotes valuation left encoded)
    (rightDenotes : ChainDenotes valuation right encoded) : left = right := by
  have equality : GroundTerm.list left none = GroundTerm.list right none :=
    AtomDenotes.canonical_functional leftCanonical rightCanonical
      (.properList leftDenotes) (.properList rightDenotes)
  injection equality

/-- Semantic satisfaction of an executable finite substitution by a total
valuation. Unbound executable variables denote themselves through the
valuation; bound variables must deep-substitute to an atom denoting the same
ground value. -/
def SubstModels (valuation : ExecutableValuation)
    (binding : Metta.Subst) : Prop :=
  ∀ name,
    AtomDenotes valuation (PLeaTTa.subst binding (.var name)) (valuation name)

/-- The empty executable substitution is modeled by every valuation. -/
theorem substModels_empty (valuation : ExecutableValuation) :
    SubstModels valuation [] := by
  intro name
  simpa using AtomDenotes.variable (valuation := valuation) name

/-- Extending the empty substitution with one closed target is modeled exactly
when that target denotes the assigned value of its fresh source name. This is
the ground fresh-capture base case; open substitutions require an additional
range-freshness preservation theorem. -/
theorem substModels_singleton_closed (valuation : ExecutableValuation)
    (fresh : String) (target : Atom) (closed : target.vars = [])
    (targetDenotes : AtomDenotes valuation target (valuation fresh)) :
    SubstModels valuation [(fresh, target)] := by
  intro name
  by_cases same : name = fresh
  · subst name
    have lookup : Metta.Subst.lookup [(fresh, target)] fresh = some target := by
      simp [Metta.Subst.lookup]
    rw [PLeaTTa.subst_var_of_lookup_closed [(fresh, target)] fresh target
      lookup closed]
    exact targetDenotes
  · have lookup : Metta.Subst.lookup [(fresh, target)] name = none := by
      simp [Metta.Subst.lookup, same]
    rw [PLeaTTa.subst_var_of_lookup_none [(fresh, target)] name lookup]
    exact .variable name

/-- A substitution modeled by a semantic valuation preserves the denotation
of every supported executable atom.  The proof is mutual with the internal
proper-list chain, so variables nested at any list depth are covered. -/
theorem AtomDenotes.subst {valuation : ExecutableValuation}
    {binding : Metta.Subst} {atom : Atom} {value : GroundTerm}
    (models : SubstModels valuation binding)
    (denotes : AtomDenotes valuation atom value) :
    AtomDenotes valuation (PLeaTTa.subst binding atom) value := by
  refine AtomDenotes.rec
    (motive_1 := fun atom value _ =>
      AtomDenotes valuation (PLeaTTa.subst binding atom) value)
    (motive_2 := fun values encoded _ =>
      ChainDenotes valuation values (PLeaTTa.subst binding encoded))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ denotes
  · intro name
    exact models name
  · intro name
    simpa using AtomDenotes.symbol (valuation := valuation) name
  · simpa using AtomDenotes.trueAtom (valuation := valuation)
  · simpa using AtomDenotes.falseAtom (valuation := valuation)
  · intro value
    simpa using AtomDenotes.integer (valuation := valuation) value
  · intro value
    simpa using AtomDenotes.float (valuation := valuation) value
  · intro value
    simpa using AtomDenotes.string (valuation := valuation) value
  · intro _items _encoded _elements elementsIH
    exact .properList elementsIH
  · intro head _items _encoded _arguments argumentsIH
    simpa [chainOf, consC, nilA] using
      (AtomDenotes.partialValue (head := head) argumentsIH)
  · simpa [nilA] using ChainDenotes.nil (valuation := valuation)
  · intro _value _atom _values _tail _head _rest headIH restIH
    simpa [consC] using ChainDenotes.cons headIH restIH

mutual

/-- Every syntactic term agreement transports independent denotation to the
executable representation, provided the two assignments agree on that term's
variables. -/
theorem TermAgrees.denotes {reference : Valuation}
    {executable : ExecutableValuation} {term : Term} {atom : Atom}
    (variables : VariablesAgreeOnTerm reference executable term)
    (agreement : TermAgrees term atom) :
    AtomDenotes executable atom (denoteTerm reference term) := by
  cases agreement with
  | sourceVariable name =>
      rw [denoteTerm, ← variables]
      exact .variable name
  | generatedVariable index =>
      rw [denoteTerm, ← variables]
      exact .variable s!"_q{index}"
  | atom notTrue notFalse => exact .symbol _
  | trueAtom => exact .trueAtom
  | falseAtom => exact .falseAtom
  | integer value => exact .integer value
  | float value => exact .float value
  | string value => exact .string value
  | @partialValue head terms encodedArguments arguments =>
      have argumentVariables :
          VariablesAgreeOnTerms reference executable terms := by
        simpa [VariablesAgreeOnTerm, VariablesAgreeOnTerms] using variables
      exact .partialValue
        (ProperListAgrees.denotes argumentVariables arguments)
  | properList elements =>
      exact .properList (ProperListAgrees.denotes variables elements)

/-- Proper-list agreement transports pointwise denotation to the internal
chain encoding without appealing to the executable compiler. -/
theorem ProperListAgrees.denotes {reference : Valuation}
    {executable : ExecutableValuation} {terms : List Term} {encoded : Atom}
    (variables : VariablesAgreeOnTerms reference executable terms)
    (agreement : ProperListAgrees terms encoded) :
    ChainDenotes executable (denoteTerms reference terms) encoded := by
  cases agreement with
  | nil => exact .nil
  | cons head rest =>
      exact .cons (TermAgrees.denotes variables.1 head)
        (ProperListAgrees.denotes variables.2 rest)

end

/-- Compiler representation agreement continues through an executable
substitution whenever that substitution is modeled by the executable semantic
valuation.  This is the value bridge required at a machine answer step. -/
theorem TermAgrees.subst_denotes {reference : Valuation}
    {executable : ExecutableValuation} {term : Term} {atom : Atom}
    {binding : Metta.Subst}
    (variables : VariablesAgreeOnTerm reference executable term)
    (agreement : TermAgrees term atom)
    (models : SubstModels executable binding) :
    AtomDenotes executable (PLeaTTa.subst binding atom)
      (denoteTerm reference term) :=
  (TermAgrees.denotes variables agreement).subst models

/-- One executable answer denotes the independently observed value of a query
under one reference valuation.  The witnessing executable valuation must agree
on every query variable; it is not inferred from the answer representation. -/
def AnswerDenotes (query : Term) (reference : Valuation)
    (answer : Atom) : Prop :=
  ∃ executable : ExecutableValuation,
    VariablesAgreeOnTerm reference executable query ∧
      AtomDenotes executable answer (denoteTerm reference query)

/-- Pointwise relation between independent answer valuations and executable
answers. `List.Forall₂` makes order, length, and duplicate multiplicity part of
the statement rather than quotienting them away. -/
def OrderedAnswersDenote (query : Term) :
    List Valuation → List Atom → Prop :=
  List.Forall₂ (AnswerDenotes query)

/-- Ordered answer denotation composes by concatenation without deduplication. -/
theorem OrderedAnswersDenote.append {query : Term}
    {leftReferences rightReferences : List Valuation}
    {leftAnswers rightAnswers : List Atom}
    (left : OrderedAnswersDenote query leftReferences leftAnswers)
    (right : OrderedAnswersDenote query rightReferences rightAnswers) :
    OrderedAnswersDenote query (leftReferences ++ rightReferences)
      (leftAnswers ++ rightAnswers) := by
  induction left with
  | nil => simpa [OrderedAnswersDenote] using right
  | cons head tail ih =>
      simpa [OrderedAnswersDenote] using List.Forall₂.cons head ih

/-- Ordered answer denotation cannot hide a missing or duplicated answer. -/
theorem OrderedAnswersDenote.length_eq {query : Term}
    {references : List Valuation} {answers : List Atom}
    (denotes : OrderedAnswersDenote query references answers) :
    references.length = answers.length := by
  induction denotes with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Pulling changes only the active branch and alternative stack; the reverse
answer accumulator is untouched.  This raw form is useful when inspecting all
constructors of the small-step relation. -/
@[simp] theorem pull_answers (c : Conf) :
    (pull c).answers = c.answers := by
  unfold pull
  generalize pullAuxTracked c.barriers c.alts = tracked
  rcases tracked with ⟨next, depth⟩
  cases next with
  | none => rfl
  | some branch => cases branch; rfl

/-- Pulling the next alternative changes control only; it preserves the
published answer sequence. -/
theorem pull_answerValues (c : Conf) :
    (pull c).answerValues = c.answerValues := by
  unfold Conf.answerValues pull
  generalize pullAuxTracked c.barriers c.alts = tracked
  rcases tracked with ⟨next, depth⟩
  cases next with
  | none => rfl
  | some branch => cases branch; rfl

/-- Every sealed semantic step either preserves the ordered answer sequence or
is the unique answer transition, which appends exactly one instantiated query.
The statement classifies every `Step` constructor, including constructors with
nested runs, without assuming termination or erasing duplicate answers. -/
theorem Step.answerValues_shape
    {program : Prog} {grounding : Metta.GroundingTable}
    {source target : Conf}
    (step : Step program grounding source target) :
    target.answerValues = source.answerValues ∨
      ∃ binding, source.cur = some ([], binding) ∧
        target.answerValues =
          source.answerValues ++ [PLeaTTa.subst binding source.qterm] := by
  cases step <;> simp [Conf.answerValues, *]

/-- A single semantic step can only extend the published answer sequence by a
suffix.  The stronger `Step.answerValues_shape` theorem identifies the sole
nonempty suffix case. -/
theorem Step.answerValues_prefix
    {program : Prog} {grounding : Metta.GroundingTable}
    {source target : Conf}
    (step : Step program grounding source target) :
    ∃ suffix, target.answerValues = source.answerValues ++ suffix := by
  rcases PLeaTTa.ObservationAgreement.Step.answerValues_shape step with
    unchanged | ⟨binding, _current, appended⟩
  · exact ⟨[], by simpa using unchanged⟩
  · exact ⟨[PLeaTTa.subst binding source.qterm], appended⟩

/-- Along every finite sealed execution, published answers are append-only and
remain in discovery order.  The suffix is a list rather than a set or bag, so
order and duplicate multiplicity are retained. -/
theorem StepStar.answerValues_prefix
    {program : Prog} {grounding : Metta.GroundingTable}
    {source target : Conf}
    (steps : StepStar program grounding source target) :
    ∃ suffix, target.answerValues = source.answerValues ++ suffix := by
  apply StepStar.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun first last _ =>
      ∃ suffix, last.answerValues = first.answerValues ++ suffix)
    (motive_3 := fun _ _ _ _ => True)
    (t := steps)
  all_goals try { intros; trivial }
  case refl =>
    intro conf
    exact ⟨[], by simp⟩
  case tail =>
    intro first middle last step _rest _stepTrivial restPrefix
    rcases PLeaTTa.ObservationAgreement.Step.answerValues_prefix step with
      ⟨head, headEq⟩
    rcases restPrefix with ⟨tail, tailEq⟩
    exact ⟨head ++ tail, by simp only [tailEq, headEq, List.append_assoc]⟩

/-- The sealed answer transition appends exactly one denoting observation in
discovery order.  No claim about how the branch was reached is hidden here:
the modeled substitution and compiler representation agreement are explicit
premises for later finite-run composition. -/
theorem step_answer_appends_denoting_observation
    (program : Prog) (grounding : Metta.GroundingTable)
    (c : Conf) (binding : Metta.Subst)
    (current : c.cur = some ([], binding))
    {reference : Valuation} {executable : ExecutableValuation}
    {query : Term}
    (variables : VariablesAgreeOnTerm reference executable query)
    (queryAgreement : TermAgrees query c.qterm)
    (models : SubstModels executable binding) :
    ∃ next,
      Step program grounding c next ∧
      next.answerValues =
        c.answerValues ++ [PLeaTTa.subst binding c.qterm] ∧
      AtomDenotes executable (PLeaTTa.subst binding c.qterm)
        (denoteTerm reference query) := by
  let answered : Conf :=
    { c with
      cur := none
      answers := PLeaTTa.subst binding c.qterm :: c.answers
      answerKeys :=
        PersistentSubst.atomExactKey
          (PLeaTTa.subst binding c.qterm) :: c.answerKeys
      answerKeys_sound := by
        simp only [List.map_cons]
        rw [c.answerKeys_sound] }
  let next := pull answered
  refine ⟨next, ?_, ?_,
    PLeaTTa.ObservationAgreement.TermAgrees.subst_denotes
      variables queryAgreement models⟩
  · change Step program grounding c (pull answered)
    exact Step.answer c binding current
  · change (pull answered).answerValues = _
    rw [pull_answerValues]
    simp [answered, Conf.answerValues]

/-- Given an already related ordered answer prefix, one sealed answer step
extends both sides by the same final observation. -/
theorem step_answer_extends_ordered_observations
    (program : Prog) (grounding : Metta.GroundingTable)
    (c : Conf) (binding : Metta.Subst)
    (current : c.cur = some ([], binding))
    {reference : Valuation} {executable : ExecutableValuation}
    {query : Term} {priorReferences : List Valuation}
    (prior : OrderedAnswersDenote query priorReferences c.answerValues)
    (variables : VariablesAgreeOnTerm reference executable query)
    (queryAgreement : TermAgrees query c.qterm)
    (models : SubstModels executable binding) :
    ∃ next,
      Step program grounding c next ∧
      OrderedAnswersDenote query (priorReferences ++ [reference])
        next.answerValues := by
  obtain ⟨next, step, answerValues, denotes⟩ :=
    step_answer_appends_denoting_observation program grounding c binding
      current variables queryAgreement models
  refine ⟨next, step, ?_⟩
  rw [answerValues]
  exact prior.append
    (.cons ⟨executable, variables, denotes⟩ .nil)

/-- End-to-end composition for the first complete supported source fragment:
an independently specified literal translates through the executable compiler,
enters the actual sealed machine, and produces the same single ordered
reference observation.  The arbitrary call semantics is intentionally unused
because the translated literal emits no goals. -/
theorem literal_compile_step_observation
    {source : Atom} {term : Term}
    (env : CEnv) (counter : Nat) (literal : Literal source term)
    (program : Prog) (grounding : Metta.GroundingTable) (world : PWorld)
    (calls : Ordered.CallSemantics)
    (reference : Valuation) (executable : ExecutableValuation)
    (variables : VariablesAgreeOnTerm reference executable term) :
    ∃ internal initial next,
      compileExpr env counter source = .ok (internal, [], counter) ∧
      initial =
        ({ cur := some ([], ([] : Metta.Subst))
           alts := []
           world := world
           counter := counter
           qterm := internal } : Conf) ∧
      Step program grounding initial next ∧
      Ordered.RunsAll calls reference [] [reference] ∧
      OrderedAnswersDenote term [reference] next.answerValues := by
  obtain ⟨internal, compiled, termAgreement⟩ :=
    compileExpr_literal_adequate env counter literal
  let initial : Conf :=
    { cur := some ([], ([] : Metta.Subst))
      alts := []
      world := world
      counter := counter
      qterm := internal }
  have prior : OrderedAnswersDenote term [] initial.answerValues := by
    simp [initial, OrderedAnswersDenote, Conf.answerValues]
  obtain ⟨next, step, denotes⟩ :=
    step_answer_extends_ordered_observations program grounding initial [] rfl
      prior variables termAgreement (substModels_empty executable)
  exact ⟨internal, initial, next, compiled, rfl, step, .nil reference, by
    simpa using denotes⟩

/-- Positive nested-value witness for variable and integer denotation through
the executable proper-list encoding. -/
theorem source_integer_list_denotes (reference : Valuation)
    (executable : ExecutableValuation)
    (hvariable : executable "x" = reference (.source "x")) :
    AtomDenotes executable (chainOf [.var "x", .gnd (.int 1)])
      (.list [reference (.source "x"), .integer 1] none) := by
  exact .properList
    (.cons (by rw [← hvariable]; exact .variable "x")
      (.cons (.integer 1) .nil))

private def integerReferenceOne : Valuation := fun _ => .integer 1
private def integerReferenceTwo : Valuation := fun _ => .integer 2
private def integerExecutableOne : ExecutableValuation := fun _ => .integer 1
private def integerExecutableTwo : ExecutableValuation := fun _ => .integer 2

/-- Positive ordered-observation witness with two distinct valuations. -/
theorem ordered_integer_answers_denote :
    OrderedAnswersDenote (.variable (.source "x"))
      [integerReferenceOne, integerReferenceTwo]
      [.gnd (.int 1), .gnd (.int 2)] := by
  exact .cons ⟨integerExecutableOne, rfl, .integer 1⟩
    (.cons ⟨integerExecutableTwo, rfl, .integer 2⟩ .nil)

/-- Negative ordered-observation witness: reversing the executable answers is
not accepted merely because the same answer bag is present. -/
theorem ordered_integer_answers_not_swapped :
    ¬ OrderedAnswersDenote (.variable (.source "x"))
      [integerReferenceOne, integerReferenceTwo]
      [.gnd (.int 2), .gnd (.int 1)] := by
  intro execution
  cases execution with
  | cons head _ =>
      rcases head with ⟨executable, variables, denotes⟩
      rcases atomDenotes_ground denotes with
        integerReading | floatReading | stringReading
      · obtain ⟨integer, groundEq, valueEq⟩ := integerReading
        simp at groundEq
        subst integer
        simp [denoteTerm, integerReferenceOne] at valueEq
      · obtain ⟨float, groundEq, _valueEq⟩ := floatReading
        simp at groundEq
      · obtain ⟨string, groundEq, _valueEq⟩ := stringReading
        simp at groundEq

/-- The canonical truth encoding also denotes the literal source atom
`True`; a later supported-source condition must exclude this ambiguity. -/
theorem true_encoding_has_two_atom_readings
    (valuation : ExecutableValuation) :
    AtomDenotes valuation (.sym "True") (.atom "true") ∧
      AtomDenotes valuation (.sym "True") (.atom "True") := by
  exact ⟨.trueAtom, .symbol "True"⟩

/-- The internal nil sentinel can also be read as a literal source atom;
canonical source terms must reserve the sentinel spelling. -/
theorem nil_encoding_has_atom_and_list_readings
    (valuation : ExecutableValuation) :
    AtomDenotes valuation nilA (.atom "#nil") ∧
      AtomDenotes valuation nilA (.list [] none) := by
  exact ⟨.symbol "#nil", .properList .nil⟩

/-- A source variable named like a generated compiler variable forces the two
independent variables to alias under the current executable encoding. This is
the concrete freshness premise the composed supported-source theorem must
exclude. -/
theorem source_generated_collision_requires_equal
    (reference : Valuation) (executable : ExecutableValuation) (index : Nat)
    (agreement : VariablesAgreeOnTerm reference executable
      (.list [.variable (.source s!"_q{index}"),
        .variable (.generated index)] none)) :
    reference (.source s!"_q{index}") = reference (.generated index) := by
  simp [VariablesAgreeOnTerm, VariablesAgreeOnTerms] at agreement
  exact agreement.1.symm.trans agreement.2

end PLeaTTa.ObservationAgreement
