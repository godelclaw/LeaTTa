-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologCanonicalRuntimeReading
Purpose: Give the supported open PeTTa term encoding one functional,
  source-guided runtime reading.
Trusted boundary: none
Main exports: CanonicalRuntimeReading,
  CanonicalRuntimeReading.functional
-/
import PLeaTTa.Proofs.PrologMguBridge
import PLeaTTa.Proofs.PrologPrefilterBridge

namespace PLeaTTa.PrologCanonicalRuntimeReading

open Metta (Atom)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PrologMguBridge
open PrologPrefilterBridge

/-!
`CanonicalRuntimeAgrees` is deliberately relational: the runtime symbols
`True` and `False` also spell accepted source boolean aliases.  That relation
is suitable for forward simulation but has no global inverse until the
supported reader normalizes those aliases.

This file makes the supported inverse explicit.  Reserved encodings have
their PeTTa meanings.  Partial values use the internal `partialC` tag rather
than the ordinary source-list spine, and the internal compound is not a
`#c` chain at all.  The restriction is structural, not an assumption that
runtime unification happens to reflect source unification.
-/

/-- One source-guided, canonical reading of the supported open runtime
encoding.

The negative fields on `atom` reserve the runtime spellings used for
booleans.  Empty lists, partial values, and proper-list cells use
structurally distinct runtime constructors, so no negative side condition is
needed to separate them.  Variables remain open and are interpreted through
the shared alpha graph. -/
inductive CanonicalRuntimeReading
    (alpha : List (LogicVar × String)) : Tree → Atom → Prop where
  | variable {identity : LogicVar} {name : String}
      (linked : (identity, name) ∈ alpha) :
      CanonicalRuntimeReading alpha (.variable identity) (.var name)
  | atom {name : String}
      (notLowerTrue : name ≠ "true")
      (notLowerFalse : name ≠ "false")
      (notRuntimeTrue : name ≠ "True")
      (notRuntimeFalse : name ≠ "False") :
      CanonicalRuntimeReading alpha (.node (.atom name) []) (.sym name)
  | trueAtom :
      CanonicalRuntimeReading alpha
        (.node (.atom "true") []) (.sym "True")
  | falseAtom :
      CanonicalRuntimeReading alpha
        (.node (.atom "false") []) (.sym "False")
  | integer (value : Int) :
      CanonicalRuntimeReading alpha
        (.node (.integer value) []) (.gnd (.int value))
  | float (value : Float) :
      CanonicalRuntimeReading alpha
        (.node (.float (PLeaTTa.PrologFloatIdentity.ofFloat value)) [])
        (.gnd (.float value))
  | string (value : String) :
      CanonicalRuntimeReading alpha
        (.node (.string value) []) (.gnd (.str value))
  | partialValue {head : String} {argumentsTree : Tree}
      {encodedArguments : Atom}
      (arguments :
        CanonicalRuntimeReading alpha argumentsTree encodedArguments) :
      CanonicalRuntimeReading alpha
        (.node (.compound "partial")
          [.node (.atom head) [], argumentsTree])
        (partialC head encodedArguments)
  | nil :
      CanonicalRuntimeReading alpha (.node .nil []) nilA
  | cons {headTree tailTree : Tree} {headAtom tailAtom : Atom}
      (head : CanonicalRuntimeReading alpha headTree headAtom)
      (tail : CanonicalRuntimeReading alpha tailTree tailAtom) :
      CanonicalRuntimeReading alpha
        (.node .cons [headTree, tailTree]) (consC headAtom tailAtom)

/-- The functional reading remains a valid witness for the broad forward
relation. -/
theorem CanonicalRuntimeReading.toCanonicalRuntimeAgrees
    {alpha : List (LogicVar × String)}
    {tree : Tree} {atom : Atom}
    (reading : CanonicalRuntimeReading alpha tree atom) :
    CanonicalRuntimeAgrees alpha tree atom := by
  induction reading with
  | «variable» linked => exact .variable linked
  | atom notLowerTrue notLowerFalse _ _ =>
      exact .atom notLowerTrue notLowerFalse
  | trueAtom => exact .trueAtom
  | falseAtom => exact .falseAtom
  | integer value => exact .integer value
  | float value => exact .float value
  | string value => exact .string value
  | partialValue arguments inductionHypothesis =>
      exact .partialValue inductionHypothesis
  | nil => exact .nil
  | cons head tail headIH tailIH =>
      exact .cons headIH tailIH

/-- The source-guided relation is a partial function from runtime atoms to
canonical open trees.  Inverse functionality of the shared alpha graph is
the only premise: without it, one runtime variable name could still denote
two independent identities. -/
theorem CanonicalRuntimeReading.functional
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {left right : Tree} {atom : Atom}
    (leftReading : CanonicalRuntimeReading alpha left atom)
    (rightReading : CanonicalRuntimeReading alpha right atom) :
    left = right := by
  induction leftReading generalizing right with
  | «variable» leftLinked =>
      cases rightReading with
      | «variable» rightLinked =>
          simp [shared.backward leftLinked rightLinked]
  | atom _ _ notRuntimeTrue notRuntimeFalse =>
      cases rightReading with
      | atom _ _ _ _ => rfl
      | trueAtom => exact False.elim (notRuntimeTrue rfl)
      | falseAtom => exact False.elim (notRuntimeFalse rfl)
  | trueAtom =>
      generalize atomEq : (Atom.sym "True") = runtimeAtom at rightReading
      cases rightReading <;>
        simp_all [partialC, partialTagA, consC, nilA]
  | falseAtom =>
      generalize atomEq : (Atom.sym "False") = runtimeAtom at rightReading
      cases rightReading <;>
        simp_all [partialC, partialTagA, consC, nilA]
  | integer _ =>
      cases rightReading with
      | integer _ => rfl
  | float _ =>
      cases rightReading with
      | float _ => rfl
  | string _ =>
      cases rightReading with
      | string _ => rfl
  | @partialValue leftHead leftTree leftAtom leftArguments
      inductionHypothesis =>
      cases rightReading with
      | @partialValue rightHead rightTree rightAtom rightArguments =>
          rw [inductionHypothesis rightArguments]
  | nil =>
      generalize atomEq : nilA = runtimeAtom at rightReading
      cases rightReading <;>
        simp_all [partialC, partialTagA, consC, nilA]
  | @cons leftHeadTree leftTailTree leftHeadAtom leftTailAtom
      leftHead leftTail headIH tailIH =>
      cases rightReading with
      | @cons rightHeadTree rightTailTree rightHeadAtom rightTailAtom
          rightHead rightTail =>
          rw [headIH rightHead, tailIH rightTail]

/-! ## Anti-vacuity at each reserved encoding -/

/-- The broad relation admits the literal atom `True`; the canonical reading
rejects it in favor of the source boolean atom `true`. -/
theorem literal_runtime_true_is_excluded :
    CanonicalRuntimeAgrees []
        (.node (.atom "True") []) (.sym "True") ∧
      ¬ CanonicalRuntimeReading []
        (.node (.atom "True") []) (.sym "True") := by
  constructor
  · exact .atom (by decide) (by decide)
  · intro reading
    have shared : SharedRuntimeAlpha [] := by
      constructor <;> intro <;> simp_all
    have equal :=
      CanonicalRuntimeReading.functional shared reading
        (CanonicalRuntimeReading.trueAtom (alpha := []))
    simp at equal

/-- The forgeable source atom `#nil` and the internal empty-list sentinel
now have distinct canonical readings and distinct runtime constructors. -/
theorem source_nil_and_empty_list_are_distinct :
    CanonicalRuntimeReading []
        (.node (.atom "#nil") []) (.sym "#nil") ∧
      CanonicalRuntimeReading [] (.node .nil []) nilA ∧
      (Atom.sym "#nil" : Atom) ≠ nilA := by
  constructor
  · exact .atom (by decide) (by decide) (by decide) (by decide)
  · exact ⟨.nil, nilA_ne_source_nil.symm⟩

private def partialArgumentsTree : Tree := .node .nil []
private def partialArgumentsAtom : Atom := nilA

/-- The intended partial-value reading remains admitted. -/
theorem partial_value_is_admitted :
    CanonicalRuntimeReading []
      (.node (.compound "partial")
        [.node (.atom "f") [], partialArgumentsTree])
      (partialC "f" partialArgumentsAtom) := by
  exact .partialValue .nil

/-- The internal partial runtime value is not admitted as an ordinary
three-element proper list.  Thus partial/list ambiguity is removed by a
constructor boundary rather than a postulated unification-reflection
premise. -/
theorem partial_runtime_list_reading_is_excluded :
    ¬ CanonicalRuntimeReading []
      (Tree.prologList
        [.node (.atom "partial") [],
          .node (.atom "f") [],
          partialArgumentsTree] none)
      (partialC "f" partialArgumentsAtom) := by
  intro reading
  cases reading

/-- The ordinary source list remains admitted at its own cons-chain spelling,
which is structurally distinct from the internal partial compound. -/
theorem source_partial_list_is_distinctly_admitted :
    CanonicalRuntimeReading []
        (Tree.prologList
          [.node (.atom "partial") [],
            .node (.atom "f") [],
            partialArgumentsTree] none)
        (chainOf [.sym "partial", .sym "f", partialArgumentsAtom]) ∧
      partialC "f" partialArgumentsAtom ≠
        chainOf [.sym "partial", .sym "f", partialArgumentsAtom] := by
  constructor
  · apply CanonicalRuntimeReading.cons
    · exact .atom (by decide) (by decide) (by decide) (by decide)
    · apply CanonicalRuntimeReading.cons
      · exact .atom (by decide) (by decide) (by decide) (by decide)
      · apply CanonicalRuntimeReading.cons
        · exact .nil
        · exact .nil
  · simp [partialArgumentsAtom, partialC, partialTagA, chainOf, consC,
      nilA]

end PLeaTTa.PrologCanonicalRuntimeReading
