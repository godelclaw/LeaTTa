-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologPrefilterBridge
Purpose: Prove that executable Prolog candidate filtering is conservative
  for alpha-related independent finite terms.
Trusted boundary: none
Main exports:
  AlphaTermAgrees.prologMatchCompat_of_denotationalUnifier
-/
import PLeaTTa.Proofs.PrologActivationBridge

namespace PLeaTTa.PrologPrefilterBridge

open Metta (Atom)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.Resolver
open PrologStateBridge
open PrologActivationBridge
open PrologActivationMacro

/-- Canonical-tree/runtime agreement after expanding the independent proper
list presentation into ordinary `nil`/`cons` nodes.  This intermediate
relation is intentionally independent of `prologMatchCompat`: it says only
which runtime atom denotes each canonical rigid tree. -/
inductive CanonicalRuntimeAgrees
    (alpha : List (LogicVar × String)) : Tree → Atom → Prop where
  | variable {identity : LogicVar} {name : String}
      (linked : (identity, name) ∈ alpha) :
      CanonicalRuntimeAgrees alpha (.variable identity) (.var name)
  | atom {name : String} (notTrue : name ≠ "true")
      (notFalse : name ≠ "false") :
      CanonicalRuntimeAgrees alpha (.node (.atom name) []) (.sym name)
  | trueAtom :
      CanonicalRuntimeAgrees alpha
        (.node (.atom "true") []) (.sym "True")
  | falseAtom :
      CanonicalRuntimeAgrees alpha
        (.node (.atom "false") []) (.sym "False")
  | integer (value : Int) :
      CanonicalRuntimeAgrees alpha
        (.node (.integer value) []) (.gnd (.int value))
  | float (value : Float) :
      CanonicalRuntimeAgrees alpha
        (.node (.float (PLeaTTa.PrologFloatIdentity.ofFloat value)) [])
        (.gnd (.float value))
  | string (value : String) :
      CanonicalRuntimeAgrees alpha
        (.node (.string value) []) (.gnd (.str value))
  | partialValue {head : String} {argumentsTree : Tree}
      {encodedArguments : Atom}
      (arguments :
        CanonicalRuntimeAgrees alpha argumentsTree encodedArguments) :
      CanonicalRuntimeAgrees alpha
        (.node (.compound "partial")
          [.node (.atom head) [], argumentsTree])
        (partialC head encodedArguments)
  | nil :
      CanonicalRuntimeAgrees alpha (.node .nil []) nilA
  | cons {headTree tailTree : Tree} {headAtom tailAtom : Atom}
      (head : CanonicalRuntimeAgrees alpha headTree headAtom)
      (tail : CanonicalRuntimeAgrees alpha tailTree tailAtom) :
      CanonicalRuntimeAgrees alpha
        (.node .cons [headTree, tailTree]) (consC headAtom tailAtom)

/-- A canonical integer tree has exactly one executable reading.  This is
the rigid-observation eliminator dual to the `integer` constructor and avoids
dependent destruction at callers whose runtime atom is itself indexed by a
substitution computation. -/
theorem CanonicalRuntimeAgrees.integer_atom
    {alpha : List (LogicVar × String)} {value : Int} {atom : Atom}
    (agreement :
      CanonicalRuntimeAgrees alpha (.node (.integer value) []) atom) :
    atom = .gnd (.int value) := by
  cases agreement
  rfl

mutual

/-- Alpha agreement implies the normalized canonical-tree/runtime relation. -/
theorem AlphaTermAgrees.canonicalRuntimeAgrees
    {alpha : List (LogicVar × String)}
    {term : Term} {atom : Atom}
    (agrees : AlphaTermAgrees alpha term atom) :
    CanonicalRuntimeAgrees alpha (Term.denote term) atom := by
  cases agrees with
  | «variable» linked => exact .variable linked
  | atom notTrue notFalse => exact .atom notTrue notFalse
  | trueAtom => exact .trueAtom
  | falseAtom => exact .falseAtom
  | integer value => exact .integer value
  | float value => exact .float value
  | string value => exact .string value
  | partialValue arguments =>
      exact .partialValue
        (AlphaProperListAgrees.canonicalRuntimeAgrees arguments)
  | properList elements =>
      exact AlphaProperListAgrees.canonicalRuntimeAgrees elements

/-- Proper-list alpha agreement normalizes to explicit canonical list cells. -/
theorem AlphaProperListAgrees.canonicalRuntimeAgrees
    {alpha : List (LogicVar × String)}
    {items : List Term} {atom : Atom}
    (agrees : AlphaProperListAgrees alpha items atom) :
    CanonicalRuntimeAgrees alpha
      (Tree.prologList (Terms.denote items) none) atom := by
  cases agrees with
  | nil => exact .nil
  | cons head rest =>
      exact .cons
        (AlphaTermAgrees.canonicalRuntimeAgrees head)
        (AlphaProperListAgrees.canonicalRuntimeAgrees rest)

end

/-- A structurally unifiable pair of canonical trees cannot be rejected by
the exact executable Prolog compatibility filter.  The two alpha graphs may
differ: variables are wildcards and only rigid structure matters. -/
theorem CanonicalRuntimeAgrees.prologMatchCompat_of_treeMayUnify
    {leftAlpha rightAlpha : List (LogicVar × String)}
    {leftTree rightTree : Tree} {leftAtom rightAtom : Atom}
    (left : CanonicalRuntimeAgrees leftAlpha leftTree leftAtom)
    (right : CanonicalRuntimeAgrees rightAlpha rightTree rightAtom)
    (compatible : TreeMayUnify leftTree rightTree) :
    PLeaTTa.prologMatchCompat leftAtom rightAtom = true := by
  induction left generalizing rightAlpha rightTree rightAtom with
  | «variable» =>
      simp [PLeaTTa.prologMatchCompat]
  | @atom leftName leftNotTrue leftNotFalse =>
      cases right with
      | «variable» =>
          simp [PLeaTTa.prologMatchCompat]
      | @atom rightName rightNotTrue rightNotFalse =>
          have names := compatible.atom_name_eq
          subst rightName
          simp [PLeaTTa.prologMatchCompat]
      | trueAtom =>
          exact False.elim (leftNotTrue compatible.atom_name_eq)
      | falseAtom =>
          exact False.elim (leftNotFalse compatible.atom_name_eq)
      | integer | float | string | partialValue | nil | cons =>
          cases compatible
  | trueAtom =>
      cases right with
      | «variable» =>
          simp [PLeaTTa.prologMatchCompat]
      | atom rightNotTrue rightNotFalse =>
          exact False.elim (rightNotTrue compatible.atom_name_eq.symm)
      | trueAtom =>
          simp [PLeaTTa.prologMatchCompat]
      | falseAtom =>
          have impossible := compatible.atom_name_eq
          contradiction
      | integer | float | string | partialValue | nil | cons =>
          cases compatible
  | falseAtom =>
      cases right with
      | «variable» =>
          simp [PLeaTTa.prologMatchCompat]
      | atom rightNotTrue rightNotFalse =>
          exact False.elim (rightNotFalse compatible.atom_name_eq.symm)
      | trueAtom =>
          have impossible := compatible.atom_name_eq
          contradiction
      | falseAtom =>
          simp [PLeaTTa.prologMatchCompat]
      | integer | float | string | partialValue | nil | cons =>
          cases compatible
  | integer leftValue =>
      cases right with
      | «variable» =>
          simp [PLeaTTa.prologMatchCompat]
      | integer rightValue =>
          have symbols := compatible.node_symbol_eq
          injection symbols with values
          subst rightValue
          simp [PLeaTTa.prologMatchCompat]
      | atom | trueAtom | falseAtom | float | string | partialValue | nil |
          cons =>
          cases compatible
  | float leftValue =>
      cases right with
      | «variable» =>
          simp [PLeaTTa.prologMatchCompat]
      | float rightValue =>
          have symbols := compatible.node_symbol_eq
          injection symbols with identities
          simp [PLeaTTa.prologMatchCompat,
            PLeaTTa.prologGroundIdentical, identities]
      | atom | trueAtom | falseAtom | integer | string | partialValue | nil |
          cons =>
          cases compatible
  | string leftValue =>
      cases right with
      | «variable» =>
          simp [PLeaTTa.prologMatchCompat]
      | string rightValue =>
          have symbols := compatible.node_symbol_eq
          injection symbols with values
          subst rightValue
          simp [PLeaTTa.prologMatchCompat]
      | atom | trueAtom | falseAtom | integer | float | partialValue | nil |
          cons =>
          cases compatible
  | @partialValue leftHead leftTree leftAtom leftArguments
      leftArgumentsIH =>
      cases right with
      | «variable» =>
          simp [partialC, partialTagA, PLeaTTa.prologMatchCompat]
      | @partialValue rightHead rightTree rightAtom rightArguments =>
          have children := compatible.node_children
          cases children with
          | cons headCompatible tailCompatible =>
              cases tailCompatible with
              | cons argumentsCompatible done =>
                  cases done
                  have heads := headCompatible.atom_name_eq
                  subst rightHead
                  have arguments :=
                    leftArgumentsIH rightArguments argumentsCompatible
                  simp [partialC, partialTagA, PLeaTTa.prologMatchCompat,
                    PLeaTTa.prologMatchCompatList, arguments]
      | atom | trueAtom | falseAtom | integer | float | string | nil | cons =>
          cases compatible
  | nil =>
      cases right with
      | «variable» =>
          simp [nilA, PLeaTTa.prologMatchCompat]
      | nil =>
          simp [nilA, PLeaTTa.prologMatchCompat]
      | atom | trueAtom | falseAtom | integer | float | string |
          partialValue | cons =>
          cases compatible
  | @cons leftHeadTree leftTailTree leftHeadAtom leftTailAtom
      leftHead leftTail leftHeadIH leftTailIH =>
      cases right with
      | «variable» =>
          simp [consC, PLeaTTa.prologMatchCompat]
      | @cons rightHeadTree rightTailTree rightHeadAtom rightTailAtom
          rightHead rightTail =>
          have parts := compatible.node₂
          have heads := leftHeadIH rightHead parts.1
          have tails := leftTailIH rightTail parts.2
          simp [consC, PLeaTTa.prologMatchCompat,
            PLeaTTa.prologMatchCompatList, heads, tails]
      | atom | trueAtom | falseAtom | integer | float | string |
          partialValue | nil =>
          cases compatible

/-- Original source-term form consumed by the clause-scan bridge. -/
theorem AlphaTermAgrees.prologMatchCompat_of_treeMayUnify
    {leftAlpha rightAlpha : List (LogicVar × String)}
    {leftTerm rightTerm : Term} {leftAtom rightAtom : Atom}
    (left : AlphaTermAgrees leftAlpha leftTerm leftAtom)
    (right : AlphaTermAgrees rightAlpha rightTerm rightAtom)
    (compatible :
      TreeMayUnify (Term.denote leftTerm) (Term.denote rightTerm)) :
    PLeaTTa.prologMatchCompat leftAtom rightAtom = true :=
  CanonicalRuntimeAgrees.prologMatchCompat_of_treeMayUnify
    (AlphaTermAgrees.canonicalRuntimeAgrees left)
    (AlphaTermAgrees.canonicalRuntimeAgrees right) compatible

mutual

/-- If every reference identity named by an alpha graph lies in the
generated namespace above `lower`, the related independent term has the same
structural freshness property. -/
theorem AlphaTermAgrees.generatedAtLeast_of_graph
    {alpha : List (LogicVar × String)}
    {term : Term} {atom : Atom}
    (agreement : AlphaTermAgrees alpha term atom)
    {lower : Nat}
    (range : ∀ identity name, (identity, name) ∈ alpha →
      ∃ index, identity = .generated index ∧ lower ≤ index) :
    term.GeneratedAtLeast lower := by
  cases agreement with
  | «variable» linked =>
      obtain ⟨index, rfl, bound⟩ := range _ _ linked
      exact bound
  | atom | trueAtom | falseAtom | integer | float | string =>
      trivial
  | partialValue arguments =>
      have generated :=
        AlphaProperListAgrees.generatedAtLeast_of_graph arguments range
      simpa [Term.GeneratedAtLeast, Terms.GeneratedAtLeast] using generated
  | properList elements =>
      exact
        AlphaProperListAgrees.generatedAtLeast_of_graph elements range

/-- Proper-list counterpart of
`AlphaTermAgrees.generatedAtLeast_of_graph`. -/
theorem AlphaProperListAgrees.generatedAtLeast_of_graph
    {alpha : List (LogicVar × String)}
    {terms : List Term} {atom : Atom}
    (agreement : AlphaProperListAgrees alpha terms atom)
    {lower : Nat}
    (range : ∀ identity name, (identity, name) ∈ alpha →
      ∃ index, identity = .generated index ∧ lower ≤ index) :
    Terms.GeneratedAtLeast lower terms := by
  cases agreement with
  | nil =>
      trivial
  | cons head rest =>
      exact
        ⟨AlphaTermAgrees.generatedAtLeast_of_graph head range,
          AlphaProperListAgrees.generatedAtLeast_of_graph rest range⟩

end

/-- Ordered alpha-related terms inherit a generated lower bound pointwise. -/
theorem AlphaTermsAgree.generatedAtLeast_of_graph
    {alpha : List (LogicVar × String)}
    {terms : List Term} {atoms : List Atom}
    (agreement : AlphaTermsAgree alpha terms atoms)
    {lower : Nat}
    (range : ∀ identity name, (identity, name) ∈ alpha →
      ∃ index, identity = .generated index ∧ lower ≤ index) :
    Terms.GeneratedAtLeast lower terms := by
  induction agreement with
  | nil =>
      trivial
  | cons head tail inductionHypothesis =>
      exact
        ⟨AlphaTermAgrees.generatedAtLeast_of_graph head range,
          inductionHypothesis⟩

/-- Append one output term to an ordered alpha-related input payload. -/
theorem AlphaTermsAgree.append_singleton
    {alpha : List (LogicVar × String)}
    {terms : List Term} {atoms : List Atom}
    (agreement : AlphaTermsAgree alpha terms atoms)
    {term : Term} {atom : Atom}
    (output : AlphaTermAgrees alpha term atom) :
    AlphaTermsAgree alpha (terms ++ [term]) (atoms ++ [atom]) := by
  induction agreement with
  | nil =>
      exact .cons output .nil
  | cons head tail inductionHypothesis =>
      exact .cons head inductionHypothesis

/-- Alpha agreement is occurrence-preserving, so both ordered payloads have
the same length. -/
theorem AlphaTermsAgree.length_eq
    {alpha : List (LogicVar × String)}
    {terms : List Term} {atoms : List Atom}
    (agreement : AlphaTermsAgree alpha terms atoms) :
    terms.length = atoms.length := by
  induction agreement with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [inductionHypothesis]

/-- Denotational unifiability is sufficient for the executable conservative
filter to retain an alpha-related pair. -/
theorem AlphaTermAgrees.prologMatchCompat_of_denotationalUnifier
    {leftAlpha rightAlpha : List (LogicVar × String)}
    {leftTerm rightTerm : Term} {leftAtom rightAtom : Atom}
    (left : AlphaTermAgrees leftAlpha leftTerm leftAtom)
    (right : AlphaTermAgrees rightAlpha rightTerm rightAtom)
    {unifier : PeTTaSpec.PrologCore.OpenSubstitution.Substitution}
    (unifies : DenotationalUnifier unifier leftTerm rightTerm) :
    PLeaTTa.prologMatchCompat leftAtom rightAtom = true :=
  AlphaTermAgrees.prologMatchCompat_of_treeMayUnify left right
    (TreeMayUnify.of_denotationalUnifier unifies)

/-- Contrapositive form consumed by the ranked clause-scan bridge:
`false` is a real rigid clash, not merely an indexing heuristic. -/
theorem AlphaTermAgrees.no_denotationalUnifier_of_prologMatchCompat_false
    {leftAlpha rightAlpha : List (LogicVar × String)}
    {leftTerm rightTerm : Term} {leftAtom rightAtom : Atom}
    (left : AlphaTermAgrees leftAlpha leftTerm leftAtom)
    (right : AlphaTermAgrees rightAlpha rightTerm rightAtom)
    (rejected : PLeaTTa.prologMatchCompat leftAtom rightAtom = false) :
    ¬ ∃ unifier, DenotationalUnifier unifier leftTerm rightTerm := by
  rintro ⟨unifier, unifies⟩
  have retained :=
    AlphaTermAgrees.prologMatchCompat_of_denotationalUnifier
      left right unifies
  simp [rejected] at retained

/-! ## Complete output-last heads -/

/-- Pointwise agreement between one independent head-equation worklist and
the two executable atom lists compared by the conservative prefilter.  Alpha
graphs are explicit per equation; no executable filtering result appears in
the relation. -/
inductive AlphaEquationsAgree :
    List (Term × Term) → List Atom → List Atom → Prop where
  | nil : AlphaEquationsAgree [] [] []
  | cons {leftAlpha rightAlpha : List (LogicVar × String)}
      {leftTerm rightTerm : Term} {leftAtom rightAtom : Atom}
      {equations : List (Term × Term)}
      {leftAtoms rightAtoms : List Atom}
      (left : AlphaTermAgrees leftAlpha leftTerm leftAtom)
      (right : AlphaTermAgrees rightAlpha rightTerm rightAtom)
      (tail : AlphaEquationsAgree equations leftAtoms rightAtoms) :
      AlphaEquationsAgree
        ((leftTerm, rightTerm) :: equations)
        (leftAtom :: leftAtoms) (rightAtom :: rightAtoms)

/-- Equal-length pointwise alpha-related payloads induce the exact
`argumentEquations` worklist relation. -/
theorem AlphaTermsAgree.alphaEquationsAgree
    {leftAlpha rightAlpha : List (LogicVar × String)}
    {leftTerms rightTerms : List Term}
    {leftAtoms rightAtoms : List Atom}
    (left : AlphaTermsAgree leftAlpha leftTerms leftAtoms)
    (right : AlphaTermsAgree rightAlpha rightTerms rightAtoms)
    (lengths : leftTerms.length = rightTerms.length) :
    AlphaEquationsAgree
      (argumentEquations leftTerms rightTerms) leftAtoms rightAtoms := by
  induction left generalizing rightTerms rightAtoms with
  | nil =>
      cases right with
      | nil => exact .nil
      | cons => simp at lengths
  | @cons leftTerm leftAtom leftTerms leftAtoms leftHead leftTail
      inductionHypothesis =>
      cases right with
      | nil => simp at lengths
      | @cons rightTerm rightAtom rightTerms rightAtoms rightHead rightTail =>
          have tailLengths :
              leftTerms.length = rightTerms.length := by
            simpa using Nat.succ.inj lengths
          exact .cons leftHead rightHead
            (inductionHypothesis rightTail tailLengths)

/-- A common independent unifier of every related equation forces exact
pointwise retention by the executable filter. -/
theorem AlphaEquationsAgree.prologMatchCompatList_of_unifier
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement : AlphaEquationsAgree equations leftAtoms rightAtoms)
    {candidate :
      PeTTaSpec.PrologCore.OpenSubstitution.Substitution}
    (unifies : DenotationalUnifiesEquations candidate equations) :
    PLeaTTa.prologMatchCompatList leftAtoms rightAtoms = true := by
  induction agreement with
  | nil =>
      rfl
  | @cons leftAlpha rightAlpha leftTerm rightTerm leftAtom rightAtom
      equations leftAtoms rightAtoms left right tail inductionHypothesis =>
      have headUnifies :
          DenotationalUnifier candidate leftTerm rightTerm :=
        unifies (leftTerm, rightTerm) (by simp)
      have tailUnifies :
          DenotationalUnifiesEquations candidate equations := by
        intro equation member
        exact unifies equation (List.mem_cons_of_mem _ member)
      simp only [PLeaTTa.prologMatchCompatList]
      rw [AlphaTermAgrees.prologMatchCompat_of_denotationalUnifier
          left right headUnifies,
        inductionHypothesis tailUnifies]
      rfl

/-- With equal prefix lengths, appending the output slot turns the full-head
compatibility test into the conjunction used by `resolutionClauseRetained`.
-/
theorem prologMatchCompatList_append_singleton_of_length_eq
    (left right : List Atom) (leftOutput rightOutput : Atom)
    (lengths : left.length = right.length) :
    PLeaTTa.prologMatchCompatList
        (left ++ [leftOutput]) (right ++ [rightOutput]) =
      (PLeaTTa.prologMatchCompatList left right &&
        PLeaTTa.prologMatchCompat leftOutput rightOutput) := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => simp [PLeaTTa.prologMatchCompatList]
      | cons rightHead rightTail => simp at lengths
  | cons leftHead leftTail inductionHypothesis =>
      cases right with
      | nil => simp at lengths
      | cons rightHead rightTail =>
          have tailLengths : leftTail.length = rightTail.length := by
            simpa using Nat.succ.inj lengths
          simp only [List.cons_append, PLeaTTa.prologMatchCompatList]
          rw [inductionHypothesis rightTail tailLengths]
          simp only [Bool.and_assoc]

/-- Exact representation contract at the conservative-filter seam.  The
independent branch supplies its already-normalized head equations; the
runtime side supplies the input atoms plus the separate output atom used by
`resolveAlts`.  Equal input arity is stated independently. -/
structure NormalizedHeadAgrees
    (branch : ClauseBranch) (argsv : List Atom) (resv : Atom)
    (clause : PLeaTTa.Clause) : Prop where
  arity : clause.params.length = argsv.length
  equations :
    AlphaEquationsAgree branch.normalizedHeadEquations
      (argsv ++ [resv]) (clause.params ++ [clause.result])

/-- Any independent head resolution is retained by the executable's
conservative output-last head filter. -/
theorem NormalizedHeadAgrees.retained_of_headResolution
    {branch : ClauseBranch} {argsv : List Atom} {resv : Atom}
    {clause : PLeaTTa.Clause}
    (agreement : NormalizedHeadAgrees branch argsv resv clause)
    (resolves : ∃ result, HeadResolution branch result) :
    resolutionClauseRetained argsv resv clause = true := by
  obtain ⟨candidate, unifies⟩ :=
    HeadResolution.exists_iff_unifiable.mp resolves
  have fullCompatibility :=
    agreement.equations.prologMatchCompatList_of_unifier unifies
  rw [prologMatchCompatList_append_singleton_of_length_eq
      argsv clause.params resv clause.result agreement.arity.symm]
      at fullCompatibility
  have split :
      PLeaTTa.prologMatchCompatList argsv clause.params = true ∧
        PLeaTTa.prologMatchCompat resv clause.result = true := by
    simpa only [Bool.and_eq_true] using fullCompatibility
  exact resolutionClauseRetained_true_iff argsv resv clause |>.mpr
    ⟨agreement.arity, split.1, split.2⟩

/-- Contrapositive consumed by ranked scan alignment: every executable skip
is an independently certified clause-head rejection, never a lost answer. -/
theorem NormalizedHeadAgrees.no_headResolution_of_rejected
    {branch : ClauseBranch} {argsv : List Atom} {resv : Atom}
    {clause : PLeaTTa.Clause}
    (agreement : NormalizedHeadAgrees branch argsv resv clause)
    (rejected : resolutionClauseRetained argsv resv clause = false) :
    ¬ ∃ result, HeadResolution branch result := by
  intro resolves
  have retained := agreement.retained_of_headResolution resolves
  rw [rejected] at retained
  contradiction

end PLeaTTa.PrologPrefilterBridge
