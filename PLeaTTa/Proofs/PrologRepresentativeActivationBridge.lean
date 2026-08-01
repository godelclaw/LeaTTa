-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologRepresentativeActivationBridge
Purpose: Activate one supported local clause from a representation-independent
  recursive-call payload.
Trusted boundary: none
Main exports:
  SharedCanonicalEquationsAgree,
  OrderedTreeMgu.unifyB_exists_canonical_alpha_mgu
-/
import PLeaTTa.Proofs.PrologRepresentativeCallFrontierBridge
import PLeaTTa.Proofs.PrologActivationUnifierBridge
import PLeaTTa.Proofs.PrologAlphaFreshFrontierBridge

namespace PLeaTTa.PrologRepresentativeActivationBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open PrologGoalAlpha
open PrologGoalMguVariant
open PrologAlphaFreshFrontierBridge
open PrologMguBridge
open PrologMguComposition
open PrologMguDirectSimulation
open PrologMguOpenAgreement
open PrologMguTopology
open PrologMguVariant
open PrologPrefilterBridge
open PrologCallEntryBridge
open PrologCallPayloadBridge
open PrologRecursiveCallPayloadBridge
open PrologStateBridge

/-! ## Canonical equation payloads

`SharedAlphaEquationsAgree` deliberately keeps source `Term`s on its
canonical side.  Recursive calls need a strictly more semantic interface:
their carried independent and executable substitutions may orient a residual
alias differently, so the common payload exists only after applying one
hidden canonical representative.

This relation is the canonical-tree analogue.  It retains the exact ordered
runtime lists and one shared alpha graph, but never asks the hidden
representative to be re-syntaxed as source terms.
-/

/-- One ordered canonical equation family represented by two runtime atom
lists under a single bidirectionally functional alpha graph. -/
inductive SharedCanonicalEquationsAgree
    (alpha : List (LogicVar × String)) :
    List TreeEquation → List Atom → List Atom → Prop where
  | nil : SharedCanonicalEquationsAgree alpha [] [] []
  | cons {leftTree rightTree : Tree} {leftAtom rightAtom : Atom}
      {equations : List TreeEquation}
      {leftAtoms rightAtoms : List Atom}
      (left : CanonicalRuntimeAgrees alpha leftTree leftAtom)
      (right : CanonicalRuntimeAgrees alpha rightTree rightAtom)
      (tail :
        SharedCanonicalEquationsAgree
          alpha equations leftAtoms rightAtoms) :
      SharedCanonicalEquationsAgree alpha
        ((leftTree, rightTree) :: equations)
        (leftAtom :: leftAtoms) (rightAtom :: rightAtoms)

/-- Canonical/runtime agreement is monotone under alpha-graph inclusion. -/
theorem CanonicalRuntimeAgrees.mono
    {smaller larger : List (LogicVar × String)}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    {tree : Tree} {atom : Atom}
    (agreement : CanonicalRuntimeAgrees smaller tree atom) :
    CanonicalRuntimeAgrees larger tree atom := by
  induction agreement with
  | «variable» linked =>
      exact .variable (included _ linked)
  | atom notTrue notFalse =>
      exact .atom notTrue notFalse
  | trueAtom =>
      exact .trueAtom
  | falseAtom =>
      exact .falseAtom
  | integer value =>
      exact .integer value
  | float value =>
      exact .float value
  | string value =>
      exact .string value
  | partialValue arguments inductionHypothesis =>
      exact .partialValue inductionHypothesis
  | nil =>
      exact .nil
  | cons head tail headInduction tailInduction =>
      exact .cons headInduction tailInduction

/-- Pointwise canonical/runtime list agreement is monotone under alpha-graph
inclusion. -/
theorem canonicalRuntimeList_mono
    {smaller larger : List (LogicVar × String)}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger) :
    ∀ {trees : List Tree} {atoms : List Atom},
      List.Forall₂ (CanonicalRuntimeAgrees smaller) trees atoms →
        List.Forall₂ (CanonicalRuntimeAgrees larger) trees atoms
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons head tail =>
      .cons
        (PLeaTTa.PrologRepresentativeActivationBridge.CanonicalRuntimeAgrees.mono
          included head)
        (canonicalRuntimeList_mono included tail)

/-- Denoting a normalized source equation worklist is exactly canonical
application of the denoted carried substitution to the raw worklist. -/
theorem ClauseBranch.denote_normalizedHeadEquations
    (branch : ClauseBranch) :
    denoteEquations branch.normalizedHeadEquations =
      TreeSubstitution.applyEquations
        (Substitution.denote branch.bindings)
        (denoteEquations branch.headEquations) := by
  unfold ClauseBranch.normalizedHeadEquations denoteEquations
    TreeSubstitution.applyEquations
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro equation _member
  rcases equation with ⟨left, right⟩
  simp only [Function.comp_apply]
  rw [Substitution.denote_applyTerm,
    Substitution.denote_applyTerm]

/-! ## Fresh-clause separation from a semantic representative -/

/-- Canonical proper/improper-list construction preserves any structural
variable predicate. -/
theorem Tree.prologList_variablesSatisfy
    {predicate : LogicVar → Prop} :
    ∀ {items : List Tree} {tail : Option Tree},
      TreesVariablesSatisfy predicate items →
      (match tail with
        | none => True
        | some finalTail => TreeVariablesSatisfy predicate finalTail) →
      TreeVariablesSatisfy predicate (Tree.prologList items tail)
  | [], none, _itemsSupported, _tailSupported => by
      simp [Tree.prologList, TreeVariablesSatisfy,
        TreesVariablesSatisfy]
  | [], some tail, _itemsSupported, tailSupported => by
      simpa [Tree.prologList] using tailSupported
  | head :: items, tail, itemsSupported, tailSupported => by
      exact
        ⟨itemsSupported.1,
          ⟨Tree.prologList_variablesSatisfy
              itemsSupported.2 tailSupported, trivial⟩⟩

mutual

/-- A generated-at-or-above source term denotes to a canonical tree all of
whose variables satisfy any predicate known for those generated identities.
This is the reusable bridge from allocator bounds to canonical support. -/
theorem Term.denote_variablesSatisfy_of_generatedAtLeast
    {lower : Nat} {predicate : LogicVar → Prop}
    (generated :
      ∀ index, lower ≤ index → predicate (.generated index)) :
    ∀ (term : Term), term.GeneratedAtLeast lower →
      TreeVariablesSatisfy predicate (Term.denote term)
  | .variable (.generated index), above => generated index above
  | .variable (.source name), above => False.elim above
  | .variable (.anonymous index), above => False.elim above
  | .atom name, _ => by
      simp [Term.denote, TreeVariablesSatisfy, TreesVariablesSatisfy]
  | .integer value, _ => by
      simp [Term.denote, TreeVariablesSatisfy, TreesVariablesSatisfy]
  | .float value, _ => by
      simp [Term.denote, TreeVariablesSatisfy, TreesVariablesSatisfy]
  | .string value, _ => by
      simp [Term.denote, TreeVariablesSatisfy, TreesVariablesSatisfy]
  | .compound functor arguments, above => by
      simpa [Term.denote, TreeVariablesSatisfy] using
        Terms.denote_variablesSatisfy_of_generatedAtLeast
          generated arguments above
  | .list items none, above =>
      Tree.prologList_variablesSatisfy
        (Terms.denote_variablesSatisfy_of_generatedAtLeast
          generated items above)
        trivial
  | .list items (some tail), above =>
      Tree.prologList_variablesSatisfy
        (Terms.denote_variablesSatisfy_of_generatedAtLeast
          generated items above.1)
        (Term.denote_variablesSatisfy_of_generatedAtLeast
          generated tail above.2)

/-- Ordered-list companion of
`Term.denote_variablesSatisfy_of_generatedAtLeast`. -/
theorem Terms.denote_variablesSatisfy_of_generatedAtLeast
    {lower : Nat} {predicate : LogicVar → Prop}
    (generated :
      ∀ index, lower ≤ index → predicate (.generated index)) :
    ∀ (terms : List Term), Terms.GeneratedAtLeast lower terms →
      TreesVariablesSatisfy predicate (Terms.denote terms)
  | [], _ => trivial
  | term :: terms, above =>
      ⟨Term.denote_variablesSatisfy_of_generatedAtLeast
          generated term above.1,
        Terms.denote_variablesSatisfy_of_generatedAtLeast
          generated terms above.2⟩

end

/-- Alpha coverage plus a generated alpha-support bound places every
canonical substitution domain below that bound. -/
theorem TreeSubstitutionVariablesSatisfy.keysGeneratedBelow
    {alpha : List (LogicVar × String)}
    {binding : TreeSubstitution} {lower : Nat}
    (covered :
      TreeSubstitutionVariablesSatisfy (AlphaCovers alpha) binding)
    (alphaBelow :
      GeneratedBelow lower (alpha.map Prod.fst)) :
    ∀ identity, identity ∈ TreeSubstitution.keys binding →
      identity.GeneratedBelowBoundary lower := by
  intro identity member
  obtain ⟨⟨source, replacement⟩, entryMember, entrySource⟩ :=
    List.mem_map.mp
      (show identity ∈ binding.map Prod.fst by
        simpa [TreeSubstitution.keys] using member)
  have sourceEq : source = identity := by
    simpa using entrySource
  subst identity
  have sourceCovered : AlphaCovers alpha source :=
    (covered (source, replacement) entryMember).1
  rcases sourceCovered with ⟨name, linked⟩
  cases source with
  | source sourceName =>
      trivial
  | anonymous anonymousIndex =>
      trivial
  | generated index =>
      exact alphaBelow index
        (List.mem_map.mpr
          ⟨(LogicVar.generated index, name), linked, rfl⟩)

/-- Every source of a stored independent-substitution entry occurs in its
full variable stream. -/
theorem Substitution.source_mem_substitutionVariables
    {entry : LogicVar × Term} {binding : Substitution}
    (member : entry ∈ binding) :
    entry.1 ∈ substitutionVariables binding := by
  induction binding with
  | nil =>
      simp at member
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp member with same | member
      · subst entry
        simp [substitutionVariables]
      · simp [substitutionVariables, inductionHypothesis member]

/-- Canonical denotation changes only replacement representation, never the
ordered substitution domain. -/
theorem Substitution.denote_keys
    (binding : Substitution) :
    TreeSubstitution.keys (Substitution.denote binding) =
      binding.map Prod.fst := by
  induction binding with
  | nil =>
      rfl
  | cons entry tail inductionHypothesis =>
      rcases entry with ⟨source, replacement⟩
      change
        (Substitution.denote tail).map Prod.fst =
          tail.map Prod.fst at inductionHypothesis
      simp [Substitution.denote, TreeSubstitution.keys,
        inductionHypothesis]

/-- An older source-substitution slice included in a bounded cursor binding
has every denoted canonical key below the same generated boundary. -/
theorem Substitution.denote_keysGeneratedBelow_of_subset
    {olderBase cursorBindings : Substitution} {lower : Nat}
    (included :
      ∀ entry, entry ∈ olderBase → entry ∈ cursorBindings)
    (cursorBelow :
      GeneratedBelow lower (substitutionVariables cursorBindings)) :
    ∀ identity,
      identity ∈ TreeSubstitution.keys (Substitution.denote olderBase) →
      identity.GeneratedBelowBoundary lower := by
  intro identity member
  have sourceMember : identity ∈ olderBase.map Prod.fst := by
    simpa [Substitution.denote_keys] using member
  obtain ⟨⟨source, replacement⟩, olderMember, sourceEq⟩ :=
    List.mem_map.mp
      sourceMember
  have exactSource : source = identity := by
    simpa using sourceEq
  subst identity
  cases source with
  | source sourceName =>
      trivial
  | anonymous anonymousIndex =>
      trivial
  | generated index =>
      exact cursorBelow index
        (Substitution.source_mem_substitutionVariables
          (included (LogicVar.generated index, replacement) olderMember))

/-- Canonical list application is exactly pointwise scalar application. -/
theorem TreeSubstitution.applyTrees_eq_map_apply
    (binding : TreeSubstitution) (trees : List Tree) :
    TreeSubstitution.applyTrees binding trees =
      trees.map (TreeSubstitution.apply binding) := by
  induction trees with
  | nil =>
      simp
  | cons tree trees inductionHypothesis =>
      simp [inductionHypothesis]

/-- Ordered denotation is pointwise scalar denotation. -/
theorem Terms.denote_eq_map
    (terms : List Term) :
    Terms.denote terms = terms.map Term.denote := by
  induction terms with
  | nil =>
      rfl
  | cons term terms inductionHypothesis =>
      simp [Terms.denote, inductionHypothesis]

/-- List-level companion of
`TreeSubstitution.apply_eq_self_of_variables_outside`. -/
theorem TreeSubstitution.applyTrees_eq_self_of_variables_outside
    {binding : TreeSubstitution} {trees : List Tree}
    (outside :
      TreesVariablesSatisfy
        (fun identity => identity ∉ TreeSubstitution.keys binding) trees) :
    TreeSubstitution.applyTrees binding trees = trees := by
  induction trees with
  | nil =>
      simp
  | cons tree trees inductionHypothesis =>
      simpa only [TreeSubstitution.applyTrees_cons] using
        congrArg₂ List.cons
          (TreeSubstitution.apply_eq_self_of_variables_outside outside.1)
          (inductionHypothesis outside.2)

/-- Equal-arity canonical pointwise equations are precisely `List.zip`; no
malformed-arity suffix is erased silently. -/
theorem treeEquations_eq_zip_of_length_eq :
    ∀ (left right : List Tree), left.length = right.length →
      treeEquations left right = List.zip left right
  | [], [], _ => rfl
  | [], _ :: _, lengths => by simp at lengths
  | _ :: _, [], lengths => by simp at lengths
  | left :: lefts, right :: rights, lengths => by
      have tailLengths : lefts.length = rights.length := by
        simpa only [List.length_cons, Nat.succ.injEq] using lengths
      simp only [treeEquations, List.zip_cons_cons, List.cons.injEq]
      exact ⟨trivial,
        treeEquations_eq_zip_of_length_eq lefts rights tailLengths⟩

/-- Denoting equal-arity source pointwise equations yields the canonical
pointwise constructor exactly. -/
theorem denoteEquations_argumentEquations_eq_treeEquations
    (left right : List Term) (lengths : left.length = right.length) :
    denoteEquations (argumentEquations left right) =
      treeEquations (Terms.denote left) (Terms.denote right) := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil =>
          rfl
      | cons other others =>
          simp at lengths
  | cons term terms inductionHypothesis =>
      cases right with
      | nil =>
          simp at lengths
      | cons other others =>
          have tailLengths : terms.length = others.length := by
            simpa only [List.length_cons, Nat.succ.injEq] using lengths
          simp only [argumentEquations, denoteEquations, Terms.denote,
            treeEquations, List.map_cons]
          exact congrArg
            (List.cons (Term.denote term, Term.denote other))
            (inductionHypothesis others tailLengths)

/-- Equal-arity source argument equations denote to the exact ordered
canonical zip; no mismatch branch is silently discarded. -/
theorem denoteEquations_argumentEquations_eq_zip :
    ∀ (left right : List Term), left.length = right.length →
      denoteEquations (argumentEquations left right) =
        List.zip (left.map Term.denote) (right.map Term.denote)
  | [], [], _ => by
      rfl
  | [], _ :: _, lengths => by
      simp at lengths
  | _ :: _, [], lengths => by
      simp at lengths
  | left :: lefts, right :: rights, lengths => by
      have tailLengths : lefts.length = rights.length := by
        simpa only [List.length_cons, Nat.succ.injEq] using lengths
      simp only [argumentEquations, denoteEquations, List.map_cons,
        List.zip_cons_cons, List.cons.injEq]
      exact ⟨trivial,
        denoteEquations_argumentEquations_eq_zip
          lefts rights tailLengths⟩

/-- A representative query payload exposes the corresponding pointwise
canonical list without choosing a source substitution spelling. -/
theorem representativeQuery_canonicalRuntimeAgrees
    {alpha : List (LogicVar × String)}
    {representative : TreeSubstitution}
    {terms : List Term} {atoms : List Atom}
    (agreement :
      List.Forall₂
        (fun term atom =>
          CanonicalRuntimeAgrees alpha
            (TreeSubstitution.apply representative (Term.denote term))
            atom)
        terms atoms) :
    List.Forall₂ (CanonicalRuntimeAgrees alpha)
      (terms.map fun term =>
        TreeSubstitution.apply representative (Term.denote term))
      atoms := by
  exact List.forall₂_map_left_iff.mpr agreement

/-- Source alpha agreement exposes its canonical denotation pointwise. -/
theorem AlphaTermsAgree.canonicalRuntimeList
    {alpha : List (LogicVar × String)}
    {terms : List Term} {atoms : List Atom}
    (agreement : AlphaTermsAgree alpha terms atoms) :
    List.Forall₂ (CanonicalRuntimeAgrees alpha)
      (terms.map Term.denote) atoms := by
  induction agreement with
  | nil =>
      exact .nil
  | cons head tail inductionHypothesis =>
      exact .cons
        (PLeaTTa.PrologPrefilterBridge.AlphaTermAgrees.canonicalRuntimeAgrees
          head)
        inductionHypothesis

/-- Pointwise canonical lists induce the exact ordered equation relation.
Equal arity is explicit so `List.zip` cannot silently truncate either side. -/
theorem SharedCanonicalEquationsAgree.of_lists
    {alpha : List (LogicVar × String)}
    {leftTrees rightTrees : List Tree}
    {leftAtoms rightAtoms : List Atom}
    (left :
      List.Forall₂ (CanonicalRuntimeAgrees alpha) leftTrees leftAtoms)
    (right :
      List.Forall₂ (CanonicalRuntimeAgrees alpha) rightTrees rightAtoms)
    (lengths : leftTrees.length = rightTrees.length) :
    SharedCanonicalEquationsAgree alpha
      (List.zip leftTrees rightTrees) leftAtoms rightAtoms := by
  induction left generalizing rightTrees rightAtoms with
  | nil =>
      cases right with
      | nil =>
          exact .nil
      | cons =>
          simp at lengths
  | @cons leftTree leftAtom leftTrees leftAtoms leftHead leftTail
      inductionHypothesis =>
      cases right with
      | nil =>
          simp at lengths
      | @cons rightTree rightAtom rightTrees rightAtoms rightHead rightTail =>
          have tailLengths : leftTrees.length = rightTrees.length := by
            simpa only [List.length_cons, Nat.succ.injEq] using lengths
          exact .cons leftHead rightHead
            (inductionHypothesis rightTail tailLengths)

/-- Canonical variable occurrences are bounded by the structural sizes of
the aligned runtime payload. -/
theorem
    SharedCanonicalEquationsAgree.logicVariables_length_le_runtime_sizes
    {alpha : List (LogicVar × String)}
    {equations : List TreeEquation}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedCanonicalEquationsAgree
        alpha equations leftAtoms rightAtoms) :
    (treeEquationsLogicVariables equations).length ≤
      (leftAtoms.map Atom.size).sum +
        (rightAtoms.map Atom.size).sum := by
  induction agreement with
  | nil =>
      simp [treeEquationsLogicVariables]
  | @cons leftTree rightTree leftAtom rightAtom equations
      leftAtoms rightAtoms left right tail inductionHypothesis =>
      have leftVariableBound :=
        treeLogicVariables_length_le_weight leftTree
      have rightVariableBound :=
        treeLogicVariables_length_le_weight rightTree
      have leftRuntimeBound :=
        PLeaTTa.PrologMguDirectSimulation.CanonicalRuntimeAgrees.weight_le_size
          left
      have rightRuntimeBound :=
        PLeaTTa.PrologMguDirectSimulation.CanonicalRuntimeAgrees.weight_le_size
          right
      simp only [treeEquationsLogicVariables, List.length_append,
        List.map_cons, List.sum_cons]
      omega

/-- The executable expression unifier's fuel covers every distinct variable
in the aligned canonical equation family. -/
theorem SharedCanonicalEquationsAgree.canonical_fuel_le_runtime_fuel
    {alpha : List (LogicVar × String)}
    {equations : List TreeEquation}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedCanonicalEquationsAgree
        alpha equations leftAtoms rightAtoms) :
    (treeEquationsLogicVariables equations).eraseDups.length ≤
      (.expr leftAtoms : Atom).size + (.expr rightAtoms : Atom).size := by
  have dedupBound :=
    logicVar_eraseDups_length_le
      (treeEquationsLogicVariables equations)
  have runtimeBound := agreement.logicVariables_length_le_runtime_sizes
  simp only [Atom.size]
  omega

/-- The semantic relation exposes the exact canonical/runtime zipped
worklists consumed by the verified Robinson-round simulation. -/
theorem SharedCanonicalEquationsAgree.alphaTreeEquationsAgree_zip
    {alpha : List (LogicVar × String)}
    {equations : List TreeEquation}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedCanonicalEquationsAgree
        alpha equations leftAtoms rightAtoms) :
    AlphaTreeEquationsAgree alpha
      equations (List.zip leftAtoms rightAtoms) := by
  induction agreement with
  | nil =>
      exact .nil
  | cons left right tail inductionHypothesis =>
      exact .cons ⟨left, right⟩ inductionHypothesis

/-- Both runtime payloads have exactly the same arity. -/
theorem SharedCanonicalEquationsAgree.runtime_lengths
    {alpha : List (LogicVar × String)}
    {equations : List TreeEquation}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedCanonicalEquationsAgree
        alpha equations leftAtoms rightAtoms) :
    leftAtoms.length = rightAtoms.length := by
  induction agreement with
  | nil =>
      rfl
  | cons left right tail inductionHypothesis =>
      simp only [List.length_cons, Nat.succ.injEq]
      exact inductionHypothesis

/-! ## Direct executable construction from canonical lists -/

/-- A canonical ordered MGU over a semantic equation payload forces the real
executable expression unifier to succeed.  The output retains the complete
topological, valuation, MGU, and mutual-factorization contract; only the
unnecessary source-`Term` intermediate has been removed. -/
theorem OrderedTreeMgu.unifyTopExact_exists_canonical_alpha_mgu
    {alpha : List (LogicVar × String)}
    {equations : List TreeEquation}
    {leftAtoms rightAtoms : List Atom}
    {canonical : TreeSubstitution}
    (shared : SharedRuntimeAlpha alpha)
    (agreement :
      SharedCanonicalEquationsAgree
        alpha equations leftAtoms rightAtoms)
    (derivation : OrderedTreeMgu equations canonical) :
    ∃ flattened runtimeResult,
      PLeaTTa.unifyTopExact
          (.expr leftAtoms) (.expr rightAtoms) =
        some runtimeResult ∧
      AlphaTreeSubstitutionAgrees alpha flattened runtimeResult ∧
      TreeSubstitutionTopological flattened ∧
      Nonempty (PLeaTTa.SubstTopological runtimeResult) ∧
      AlphaValuationAgrees alpha flattened runtimeResult ∧
      TreeIsMgu flattened equations ∧
      TreeFactorsThrough flattened canonical ∧
      TreeFactorsThrough canonical flattened := by
  obtain ⟨flattened, smallRounds⟩ :=
    PLeaTTa.PrologMguDirectSimulation.OrderedTreeMgu.treeUnifyRounds_exists
      derivation
  have rounds :
      TreeUnifyRounds
        ((.expr leftAtoms : Atom).size +
          (.expr rightAtoms : Atom).size)
        equations [] flattened :=
    smallRounds.mono agreement.canonical_fuel_le_runtime_fuel
  have equationsAgreement :
      AlphaTreeEquationsAgree alpha
        equations (List.zip leftAtoms rightAtoms) :=
    agreement.alphaTreeEquationsAgree_zip
  obtain ⟨runtimeResult, runtimeExact, runtimeAgreement⟩ :=
    rounds.runtime shared equationsAgreement
      (AlphaTreeSubstitutionAgrees.nil (alpha := alpha))
  have executableExact :
      PLeaTTa.unifyTopExact
          (.expr leftAtoms) (.expr rightAtoms) =
        some runtimeResult := by
    unfold PLeaTTa.unifyTopExact Metta.Unify.unifyTopWith
    rw [unifyRoundsWith_expression_eq_zip
      PLeaTTa.prologGroundIdentical
      ((.expr leftAtoms : Atom).size +
        (.expr rightAtoms : Atom).size)
      leftAtoms rightAtoms []
      agreement.runtime_lengths]
    exact runtimeExact
  have flattenedMgu : TreeIsMgu flattened equations :=
    rounds.isMostGeneral
  have canonicalMgu : TreeIsMgu canonical equations :=
    derivation.isMostGeneral
  have flattenedTopological :
      TreeSubstitutionTopological flattened :=
    rounds.result_topological TreeSubstitutionTopological.nil
  have runtimeTopological :
      PLeaTTa.SubstTopological runtimeResult :=
    AlphaTreeSubstitutionAgrees.runtime_topological
      shared runtimeAgreement flattenedTopological
  have flattenedValuation :
      AlphaValuationAgrees alpha flattened runtimeResult :=
    AlphaTreeSubstitutionAgrees.valuation
      shared runtimeAgreement flattenedTopological
  exact
    ⟨flattened, runtimeResult, executableExact, runtimeAgreement,
      flattenedTopological, ⟨runtimeTopological⟩, flattenedValuation,
      flattenedMgu,
      canonicalMgu.2 flattened flattenedMgu.1,
      flattenedMgu.2 canonical canonicalMgu.1⟩

/-- Composition through the machine's carried binding preserves the full
canonical-list simulation witness and pins the exact empty/nonempty
installation branch of `unifyB`. -/
theorem OrderedTreeMgu.unifyB_exists_canonical_alpha_mgu
    (base : Subst)
    {alpha : List (LogicVar × String)}
    {equations : List TreeEquation}
    {leftAtoms rightAtoms : List Atom}
    {canonical : TreeSubstitution}
    (shared : SharedRuntimeAlpha alpha)
    (agreement :
      SharedCanonicalEquationsAgree alpha equations
        (leftAtoms.map (PLeaTTa.subst base))
        (rightAtoms.map (PLeaTTa.subst base)))
    (derivation : OrderedTreeMgu equations canonical) :
    ∃ flattened generated installed,
      PLeaTTa.unifyTopExact
          (.expr (leftAtoms.map (PLeaTTa.subst base)))
          (.expr (rightAtoms.map (PLeaTTa.subst base))) =
        some generated ∧
      AlphaTreeSubstitutionAgrees alpha flattened generated ∧
      TreeSubstitutionTopological flattened ∧
      Nonempty (PLeaTTa.SubstTopological generated) ∧
      AlphaValuationAgrees alpha flattened generated ∧
      TreeIsMgu flattened equations ∧
      TreeFactorsThrough flattened canonical ∧
      TreeFactorsThrough canonical flattened ∧
      PLeaTTa.unifyB base (.expr leftAtoms) (.expr rightAtoms) =
        some installed ∧
      installed =
        match generated with
        | [] => base
        | _ :: _ => Metta.Subst.compose generated base := by
  obtain
    ⟨flattened, generated, generatedExact, generatedAgreement,
      flattenedTopological, generatedTopological, generatedValuation,
      flattenedMgu, flattenedFactors, canonicalFactors⟩ :=
    PLeaTTa.PrologRepresentativeActivationBridge.OrderedTreeMgu.unifyTopExact_exists_canonical_alpha_mgu
      shared agreement derivation
  cases generated with
  | nil =>
      refine
        ⟨flattened, [], base, generatedExact, generatedAgreement,
          flattenedTopological, generatedTopological, generatedValuation,
          flattenedMgu, flattenedFactors, canonicalFactors, ?_, rfl⟩
      simp [PLeaTTa.unifyB, PLeaTTa.subst_expr, generatedExact]
  | cons entry generated =>
      let complete := entry :: generated
      let installed := Metta.Subst.compose complete base
      refine
        ⟨flattened, complete, installed, generatedExact,
          generatedAgreement, flattenedTopological, generatedTopological,
          generatedValuation, flattenedMgu, flattenedFactors,
          canonicalFactors, ?_, rfl⟩
      simp [PLeaTTa.unifyB, PLeaTTa.subst_expr,
        complete, installed, generatedExact]

/-! ## Representation-independent retained-clause activation -/

/-- The current ambient alpha graph can be extended by the exact clause-copy
graph selected by one supported prepared occurrence.

The supported occurrence hides the source clause and its independent fresh
seed in `Prop`; eliminating that certificate into data would be unsound.
This proposition instead eliminates it only into the two cross-disjointness
facts required by `SharedRuntimeAlpha.append_of_projection_disjoint`. -/
inductive SupportedPreparedCandidateAgrees.ClauseAlphaMergeSafe
    {callGeneration : Generation} {predicate : String}
    {arguments : List Term} {bindings : Substitution}
    (ambientAlpha : List (LogicVar × String))
    (argsv : List Atom) (result : Atom) (rest : List PLeaTTa.Goal)
    (binding : Subst) (qterm : Atom) (seed : Nat) :
    {branch : ClauseBranch} → {clause : PLeaTTa.Clause} →
      SupportedPreparedCandidateAgrees callGeneration predicate arguments
        bindings branch clause → Prop where
  | intro (reference : VersionedClause) (freshSeed : Nat)
      (executable : PLeaTTa.Clause)
      (base : CandidateClauseAgrees predicate reference executable)
      (encoding :
        OpenBindingAgreement.EncodingInjectiveOn
          reference.clause.variables)
      (bodySupported :
        CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
          reference.clause.variables reference.clause.variables base.body)
      (referenceDisjoint :
        List.Disjoint (ambientAlpha.map Prod.fst)
          ((RuntimeAlpha.graph
            (referenceFreshTargets
              (reference.clause.freshCopy freshSeed).firstFresh
              reference.clause.variables)
            (executableFreshTargets
              (resolutionFreshSuffix argsv result rest binding qterm seed)
              reference.clause.variables)).map Prod.fst))
      (executableDisjoint :
        List.Disjoint (ambientAlpha.map Prod.snd)
          ((RuntimeAlpha.graph
            (referenceFreshTargets
              (reference.clause.freshCopy freshSeed).firstFresh
              reference.clause.variables)
            (executableFreshTargets
              (resolutionFreshSuffix argsv result rest binding qterm seed)
              reference.clause.variables)).map Prod.snd)) :
      ClauseAlphaMergeSafe ambientAlpha argsv result rest binding qterm seed
        (.intro reference freshSeed executable base encoding bodySupported)

/-- The immediate-call freshness discipline constructs merge safety.

All ambient canonical identities lie below the selected clause interval, and
all ambient runtime names are live below the executable suffix seed. -/
theorem SupportedPreparedCandidateAgrees.ClauseAlphaMergeSafe.ofBelow
    {queryAlpha : List (LogicVar × String)}
    {cursor : PreparedCursor} {branch : ClauseBranch}
    {clause : PLeaTTa.Clause}
    {argsv : List Atom} {result : Atom} {rest : List PLeaTTa.Goal}
    {binding : Subst} {qterm : Atom} {seed : Nat}
    (wellFormed : cursor.WellFormed)
    (member : branch ∈ cursor.remaining)
    (agreement :
      SupportedPreparedCandidateAgrees cursor.callGeneration
        cursor.predicate cursor.arguments cursor.bindings branch clause)
    (queryReferenceBelow :
      GeneratedBelow cursor.reservationStart (queryAlpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ queryAlpha.map Prod.snd →
        name ∈
          resolutionOccupiedVars argsv result rest binding qterm)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars argsv result rest binding qterm) ≤ seed) :
    ClauseAlphaMergeSafe queryAlpha argsv result rest binding qterm seed
      agreement := by
  cases agreement with
  | intro reference freshSeed _ base encoding bodySupported =>
      have startsAbove :
          cursor.reservationStart ≤
            (reference.clause.freshCopy freshSeed).firstFresh := by
        have starts := wellFormed.1.start_le_member_first member
        simpa [preparedBranchOf] using starts
      have queryBelowFresh :
          GeneratedBelow
            (reference.clause.freshCopy freshSeed).firstFresh
            (queryAlpha.map Prod.fst) :=
        queryReferenceBelow.mono startsAbove
      let clauseAgreement :=
        freshenClause_alpha_agrees reference.clause freshSeed
          (resolutionFreshSuffix argsv result rest binding qterm seed)
          encoding
      refine .intro reference freshSeed _ base encoding bodySupported ?_ ?_
      · rw [clauseAgreement.graph_reference]
        exact
          referenceFreshTargets_disjoint_of_generatedBelow queryBelowFresh
      · rw [clauseAgreement.graph_executable]
        exact
          executableFreshTargets_disjoint_of_highWater
            argsv result rest binding qterm seed queryExecutableLive highWater

/-- A retained allocator gap derives the exact cross-disjointness required
to merge the selected clause graph.

Unlike `ofBelow`, this theorem permits ambient alpha entries allocated after
the complete retained reservation.  It excludes only the source interval of
the frozen cursor and the executable seed interval of its alternative bank. -/
theorem
    SupportedPreparedCandidateAgrees.ClauseAlphaMergeSafe.ofAllocationGap
    {ambientAlpha : List (LogicVar × String)}
    {cursor : PreparedCursor} {branch : ClauseBranch}
    {clause : PLeaTTa.Clause}
    {argsv : List Atom} {result : Atom} {rest : List PLeaTTa.Goal}
    {binding : Subst} {qterm : Atom} {seed executableEnd : Nat}
    (wellFormed : cursor.WellFormed)
    (member : branch ∈ cursor.remaining)
    (agreement :
      SupportedPreparedCandidateAgrees cursor.callGeneration
        cursor.predicate cursor.arguments cursor.bindings branch clause)
    (gap :
      AlphaAllocationGap ambientAlpha cursor.reservationStart
        cursor.reservedUntil seed executableEnd)
    (seedReserved : seed + 1 ≤ executableEnd) :
    ClauseAlphaMergeSafe ambientAlpha argsv result rest binding qterm seed
      agreement := by
  cases agreement with
  | intro reference freshSeed executable base encoding bodySupported =>
      let clauseAgreement :=
        freshenClause_alpha_agrees reference.clause freshSeed
          (resolutionFreshSuffix argsv result rest binding qterm seed)
          encoding
      have selectedStart :
          cursor.reservationStart ≤
            (reference.clause.freshCopy freshSeed).firstFresh := by
        have starts := wellFormed.1.start_le_member_first member
        simpa [preparedBranchOf] using starts
      have selectedEnd :
          (reference.clause.freshCopy freshSeed).nextFresh ≤
            cursor.reservedUntil := by
        have ends := wellFormed.1.member_next_le_final member
        simpa [preparedBranchOf] using ends
      refine .intro reference freshSeed _ base encoding bodySupported
        ?_ ?_
      · rw [clauseAgreement.graph_reference, List.disjoint_left]
        intro identity ambientMember targetMember
        obtain ⟨index, identityShape, targetLower⟩ :=
          referenceFreshTargets_generated_lower targetMember
        subst identity
        have targetUpper :
            index <
              (reference.clause.freshCopy freshSeed).nextFresh := by
          simpa [reference.clause.freshCopy_next] using
            (referenceFreshTargets_generatedBelow
              (reference.clause.freshCopy freshSeed).firstFresh
              reference.clause.variables index targetMember)
        rcases gap.1 index ambientMember with below | above
        · exact False.elim
            ((Nat.not_lt_of_ge
              (Nat.le_trans selectedStart targetLower)) below)
        · exact False.elim
            ((Nat.not_lt_of_ge
              (Nat.le_trans selectedEnd above)) targetUpper)
      · rw [clauseAgreement.graph_executable, List.disjoint_left]
        intro name ambientMember targetMember
        simp only [executableFreshTargets, List.mem_map] at targetMember
        obtain ⟨source, _sourceMember, targetShape⟩ := targetMember
        have targetWater :
            resolutionSeedHighWaterName name = seed + 1 := by
          rw [← targetShape, resolutionFreshSuffix,
            resolutionSeedHighWaterName_append_compact]
        rcases gap.2 name ambientMember with below | above
        · rw [targetWater] at below
          omega
        · rw [targetWater] at above
          omega

/-- A source-resolved supported clause at the semantic retained frontier
forces the actual executable head unifier to succeed.

The theorem does not choose the same residual alias orientation in the two
implementations.  Instead it transports source unifiability from the actual
cursor binding to the hidden semantic representative, recomputes the
deterministic ordered MGU there, and invokes the verified executable Robinson
simulation.  Its strongest bridge result is the `TreeSubstitutionVariants`
certificate between the exact independent successor and the executable
canonical MGU composed with the same hidden representative. -/
theorem
    SupportedPreparedCandidateAgrees.unifyB_representativeWith_of_headResolution_extension
    {payloadAlpha ambientAlpha : List (LogicVar × String)}
    {cursor : PreparedCursor} {branch : ClauseBranch}
    {clause : PLeaTTa.Clause}
    {args : List Atom} {result : Atom} {rest : List PLeaTTa.Goal}
    {binding : Subst} {qterm : Atom} {seed barrier : Nat}
    {referenceFrontier executableFrontier : Nat}
    {protectedExecutableEnd : Nat}
    {independentResult : Substitution}
    {residualRepresentative : TreeSubstitution}
    {olderBase : Substitution}
    (query :
      RepresentativeNormalizedCallAgreesWith payloadAlpha cursor
        (args.map (PLeaTTa.subst binding))
        (PLeaTTa.subst binding result)
        residualRepresentative olderBase)
    (wellFormed : cursor.WellFormed)
    (member : branch ∈ cursor.remaining)
    (agreement :
      SupportedPreparedCandidateAgrees cursor.callGeneration
        cursor.predicate cursor.arguments cursor.bindings branch clause)
    (arity : clause.params.length = args.length)
    (payloadIncluded :
      ∀ pair, pair ∈ payloadAlpha → pair ∈ ambientAlpha)
    (ambientShared : SharedRuntimeAlpha ambientAlpha)
    (payloadReferenceBelow :
      GeneratedBelow cursor.reservationStart (payloadAlpha.map Prod.fst))
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars
          (args.map (PLeaTTa.subst binding)) result rest binding qterm) ≤
        seed)
    (ambientFresh :
      AlphaFreshFrontier ambientAlpha referenceFrontier executableFrontier)
    (referenceEnd : branch.nextFresh ≤ referenceFrontier)
    (executableEnd : seed + 1 ≤ executableFrontier)
    (ambientGap :
      AlphaAllocationGap ambientAlpha cursor.reservationStart
        cursor.reservedUntil seed protectedExecutableEnd)
    (seedReserved : seed + 1 ≤ protectedExecutableEnd)
    (resolved : HeadResolution branch independentResult) :
    ∃ alpha sourceCanonical representative semanticCanonical
        flattened generated installed,
      SharedRuntimeAlpha alpha ∧
      (∀ pair, pair ∈ ambientAlpha → pair ∈ alpha) ∧
      AlphaExtendsAbove ambientAlpha alpha branch.firstFresh seed ∧
      AlphaFreshFrontier alpha referenceFrontier executableFrontier ∧
      AlphaAllocationGap alpha branch.nextFresh cursor.reservedUntil
        (seed + 1) protectedExecutableEnd ∧
      AlphaGoalsAgree alpha barrier branch.body
        (freshenResolutionClause
          (args.map (PLeaTTa.subst binding)) args result rest binding
          qterm seed barrier clause).body ∧
      representative =
        residualRepresentative ++ Substitution.denote olderBase ∧
      independentResult =
        TreeSubstitution.reify sourceCanonical ++ branch.bindings ∧
      OrderedTreeMgu
        (denoteEquations branch.normalizedHeadEquations) sourceCanonical ∧
      TreeSubstitutionVariants
        (Substitution.denote independentResult)
        (flattened ++ representative) ∧
      OrderedTreeMgu
        (TreeSubstitution.applyEquations representative
          (denoteEquations branch.headEquations))
        semanticCanonical ∧
      SharedCanonicalEquationsAgree alpha
        (TreeSubstitution.applyEquations representative
          (denoteEquations branch.headEquations))
        ((args ++ [result]).map (PLeaTTa.subst binding))
        (((freshenResolutionClause
            (args.map (PLeaTTa.subst binding)) args result rest binding
            qterm seed barrier clause).params ++
          [(freshenResolutionClause
            (args.map (PLeaTTa.subst binding)) args result rest binding
            qterm seed barrier clause).result]).map
          (PLeaTTa.subst binding)) ∧
      PLeaTTa.unifyTopExact
          (.expr ((args ++ [result]).map (PLeaTTa.subst binding)))
          (.expr
            (((freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result]).map
              (PLeaTTa.subst binding))) =
        some generated ∧
      AlphaTreeSubstitutionAgrees alpha flattened generated ∧
      TreeSubstitutionTopological flattened ∧
      Nonempty (PLeaTTa.SubstTopological generated) ∧
      AlphaValuationAgrees alpha flattened generated ∧
      TreeIsMgu flattened
        (TreeSubstitution.applyEquations representative
          (denoteEquations branch.headEquations)) ∧
      TreeFactorsThrough flattened semanticCanonical ∧
      TreeFactorsThrough semanticCanonical flattened ∧
      PLeaTTa.unifyB binding (.expr (args ++ [result]))
          (.expr
            ((freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result])) =
        some installed ∧
      installed =
        match generated with
        | [] => binding
        | _ :: _ => Metta.Subst.compose generated binding := by
  have mergeSafe :
      SupportedPreparedCandidateAgrees.ClauseAlphaMergeSafe ambientAlpha
        (args.map (PLeaTTa.subst binding)) result rest binding qterm seed
        agreement :=
    SupportedPreparedCandidateAgrees.ClauseAlphaMergeSafe.ofAllocationGap
      wellFormed member agreement ambientGap seedReserved
  cases mergeSafe with
  | intro reference freshSeed executable base encoding bodySupported
      referenceDisjoint executableDisjoint =>
      let representative :=
        residualRepresentative ++ Substitution.denote olderBase
      have baseVariants := query.variants
      have residualCovered := query.residualCovered
      have olderBaseIncluded := query.olderBaseIncluded
      have queryArguments := query.arguments
      have startsAbove :
          cursor.reservationStart ≤
            (reference.clause.freshCopy freshSeed).firstFresh := by
        have starts := wellFormed.1.start_le_member_first member
        simpa [preparedBranchOf] using starts
      have queryBelowFresh :
          GeneratedBelow
            (reference.clause.freshCopy freshSeed).firstFresh
            (payloadAlpha.map Prod.fst) :=
        payloadReferenceBelow.mono startsAbove
      have cursorBelowStart :
          GeneratedBelow cursor.reservationStart
            (substitutionVariables cursor.bindings) := by
        intro index indexMember
        exact wellFormed.2.1 index
          (List.mem_append_right _ indexMember)
      have cursorBelowFresh :
          GeneratedBelow
            (reference.clause.freshCopy freshSeed).firstFresh
            (substitutionVariables cursor.bindings) :=
        cursorBelowStart.mono startsAbove
      have residualKeysBelow :
          ∀ identity,
            identity ∈
                TreeSubstitution.keys residualRepresentative →
              identity.GeneratedBelowBoundary
                (reference.clause.freshCopy freshSeed).firstFresh :=
        PLeaTTa.PrologRepresentativeActivationBridge.TreeSubstitutionVariablesSatisfy.keysGeneratedBelow
          residualCovered queryBelowFresh
      have olderKeysBelow :
          ∀ identity,
            identity ∈
                TreeSubstitution.keys
                  (Substitution.denote olderBase) →
              identity.GeneratedBelowBoundary
                (reference.clause.freshCopy freshSeed).firstFresh :=
        Substitution.denote_keysGeneratedBelow_of_subset
          olderBaseIncluded cursorBelowFresh
      have representativeKeysBelow :
          ∀ identity,
            identity ∈ TreeSubstitution.keys representative →
              identity.GeneratedBelowBoundary
                (reference.clause.freshCopy freshSeed).firstFresh := by
        intro identity identityMember
        have split :
            identity ∈ TreeSubstitution.keys residualRepresentative ∨
              identity ∈
                TreeSubstitution.keys (Substitution.denote olderBase) := by
          simpa [representative, TreeSubstitution.keys, List.map_append] using
            identityMember
        rcases split with residualMember | olderMember
        · exact residualKeysBelow identity residualMember
        · exact olderKeysBelow identity olderMember
      have headAgreement :=
        freshCopy_prefilter_head_alpha_agrees base freshSeed
      rcases headAgreement.outputLast with
        ⟨referenceParameters, referenceResult, referenceArguments,
          parameterAgreement, resultAgreement⟩
      have fullClauseAgreement :
          AlphaTermsAgree
            (prefilterAlpha reference.clause freshSeed)
            (reference.clause.freshCopy freshSeed).clause.arguments
            (clause.params ++ [clause.result]) := by
        rw [referenceArguments]
        exact AlphaTermsAgree.append_singleton
          parameterAgreement resultAgreement
      have clauseGenerated :
          Terms.GeneratedAtLeast
            (reference.clause.freshCopy freshSeed).firstFresh
            (reference.clause.freshCopy freshSeed).clause.arguments :=
        AlphaTermsAgree.generatedAtLeast_of_graph
          fullClauseAgreement (prefilterAlpha_generated_range encoding)
      have clauseCanonicalOutside :
          TreesVariablesSatisfy
            (fun identity =>
              identity ∉ TreeSubstitution.keys representative)
            (Terms.denote
              (reference.clause.freshCopy
                freshSeed).clause.arguments) :=
        Terms.denote_variablesSatisfy_of_generatedAtLeast
          (fun index above identityMember =>
            (representativeKeysBelow
              (LogicVar.generated index) identityMember
            ).ne_generated_atLeast above rfl)
          _ clauseGenerated
      have representativeFixesClause :
          TreeSubstitution.applyTrees representative
              (Terms.denote
                (reference.clause.freshCopy freshSeed).clause.arguments) =
            Terms.denote
              (reference.clause.freshCopy
                freshSeed).clause.arguments :=
        TreeSubstitution.applyTrees_eq_self_of_variables_outside
          clauseCanonicalOutside
      have queryLength := queryArguments.length_eq
      have clauseLength := AlphaTermsAgree.length_eq fullClauseAgreement
      have rawLengths :
          cursor.arguments.length =
            (reference.clause.freshCopy
              freshSeed).clause.arguments.length := by
        simp only [List.length_append, List.length_singleton,
          List.length_map] at queryLength clauseLength
        omega
      have normalizedEquations :
          (preparedBranchOf cursor.callGeneration cursor.arguments
              cursor.bindings freshSeed reference).normalizedHeadEquations =
            argumentEquations
              (cursor.bindings.applyTerms cursor.arguments)
              (cursor.bindings.applyTerms
                (reference.clause.freshCopy
                  freshSeed).clause.arguments) :=
        preparedBranchOf_normalizedHeadEquations_eq
          cursor.callGeneration cursor.arguments cursor.bindings freshSeed
          reference rawLengths
      rcases resolved with
        ⟨sourceExtension,
          ⟨sourceCanonical, sourceOrdered, sourceExtensionShape⟩,
          independentShape⟩
      have sourceAppliedMgu :
          TreeIsMgu sourceCanonical
            (TreeSubstitution.applyEquations
              (Substitution.denote cursor.bindings)
              (denoteEquations
                (preparedBranchOf cursor.callGeneration cursor.arguments
                  cursor.bindings freshSeed reference).headEquations)) := by
        have sourceMgu := sourceOrdered.isMostGeneral
        rw [
          PLeaTTa.PrologRepresentativeActivationBridge.ClauseBranch.denote_normalizedHeadEquations
            (preparedBranchOf cursor.callGeneration cursor.arguments
              cursor.bindings freshSeed reference)] at sourceMgu
        simpa [preparedBranchOf] using sourceMgu
      have representativeHasUnifier :
          ∃ candidate,
            TreeUnifiesEquations candidate
              (TreeSubstitution.applyEquations representative
                (denoteEquations
                  (preparedBranchOf cursor.callGeneration cursor.arguments
                    cursor.bindings freshSeed reference).headEquations)) :=
        (PrologSequentialMgu.TreeSubstitutionVariants.applied_has_unifier_iff
          baseVariants
          (denoteEquations
            (preparedBranchOf cursor.callGeneration cursor.arguments
              cursor.bindings freshSeed reference).headEquations)).1
          ⟨sourceCanonical, sourceAppliedMgu.1⟩
      obtain ⟨semanticCandidate, semanticUnifies⟩ :=
        representativeHasUnifier
      obtain ⟨semanticCanonical, semanticOrdered⟩ :=
        OrderedTreeMgu.complete semanticCandidate semanticUnifies
      have semanticMgu := semanticOrdered.isMostGeneral
      let clauseAlpha :=
        RuntimeAlpha.graph
          (referenceFreshTargets
            (reference.clause.freshCopy freshSeed).firstFresh
            reference.clause.variables)
          (executableFreshTargets
            (resolutionFreshSuffix
              (args.map (PLeaTTa.subst binding)) result rest binding
              qterm seed)
            reference.clause.variables)
      let alpha := ambientAlpha ++ clauseAlpha
      let clauseAgreement :=
        freshenClause_alpha_agrees reference.clause freshSeed
          (resolutionFreshSuffix
            (args.map (PLeaTTa.subst binding)) result rest binding qterm
            seed)
          encoding
      have combinedShared : SharedRuntimeAlpha alpha := by
        have clauseShared : SharedRuntimeAlpha clauseAlpha := by
          exact RuntimeAlpha.graph_shared clauseAgreement
        have cross :
            List.Disjoint (ambientAlpha.map Prod.fst)
                (clauseAlpha.map Prod.fst) ∧
              List.Disjoint (ambientAlpha.map Prod.snd)
                (clauseAlpha.map Prod.snd) := by
          exact ⟨referenceDisjoint, executableDisjoint⟩
        exact ambientShared.append_of_projection_disjoint clauseShared
          cross.1 cross.2
      have queryIncluded :
          ∀ pair, pair ∈ ambientAlpha → pair ∈ alpha := by
        intro pair pairMember
        exact List.mem_append_left clauseAlpha pairMember
      have extensionAbove :
          AlphaExtendsAbove ambientAlpha alpha
            (reference.clause.freshCopy freshSeed).firstFresh seed := by
        refine ⟨clauseAlpha, rfl, ?_, ?_, ?_⟩
        · intro identity name pairMember
          have targetMember : identity ∈ clauseAlpha.map Prod.fst :=
            List.mem_map.mpr ⟨(identity, name), pairMember, rfl⟩
          rw [clauseAgreement.graph_reference] at targetMember
          obtain ⟨index, targetShape, _targetLower⟩ :=
            referenceFreshTargets_generated_lower targetMember
          exact ⟨index, targetShape⟩
        · intro index targetMember
          rw [clauseAgreement.graph_reference] at targetMember
          obtain ⟨targetIndex, targetShape, targetLower⟩ :=
            referenceFreshTargets_generated_lower targetMember
          injection targetShape with indexEq
          simpa [indexEq] using targetLower
        · intro name targetMember
          rw [clauseAgreement.graph_executable] at targetMember
          simp only [executableFreshTargets, List.mem_map] at targetMember
          obtain ⟨source, _sourceMember, targetShape⟩ := targetMember
          rw [← targetShape, resolutionFreshSuffix,
            resolutionSeedHighWaterName_append_compact]
          omega
      have clauseFresh :
          AlphaFreshFrontier clauseAlpha
            (reference.clause.freshCopy freshSeed).nextFresh
            (seed + 1) := by
        simpa [clauseAlpha, resolutionFreshSuffix,
          reference.clause.freshCopy_next] using
          (clauseAlpha_freshFrontier
            (reference.clause.freshCopy freshSeed).firstFresh seed
            reference.clause.variables)
      have combinedFresh :
          AlphaFreshFrontier alpha
            referenceFrontier executableFrontier := by
        exact AlphaFreshFrontier.append
          ambientFresh
          (clauseFresh.mono
            (by simpa [preparedBranchOf] using referenceEnd)
            executableEnd)
      have referenceAdvance :
          cursor.reservationStart ≤
            (preparedBranchOf cursor.callGeneration cursor.arguments
              cursor.bindings freshSeed reference).nextFresh := by
        exact Nat.le_trans
          (wellFormed.1.start_le_member_first member)
          (wellFormed.1.member_first_le_next member)
      have ambientNextGap :
          AlphaAllocationGap ambientAlpha
            (preparedBranchOf cursor.callGeneration cursor.arguments
              cursor.bindings freshSeed reference).nextFresh
            cursor.reservedUntil (seed + 1) protectedExecutableEnd :=
        ambientGap.advance referenceAdvance (Nat.le_succ seed)
      have clauseNextGap :
          AlphaAllocationGap clauseAlpha
            (preparedBranchOf cursor.callGeneration cursor.arguments
              cursor.bindings freshSeed reference).nextFresh
            cursor.reservedUntil (seed + 1) protectedExecutableEnd := by
        apply AlphaAllocationGap.of_frontier
        simpa [preparedBranchOf] using clauseFresh
      have combinedGap :
          AlphaAllocationGap alpha
            (preparedBranchOf cursor.callGeneration cursor.arguments
              cursor.bindings freshSeed reference).nextFresh
            cursor.reservedUntil (seed + 1) protectedExecutableEnd :=
        ambientNextGap.append clauseNextGap
      have bodyAgreement :=
        freshenClause_body_alpha_agrees
          base bodySupported freshSeed
          (args.map (PLeaTTa.subst binding)) args result rest binding
          qterm seed barrier
      have bodyControl :
          AlphaGoalsAgree alpha barrier
            (reference.clause.freshCopy freshSeed).clause.body
            (freshenResolutionClause
              (args.map (PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).body := by
        have enlarged :=
          PLeaTTa.PrologGoalMguVariant.AlphaGoalsAgree.mono
            (fun pair pairMember =>
              List.mem_append_right ambientAlpha pairMember)
            bodyAgreement
        simpa [alpha, clauseAlpha, preparedBranchOf] using enlarged
      have queryCanonicalSmall :
          List.Forall₂ (CanonicalRuntimeAgrees payloadAlpha)
            (cursor.arguments.map fun term =>
              TreeSubstitution.apply representative (Term.denote term))
            (args.map (PLeaTTa.subst binding) ++
              [PLeaTTa.subst binding result]) :=
        representativeQuery_canonicalRuntimeAgrees queryArguments
      have queryCanonical :
          List.Forall₂ (CanonicalRuntimeAgrees alpha)
            (cursor.arguments.map fun term =>
              TreeSubstitution.apply representative (Term.denote term))
            ((args ++ [result]).map (PLeaTTa.subst binding)) := by
        have enlarged :
            List.Forall₂ (CanonicalRuntimeAgrees alpha)
              (cursor.arguments.map fun term =>
                TreeSubstitution.apply representative (Term.denote term))
              (args.map (PLeaTTa.subst binding) ++
                [PLeaTTa.subst binding result]) := by
          exact canonicalRuntimeList_mono
            (fun pair pairMember =>
              List.mem_append_left clauseAlpha
                (payloadIncluded pair pairMember))
            queryCanonicalSmall
        simpa only [List.map_append, List.map_singleton] using enlarged
      have freshened :=
        freshenClause_actual_alpha_agrees
          base encoding freshSeed
          (args.map (PLeaTTa.subst binding)) args result rest binding qterm
          seed barrier
      rcases freshened.headPayload.outputLast with
        ⟨freshParameters, freshResult, freshArguments,
          freshParameterAgreement, freshResultAgreement⟩
      have freshClauseTerms :
          AlphaTermsAgree clauseAlpha
            (reference.clause.freshCopy freshSeed).clause.arguments
            ((freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result]) := by
        rw [freshArguments]
        simpa [clauseAlpha] using
          AlphaTermsAgree.append_singleton
            freshParameterAgreement freshResultAgreement
      have clauseCanonicalSmall :=
        PLeaTTa.PrologRepresentativeActivationBridge.AlphaTermsAgree.canonicalRuntimeList
          freshClauseTerms
      have clauseCanonical :
          List.Forall₂ (CanonicalRuntimeAgrees alpha)
            ((reference.clause.freshCopy
              freshSeed).clause.arguments.map Term.denote)
            ((freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result]) := by
        exact canonicalRuntimeList_mono
          (fun pair pairMember =>
            List.mem_append_right ambientAlpha pairMember)
          clauseCanonicalSmall
      have stableExecutable :=
        subst_freshenResolutionClause_head_eq_self
          (args.map (PLeaTTa.subst binding)) args result rest binding qterm
          seed barrier highWater clause
      have canonicalHeadAgreement :
          SharedCanonicalEquationsAgree alpha
            (treeEquations
              (TreeSubstitution.applyTrees representative
                (Terms.denote cursor.arguments))
              (Terms.denote
                (reference.clause.freshCopy
                  freshSeed).clause.arguments))
            ((args ++ [result]).map (PLeaTTa.subst binding))
            (((freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result]).map
              (PLeaTTa.subst binding)) := by
        rw [treeEquations_eq_zip_of_length_eq]
        · have canonicalLengths :
              (cursor.arguments.map fun term =>
                TreeSubstitution.apply representative
                  (Term.denote term)).length =
                ((reference.clause.freshCopy
                  freshSeed).clause.arguments.map Term.denote).length := by
            simpa only [List.length_map] using rawLengths
          have zipped :=
            SharedCanonicalEquationsAgree.of_lists
              queryCanonical clauseCanonical canonicalLengths
          simpa [TreeSubstitution.applyTrees_eq_map_apply,
            Terms.denote_eq_map, Function.comp_def, stableExecutable.1,
            stableExecutable.2] using zipped
        · simpa only [TreeSubstitution.applyTrees_length,
            Terms.denote_eq_map, List.length_map] using rawLengths
      have rawEquationShape :
          denoteEquations
              (preparedBranchOf cursor.callGeneration cursor.arguments
                cursor.bindings freshSeed reference).headEquations =
            treeEquations (Terms.denote cursor.arguments)
              (Terms.denote
                (reference.clause.freshCopy
                  freshSeed).clause.arguments) := by
        simpa [preparedBranchOf] using
          denoteEquations_argumentEquations_eq_treeEquations
            cursor.arguments
            (reference.clause.freshCopy
              freshSeed).clause.arguments rawLengths
      have semanticEquationShape :
          TreeSubstitution.applyEquations representative
              (denoteEquations
                (preparedBranchOf cursor.callGeneration cursor.arguments
                  cursor.bindings freshSeed reference).headEquations) =
            treeEquations
              (TreeSubstitution.applyTrees representative
                (Terms.denote cursor.arguments))
              (Terms.denote
                (reference.clause.freshCopy
                  freshSeed).clause.arguments) := by
        rw [rawEquationShape,
          TreeSubstitution.applyEquations_treeEquations
            representative]
        · rw [representativeFixesClause]
        · simpa only [Terms.denote_eq_map, List.length_map] using rawLengths
      have equationAgreement :
          SharedCanonicalEquationsAgree alpha
            (TreeSubstitution.applyEquations representative
              (denoteEquations
                (preparedBranchOf cursor.callGeneration cursor.arguments
                  cursor.bindings freshSeed reference).headEquations))
            ((args ++ [result]).map (PLeaTTa.subst binding))
            (((freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result]).map
              (PLeaTTa.subst binding)) := by
        rw [semanticEquationShape]
        exact canonicalHeadAgreement
      obtain
        ⟨flattened, generated, installed, generatedExact,
          generatedAgreement, flattenedTopological, generatedTopological,
          generatedValuation, flattenedMgu, flattenedFactors,
          semanticFactors, installedExact, installedShape⟩ :=
        PLeaTTa.PrologRepresentativeActivationBridge.OrderedTreeMgu.unifyB_exists_canonical_alpha_mgu
          binding combinedShared equationAgreement semanticOrdered
      have sourceSemanticVariants :
          TreeSubstitutionVariants
            (sourceCanonical ++ Substitution.denote cursor.bindings)
            (semanticCanonical ++ representative) :=
        PLeaTTa.PrologSequentialMgu.sequential_mgu_composites_are_variants
          baseVariants sourceAppliedMgu semanticMgu
      have semanticFlattenedVariants :
          TreeSubstitutionVariants
            (semanticCanonical ++ representative)
            (flattened ++ representative) :=
        PLeaTTa.PrologSequentialMgu.sequential_mgu_composites_are_variants
          (TreeSubstitutionVariants.refl representative)
          semanticMgu flattenedMgu
      have independentDenote :
          Substitution.denote independentResult =
            sourceCanonical ++ Substitution.denote cursor.bindings := by
        rw [independentShape, sourceExtensionShape,
          Substitution.denote_append,
          TreeSubstitution.denote_reify
            (sourceOrdered.binding_wellFormed
              (denoteEquations_wellFormed
                (preparedBranchOf cursor.callGeneration cursor.arguments
                  cursor.bindings freshSeed reference
                ).normalizedHeadEquations))]
        simp [preparedBranchOf]
      have successorVariants :
          TreeSubstitutionVariants
            (Substitution.denote independentResult)
            (flattened ++ representative) := by
        rw [independentDenote]
        exact sourceSemanticVariants.trans semanticFlattenedVariants
      exact
        ⟨alpha, sourceCanonical, representative, semanticCanonical,
          flattened, generated, installed, combinedShared,
          queryIncluded, by simpa [preparedBranchOf] using extensionAbove,
          by simpa [preparedBranchOf] using combinedFresh,
          by simpa [preparedBranchOf] using combinedGap,
          by simpa [preparedBranchOf] using bodyControl,
          rfl,
          by simpa [sourceExtensionShape] using independentShape,
          sourceOrdered, successorVariants, semanticOrdered,
          equationAgreement, generatedExact, generatedAgreement,
          flattenedTopological, generatedTopological, generatedValuation,
          flattenedMgu, flattenedFactors, semanticFactors,
          installedExact, installedShape⟩

/-- Immediate-call specialization of
`unifyB_representativeWith_of_headResolution_extension`.

When the payload graph is still the ambient graph, the original below/live
high-water premises derive both cross-disjointness and the exact post-copy
frontier.  Existing activation callers therefore keep the original API. -/
theorem
    SupportedPreparedCandidateAgrees.unifyB_representativeWith_of_headResolution
    {queryAlpha : List (LogicVar × String)}
    {cursor : PreparedCursor} {branch : ClauseBranch}
    {clause : PLeaTTa.Clause}
    {args : List Atom} {result : Atom} {rest : List PLeaTTa.Goal}
    {binding : Subst} {qterm : Atom} {seed barrier : Nat}
    {independentResult : Substitution}
    {residualRepresentative : TreeSubstitution}
    {olderBase : Substitution}
    (query :
      RepresentativeNormalizedCallAgreesWith queryAlpha cursor
        (args.map (PLeaTTa.subst binding))
        (PLeaTTa.subst binding result)
        residualRepresentative olderBase)
    (wellFormed : cursor.WellFormed)
    (member : branch ∈ cursor.remaining)
    (agreement :
      SupportedPreparedCandidateAgrees cursor.callGeneration
        cursor.predicate cursor.arguments cursor.bindings branch clause)
    (arity : clause.params.length = args.length)
    (queryShared : SharedRuntimeAlpha queryAlpha)
    (queryReferenceBelow :
      GeneratedBelow cursor.reservationStart (queryAlpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ queryAlpha.map Prod.snd →
        name ∈
          resolutionOccupiedVars
            (args.map (PLeaTTa.subst binding)) result rest binding qterm)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars
          (args.map (PLeaTTa.subst binding)) result rest binding qterm) ≤
        seed)
    (resolved : HeadResolution branch independentResult) :
    ∃ alpha sourceCanonical representative semanticCanonical
        flattened generated installed,
      SharedRuntimeAlpha alpha ∧
      (∀ pair, pair ∈ queryAlpha → pair ∈ alpha) ∧
      AlphaFreshFrontier alpha branch.nextFresh (seed + 1) ∧
      AlphaGoalsAgree alpha barrier branch.body
        (freshenResolutionClause
          (args.map (PLeaTTa.subst binding)) args result rest binding
          qterm seed barrier clause).body ∧
      representative =
        residualRepresentative ++ Substitution.denote olderBase ∧
      independentResult =
        TreeSubstitution.reify sourceCanonical ++ branch.bindings ∧
      OrderedTreeMgu
        (denoteEquations branch.normalizedHeadEquations) sourceCanonical ∧
      TreeSubstitutionVariants
        (Substitution.denote independentResult)
        (flattened ++ representative) ∧
      OrderedTreeMgu
        (TreeSubstitution.applyEquations representative
          (denoteEquations branch.headEquations))
        semanticCanonical ∧
      SharedCanonicalEquationsAgree alpha
        (TreeSubstitution.applyEquations representative
          (denoteEquations branch.headEquations))
        ((args ++ [result]).map (PLeaTTa.subst binding))
        (((freshenResolutionClause
            (args.map (PLeaTTa.subst binding)) args result rest binding
            qterm seed barrier clause).params ++
          [(freshenResolutionClause
            (args.map (PLeaTTa.subst binding)) args result rest binding
            qterm seed barrier clause).result]).map
          (PLeaTTa.subst binding)) ∧
      PLeaTTa.unifyTopExact
          (.expr ((args ++ [result]).map (PLeaTTa.subst binding)))
          (.expr
            (((freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result]).map
              (PLeaTTa.subst binding))) =
        some generated ∧
      AlphaTreeSubstitutionAgrees alpha flattened generated ∧
      TreeSubstitutionTopological flattened ∧
      Nonempty (PLeaTTa.SubstTopological generated) ∧
      AlphaValuationAgrees alpha flattened generated ∧
      TreeIsMgu flattened
        (TreeSubstitution.applyEquations representative
          (denoteEquations branch.headEquations)) ∧
      TreeFactorsThrough flattened semanticCanonical ∧
      TreeFactorsThrough semanticCanonical flattened ∧
      PLeaTTa.unifyB binding (.expr (args ++ [result]))
          (.expr
            ((freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result])) =
        some installed ∧
      installed =
        match generated with
        | [] => binding
        | _ :: _ => Metta.Subst.compose generated binding := by
  cases agreement with
  | intro reference freshSeed _ base encoding bodySupported =>
      have startsAbove :
          cursor.reservationStart ≤
            (reference.clause.freshCopy freshSeed).firstFresh := by
        have starts := wellFormed.1.start_le_member_first member
        simpa [preparedBranchOf] using starts
      have queryBelowFresh :
          GeneratedBelow
            (reference.clause.freshCopy freshSeed).firstFresh
            (queryAlpha.map Prod.fst) :=
        queryReferenceBelow.mono startsAbove
      have queryEnd :
          cursor.reservationStart ≤
            (reference.clause.freshCopy freshSeed).nextFresh := by
        exact Nat.le_trans startsAbove (by
          rw [reference.clause.freshCopy_next]
          exact Nat.le_add_right _ _)
      have queryFresh :
          AlphaFreshFrontier queryAlpha
            (preparedBranchOf cursor.callGeneration cursor.arguments
              cursor.bindings freshSeed reference).nextFresh
            (seed + 1) := by
        constructor
        · simpa [preparedBranchOf] using
            queryReferenceBelow.mono queryEnd
        · exact Nat.le_trans
            (Nat.le_trans
              (resolutionSeedHighWaterNames_le_of_subset
                queryExecutableLive)
              highWater)
            (Nat.le_add_right seed 1)
      have supported :
          SupportedPreparedCandidateAgrees cursor.callGeneration
            cursor.predicate cursor.arguments cursor.bindings
            (preparedBranchOf cursor.callGeneration cursor.arguments
              cursor.bindings freshSeed reference)
            clause :=
        .intro reference freshSeed clause base encoding bodySupported
      have queryLowFrontier :
          AlphaFreshFrontier queryAlpha cursor.reservationStart seed := by
        constructor
        · exact queryReferenceBelow
        · exact Nat.le_trans
            (resolutionSeedHighWaterNames_le_of_subset
              queryExecutableLive)
            highWater
      have queryGap :
          AlphaAllocationGap queryAlpha cursor.reservationStart
            cursor.reservedUntil seed (seed + 1) :=
        AlphaAllocationGap.of_frontier queryLowFrontier
      obtain
        ⟨alpha, sourceCanonical, representative, semanticCanonical,
          flattened, generated, installed, resultBundle⟩ :=
        PLeaTTa.PrologRepresentativeActivationBridge.SupportedPreparedCandidateAgrees.unifyB_representativeWith_of_headResolution_extension
          query wellFormed member supported
          arity (fun _ member => member) queryShared queryReferenceBelow
          highWater queryFresh (Nat.le_refl _) (Nat.le_refl _) queryGap
          (Nat.le_refl _) resolved
      exact
        ⟨alpha, sourceCanonical, representative, semanticCanonical,
          flattened, generated, installed, resultBundle.1,
          resultBundle.2.1, resultBundle.2.2.2.1,
          resultBundle.2.2.2.2.2⟩

/-- Existential compatibility view of
`unifyB_representativeWith_of_headResolution`.

The fixed theorem above is the compositional API.  This wrapper preserves the
earlier statement for callers which need only head-success existence. -/
theorem
    SupportedPreparedCandidateAgrees.unifyB_representative_of_headResolution
    {queryAlpha : List (LogicVar × String)}
    {cursor : PreparedCursor} {branch : ClauseBranch}
    {clause : PLeaTTa.Clause}
    {args : List Atom} {result : Atom} {rest : List PLeaTTa.Goal}
    {binding : Subst} {qterm : Atom} {seed barrier : Nat}
    {independentResult : Substitution}
    (query :
      RepresentativeNormalizedCallAgrees queryAlpha cursor
        (args.map (PLeaTTa.subst binding))
        (PLeaTTa.subst binding result))
    (wellFormed : cursor.WellFormed)
    (member : branch ∈ cursor.remaining)
    (agreement :
      SupportedPreparedCandidateAgrees cursor.callGeneration
        cursor.predicate cursor.arguments cursor.bindings branch clause)
    (arity : clause.params.length = args.length)
    (queryShared : SharedRuntimeAlpha queryAlpha)
    (queryReferenceBelow :
      GeneratedBelow cursor.reservationStart (queryAlpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ queryAlpha.map Prod.snd →
        name ∈
          resolutionOccupiedVars
            (args.map (PLeaTTa.subst binding)) result rest binding qterm)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars
          (args.map (PLeaTTa.subst binding)) result rest binding qterm) ≤
        seed)
    (resolved : HeadResolution branch independentResult) :
    ∃ alpha sourceCanonical representative semanticCanonical
        flattened generated installed,
      SharedRuntimeAlpha alpha ∧
      independentResult =
        TreeSubstitution.reify sourceCanonical ++ branch.bindings ∧
      OrderedTreeMgu
        (denoteEquations branch.normalizedHeadEquations) sourceCanonical ∧
      TreeSubstitutionVariants
        (Substitution.denote independentResult)
        (flattened ++ representative) ∧
      OrderedTreeMgu
        (TreeSubstitution.applyEquations representative
          (denoteEquations branch.headEquations))
        semanticCanonical ∧
      SharedCanonicalEquationsAgree alpha
        (TreeSubstitution.applyEquations representative
          (denoteEquations branch.headEquations))
        ((args ++ [result]).map (PLeaTTa.subst binding))
        (((freshenResolutionClause
            (args.map (PLeaTTa.subst binding)) args result rest binding
            qterm seed barrier clause).params ++
          [(freshenResolutionClause
            (args.map (PLeaTTa.subst binding)) args result rest binding
            qterm seed barrier clause).result]).map
          (PLeaTTa.subst binding)) ∧
      PLeaTTa.unifyTopExact
          (.expr ((args ++ [result]).map (PLeaTTa.subst binding)))
          (.expr
            (((freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result]).map
              (PLeaTTa.subst binding))) =
        some generated ∧
      AlphaTreeSubstitutionAgrees alpha flattened generated ∧
      TreeSubstitutionTopological flattened ∧
      Nonempty (PLeaTTa.SubstTopological generated) ∧
      AlphaValuationAgrees alpha flattened generated ∧
      TreeIsMgu flattened
        (TreeSubstitution.applyEquations representative
          (denoteEquations branch.headEquations)) ∧
      TreeFactorsThrough flattened semanticCanonical ∧
      TreeFactorsThrough semanticCanonical flattened ∧
      PLeaTTa.unifyB binding (.expr (args ++ [result]))
          (.expr
            ((freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result])) =
        some installed ∧
      installed =
        match generated with
        | [] => binding
        | _ :: _ => Metta.Subst.compose generated binding := by
  obtain ⟨residualRepresentative, olderBase, exactQuery⟩ :=
    query.existsWith
  obtain
    ⟨alpha, sourceCanonical, representative, semanticCanonical,
      flattened, generated, installed, shared, _queryIncluded,
      _freshFrontier, _bodyControl, _representativeExact, tail⟩ :=
    PLeaTTa.PrologRepresentativeActivationBridge.SupportedPreparedCandidateAgrees.unifyB_representativeWith_of_headResolution
      exactQuery wellFormed member agreement arity queryShared
      queryReferenceBelow queryExecutableLive highWater resolved
  exact
    ⟨alpha, sourceCanonical, representative, semanticCanonical,
      flattened, generated, installed, shared, tail⟩

/-! ## Anti-vacuity: the representative must stay below the reservation -/

private def captureWitnessIdentity : LogicVar := .generated 7

private def captureWitnessRepresentative : TreeSubstitution :=
  [(captureWitnessIdentity, .node (.atom "captured") [])]

/-- If the hidden representative is allowed to own a freshly reserved clause
variable, applying it changes that clause variable before head unification.
This concrete capture rejects dropping the alpha-coverage/below-reservation
premise used by `unifyB_representative_of_headResolution`. -/
theorem uncovered_representative_can_capture_reserved_variable :
    TreeSubstitution.apply captureWitnessRepresentative
        (.variable captureWitnessIdentity) ≠
      .variable captureWitnessIdentity := by
  simp [captureWitnessRepresentative, captureWitnessIdentity,
    TreeSubstitution.apply, Tree.instantiateOne]

end PLeaTTa.PrologRepresentativeActivationBridge
