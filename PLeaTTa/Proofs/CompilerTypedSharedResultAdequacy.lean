/-
Module: PLeaTTa.Proofs.CompilerTypedSharedResultAdequacy
Purpose: Relate PLeaTTa's executable typed-output resolution to the
  independent semantic MGU specification.
Trusted boundary: none
Main exports: unifyTopExact_fresh_variable,
  resolveTypedSharedResult_two_unary_partial,
  bindTypedSharedResult_initial_adequate
-/
import PLeaTTa.PeTTaSpec.TypedSharedResult
import PLeaTTa.Proofs.OpenBindingAgreement
import PLeaTTa.Proofs.PrologCoreAdequacy
import PLeaTTa.Proofs.CompilerTypedBranchAdequacy

namespace PLeaTTa.CompilerTypedSharedResultAdequacy

open Metta (Atom Subst)
open PLeaTTa.CompilerAdequacy
open PLeaTTa.CompilerTypedBranchAdequacy
open PLeaTTa.OpenBindingAgreement
open PLeaTTa.PeTTaSpec.PrologCore
open PLeaTTa.PeTTaSpec.PrologCore.OpenSubstitution
open PLeaTTa.PeTTaSpec.PrologCore.TypedSharedResult

/-- Boolean occurs-check rejection implies absence from the executable
syntactic variable list.  This direction is kept explicit because the
finite-tree premise is load-bearing at the PeTTa/SWI anchoring seam. -/
theorem not_mem_vars_of_occurs_eq_false (name : String) (atom : Atom)
    (occurs : Metta.Subst.occurs name atom = false) :
    name ∉ atom.vars := by
  induction atom with
  | sym symbol => simp [Atom.vars]
  | var variableName =>
      simpa [Metta.Subst.occurs, Atom.vars] using occurs
  | gnd ground => simp [Atom.vars]
  | expr atoms induction =>
      simp only [Metta.Subst.occurs] at occurs
      simp only [Atom.vars]
      rw [List.mem_flatten]
      intro member
      rcases member with ⟨variableList, variableListMember, nameMember⟩
      rcases List.mem_map.mp variableListMember with
        ⟨child, childMember, rfl⟩
      have childOccurs : Metta.Subst.occurs name child = false := by
        have all := List.any_eq_false.mp occurs
        simpa only [Bool.not_eq_true] using
          (all ⟨child, childMember⟩ (by simp))
      exact induction child childMember childOccurs nameMember

/-- A fresh executable variable is eliminated to its target by the exact
PeTTa wrapper.  This theorem proves success; it does not assume an underlying
unifier result. -/
theorem unifyTopExact_fresh_variable (fresh : String) (target : Atom)
    (occurs : Metta.Subst.occurs fresh target = false) :
    unifyTopExact (.var fresh) target = some [(fresh, target)] := by
  have underlying : Metta.Unify.unifyTopWith prologGroundIdentical
      (.var fresh) target =
      some [(fresh, target)] :=
    PLeaTTa.PrologCoreAdequacy.unifyTopWith_fresh_variable
      prologGroundIdentical fresh target occurs
  have freshForTarget : fresh ∉ target.vars :=
    not_mem_vars_of_occurs_eq_false fresh target occurs
  have topological : SubstTopological [(fresh, target)] :=
    SubstTopological.cons_of_fresh [] emptySubstTopological fresh target
      (by simp [Metta.Subst.lookup]) freshForTarget
      (by simp [AtomAvoids, Metta.Subst.lookup])
  have lookup : Metta.Subst.lookup [(fresh, target)] fresh = some target := by
    simp [Metta.Subst.lookup]
  have exact : subst [(fresh, target)] (.var fresh) =
      subst [(fresh, target)] target :=
    topological.subst_var_of_lookup [(fresh, target)] fresh target lookup
  exact unifyTopExact_of_underlying_exact (.var fresh) target
    [(fresh, target)] underlying exact

/-- The exact executable unifier succeeds constructively on the first
nontrivial later-branch shape: same-headed unary `partial/2` values whose
only differing arguments are distinct variables.  The returned orientation
is the structural unifier's left-to-right elimination choice; no success
hypothesis or semantic witness is assumed. -/
theorem unifyTopExact_unary_partial_alias (head left right : String)
    (different : left ≠ right) :
    unifyTopExact (partialValue head [.var left])
      (partialValue head [.var right]) = some [(left, .var right)] := by
  unfold partialValue partialC partialTagA chainOf consC nilA unifyTopExact
  simp [Metta.Unify.unifyTopWith, Atom.size,
    Metta.Unify.unifyRoundsWith,
    Metta.Unify.decomposeAllWith, Metta.Unify.decomposeEqWith,
    Metta.Unify.decomposeListWith, different,
    Metta.Subst.occurs, Metta.Subst.extend, Metta.Subst.erase]

/-- After the first incomplete branch has bound `output` to one unary
partial value, a compatible later branch succeeds, aliases the differing
argument left-to-right, and composes that alias through the earlier value.
This is the concrete executable counterpart of
`two_unary_partial_branches_is_mgu`. -/
theorem bindTypedSharedResult_after_unary_partial
    (head output left right : String)
    (outputNeLeft : output ≠ left) (outputNeRight : output ≠ right)
    (leftNeRight : left ≠ right) (goals : List Goal) :
    bindTypedSharedResult (.var output)
      [(output, partialValue head [.var left])]
      (partialValue head [.var right], goals) =
    .ok [(output, partialValue head [.var right]),
      (left, .var right)] := by
  have branchBeq :
      (partialValue head [.var right] == .var output) = false := by
    rfl
  have sharedSubst :
      subst [(output, partialValue head [.var left])] (.var output) =
        partialValue head [.var left] := by
    simp [subst, substN, Metta.Subst.lookup, partialValue, partialC,
      partialTagA, chainOf, consC, nilA, Ne.symm outputNeLeft]
  have branchSubst :
      subst [(output, partialValue head [.var left])]
        (partialValue head [.var right]) =
      partialValue head [.var right] := by
    apply subst_eq_self_of_domain_free
    intro name member
    simp only [Metta.Subst.lookup]
    by_cases same : name = output
    · subst name
      have equality : output = right := by
        simpa [partialValue, partialC, partialTagA, chainOf, consC, nilA,
          Atom.vars] using member
      exact False.elim (outputNeRight equality)
    · simp [same]
  unfold bindTypedSharedResult
  simp only [branchBeq, Bool.false_eq_true, if_false, sharedSubst,
    branchSubst, unifyTopExact_unary_partial_alias head left right
      leftNeRight]
  simp [Metta.Subst.compose, Metta.Subst.apply, Metta.Subst.lookup,
    partialValue, partialC, partialTagA, chainOf, consC, nilA]

/-- The executable first raw branch binds a fresh shared output to the branch
result exactly.  Later branches are a separate structural-decomposition
obligation rather than being hidden in this initial equation. -/
theorem bindTypedSharedResult_fresh_initial (fresh : String) (target : Atom)
    (goals : List Goal) (different : target ≠ .var fresh)
    (occurs : Metta.Subst.occurs fresh target = false) :
    bindTypedSharedResult (.var fresh) [] (target, goals) =
      .ok [(fresh, target)] := by
  have beqFalse : (target == Atom.var fresh) = false := by
    cases target with
    | sym name => rfl
    | var name =>
        change (name == fresh) = false
        apply beq_eq_false_iff_ne.mpr
        intro equality
        apply different
        cases equality
        rfl
    | gnd ground => rfl
    | expr atoms => rfl
  have sharedFixed : subst [] (.var fresh) = .var fresh := by
    apply subst_eq_self_of_domain_free [] (.var fresh)
    simp [Metta.Subst.lookup]
  have targetFixed : subst [] target = target := by
    apply subst_eq_self_of_domain_free [] target
    simp [Metta.Subst.lookup]
  unfold bindTypedSharedResult
  simp only [beqFalse, Bool.false_eq_true, if_false, sharedFixed, targetFixed,
    unifyTopExact_fresh_variable fresh target occurs, Metta.Subst.compose,
    List.map_nil, List.nil_append]

/-- The executable left fold over two compatible unary partial branches
computes the composed binding established by the two one-step theorems. -/
theorem foldlM_bindTypedSharedResult_two_unary_partial
    (head output left right : String)
    (outputNeLeft : output ≠ left) (outputNeRight : output ≠ right)
    (leftNeRight : left ≠ right) (firstGoals secondGoals : List Goal) :
    let final : Subst :=
      [(output, partialValue head [.var right]), (left, .var right)]
    [(partialValue head [.var left], firstGoals),
       (partialValue head [.var right], secondGoals)].foldlM
        (bindTypedSharedResult (.var output)) [] = .ok final := by
  dsimp only
  let firstBinding : Subst :=
    [(output, partialValue head [.var left])]
  let final : Subst :=
    [(output, partialValue head [.var right]), (left, .var right)]
  have first : bindTypedSharedResult (.var output) []
      (partialValue head [.var left], firstGoals) = .ok firstBinding := by
    apply bindTypedSharedResult_fresh_initial
    · intro equality
      cases equality
    · simp [Metta.Subst.occurs, partialValue, partialC, partialTagA,
        chainOf, consC, nilA, outputNeLeft]
  have second : bindTypedSharedResult (.var output) firstBinding
      (partialValue head [.var right], secondGoals) = .ok final := by
    simpa [firstBinding, final] using
      bindTypedSharedResult_after_unary_partial head output left right
        outputNeLeft outputNeRight leftNeRight secondGoals
  simp only [List.foldlM]
  rw [first]
  change Except.bind (Except.ok firstBinding)
      (fun state => Except.bind
        (bindTypedSharedResult (.var output) state
          (partialValue head [.var right], secondGoals))
        (fun finalState => Except.ok finalState)) = .ok final
  rw [show Except.bind (Except.ok firstBinding)
      (fun state => Except.bind
        (bindTypedSharedResult (.var output) state
          (partialValue head [.var right], secondGoals))
        (fun finalState => Except.ok finalState)) =
      Except.bind
        (bindTypedSharedResult (.var output) firstBinding
          (partialValue head [.var right], secondGoals))
        (fun finalState => Except.ok finalState) by rfl]
  rw [second]
  rfl

/-- End-to-end executable resolution of two compatible incomplete typed
branches.  The final binding is applied retroactively to every raw branch;
the output list keeps its original order and duplicate-sensitive shape. -/
theorem resolveTypedSharedResult_two_unary_partial
    (head output left right : String)
    (outputNeLeft : output ≠ left) (outputNeRight : output ≠ right)
    (leftNeRight : left ≠ right) (firstGoals secondGoals : List Goal) :
    let final : Subst :=
      [(output, partialValue head [.var right]), (left, .var right)]
    resolveTypedSharedResult (.var output)
      [(partialValue head [.var left], firstGoals),
       (partialValue head [.var right], secondGoals)] =
      .ok (partialValue head [.var right],
        [(partialValue head [.var right],
            substCompiledGoals final firstGoals),
         (partialValue head [.var right],
            substCompiledGoals final secondGoals)]) := by
  dsimp only
  let final : Subst :=
    [(output, partialValue head [.var right]), (left, .var right)]
  have folded :
      [(partialValue head [.var left], firstGoals),
       (partialValue head [.var right], secondGoals)].foldlM
          (bindTypedSharedResult (.var output)) [] = .ok final := by
    simpa [final] using
      foldlM_bindTypedSharedResult_two_unary_partial head output left right
        outputNeLeft outputNeRight leftNeRight firstGoals secondGoals
  unfold resolveTypedSharedResult
  rw [folded]
  change Except.bind (Except.ok final)
      (fun binding => Except.ok
        (subst binding (.var output),
         substCompiledBranches binding
           [(partialValue head [.var left], firstGoals),
            (partialValue head [.var right], secondGoals)])) = _
  rw [show Except.bind (Except.ok final)
      (fun binding => Except.ok
        (subst binding (.var output),
         substCompiledBranches binding
           [(partialValue head [.var left], firstGoals),
            (partialValue head [.var right], secondGoals)])) =
      Except.ok
        (subst final (.var output),
         substCompiledBranches final
           [(partialValue head [.var left], firstGoals),
            (partialValue head [.var right], secondGoals)]) by rfl]
  congr 2
  · simp [final, subst, substN, Metta.Subst.lookup, partialValue, partialC,
      partialTagA, chainOf, consC, nilA, Ne.symm outputNeRight,
      Ne.symm leftNeRight]
  · simp [final, substCompiledBranches, subst, substN, Metta.Subst.lookup,
      partialValue, partialC, partialTagA, chainOf, consC, nilA,
      Ne.symm outputNeLeft,
      Ne.symm outputNeRight, Ne.symm leftNeRight]

/-- Representation agreement for the same one-argument `partial/2` context
on the independent and executable sides. -/
theorem unaryPartialTerm_agrees (head : String) {term : Term} {atom : Atom}
    (argument : TermAgrees term atom) :
    TermAgrees (unaryPartialTerm head term) (partialValue head [atom]) := by
  unfold unaryPartialTerm partialValue
  exact .partialValue (.cons argument .nil)

/-- Independent substitution produced by the first two incompatible-by-name
but structurally compatible incomplete typed branches. -/
def twoUnaryPartialReferenceBinding (head sourceName : String)
    (outputIndex leftIndex : Nat) : Substitution :=
  [(.generated leftIndex, .variable (.source sourceName)),
   (.generated outputIndex,
    unaryPartialTerm head (.variable (.generated leftIndex)))]

/-- Executable counterpart of `twoUnaryPartialReferenceBinding`, after the
later alias has been composed through the first partial value. -/
def twoUnaryPartialExecutableBinding (head sourceName : String)
    (outputIndex leftIndex : Nat) : Subst :=
  [(compilerGeneratedName outputIndex,
    partialValue head [.var sourceName]),
   (compilerGeneratedName leftIndex, .var sourceName)]

/-- Complete finite observation surface for the two-branch binding bridge:
the shared output, both argument identities, and both raw partial values. -/
def twoUnaryPartialPairs (head sourceName : String)
    (outputIndex leftIndex : Nat) : List (Term × Atom) :=
  [(.variable (.generated outputIndex),
      .var (compilerGeneratedName outputIndex)),
   (.variable (.generated leftIndex),
      .var (compilerGeneratedName leftIndex)),
   (.variable (.source sourceName), .var sourceName),
   (unaryPartialTerm head (.variable (.generated leftIndex)),
      partialValue head [.var (compilerGeneratedName leftIndex)]),
   (unaryPartialTerm head (.variable (.source sourceName)),
      partialValue head [.var sourceName])]

/-- The semantic two-branch MGU and the computed executable substitution
agree before and after substitution on every relevant term.  The explicit
name inequalities rule out the real source/generated `_qN` collision rather
than silently identifying independent variables through executable strings. -/
theorem two_unary_partial_bindings_agree
    (head sourceName : String) (outputIndex leftIndex : Nat)
    (indexDifferent : outputIndex ≠ leftIndex)
    (generatedDifferent :
      compilerGeneratedName outputIndex ≠ compilerGeneratedName leftIndex)
    (outputFresh : compilerGeneratedName outputIndex ≠ sourceName)
    (leftFresh : compilerGeneratedName leftIndex ≠ sourceName) :
    BindingsAgreeOn
      (twoUnaryPartialReferenceBinding head sourceName outputIndex leftIndex)
      (twoUnaryPartialExecutableBinding head sourceName outputIndex leftIndex)
      (twoUnaryPartialPairs head sourceName outputIndex leftIndex) := by
  have referenceOutput :
      Substitution.applyTerm
          (twoUnaryPartialReferenceBinding head sourceName outputIndex
            leftIndex)
          (.variable (.generated outputIndex)) =
        unaryPartialTerm head (.variable (.source sourceName)) := by
    simp [twoUnaryPartialReferenceBinding, Substitution.applyTerm,
      Term.instantiateOne, Terms.instantiateOne, unaryPartialTerm]
  have referenceLeft :
      Substitution.applyTerm
          (twoUnaryPartialReferenceBinding head sourceName outputIndex
            leftIndex)
          (.variable (.generated leftIndex)) =
        .variable (.source sourceName) := by
    simp [twoUnaryPartialReferenceBinding, Substitution.applyTerm,
      Term.instantiateOne, unaryPartialTerm, Ne.symm indexDifferent]
  have referenceSource :
      Substitution.applyTerm
          (twoUnaryPartialReferenceBinding head sourceName outputIndex
            leftIndex)
          (.variable (.source sourceName)) =
        .variable (.source sourceName) := by
    simp [twoUnaryPartialReferenceBinding, Substitution.applyTerm,
      Term.instantiateOne]
  have referenceFirst :
      Substitution.applyTerm
          (twoUnaryPartialReferenceBinding head sourceName outputIndex
            leftIndex)
          (unaryPartialTerm head (.variable (.generated leftIndex))) =
        unaryPartialTerm head (.variable (.source sourceName)) := by
    simp [twoUnaryPartialReferenceBinding, Substitution.applyTerm,
      Term.instantiateOne, Terms.instantiateOne, unaryPartialTerm,
      Ne.symm indexDifferent]
  have referenceSecond :
      Substitution.applyTerm
          (twoUnaryPartialReferenceBinding head sourceName outputIndex
            leftIndex)
          (unaryPartialTerm head (.variable (.source sourceName))) =
        unaryPartialTerm head (.variable (.source sourceName)) := by
    simp [twoUnaryPartialReferenceBinding, Substitution.applyTerm,
      Term.instantiateOne, Terms.instantiateOne, unaryPartialTerm]
  have executableOutput :
      subst
          (twoUnaryPartialExecutableBinding head sourceName outputIndex
            leftIndex)
          (.var (compilerGeneratedName outputIndex)) =
        partialValue head [.var sourceName] := by
    simp [twoUnaryPartialExecutableBinding, subst, substN,
      Metta.Subst.lookup, partialValue, partialC, partialTagA, chainOf,
      consC, nilA,
      Ne.symm outputFresh, Ne.symm leftFresh]
  have executableLeft :
      subst
          (twoUnaryPartialExecutableBinding head sourceName outputIndex
            leftIndex)
          (.var (compilerGeneratedName leftIndex)) = .var sourceName := by
    simp [twoUnaryPartialExecutableBinding, subst, substN,
      Metta.Subst.lookup,
      Ne.symm generatedDifferent, Ne.symm outputFresh, Ne.symm leftFresh]
  have executableSource :
      subst
          (twoUnaryPartialExecutableBinding head sourceName outputIndex
            leftIndex)
          (.var sourceName) = .var sourceName := by
    simp [twoUnaryPartialExecutableBinding, subst, substN,
      Metta.Subst.lookup, Ne.symm outputFresh, Ne.symm leftFresh]
  have executableFirst :
      subst
          (twoUnaryPartialExecutableBinding head sourceName outputIndex
            leftIndex)
          (partialValue head [.var (compilerGeneratedName leftIndex)]) =
        partialValue head [.var sourceName] := by
    simp [twoUnaryPartialExecutableBinding, subst, substN,
      Metta.Subst.lookup, partialValue, partialC, partialTagA, chainOf,
      consC, nilA,
      Ne.symm generatedDifferent, Ne.symm outputFresh, Ne.symm leftFresh]
  have executableSecond :
      subst
          (twoUnaryPartialExecutableBinding head sourceName outputIndex
            leftIndex)
          (partialValue head [.var sourceName]) =
        partialValue head [.var sourceName] := by
    simp [twoUnaryPartialExecutableBinding, subst, substN,
      Metta.Subst.lookup, partialValue, partialC, partialTagA, chainOf,
      consC, nilA,
      Ne.symm outputFresh, Ne.symm leftFresh]
  intro pair member
  simp only [twoUnaryPartialPairs, List.mem_cons, List.not_mem_nil, or_false]
    at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · constructor
    · exact .generatedVariable outputIndex
    · unfold TermStateAgrees
      rw [referenceOutput, executableOutput]
      exact unaryPartialTerm_agrees head (.sourceVariable sourceName)
  · constructor
    · exact .generatedVariable leftIndex
    · unfold TermStateAgrees
      rw [referenceLeft, executableLeft]
      exact .sourceVariable sourceName
  · constructor
    · exact .sourceVariable sourceName
    · unfold TermStateAgrees
      rw [referenceSource, executableSource]
      exact .sourceVariable sourceName
  · constructor
    · exact unaryPartialTerm_agrees head (.generatedVariable leftIndex)
    · unfold TermStateAgrees
      rw [referenceFirst, executableFirst]
      exact unaryPartialTerm_agrees head (.sourceVariable sourceName)
  · constructor
    · exact unaryPartialTerm_agrees head (.sourceVariable sourceName)
    · unfold TermStateAgrees
      rw [referenceSecond, executableSecond]
      exact unaryPartialTerm_agrees head (.sourceVariable sourceName)

/-- First composed two-branch adequacy slice for shared typed results.  It
connects the independent MGU resolution, the executable fold/resolution, the
binding bridge, and the final ordered branch bag in one checked statement.
The empty branch-local goals keep this theorem honest while general
cross-representation goal-substitution transport remains open. -/
theorem two_unary_partial_empty_goals_adequate
    (head sourceName : String) (outputIndex leftIndex : Nat)
    (indexDifferent : outputIndex ≠ leftIndex)
    (generatedDifferent :
      compilerGeneratedName outputIndex ≠ compilerGeneratedName leftIndex)
    (outputFresh : compilerGeneratedName outputIndex ≠ sourceName)
    (leftFresh : compilerGeneratedName leftIndex ≠ sourceName) :
    ResolvesTypedSharedResult (.variable (.generated outputIndex))
      [(unaryPartialTerm head (.variable (.generated leftIndex)), []),
       (unaryPartialTerm head (.variable (.source sourceName)), [])]
      (unaryPartialTerm head (.variable (.source sourceName)))
      [(unaryPartialTerm head (.variable (.source sourceName)), []),
       (unaryPartialTerm head (.variable (.source sourceName)), [])] ∧
    resolveTypedSharedResult (.var (compilerGeneratedName outputIndex))
      [(partialValue head [.var (compilerGeneratedName leftIndex)], []),
       (partialValue head [.var sourceName], [])] =
      .ok (partialValue head [.var sourceName],
        [(partialValue head [.var sourceName], []),
         (partialValue head [.var sourceName], [])]) ∧
    BindingsAgreeOn
      (twoUnaryPartialReferenceBinding head sourceName outputIndex leftIndex)
      (twoUnaryPartialExecutableBinding head sourceName outputIndex leftIndex)
      (twoUnaryPartialPairs head sourceName outputIndex leftIndex) ∧
    TermAgrees (unaryPartialTerm head (.variable (.source sourceName)))
      (partialValue head [.var sourceName]) ∧
    TypedBranchesAgree
      [(unaryPartialTerm head (.variable (.source sourceName)), []),
       (unaryPartialTerm head (.variable (.source sourceName)), [])]
      [(partialValue head [.var sourceName], []),
       (partialValue head [.var sourceName], [])] := by
  have referenceGeneratedDifferent :
      (LogicVar.generated outputIndex) ≠ .generated leftIndex := by
    intro equality
    exact indexDifferent (LogicVar.generated.inj equality)
  have referenceOutputFresh :
      (LogicVar.generated outputIndex) ≠ .source sourceName := by
    intro equality
    cases equality
  have referenceLeftFresh :
      (LogicVar.generated leftIndex) ≠ .source sourceName := by
    intro equality
    cases equality
  have semantic := two_unary_partial_branches_resolve head
    (.generated outputIndex) (.generated leftIndex) (.source sourceName)
    referenceGeneratedDifferent referenceOutputFresh referenceLeftFresh [] []
  have executable := resolveTypedSharedResult_two_unary_partial head
    (compilerGeneratedName outputIndex) (compilerGeneratedName leftIndex)
    sourceName generatedDifferent outputFresh leftFresh [] []
  have bindings := two_unary_partial_bindings_agree head sourceName
    outputIndex leftIndex indexDifferent generatedDifferent outputFresh
    leftFresh
  have resultAgreement :
      TermAgrees (unaryPartialTerm head (.variable (.source sourceName)))
        (partialValue head [.var sourceName]) :=
    unaryPartialTerm_agrees head (.sourceVariable sourceName)
  refine ⟨?_, ?_, bindings, resultAgreement, ?_⟩
  · simpa [twoUnaryPartialReferenceBinding] using semantic
  · simpa [twoUnaryPartialExecutableBinding, substCompiledGoals] using
      executable
  · exact .cons resultAgreement .nil
      (.cons resultAgreement .nil .nil)

/-- Independent/executable pair list observed by the first shared-output
binding.  It includes both the shared variable and the target, before and
after substitution. -/
def freshSharedPairs (index : Nat) (referenceValue : Term)
    (executableValue : Atom) : List (Term × Atom) :=
  [(.variable (.generated index), .var (compilerGeneratedName index)),
   (referenceValue, executableValue)]

/-- The independent singleton MGU and executable singleton binding agree on
the complete first-constraint surface.  Neither side is defined through the
other: pre-state `TermAgrees` and both freshness conditions are premises. -/
theorem fresh_singleton_bindings_agree (index : Nat)
    (referenceValue : Term) (executableValue : Atom)
    (agreement : TermAgrees referenceValue executableValue)
    (referenceFresh :
      Term.occurs (.generated index) referenceValue = false)
    (executableFresh :
      compilerGeneratedName index ∉ executableValue.vars) :
    BindingsAgreeOn [(.generated index, referenceValue)]
      [(compilerGeneratedName index, executableValue)]
      (freshSharedPairs index referenceValue executableValue) := by
  let name := compilerGeneratedName index
  let referenceBinding : Substitution :=
    [(.generated index, referenceValue)]
  let executableBinding : Subst := [(name, executableValue)]
  have topological : SubstTopological executableBinding := by
    apply SubstTopological.cons_of_fresh [] emptySubstTopological name
      executableValue
    · simp [Metta.Subst.lookup]
    · exact executableFresh
    · simp [AtomAvoids, Metta.Subst.lookup]
  have lookup : Metta.Subst.lookup executableBinding name =
      some executableValue := by
    simp [executableBinding, Metta.Subst.lookup]
  have executableValueFixed : subst executableBinding executableValue =
      executableValue := by
    apply subst_eq_self_of_domain_free executableBinding executableValue
    intro candidate member
    by_cases same : candidate = name
    · subst candidate
      exact False.elim (executableFresh member)
    · simp [executableBinding, Metta.Subst.lookup, same]
  have executableShared : subst executableBinding (.var name) =
      executableValue := by
    exact (topological.subst_var_of_lookup executableBinding name
      executableValue lookup).trans executableValueFixed
  have referenceValueFixed : referenceBinding.applyTerm referenceValue =
      referenceValue := by
    exact Term.instantiateOne_eq_self_of_occurs_false (.generated index)
      referenceValue referenceValue referenceFresh
  intro pair member
  simp only [freshSharedPairs, List.mem_cons, List.not_mem_nil, or_false]
    at member
  rcases member with rfl | rfl
  · constructor
    · exact TermAgrees.generatedVariable index
    · unfold TermStateAgrees
      change TermAgrees
        (referenceBinding.applyTerm (.variable (.generated index)))
        (subst executableBinding (.var name))
      rw [show referenceBinding.applyTerm (.variable (.generated index)) =
          referenceValue by
            simp [referenceBinding,
              PLeaTTa.PeTTaSpec.PrologCore.OpenSubstitution.Substitution.applyTerm,
              Term.instantiateOne],
        executableShared]
      exact agreement
  · constructor
    · exact agreement
    · unfold TermStateAgrees
      change TermAgrees (referenceBinding.applyTerm referenceValue)
        (subst executableBinding executableValue)
      rw [referenceValueFixed, executableValueFixed]
      exact agreement

/-- First-constraint adequacy for typed shared-output resolution.  The
independent result is a semantic MGU, the executable result is computed
exactly, and their before/after states agree on both relevant terms. -/
theorem bindTypedSharedResult_initial_adequate (index : Nat)
    (referenceValue : Term) (executableValue : Atom) (goals : List Goal)
    (agreement : TermAgrees referenceValue executableValue)
    (referenceFresh :
      Term.occurs (.generated index) referenceValue = false)
    (executableFresh :
      compilerGeneratedName index ∉ executableValue.vars) :
    ∃ referenceBinding : Substitution, ∃ executableBinding : Subst,
      IsMostGeneralUnifier referenceBinding
        [(.variable (.generated index), referenceValue)] ∧
      bindTypedSharedResult (.var (compilerGeneratedName index)) []
          (executableValue, goals) = .ok executableBinding ∧
      BindingsAgreeOn referenceBinding executableBinding
        (freshSharedPairs index referenceValue executableValue) := by
  let name := compilerGeneratedName index
  let referenceBinding : Substitution :=
    [(.generated index, referenceValue)]
  let executableBinding : Subst := [(name, executableValue)]
  have different : executableValue ≠ .var name := by
    intro equality
    subst executableValue
    apply executableFresh
    simp [name, Atom.vars]
  have occurs : Metta.Subst.occurs name executableValue = false :=
    occurs_eq_false_of_not_mem_vars name executableValue executableFresh
  refine ⟨referenceBinding, executableBinding, ?_, ?_, ?_⟩
  · exact singleton_variable_is_mgu (.generated index) referenceValue
      referenceFresh
  · exact bindTypedSharedResult_fresh_initial name executableValue goals
      different occurs
  · exact fresh_singleton_bindings_agree index referenceValue executableValue
      agreement referenceFresh executableFresh

end PLeaTTa.CompilerTypedSharedResultAdequacy
