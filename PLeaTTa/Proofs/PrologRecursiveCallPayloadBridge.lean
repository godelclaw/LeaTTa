-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologRecursiveCallPayloadBridge
Purpose: Interpret one active recursive-call payload through the shared
  cumulative residual-MGU representative rather than requiring identical
  carried substitution orientation.
Trusted boundary: none
Main exports:
  AlphaTermsSupported,
  AlphaCumulativeResidualVariantAgreesOn.applyTerms,
  AlphaCumulativeResidualVariantAgreesOn.applyOutputLast,
  NormalizedAlphaGoalsAgree.localCallHead,
  TaskPayloadAgrees.applyLocalCall
-/
import PLeaTTa.Proofs.PrologOrdinaryStepBridge

namespace PLeaTTa.PrologRecursiveCallPayloadBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open PrologGoalAlpha
open PrologCallPayloadBridge
open PrologMguBridge
open PrologMguComposition
open PrologMguOpenAgreement
open PrologMguTopology
open PrologMguVariant
open PrologOrdinaryStepBridge
open PrologPrefilterBridge
open PrologStateBridge

/-!
After one or more clause-head MGUs, the independent and executable
association lists may orient a residual alias in opposite directions.
`NormalizedCallAgrees` is consequently too syntactic for recursive calls:
applying the independently chosen association list need not give the exact
runtime atom spelling.

The cumulative payload already stores one hidden semantic representative
which interprets the executable substitution.  This module lifts that
single representative through every leaf of an output-last call.  The
support premise is occurrence-sensitive, so an unrelated live alpha link
cannot certify an active query variable.
-/

/-- Every alpha link traversed by every term in one ordered payload is
present in the observable cumulative support. -/
def AlphaTermsSupported
    (alpha support : List (LogicVar × String))
    (terms : List Term) : Prop :=
  ∀ term, term ∈ terms →
    AlphaTreeSupported alpha support (Term.denote term)

/-- A cumulative residual variant applies one shared hidden representative
to an entire ordered source/runtime payload.

The representative is chosen once outside the `Forall₂`; it cannot vary by
argument.  This is the load-bearing distinction from applying a
single-term existential independently at every leaf. -/
theorem AlphaCumulativeResidualVariantAgreesOn.applyTerms
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {runtime : Subst}
    (cumulative :
      AlphaCumulativeResidualVariantAgreesOn
        alpha support canonical referenceBase runtime)
    {references : List Term} {executables : List Atom}
    (leaves : AlphaTermsAgree alpha references executables)
    (supported : AlphaTermsSupported alpha support references) :
    ∃ representative : TreeSubstitution,
      TreeSubstitutionVariants
        (canonical ++ Substitution.denote referenceBase)
        (representative ++ Substitution.denote referenceBase) ∧
      TreeSubstitutionVariablesSatisfy
        (AlphaCovers alpha) representative ∧
      List.Forall₂
        (fun term atom =>
          CanonicalRuntimeAgrees alpha
            (TreeSubstitution.apply
              (representative ++ Substitution.denote referenceBase)
              (Term.denote term))
            (PLeaTTa.subst runtime atom))
        references executables := by
  rcases cumulative with
    ⟨representative, variants, _canonicalTopological,
      representativeCovered, _runtimeTopological, valuation⟩
  refine ⟨representative, variants, representativeCovered, ?_⟩
  induction leaves with
  | nil =>
      exact .nil
  | cons head tail inductionHypothesis =>
      exact .cons
        (canonicalRuntimeAgrees_apply_on
          (AlphaTermAgrees.canonicalRuntimeAgrees head)
          valuation (supported _ (by simp)))
        (inductionHypothesis
          (fun term member => supported term (by simp [member])))

/-- Output-last specialization used by the local resolver.  Inputs and the
result share one cumulative representative and retain exact order. -/
theorem AlphaCumulativeResidualVariantAgreesOn.applyOutputLast
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {runtime : Subst}
    (cumulative :
      AlphaCumulativeResidualVariantAgreesOn
        alpha support canonical referenceBase runtime)
    {referenceArguments : List Term} {referenceResult : Term}
    {executableArguments : List Atom} {executableResult : Atom}
    (arguments :
      AlphaTermsAgree alpha referenceArguments executableArguments)
    (result :
      AlphaTermAgrees alpha referenceResult executableResult)
    (supported :
      AlphaTermsSupported alpha support
        (referenceArguments ++ [referenceResult])) :
    ∃ representative : TreeSubstitution,
      TreeSubstitutionVariants
        (canonical ++ Substitution.denote referenceBase)
        (representative ++ Substitution.denote referenceBase) ∧
      TreeSubstitutionVariablesSatisfy
        (AlphaCovers alpha) representative ∧
      List.Forall₂
        (fun term atom =>
          CanonicalRuntimeAgrees alpha
            (TreeSubstitution.apply
              (representative ++ Substitution.denote referenceBase)
              (Term.denote term))
            (PLeaTTa.subst runtime atom))
        (referenceArguments ++ [referenceResult])
        (executableArguments ++ [executableResult]) :=
  PLeaTTa.PrologRecursiveCallPayloadBridge.AlphaCumulativeResidualVariantAgreesOn.applyTerms
    cumulative (AlphaTermsAgree.append_singleton arguments result) supported

/-- Inverting a normalized source call against an executable *local-call*
head recovers the exact output-last leaf agreement.

The executable shape is a premise.  This is intentional: independent source
syntax has only `Goal.call`, while the compiler may translate that syntax to
local `.call`, imported `.bin`, or specialized `.spread`.  Ownership is not
smuggled into the source constructor. -/
theorem NormalizedAlphaGoalsAgree.localCallHead
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {predicate : String} {referencePayload : List Term}
    {executableArguments : List Atom} {executableResult : Atom}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      NormalizedAlphaGoalsAgree alpha barrier
        (.call predicate referencePayload :: references)
        (.call predicate executableArguments executableResult ::
          executables)) :
    ∃ referenceArguments referenceResult,
      referencePayload = referenceArguments ++ [referenceResult] ∧
        AlphaTermsAgree alpha referenceArguments executableArguments ∧
        AlphaTermAgrees alpha referenceResult executableResult ∧
        NormalizedAlphaGoalsAgree alpha barrier references executables := by
  cases agreement with
  | cons head tail =>
      cases head with
      | definedCall arguments result =>
          exact ⟨_, _, rfl, arguments, result, tail⟩

/-- An active task payload interprets all leaves of a recursive call through
the same hidden cumulative representative.  No equality between the source
and executable carried association lists is asserted. -/
theorem TaskPayloadAgrees.applyLocalCall
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Subst}
    {predicate : String} {referencePayload : List Term}
    {executableArguments : List Atom} {executableResult : Atom}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (payload :
      TaskPayloadAgrees alpha support barrier canonical referenceBase current
        runtime
        (.call predicate referencePayload :: references)
        (.call predicate executableArguments executableResult ::
          executables))
    (supported :
      AlphaTermsSupported alpha support referencePayload) :
    ∃ referenceArguments referenceResult representative,
      referencePayload = referenceArguments ++ [referenceResult] ∧
        TreeSubstitutionVariants
          (canonical ++ Substitution.denote referenceBase)
          (representative ++ Substitution.denote referenceBase) ∧
        TreeSubstitutionVariablesSatisfy
          (AlphaCovers alpha) representative ∧
        List.Forall₂
          (fun term atom =>
            CanonicalRuntimeAgrees alpha
              (TreeSubstitution.apply
                (representative ++ Substitution.denote referenceBase)
                (Term.denote term))
              (PLeaTTa.subst runtime atom))
          referencePayload
          (executableArguments ++ [executableResult]) := by
  rcases
      NormalizedAlphaGoalsAgree.localCallHead payload.control with
    ⟨referenceArguments, referenceResult, payloadShape,
      arguments, result, _tail⟩
  subst referencePayload
  obtain ⟨representative, variants, representativeCovered, leaves⟩ :=
    PLeaTTa.PrologRecursiveCallPayloadBridge.AlphaCumulativeResidualVariantAgreesOn.applyOutputLast
      payload.valuation arguments result supported
  exact
    ⟨referenceArguments, referenceResult, representative, rfl,
      variants, representativeCovered, leaves⟩

/-! ## Representation-independent normalized calls -/

/-- A normalized local-call payload interpreted through one semantic
representative of the carried source substitution.

Unlike `NormalizedCallAgrees`, this relation does not require the
independent ordered MGU and the executable MGU to choose the same residual
alias orientation.  The representative is selected once for the whole
ordered output-last payload, and mutual factorization keeps it tied to the
actual source cursor binding. -/
def RepresentativeNormalizedCallAgrees
    (alpha : List (LogicVar × String))
    (cursor : PreparedCursor) (argsv : List Atom) (resv : Atom) : Prop :=
  ∃ residualRepresentative : TreeSubstitution,
    ∃ olderBase : Substitution,
    TreeSubstitutionVariants
        (Substitution.denote cursor.bindings)
        (residualRepresentative ++ Substitution.denote olderBase) ∧
    TreeSubstitutionVariablesSatisfy
      (AlphaCovers alpha) residualRepresentative ∧
    (∀ entry, entry ∈ olderBase → entry ∈ cursor.bindings) ∧
    List.Forall₂
      (fun term atom =>
        CanonicalRuntimeAgrees alpha
          (TreeSubstitution.apply
            (residualRepresentative ++ Substitution.denote olderBase)
            (Term.denote term))
          atom)
      cursor.arguments (argsv ++ [resv])

/-- Pointwise syntactic alpha agreement after applying a source
substitution embeds into the representative relation with that exact
source substitution as its own representative. -/
theorem AlphaTermsAgree.appliedCanonicalRuntimeAgrees
    {alpha : List (LogicVar × String)}
    {bindings : Substitution}
    {references : List Term} {executables : List Atom}
    (agreement :
      AlphaTermsAgree alpha
        (bindings.applyTerms references) executables) :
    List.Forall₂
      (fun term atom =>
        CanonicalRuntimeAgrees alpha
          (TreeSubstitution.apply
            (Substitution.denote bindings) (Term.denote term))
          atom)
      references executables := by
  induction references generalizing executables with
  | nil =>
      simp only [Substitution.applyTerms_empty] at agreement
      cases agreement
      exact .nil
  | cons term terms inductionHypothesis =>
      simp only [Substitution.applyTerms_cons] at agreement
      cases agreement with
      | cons head tail =>
          exact .cons
            (by
              rw [← Substitution.denote_applyTerm]
              exact
                PLeaTTa.PrologPrefilterBridge.AlphaTermAgrees.canonicalRuntimeAgrees
                  head)
            (inductionHypothesis tail)

/-- The original syntactic call relation is a strict special case of the
semantic representative relation. -/
theorem NormalizedCallAgrees.representative
    {alpha : List (LogicVar × String)}
    {cursor : PreparedCursor} {argsv : List Atom} {resv : Atom}
    (agreement :
      NormalizedCallAgrees alpha cursor argsv resv) :
    RepresentativeNormalizedCallAgrees alpha cursor argsv resv :=
  ⟨[], cursor.bindings, by simp [TreeSubstitutionVariants.refl],
    by
      intro entry member
      simp at member,
    fun _ member => member,
    by
      simpa using
        PLeaTTa.PrologRecursiveCallPayloadBridge.AlphaTermsAgree.appliedCanonicalRuntimeAgrees
          agreement.arguments⟩

/-- A recursive local call in an active task constructs the semantic
normalized-call relation at the exact runtime values inspected by the
resolver prefilter.

The source cursor equalities are the only connection requested from call
opening.  Residual orientation remains hidden behind the representative
already supplied by `TaskPayloadAgrees.applyLocalCall`. -/
theorem TaskPayloadAgrees.representativeNormalizedCallAgrees
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Subst}
    {predicate : String} {referencePayload : List Term}
    {executableArguments : List Atom} {executableResult : Atom}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (payload :
      TaskPayloadAgrees alpha support barrier canonical referenceBase current
        runtime
        (.call predicate referencePayload :: references)
        (.call predicate executableArguments executableResult ::
          executables))
    (supported :
      AlphaTermsSupported alpha support referencePayload)
    (cursor : PreparedCursor)
    (cursorArguments : cursor.arguments = referencePayload)
    (cursorBindings : cursor.bindings = current) :
    RepresentativeNormalizedCallAgrees alpha cursor
      (executableArguments.map (PLeaTTa.subst runtime))
      (PLeaTTa.subst runtime executableResult) := by
  obtain
    ⟨_referenceArguments, _referenceResult, representative,
      _payloadShape, variants, representativeCovered, leaves⟩ :=
    PLeaTTa.PrologRecursiveCallPayloadBridge.TaskPayloadAgrees.applyLocalCall
      payload supported
  refine
    ⟨representative, referenceBase, ?_, representativeCovered, ?_, ?_⟩
  · rw [cursorBindings, payload.denoteCurrent]
    exact variants
  · intro entry member
    rw [cursorBindings, payload.bindingShape]
    simp [member]
  · rw [cursorArguments]
    simpa only [List.map_append, List.map_singleton] using
      (List.forall₂_map_right_iff.mpr leaves)

/-! ## Anti-vacuity: recursive calls really need the representative -/

private def recursiveWitnessX : LogicVar := .source "$recursive_x"
private def recursiveWitnessY : LogicVar := .source "$recursive_y"
private def recursiveWitnessAlpha : List (LogicVar × String) :=
  [(recursiveWitnessX, "$runtime_x"),
   (recursiveWitnessY, "$runtime_y")]
private def recursiveWitnessCanonical : TreeSubstitution :=
  [(recursiveWitnessX, .variable recursiveWitnessY)]
private def recursiveWitnessRepresentative : TreeSubstitution :=
  [(recursiveWitnessY, .variable recursiveWitnessX)]
private def recursiveWitnessRuntime : Subst :=
  [("$runtime_y", .var "$runtime_x")]

/-- Opposite residual alias orientations satisfy the cumulative call
relation, and its hidden representative interprets the active runtime leaf,
while direct application of the independently chosen source spelling does
not.  This rejects replacing `applyTerms` by syntactic normalized-query
equality. -/
theorem recursive_call_orientation_requires_representative :
    AlphaCumulativeResidualVariantAgreesOn
        recursiveWitnessAlpha recursiveWitnessAlpha
        recursiveWitnessCanonical [] recursiveWitnessRuntime ∧
      (∃ representative,
        TreeSubstitutionVariants
          recursiveWitnessCanonical representative ∧
        TreeSubstitutionVariablesSatisfy
          (AlphaCovers recursiveWitnessAlpha) representative ∧
        CanonicalRuntimeAgrees recursiveWitnessAlpha
          (TreeSubstitution.apply representative
            (.variable recursiveWitnessX))
          (PLeaTTa.subst recursiveWitnessRuntime
            (.var "$runtime_x"))) ∧
      ¬ CanonicalRuntimeAgrees recursiveWitnessAlpha
          (TreeSubstitution.apply recursiveWitnessCanonical
            (.variable recursiveWitnessX))
          (PLeaTTa.subst recursiveWitnessRuntime
            (.var "$runtime_x")) := by
  have canonicalMgu :
      TreeIsMgu recursiveWitnessCanonical
        [(.variable recursiveWitnessX, .variable recursiveWitnessY)] := by
    exact tree_singleton_variable_is_mgu recursiveWitnessX
      (.variable recursiveWitnessY) (by
        simp [Tree.occurs, recursiveWitnessX, recursiveWitnessY])
  have representativeMgu :
      TreeIsMgu recursiveWitnessRepresentative
        [(.variable recursiveWitnessX, .variable recursiveWitnessY)] := by
    exact tree_singleton_right_variable_is_mgu
      (.variable recursiveWitnessX) recursiveWitnessY (by
        simp [Tree.occurs, recursiveWitnessX, recursiveWitnessY])
  have variants :
      TreeSubstitutionVariants
        recursiveWitnessCanonical recursiveWitnessRepresentative :=
    PrologMguVariant.TreeIsMgu.variants canonicalMgu representativeMgu
  have canonicalTopological :
      TreeSubstitutionTopological recursiveWitnessCanonical :=
    TreeSubstitutionTopological.singleton recursiveWitnessX
      (.variable recursiveWitnessY) (by
        simp [Tree.occurs, recursiveWitnessX, recursiveWitnessY])
  have runtimeTopological :
      PLeaTTa.SubstTopological recursiveWitnessRuntime :=
    PLeaTTa.SubstTopological.cons_of_fresh []
      PLeaTTa.emptySubstTopological "$runtime_y" (.var "$runtime_x")
      (by simp [Metta.Subst.lookup])
      (by simp [Atom.vars])
      (by simp [PLeaTTa.AtomAvoids, Metta.Subst.lookup])
  have representativeX :
      TreeSubstitution.apply recursiveWitnessRepresentative
          (.variable recursiveWitnessX) =
        .variable recursiveWitnessX := by
    simp [recursiveWitnessRepresentative, recursiveWitnessX,
      recursiveWitnessY, TreeSubstitution.apply, Tree.instantiateOne]
  have representativeY :
      TreeSubstitution.apply recursiveWitnessRepresentative
          (.variable recursiveWitnessY) =
        .variable recursiveWitnessX := by
    simp [recursiveWitnessRepresentative, recursiveWitnessX,
      recursiveWitnessY, TreeSubstitution.apply, Tree.instantiateOne]
  have runtimeX :
      PLeaTTa.subst recursiveWitnessRuntime (.var "$runtime_x") =
        .var "$runtime_x" :=
    PLeaTTa.subst_var_of_lookup_none
      recursiveWitnessRuntime "$runtime_x" (by
        simp [recursiveWitnessRuntime, Metta.Subst.lookup])
  have runtimeY :
      PLeaTTa.subst recursiveWitnessRuntime (.var "$runtime_y") =
        .var "$runtime_x" := by
    rw [runtimeTopological.subst_var_of_lookup
      recursiveWitnessRuntime "$runtime_y" (.var "$runtime_x")
      (by simp [recursiveWitnessRuntime, Metta.Subst.lookup])]
    exact runtimeX
  have valuation :
      AlphaValuationAgreesOn
        recursiveWitnessAlpha recursiveWitnessAlpha
        recursiveWitnessRepresentative recursiveWitnessRuntime := by
    intro identity name member
    simp only [recursiveWitnessAlpha, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with member | member
    · have identityEq : identity = recursiveWitnessX := by
        simpa using congrArg Prod.fst member
      have nameEq : name = "$runtime_x" := by
        simpa using congrArg Prod.snd member
      subst identity
      subst name
      rw [representativeX, runtimeX]
      exact
        (CanonicalRuntimeAgrees.variable
          (alpha := recursiveWitnessAlpha)
          (by simp [recursiveWitnessAlpha, recursiveWitnessX]))
    · have identityEq : identity = recursiveWitnessY := by
        simpa using congrArg Prod.fst member
      have nameEq : name = "$runtime_y" := by
        simpa using congrArg Prod.snd member
      subst identity
      subst name
      rw [representativeY, runtimeY]
      exact
        (CanonicalRuntimeAgrees.variable
          (alpha := recursiveWitnessAlpha)
          (by simp [recursiveWitnessAlpha, recursiveWitnessX,
            recursiveWitnessY]))
  have representativeCovered :
      TreeSubstitutionVariablesSatisfy
        (AlphaCovers recursiveWitnessAlpha)
        recursiveWitnessRepresentative := by
    intro entry member
    have entryEq :
        entry =
          (recursiveWitnessY, .variable recursiveWitnessX) := by
      simpa [recursiveWitnessRepresentative] using member
    subst entry
    exact
      ⟨⟨"$runtime_y",
          by simp [recursiveWitnessAlpha, recursiveWitnessY]⟩,
        ⟨"$runtime_x",
          by simp [recursiveWitnessAlpha, recursiveWitnessX]⟩⟩
  have cumulative :
      AlphaCumulativeResidualVariantAgreesOn
        recursiveWitnessAlpha recursiveWitnessAlpha
        recursiveWitnessCanonical [] recursiveWitnessRuntime :=
    ⟨recursiveWitnessRepresentative,
      by
        change TreeSubstitutionVariants
          recursiveWitnessCanonical recursiveWitnessRepresentative
        exact variants,
      canonicalTopological, representativeCovered, ⟨runtimeTopological⟩,
      by
        change AlphaValuationAgreesOn
          recursiveWitnessAlpha recursiveWitnessAlpha
          recursiveWitnessRepresentative recursiveWitnessRuntime
        exact valuation⟩
  have rawLeaf :
      AlphaTermAgrees recursiveWitnessAlpha
        (.variable recursiveWitnessX) (.var "$runtime_x") :=
    .variable (by simp [recursiveWitnessAlpha])
  have supported :
      AlphaTermsSupported recursiveWitnessAlpha recursiveWitnessAlpha
        [(.variable recursiveWitnessX : Term)] := by
    intro term member
    simp only [List.mem_singleton] at member
    subst term
    intro name linked
    exact linked
  obtain ⟨representative, related, representativeCovered, applied⟩ :=
    PLeaTTa.PrologRecursiveCallPayloadBridge.AlphaCumulativeResidualVariantAgreesOn.applyTerms
      cumulative
      (AlphaTermsAgree.cons rawLeaf AlphaTermsAgree.nil)
      supported
  have appliedHead :
      CanonicalRuntimeAgrees recursiveWitnessAlpha
        (TreeSubstitution.apply representative
          (.variable recursiveWitnessX))
        (PLeaTTa.subst recursiveWitnessRuntime
          (.var "$runtime_x")) := by
    cases applied with
    | cons head tail =>
        simpa only [Substitution.denote, List.append_nil, Term.denote] using
          head
  refine ⟨cumulative, ⟨representative,
    by
      simpa only [Substitution.denote, List.append_nil] using related,
    representativeCovered,
    appliedHead⟩,
    ?_⟩
  have canonicalApplied :
      TreeSubstitution.apply recursiveWitnessCanonical
          (.variable recursiveWitnessX) =
        .variable recursiveWitnessY := by
    simp [recursiveWitnessCanonical, recursiveWitnessX, recursiveWitnessY,
      TreeSubstitution.apply, Tree.instantiateOne]
  have runtimeApplied :
      PLeaTTa.subst recursiveWitnessRuntime (.var "$runtime_x") =
        .var "$runtime_x" := by
    exact PLeaTTa.subst_var_of_lookup_none
      recursiveWitnessRuntime "$runtime_x" (by
        simp [recursiveWitnessRuntime, Metta.Subst.lookup])
  rw [canonicalApplied, runtimeApplied]
  change ¬ CanonicalRuntimeAgrees recursiveWitnessAlpha
    (.variable recursiveWitnessY) (.var "$runtime_x")
  intro impossible
  cases impossible with
  | «variable» linked =>
      simp [recursiveWitnessAlpha, recursiveWitnessX, recursiveWitnessY] at linked

/-- Minimal call token used to show that the representative relation is
strictly more expressive than syntactic normalized-call agreement. -/
private def recursiveWitnessCursor : PreparedCursor where
  callGeneration := 0
  predicate := "recursive"
  arguments := [.variable recursiveWitnessX]
  bindings := [(recursiveWitnessX, .variable recursiveWitnessY)]
  reservationStart := 0
  remaining := []
  reservedUntil := 0

/-- The representation-independent call relation is inhabited on the
opposite-orientation recursive witness, while the old syntactic relation is
not.

This is an anti-vacuity check on the new abstraction itself: it accepts a
real semantic residual variant that `NormalizedCallAgrees` provably cannot
express, rather than merely renaming the older premise. -/
theorem representative_call_strictly_extends_normalized_call :
    RepresentativeNormalizedCallAgrees recursiveWitnessAlpha
        recursiveWitnessCursor []
        (PLeaTTa.subst recursiveWitnessRuntime (.var "$runtime_x")) ∧
      ¬ NormalizedCallAgrees recursiveWitnessAlpha
        recursiveWitnessCursor []
        (PLeaTTa.subst recursiveWitnessRuntime (.var "$runtime_x")) := by
  rcases recursive_call_orientation_requires_representative with
    ⟨_cumulative,
      ⟨representative, variants, representativeCovered, reading⟩,
      notDirect⟩
  constructor
  · refine ⟨representative, [], ?_, representativeCovered, ?_, ?_⟩
    · simpa [recursiveWitnessCursor, recursiveWitnessCanonical,
        Substitution.denote, Term.denote] using variants
    · intro entry member
      simp at member
    · exact .cons
        (by
          simpa only [Substitution.denote, List.append_nil, Term.denote] using
            reading)
        .nil
  · intro syntactic
    have direct :
        CanonicalRuntimeAgrees recursiveWitnessAlpha
          (TreeSubstitution.apply recursiveWitnessCanonical
            (.variable recursiveWitnessX))
          (PLeaTTa.subst recursiveWitnessRuntime
            (.var "$runtime_x")) := by
      cases syntactic.arguments with
      | cons head tail =>
          simpa [recursiveWitnessCursor, recursiveWitnessCanonical,
              recursiveWitnessX, recursiveWitnessY,
              TreeSubstitution.apply, Tree.instantiateOne,
              Term.instantiateOne, Term.denote] using
            (PLeaTTa.PrologPrefilterBridge.AlphaTermAgrees.canonicalRuntimeAgrees
              head)
    exact notDirect direct

end PLeaTTa.PrologRecursiveCallPayloadBridge
