-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologMguDirectSimulation
Purpose: Source-guided simulation of the independent ordered finite-tree
  unifier by the executable comparator-parametric worklist algorithm.
Trusted boundary: none
Main exports:
  CanonicalRuntimeAgrees.occurs_eq,
  CanonicalRuntimeAgrees.instantiateOne,
  CanonicalRuntimeAgrees.decomposeEqWith_same,
  CanonicalRuntimeAgrees.unifyTopExact_bindLeft,
  CanonicalRuntimeAgrees.unifyTopExact_bindRight
-/
import PLeaTTa.Proofs.PrologMguExecutableOpenFactor

namespace PLeaTTa.PrologMguDirectSimulation

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PrologMguBridge
open PrologMguOpenAgreement
open PrologMguExecutableOpenFactor
open PrologPrefilterBridge

/-! ## Exact alpha transport of the occurs check -/

mutual

/-- A bidirectionally functional shared alpha graph transports the
finite-tree occurs check exactly.  The inverse-functional half is
load-bearing: without it, two independent variables could share one
executable name and create a false runtime occurrence. -/
theorem CanonicalRuntimeAgrees.occurs_eq
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {source : LogicVar} {name : String}
    (linked : (source, name) ∈ alpha)
    {tree : Tree} {atom : Atom}
    (agreement : CanonicalRuntimeAgrees alpha tree atom) :
    Tree.occurs source tree =
      Metta.Subst.occurs name atom := by
  induction agreement with
  | @«variable» identity runtimeName identityLinked =>
      by_cases sameIdentity : identity = source
      · subst identity
        have sameName : runtimeName = name :=
          shared.forward identityLinked linked
        subst runtimeName
        simp [Tree.occurs, Metta.Subst.occurs]
      · have differentName : runtimeName ≠ name := by
          intro sameName
          subst runtimeName
          exact sameIdentity (shared.backward identityLinked linked)
        have reverseDifferent : name ≠ runtimeName :=
          fun sameName => differentName sameName.symm
        simp [Tree.occurs, Metta.Subst.occurs, sameIdentity,
          reverseDifferent]
  | atom | trueAtom | falseAtom | integer | float | string | nil =>
      simp [Tree.occurs, Trees.occurs, nilA, Metta.Subst.occurs]
  | @partialValue head argumentsTree encodedArguments arguments
      inductionHypothesis =>
      simpa [Tree.occurs, Trees.occurs, chainOf, consC, nilA,
        Metta.Subst.occurs] using inductionHypothesis
  | @cons headTree tailTree headAtom tailAtom head tail
      headInduction tailInduction =>
      simp [Tree.occurs, Trees.occurs, consC,
        Metta.Subst.occurs, headInduction, tailInduction]

end

/-! ## Exact one-pass normalization -/

/-- One alpha-aligned canonical singleton substitution commutes with the
executable unifier's one-pass singleton application.  This is deliberately
about `Tree.instantiateOne` and `Metta.Subst.apply`, not the deep semantic
substitutions used by the MGU theorems: these are the two operations that
normalize the remaining worklist after one elimination round. -/
theorem CanonicalRuntimeAgrees.instantiateOne
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {source : LogicVar} {name : String}
    (linked : (source, name) ∈ alpha)
    {replacement : Tree} {target : Atom}
    (replacementAgreement :
      CanonicalRuntimeAgrees alpha replacement target)
    {tree : Tree} {atom : Atom}
    (agreement : CanonicalRuntimeAgrees alpha tree atom) :
    CanonicalRuntimeAgrees alpha
      (Tree.instantiateOne source replacement tree)
      (Metta.Subst.apply [(name, target)] atom) := by
  induction agreement with
  | @«variable» identity runtimeName identityLinked =>
      by_cases sameIdentity : identity = source
      · subst identity
        have sameName : runtimeName = name :=
          shared.forward identityLinked linked
        subst runtimeName
        simpa [Tree.instantiateOne, Metta.Subst.apply,
          Metta.Subst.lookup] using replacementAgreement
      · have differentName : runtimeName ≠ name := by
          intro sameName
          subst runtimeName
          exact sameIdentity (shared.backward identityLinked linked)
        have reverseDifferent : name ≠ runtimeName :=
          fun sameName => differentName sameName.symm
        simpa [Tree.instantiateOne, Metta.Subst.apply,
          Metta.Subst.lookup, sameIdentity, differentName,
          reverseDifferent] using
            (CanonicalRuntimeAgrees.variable identityLinked)
  | atom notTrue notFalse =>
      simpa [Tree.instantiateOne, Trees.instantiateOne,
        Metta.Subst.apply] using
        (CanonicalRuntimeAgrees.atom (alpha := alpha) notTrue notFalse)
  | trueAtom =>
      simpa [Tree.instantiateOne, Trees.instantiateOne,
        Metta.Subst.apply] using
        (CanonicalRuntimeAgrees.trueAtom (alpha := alpha))
  | falseAtom =>
      simpa [Tree.instantiateOne, Trees.instantiateOne,
        Metta.Subst.apply] using
        (CanonicalRuntimeAgrees.falseAtom (alpha := alpha))
  | integer value =>
      simpa [Tree.instantiateOne, Trees.instantiateOne,
        Metta.Subst.apply] using
        (CanonicalRuntimeAgrees.integer (alpha := alpha) value)
  | float value =>
      simpa [Tree.instantiateOne, Trees.instantiateOne,
        Metta.Subst.apply] using
        (CanonicalRuntimeAgrees.float (alpha := alpha) value)
  | string value =>
      simpa [Tree.instantiateOne, Trees.instantiateOne,
        Metta.Subst.apply] using
        (CanonicalRuntimeAgrees.string (alpha := alpha) value)
  | partialValue arguments inductionHypothesis =>
      simpa [Tree.instantiateOne, Trees.instantiateOne,
        chainOf, consC, nilA, Metta.Subst.apply] using
          (CanonicalRuntimeAgrees.partialValue inductionHypothesis)
  | nil =>
      simpa [Tree.instantiateOne, Trees.instantiateOne,
        nilA, Metta.Subst.apply] using
        (CanonicalRuntimeAgrees.nil (alpha := alpha))
  | cons head tail headInduction tailInduction =>
      simpa [Tree.instantiateOne, Trees.instantiateOne,
        consC, Metta.Subst.apply] using
          (CanonicalRuntimeAgrees.cons headInduction tailInduction)

/-! ## Source-guided reflexive decomposition -/

mutual

/-- Structural comparator-equivalence produces no executable variable
constraints. -/
theorem atomEquivalent_decomposeEqWith_empty
    (groundEq : Metta.Ground → Metta.Ground → Bool) :
    ∀ {left right : Atom},
      PLeaTTa.AtomEquivalentWith groundEq left right →
        Metta.Unify.decomposeEqWith groundEq left right = some []
  | _, _, .symbol _ => by
      simp [Metta.Unify.decomposeEqWith]
  | _, _, .variable _ => by
      simp [Metta.Unify.decomposeEqWith]
  | _, _, .ground identical => by
      simp [Metta.Unify.decomposeEqWith, identical]
  | _, _, .expression children => by
      simpa [Metta.Unify.decomposeEqWith] using
        atomsEquivalent_decomposeListWith_empty groundEq children

/-- Ordered-list companion to empty structural decomposition. -/
theorem atomsEquivalent_decomposeListWith_empty
    (groundEq : Metta.Ground → Metta.Ground → Bool) :
    ∀ {left right : List Atom},
      PLeaTTa.AtomsEquivalentWith groundEq left right →
        Metta.Unify.decomposeListWith groundEq left right = some []
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      simp [Metta.Unify.decomposeListWith,
        atomEquivalent_decomposeEqWith_empty groundEq head,
        atomsEquivalent_decomposeListWith_empty groundEq tail]

end

/-- Two executable encodings of the same canonical tree decompose to no
constraints.  This is stronger than semantic equivalence: it pins the exact
worklist shape consumed by the executable round loop, including distinct
IEEE NaN payloads with one SWI identity. -/
theorem CanonicalRuntimeAgrees.decomposeEqWith_same
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {tree : Tree} {left right : Atom}
    (leftAgreement : CanonicalRuntimeAgrees alpha tree left)
    (rightAgreement : CanonicalRuntimeAgrees alpha tree right) :
    Metta.Unify.decomposeEqWith PLeaTTa.prologGroundIdentical left right =
      some [] := by
  exact
    atomEquivalent_decomposeEqWith_empty
      PLeaTTa.prologGroundIdentical
      (CanonicalRuntimeAgrees.equivalent_of_same
        shared.forward leftAgreement rightAgreement)

/-- An empty structural decomposition makes the top-level executable
unifier return the empty substitution exactly. -/
theorem unifyTopExact_of_decompose_empty
    (left right : Atom)
    (decomposed :
      Metta.Unify.decomposeEqWith PLeaTTa.prologGroundIdentical
          left right =
        some []) :
    PLeaTTa.unifyTopExact left right = some [] := by
  have positive : 0 < left.size + right.size := by
    cases left <;> cases right <;> simp [Atom.size]
  obtain ⟨fuel, fuelEq⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  unfold PLeaTTa.unifyTopExact Metta.Unify.unifyTopWith
  rw [fuelEq]
  simp [Metta.Unify.unifyRoundsWith,
    Metta.Unify.decomposeAllWith, decomposed]

/-- The reflexive independent MGU and the executable empty result have the
same exact substitution spelling. -/
theorem CanonicalRuntimeAgrees.unifyTopExact_reflexive
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {tree : Tree} {left right : Atom}
    (leftAgreement : CanonicalRuntimeAgrees alpha tree left)
    (rightAgreement : CanonicalRuntimeAgrees alpha tree right) :
    PLeaTTa.unifyTopExact left right = some [] ∧
      AlphaTreeSubstitutionAgrees alpha [] [] := by
  exact
    ⟨unifyTopExact_of_decompose_empty left right
        (PLeaTTa.PrologMguDirectSimulation.CanonicalRuntimeAgrees.decomposeEqWith_same
          shared leftAgreement rightAgreement),
      .nil⟩

/-! ## Ordered variable-elimination base cases -/

/-- Runtime spelling of an independent left-variable elimination is the
exact singleton chosen by the executable algorithm. -/
theorem CanonicalRuntimeAgrees.unifyTopExact_bindLeft
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {source : LogicVar} {name : String}
    (linked : (source, name) ∈ alpha)
    {value : Tree} {target : Atom}
    (agreement : CanonicalRuntimeAgrees alpha value target)
    (absent : Tree.occurs source value = false) :
    PLeaTTa.unifyTopExact (.var name) target =
        some [(name, target)] ∧
      AlphaTreeSubstitutionAgrees alpha
        [(source, value)] [(name, target)] := by
  have runtimeAbsent :
      Metta.Subst.occurs name target = false := by
    rw [← PLeaTTa.PrologMguDirectSimulation.CanonicalRuntimeAgrees.occurs_eq
      shared linked agreement]
    exact absent
  constructor
  · exact
      PLeaTTa.PrologCoreAdequacy.unifyTopWith_fresh_variable
        PLeaTTa.prologGroundIdentical name target runtimeAbsent
  · exact .cons linked agreement .nil

/-- Runtime spelling of an independent right-variable elimination is the
same singleton, with the executable decomposition preserving the canonical
right-variable orientation. -/
theorem CanonicalRuntimeAgrees.unifyTopExact_bindRight
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {target : LogicVar} {name : String}
    (linked : (target, name) ∈ alpha)
    {value : Tree} {source : Atom}
    (agreement : CanonicalRuntimeAgrees alpha value source)
    (notVariable : ∀ identity, value ≠ .variable identity)
    (absent : Tree.occurs target value = false) :
    PLeaTTa.unifyTopExact source (.var name) =
        some [(name, source)] ∧
      AlphaTreeSubstitutionAgrees alpha
        [(target, value)] [(name, source)] := by
  have runtimeAbsent :
      Metta.Subst.occurs name source = false := by
    rw [← PLeaTTa.PrologMguDirectSimulation.CanonicalRuntimeAgrees.occurs_eq
      shared linked agreement]
    exact absent
  have sourceNotVariable : ∀ candidate, source ≠ .var candidate := by
    intro candidate equality
    subst source
    cases agreement with
    | «variable» candidateLinked =>
        exact notVariable _ rfl
  have underlying :
      Metta.Unify.unifyTopWith PLeaTTa.prologGroundIdentical
          source (.var name) =
        some [(name, source)] := by
    have decomposition :
        Metta.Unify.decomposeEqWith PLeaTTa.prologGroundIdentical
            source (.var name) =
          some [(name, source)] := by
      cases source <;> simp_all [Metta.Unify.decomposeEqWith]
    have positive :
        0 < source.size + (Atom.var name).size := by
      cases source <;> simp [Atom.size]
    obtain ⟨fuel, fuelEq⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
    have done :
        Metta.Unify.unifyRoundsWith PLeaTTa.prologGroundIdentical
            fuel [] [(name, source)] =
          some [(name, source)] := by
      cases fuel <;> rfl
    unfold Metta.Unify.unifyTopWith
    rw [fuelEq]
    simp [Metta.Unify.unifyRoundsWith,
      Metta.Unify.decomposeAllWith, decomposition, runtimeAbsent,
      Metta.Subst.extend, Metta.Subst.erase, done]
  constructor
  · simpa [PLeaTTa.unifyTopExact] using underlying
  · exact .cons linked agreement .nil

/-! ### Anti-vacuity -/

private def occursWitnessLeft : LogicVar := .source "left"
private def occursWitnessRight : LogicVar := .source "right"
private def occursWitnessAlpha : List (LogicVar × String) :=
  [(occursWitnessLeft, "X"), (occursWitnessRight, "Y")]

private theorem occursWitnessShared :
    SharedRuntimeAlpha occursWitnessAlpha := by
  constructor <;>
    intro left right name leftMember rightMember <;>
    simp [occursWitnessAlpha, occursWitnessLeft, occursWitnessRight]
      at leftMember rightMember <;>
    rcases leftMember with leftMember | leftMember <;>
    rcases rightMember with rightMember | rightMember <;>
    simp_all

/-- A distinct alpha-linked variable is absent on both sides, while the
linked source itself occurs on both sides.  This rejects a one-way or
constant occurs transport theorem. -/
theorem occurs_transport_distinguishes_aliases :
    Tree.occurs occursWitnessLeft (.variable occursWitnessLeft) =
        Metta.Subst.occurs "X" (.var "X") ∧
      Tree.occurs occursWitnessLeft (.variable occursWitnessRight) =
        Metta.Subst.occurs "X" (.var "Y") ∧
      Metta.Subst.occurs "X" (.var "X") = true ∧
      Metta.Subst.occurs "X" (.var "Y") = false := by
  have selfAgreement :
      CanonicalRuntimeAgrees occursWitnessAlpha
        (.variable occursWitnessLeft) (.var "X") :=
    .variable (by simp [occursWitnessAlpha])
  have otherAgreement :
      CanonicalRuntimeAgrees occursWitnessAlpha
        (.variable occursWitnessRight) (.var "Y") :=
    .variable (by simp [occursWitnessAlpha])
  exact
    ⟨PLeaTTa.PrologMguDirectSimulation.CanonicalRuntimeAgrees.occurs_eq
        occursWitnessShared (by simp [occursWitnessAlpha]) selfAgreement,
      PLeaTTa.PrologMguDirectSimulation.CanonicalRuntimeAgrees.occurs_eq
        occursWitnessShared (by simp [occursWitnessAlpha]) otherAgreement,
      by simp [Metta.Subst.occurs],
      by simp [Metta.Subst.occurs]⟩

end PLeaTTa.PrologMguDirectSimulation
