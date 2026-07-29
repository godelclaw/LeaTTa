-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologMguBridge
Purpose: Transport one canonical Prolog unifier through one shared runtime
  alpha map into the actual comparator-parametric executable unifier.
Trusted boundary: none
Main exports: AlphaValuationAgrees,
  SharedAlphaEquationsAgree,
  unifyTopExact_complete_of_shared_alpha_equations,
  unifyB_complete_of_shared_alpha_equations
-/
import PLeaTTa.Proofs.PrologPrefilterCallBridge

namespace PLeaTTa.PrologMguBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Canonical
open PrologStateBridge
open PrologPrefilterBridge

/-! ## One shared alpha map

The conservative prefilter may use independent alpha maps on the two sides
because variables are wildcards there.  MGU transport cannot: repeated
variables must retain one name across every equation.  The following
functional condition is the exact part of a finite alpha bijection needed to
compare two runtime realizations of the same canonical tree. -/

/-- One canonical identity has at most one executable spelling in the shared
alpha graph. -/
def AlphaForwardFunctional (alpha : List (LogicVar × String)) : Prop :=
  ∀ {identity left right},
    (identity, left) ∈ alpha →
    (identity, right) ∈ alpha →
    left = right

/-- One executable spelling has at most one canonical identity in the shared
alpha graph.  Later substitution construction needs this inverse direction;
the completeness transport below needs only `AlphaForwardFunctional`. -/
def AlphaBackwardFunctional (alpha : List (LogicVar × String)) : Prop :=
  ∀ {left right name},
    (left, name) ∈ alpha →
    (right, name) ∈ alpha →
    left = right

/-- A finite shared runtime alpha graph is functional in both directions.
This is deliberately a property of the graph itself, so query and freshly
copied clause graphs can later be merged only after their cross-disjointness
has been proved.  Exact duplicate pairs are observationally irrelevant; the
two functional fields exclude every aliasing ambiguity. -/
structure SharedRuntimeAlpha (alpha : List (LogicVar × String)) : Prop where
  forward : AlphaForwardFunctional alpha
  backward : AlphaBackwardFunctional alpha

private def conflictingAlpha : List (LogicVar × String) :=
  [(.source "X", "left"), (.source "X", "right")]

/-- A graph that renames one repeated canonical variable two different ways
is rejected.  This is the small anti-vacuity guard for the shared-alpha
condition: independent per-equation renamings cannot be merged merely by
concatenating their graphs. -/
theorem conflicting_alpha_is_not_shared :
    ¬ SharedRuntimeAlpha conflictingAlpha := by
  intro shared
  have impossible : "left" = "right" :=
    shared.forward (identity := .source "X") (left := "left")
      (right := "right") (by simp [conflictingAlpha])
      (by simp [conflictingAlpha])
  simp at impossible

/-! ## Substitution-independent semantic relation -/

/-- Canonical and executable substitutions agree on every variable named by
one alpha graph.  The relation speaks only about their denotations; it does
not assume identical substitution orientation or list spelling. -/
def AlphaValuationAgrees (alpha : List (LogicVar × String))
    (canonical : TreeSubstitution) (runtime : Subst) : Prop :=
  ∀ {identity name}, (identity, name) ∈ alpha →
    CanonicalRuntimeAgrees alpha
      (TreeSubstitution.apply canonical (.variable identity))
      (PLeaTTa.subst runtime (.var name))

/-- Deep executable substitution commutes with the chain encoder. -/
private theorem subst_chainOf_local (runtime : Subst) (atoms : List Atom) :
    PLeaTTa.subst runtime (chainOf atoms) =
      chainOf (atoms.map (PLeaTTa.subst runtime)) := by
  induction atoms with
  | nil =>
      simp [chainOf, nilA]
  | cons head tail inductionHypothesis =>
      change
        PLeaTTa.subst runtime (consC head (chainOf tail)) =
          consC (PLeaTTa.subst runtime head)
            (chainOf (tail.map (PLeaTTa.subst runtime)))
      rw [show
        PLeaTTa.subst runtime (consC head (chainOf tail)) =
          consC (PLeaTTa.subst runtime head)
            (PLeaTTa.subst runtime (chainOf tail)) by
              simp [consC, PLeaTTa.subst_expr]]
      rw [inductionHypothesis]

/-- Semantic valuation agreement lifts structurally through every supported
canonical/runtime term.  This is the reusable substitution lemma: it neither
constructs nor inspects an executable unifier result. -/
theorem canonicalRuntimeAgrees_apply
    {alpha : List (LogicVar × String)}
    {tree : Tree} {atom : Atom}
    (agreement : CanonicalRuntimeAgrees alpha tree atom)
    {canonical : TreeSubstitution} {runtime : Subst}
    (valuation : AlphaValuationAgrees alpha canonical runtime) :
    CanonicalRuntimeAgrees alpha
      (TreeSubstitution.apply canonical tree)
      (PLeaTTa.subst runtime atom) := by
  induction agreement with
  | «variable» linked =>
      exact valuation linked
  | atom notTrue notFalse =>
      simpa using
        (CanonicalRuntimeAgrees.atom (alpha := alpha) notTrue notFalse)
  | trueAtom =>
      simpa using (CanonicalRuntimeAgrees.trueAtom (alpha := alpha))
  | falseAtom =>
      simpa using (CanonicalRuntimeAgrees.falseAtom (alpha := alpha))
  | integer value =>
      simpa using (CanonicalRuntimeAgrees.integer (alpha := alpha) value)
  | float value =>
      simpa using (CanonicalRuntimeAgrees.float (alpha := alpha) value)
  | string value =>
      simpa using (CanonicalRuntimeAgrees.string (alpha := alpha) value)
  | partialValue arguments inductionHypothesis =>
      simpa [TreeSubstitution.apply_node, subst_chainOf_local] using
        (CanonicalRuntimeAgrees.partialValue inductionHypothesis)
  | nil =>
      simpa [nilA] using (CanonicalRuntimeAgrees.nil (alpha := alpha))
  | cons head tail headInduction tailInduction =>
      simpa [TreeSubstitution.apply_node, consC, PLeaTTa.subst_expr] using
        (CanonicalRuntimeAgrees.cons headInduction tailInduction)

/-! ## Common canonical denotation implies runtime comparator equivalence -/

/-- Exact chain construction preserves comparator-relative equivalence. -/
private theorem chainOf_equivalent
    {left right : List Atom}
    (equivalent :
      AtomsEquivalentWith PLeaTTa.prologGroundIdentical left right) :
    AtomEquivalentWith PLeaTTa.prologGroundIdentical
      (chainOf left) (chainOf right) := by
  induction left generalizing right with
  | nil =>
      cases equivalent
      exact .symbol "#nil"
  | cons leftHead leftTail inductionHypothesis =>
      cases equivalent with
      | cons head tail =>
          exact .expression
            (.cons (.symbol "#c")
              (.cons head
                (.cons (inductionHypothesis tail) .nil)))

/-- Inversion for the non-injective runtime-float-to-Prolog-key projection.
The canonical-key equality is retained explicitly rather than asking
dependent elimination to recover raw `Float` equality, which is false for
distinct NaN payloads. -/
private theorem canonicalRuntimeAgrees_float_inv
    {alpha : List (LogicVar × String)}
    {identity : PLeaTTa.PrologFloatIdentity} {atom : Atom}
    (agreement :
      CanonicalRuntimeAgrees alpha (.node (.float identity) []) atom) :
    ∃ value : Float,
      atom = .gnd (.float value) ∧
        PLeaTTa.PrologFloatIdentity.ofFloat value = identity := by
  cases agreement with
  | float value =>
      exact ⟨value, rfl, rfl⟩

/-- Runtime spelling of one independent Prolog atom at the PeTTa boundary. -/
private def runtimeAtomName (name : String) : String :=
  if name = "true" then "True"
  else if name = "false" then "False"
  else name

/-- Inversion for the three source-atom spelling constructors. -/
private theorem canonicalRuntimeAgrees_atom_inv
    {alpha : List (LogicVar × String)}
    {name : String} {atom : Atom}
    (agreement :
      CanonicalRuntimeAgrees alpha (.node (.atom name) []) atom) :
    atom = .sym (runtimeAtomName name) := by
  cases agreement with
  | atom notTrue notFalse =>
      simp [runtimeAtomName, notTrue, notFalse]
  | trueAtom =>
      simp [runtimeAtomName]
  | falseAtom =>
      simp [runtimeAtomName]

/-- Two runtime encodings of the same canonical tree are equivalent under
exact Prolog ground identity.  Forward functionality is load-bearing only
for variables; NaN payloads are compared by their shared canonical float
identity rather than by raw `Float` equality. -/
theorem CanonicalRuntimeAgrees.equivalent_of_same
    {alpha : List (LogicVar × String)}
    (functional : AlphaForwardFunctional alpha)
    {tree : Tree} {left right : Atom}
    (leftAgreement : CanonicalRuntimeAgrees alpha tree left)
    (rightAgreement : CanonicalRuntimeAgrees alpha tree right) :
    AtomEquivalentWith PLeaTTa.prologGroundIdentical left right := by
  induction leftAgreement generalizing right with
  | «variable» leftLinked =>
      cases rightAgreement with
      | «variable» rightLinked =>
          rw [functional leftLinked rightLinked]
          exact .variable _
  | atom notTrue notFalse =>
      have rightShape := canonicalRuntimeAgrees_atom_inv rightAgreement
      rw [rightShape]
      simp [runtimeAtomName, notTrue, notFalse]
      exact .symbol _
  | trueAtom =>
      have rightShape := canonicalRuntimeAgrees_atom_inv rightAgreement
      rw [rightShape]
      simp [runtimeAtomName]
      exact .symbol _
  | falseAtom =>
      have rightShape := canonicalRuntimeAgrees_atom_inv rightAgreement
      rw [rightShape]
      simp [runtimeAtomName]
      exact .symbol _
  | integer value =>
      cases rightAgreement with
      | integer =>
          exact .ground (PLeaTTa.prologGroundIdentical_self _)
  | float value =>
      obtain ⟨rightValue, rfl, identity⟩ :=
        canonicalRuntimeAgrees_float_inv rightAgreement
      apply AtomEquivalentWith.ground
      rw [PLeaTTa.prologGroundIdentical_eq_true_iff]
      simp only [PLeaTTa.PrologGroundIdentity.ofGround,
        PrologGroundIdentity.floating.injEq]
      exact identity.symm
  | string value =>
      cases rightAgreement with
      | string =>
          exact .ground (PLeaTTa.prologGroundIdentical_self _)
  | partialValue arguments inductionHypothesis =>
      cases rightAgreement with
      | partialValue rightArguments =>
          apply chainOf_equivalent
          exact .cons (.symbol "partial")
            (.cons (.symbol _) (.cons
              (inductionHypothesis rightArguments) .nil))
  | nil =>
      cases rightAgreement with
      | nil =>
          exact .symbol _
  | cons head tail headInduction tailInduction =>
      cases rightAgreement with
      | cons rightHead rightTail =>
          exact .expression
            (.cons (.symbol "#c")
              (.cons (headInduction rightHead)
                (.cons (tailInduction rightTail) .nil)))

/-! ## Ordered head-equation transport -/

/-- Every equation in one canonical head worklist is represented by the two
runtime atom lists under the same alpha graph.  Unlike the conservative
prefilter relation, this type cannot choose a fresh graph per equation. -/
inductive SharedAlphaEquationsAgree
    (alpha : List (LogicVar × String)) :
    List (Term × Term) → List Atom → List Atom → Prop where
  | nil : SharedAlphaEquationsAgree alpha [] [] []
  | cons {leftTerm rightTerm : Term} {leftAtom rightAtom : Atom}
      {equations : List (Term × Term)}
      {leftAtoms rightAtoms : List Atom}
      (left : AlphaTermAgrees alpha leftTerm leftAtom)
      (right : AlphaTermAgrees alpha rightTerm rightAtom)
      (tail :
        SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms) :
      SharedAlphaEquationsAgree alpha
        ((leftTerm, rightTerm) :: equations)
        (leftAtom :: leftAtoms) (rightAtom :: rightAtoms)

/-- A shared-alpha valuation implementing one canonical unifier makes the
two complete runtime head payloads comparator-equivalent after deep
substitution. -/
theorem SharedAlphaEquationsAgree.atomsEquivalent_of_unifier
    {alpha : List (LogicVar × String)}
    (functional : AlphaForwardFunctional alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    {candidate : Substitution} {runtime : Subst}
    (valuation :
      AlphaValuationAgrees alpha (Substitution.denote candidate) runtime)
    (unifies : DenotationalUnifiesEquations candidate equations) :
    AtomsEquivalentWith PLeaTTa.prologGroundIdentical
      (leftAtoms.map (PLeaTTa.subst runtime))
      (rightAtoms.map (PLeaTTa.subst runtime)) := by
  induction agreement with
  | nil =>
      exact .nil
  | @cons leftTerm rightTerm leftAtom rightAtom equations leftAtoms
      rightAtoms left right tail inductionHypothesis =>
      have leftApplied :=
        canonicalRuntimeAgrees_apply
          (AlphaTermAgrees.canonicalRuntimeAgrees left) valuation
      have rightApplied :=
        canonicalRuntimeAgrees_apply
          (AlphaTermAgrees.canonicalRuntimeAgrees right) valuation
      have headEquality :
          TreeSubstitution.apply (Substitution.denote candidate)
              (Term.denote leftTerm) =
            TreeSubstitution.apply (Substitution.denote candidate)
              (Term.denote rightTerm) :=
        unifies (leftTerm, rightTerm) (by simp)
      rw [headEquality] at leftApplied
      exact .cons
        (CanonicalRuntimeAgrees.equivalent_of_same
          functional leftApplied rightApplied)
        (inductionHypothesis (by
          intro equation member
          exact unifies equation (List.mem_cons_of_mem _ member)))

/-- The comparator-relative unifier witness for the two expression payloads
assembled from a shared-alpha canonical head. -/
theorem SharedAlphaEquationsAgree.deepEquivalentUnifies
    {alpha : List (LogicVar × String)}
    (functional : AlphaForwardFunctional alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    {candidate : Substitution} {runtime : Subst}
    (valuation :
      AlphaValuationAgrees alpha (Substitution.denote candidate) runtime)
    (unifies : DenotationalUnifiesEquations candidate equations) :
    PLeaTTa.DeepEquivalentUnifies PLeaTTa.prologGroundIdentical runtime
      [(.expr leftAtoms, .expr rightAtoms)] := by
  intro equation member
  simp only [List.mem_singleton] at member
  subst equation
  simp only [PLeaTTa.subst_expr]
  exact .expression
    (agreement.atomsEquivalent_of_unifier functional valuation unifies)

/-- A canonical shared-alpha head unifier reaches the actual executable
top-level unifier. -/
theorem unifyTopExact_complete_of_shared_alpha_equations
    {alpha : List (LogicVar × String)}
    (functional : AlphaForwardFunctional alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    {candidate : Substitution} {runtime : Subst}
    (valuation :
      AlphaValuationAgrees alpha (Substitution.denote candidate) runtime)
    (unifies : DenotationalUnifiesEquations candidate equations) :
    ∃ result,
      PLeaTTa.unifyTopExact (.expr leftAtoms) (.expr rightAtoms) =
        some result := by
  apply PLeaTTa.unifyTopExact_complete_of_prolog_equivalent_unifier
    (.expr leftAtoms) (.expr rightAtoms) runtime
  exact agreement.deepEquivalentUnifies functional valuation unifies
    (.expr leftAtoms, .expr rightAtoms) (by simp)

/-- The same bridge after an existing executable binding has normalized the
raw head payload.  The relation is stated on the exact post-`base` atoms,
matching `unifyB` rather than assuming the base substitution is empty. -/
theorem unifyB_complete_of_shared_alpha_equations
    (base : Subst)
    {alpha : List (LogicVar × String)}
    (functional : AlphaForwardFunctional alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations
        (leftAtoms.map (PLeaTTa.subst base))
        (rightAtoms.map (PLeaTTa.subst base)))
    {candidate : Substitution} {runtime : Subst}
    (valuation :
      AlphaValuationAgrees alpha (Substitution.denote candidate) runtime)
    (unifies : DenotationalUnifiesEquations candidate equations) :
    ∃ result,
      PLeaTTa.unifyB base (.expr leftAtoms) (.expr rightAtoms) =
        some result := by
  apply PLeaTTa.unifyB_complete_of_prolog_equivalent_unifier
    base (.expr leftAtoms) (.expr rightAtoms) runtime
  simpa only [PLeaTTa.subst_expr] using
    (agreement.deepEquivalentUnifies functional valuation unifies
      (.expr (leftAtoms.map (PLeaTTa.subst base)),
        .expr (rightAtoms.map (PLeaTTa.subst base))) (by simp))

/-! ## Anti-vacuity: repeated variable plus distinct NaN payloads -/

private def nanAlpha : List (LogicVar × String) :=
  [(.source "X", "X")]

private def nanCanonicalEquations :
    List (Term × Term) :=
  [(.variable (.source "X"), .float .nan),
   (.variable (.source "X"), .float .nan)]

private def nanCanonicalBinding : Substitution :=
  [(.source "X", .float .nan)]

/-- The bridge is strong enough to preserve one repeated-variable constraint
across two distinct runtime NaN payloads.  A relation that forgot either the
shared alpha map or Prolog's NaN identity could not prove this witness. -/
theorem repeated_variable_distinct_nan_payloads_complete
    (left right : Float)
    (leftNan : left.isNaN = true)
    (rightNan : right.isNaN = true) :
    ∃ result,
      PLeaTTa.unifyTopExact
          (.expr [.var "X", .var "X"])
          (.expr [.gnd (.float left), .gnd (.float right)]) =
        some result := by
  let runtime : Subst := [("X", .gnd (.float left))]
  have functional : AlphaForwardFunctional nanAlpha := by
    intro identity first second firstMember secondMember
    simp [nanAlpha] at firstMember secondMember
    exact firstMember.2.trans secondMember.2.symm
  have agreement :
      SharedAlphaEquationsAgree nanAlpha nanCanonicalEquations
        [.var "X", .var "X"]
        [.gnd (.float left), .gnd (.float right)] := by
    exact .cons
      (.variable (by simp [nanAlpha]))
      (by
        simpa [PLeaTTa.PrologFloatIdentity.ofFloat, leftNan] using
          (AlphaTermAgrees.float (alpha := nanAlpha) left))
      (.cons
        (.variable (by simp [nanAlpha]))
        (by
          simpa [PLeaTTa.PrologFloatIdentity.ofFloat, rightNan] using
            (AlphaTermAgrees.float (alpha := nanAlpha) right))
        .nil)
  have valuation :
      AlphaValuationAgrees nanAlpha
        (Substitution.denote nanCanonicalBinding) runtime := by
    intro identity name member
    simp [nanAlpha] at member
    rcases member with ⟨rfl, rfl⟩
    change
      CanonicalRuntimeAgrees nanAlpha
        (TreeSubstitution.apply
          [(.source "X", .node (.float .nan) [])]
          (.variable (.source "X")))
        (PLeaTTa.subst runtime (.var "X"))
    simpa [TreeSubstitution.apply, Tree.instantiateOne, runtime,
      PLeaTTa.subst, PLeaTTa.substN, Metta.Subst.lookup,
      PLeaTTa.PrologFloatIdentity.ofFloat, leftNan] using
        (CanonicalRuntimeAgrees.float (alpha := nanAlpha) left)
  have unifies :
      DenotationalUnifiesEquations nanCanonicalBinding
        nanCanonicalEquations := by
    intro equation member
    have equationShape :
        equation =
          (.variable (.source "X"), .float .nan) := by
      simpa [nanCanonicalEquations] using member
    subst equation
    simp [DenotationalUnifier, nanCanonicalBinding, Term.denote,
      Substitution.denote, TreeSubstitution.apply, Tree.instantiateOne]
  exact unifyTopExact_complete_of_shared_alpha_equations
    functional agreement valuation unifies

end PLeaTTa.PrologMguBridge
