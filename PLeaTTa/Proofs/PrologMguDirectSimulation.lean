-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologMguDirectSimulation
Purpose: Source-guided simulation of the independent ordered finite-tree
  unifier by the executable comparator-parametric worklist algorithm.
Trusted boundary: none
Main exports:
  CanonicalRuntimeAgrees.occurs_eq,
  CanonicalRuntimeAgrees.instantiateOne,
  treeEquationsDecompose_iff_function,
  TreeEquationsDecompose.instantiateOne_unificationEquivalent,
  treeUnifyRounds_complete_of_unifier,
  TreeDecomposes.runtime,
  TreeEquationsDecompose.runtime,
  TreeUnifyRounds.runtime,
  TreeUnifyRounds.result_topological,
  TreeUnifyRounds.isMostGeneral,
  OrderedTreeMgu.unifyTopExact_exists_alpha_mgu,
  OrderedTreeMgu.unifyB_exists_alpha_mgu,
  FreshenedClauseAlphaAgrees.unifyB_exists_direct_alpha_mgu,
  CanonicalRuntimeAgrees.unifyTopExact_bindLeft,
  CanonicalRuntimeAgrees.unifyTopExact_bindRight
-/
import PLeaTTa.Proofs.PrologMguExecutableOpenFactor

namespace PLeaTTa.PrologMguDirectSimulation

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Resolver
open PeTTaSpec.PrologCore.Canonical
open PrologMguBridge
open PrologMguOpenAgreement
open PrologMguExecutableOpenFactor
open PrologMguTopology
open PrologPrefilterBridge
open PrologStateBridge

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
      simpa [Tree.occurs, Trees.occurs, partialC, partialTagA, chainOf,
        consC, nilA, Metta.Subst.occurs] using inductionHypothesis
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
      simpa [Tree.instantiateOne, Trees.instantiateOne, partialC,
        partialTagA, chainOf, consC, nilA, Metta.Subst.apply] using
          (CanonicalRuntimeAgrees.partialValue inductionHypothesis)
  | nil =>
      simpa [Tree.instantiateOne, Trees.instantiateOne,
        nilA, Metta.Subst.apply] using
        (CanonicalRuntimeAgrees.nil (alpha := alpha))
  | cons head tail headInduction tailInduction =>
      simpa [Tree.instantiateOne, Trees.instantiateOne,
        consC, Metta.Subst.apply] using
          (CanonicalRuntimeAgrees.cons headInduction tailInduction)

/-! ## Source-guided equation and constraint worklists -/

/-- One canonical/runtime equation pair is represented pointwise under the
same alpha graph. -/
structure AlphaTreeEquationAgrees
    (alpha : List (LogicVar × String))
    (canonical : TreeEquation) (runtime : Atom × Atom) : Prop where
  left : CanonicalRuntimeAgrees alpha canonical.1 runtime.1
  right : CanonicalRuntimeAgrees alpha canonical.2 runtime.2

/-- Ordered worklist agreement; order is part of the relation. -/
abbrev AlphaTreeEquationsAgree
    (alpha : List (LogicVar × String))
    (canonical : List TreeEquation)
    (runtime : List (Atom × Atom)) : Prop :=
  List.Forall₂ (AlphaTreeEquationAgrees alpha) canonical runtime

/-- A canonical/runtime variable constraint has an alpha-aligned key and a
structurally aligned replacement. -/
structure AlphaTreeConstraintAgrees
    (alpha : List (LogicVar × String))
    (canonical : LogicVar × Tree)
    (runtime : String × Atom) : Prop where
  key : (canonical.1, runtime.1) ∈ alpha
  replacement :
    CanonicalRuntimeAgrees alpha canonical.2 runtime.2

/-- Ordered flattened-constraint agreement. -/
abbrev AlphaTreeConstraintsAgree
    (alpha : List (LogicVar × String))
    (canonical : List (LogicVar × Tree))
    (runtime : List (String × Atom)) : Prop :=
  List.Forall₂ (AlphaTreeConstraintAgrees alpha) canonical runtime

/-- Canonical one-pass normalization of the remaining flattened
constraints after eliminating one variable. -/
def normalizeTreeConstraints
    (source : LogicVar) (replacement : Tree)
    (constraints : List (LogicVar × Tree)) : List TreeEquation :=
  constraints.map fun item =>
    (Tree.instantiateOne source replacement (.variable item.1),
      Tree.instantiateOne source replacement item.2)

/-- The exact equation worklist produced after eliminating one aligned
constraint remains pointwise alpha-related.  Both sides use their real
one-pass operations; no deep-substitution theorem or decoded runtime atom is
smuggled into the statement. -/
theorem AlphaTreeConstraintsAgree.instantiateOne
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {source : LogicVar} {name : String}
    (linked : (source, name) ∈ alpha)
    {replacement : Tree} {target : Atom}
    (replacementAgreement :
      CanonicalRuntimeAgrees alpha replacement target)
    {canonical : List (LogicVar × Tree)}
    {runtime : List (String × Atom)}
    (agreement :
      AlphaTreeConstraintsAgree alpha canonical runtime) :
    AlphaTreeEquationsAgree alpha
      (normalizeTreeConstraints source replacement canonical)
      (runtime.map fun item =>
        (Metta.Subst.apply [(name, target)] (.var item.1),
          Metta.Subst.apply [(name, target)] item.2)) := by
  unfold normalizeTreeConstraints
  induction agreement with
  | nil =>
      exact .nil
  | @cons canonicalHead runtimeHead canonicalTail runtimeTail
      head tail inductionHypothesis =>
      exact .cons
        ⟨PLeaTTa.PrologMguDirectSimulation.CanonicalRuntimeAgrees.instantiateOne
            shared linked replacementAgreement
              (CanonicalRuntimeAgrees.variable head.key),
          PLeaTTa.PrologMguDirectSimulation.CanonicalRuntimeAgrees.instantiateOne
            shared linked replacementAgreement head.replacement⟩
        inductionHypothesis

mutual

/-- Canonical structural decomposition into the ordered variable
constraints consumed by Robinson elimination.  This is an independent,
relation-valued counterpart of executable `decomposeEqWith`: no runtime
atom or Boolean ground comparator appears here. -/
inductive TreeDecomposes :
    Tree → Tree → List (LogicVar × Tree) → Prop where
  | reflexiveVariable (identity : LogicVar) :
      TreeDecomposes (.variable identity) (.variable identity) []
  | bindLeft (source : LogicVar) (value : Tree)
      (different : value ≠ .variable source) :
      TreeDecomposes (.variable source) value [(source, value)]
  | bindRight (value : Tree) (target : LogicVar)
      (notVariable : ∀ identity, value ≠ .variable identity) :
      TreeDecomposes value (.variable target) [(target, value)]
  | node (symbol : RigidSymbol) {left right : List Tree}
      {constraints : List (LogicVar × Tree)}
      (children : TreesDecompose left right constraints) :
      TreeDecomposes (.node symbol left) (.node symbol right) constraints

/-- Ordered child-list decomposition.  Head constraints precede tail
constraints exactly, matching executable list decomposition. -/
inductive TreesDecompose :
    List Tree → List Tree → List (LogicVar × Tree) → Prop where
  | nil : TreesDecompose [] [] []
  | cons {leftHead rightHead : Tree} {leftTail rightTail : List Tree}
      {headConstraints tailConstraints : List (LogicVar × Tree)}
      (head :
        TreeDecomposes leftHead rightHead headConstraints)
      (tail :
        TreesDecompose leftTail rightTail tailConstraints) :
      TreesDecompose
        (leftHead :: leftTail) (rightHead :: rightTail)
        (headConstraints ++ tailConstraints)

end

/-- Independent ordered decomposition of a complete equation worklist.
Constraints from earlier equations precede constraints from later equations,
matching the executable `decomposeAllWith` traversal. -/
inductive TreeEquationsDecompose :
    List TreeEquation → List (LogicVar × Tree) → Prop where
  | nil : TreeEquationsDecompose [] []
  | cons {left right : Tree} {equations : List TreeEquation}
      {headConstraints tailConstraints : List (LogicVar × Tree)}
      (head : TreeDecomposes left right headConstraints)
      (tail : TreeEquationsDecompose equations tailConstraints) :
      TreeEquationsDecompose
        ((left, right) :: equations)
        (headConstraints ++ tailConstraints)

/-! ## Independent executable presentation of canonical decomposition -/

mutual

/-- Canonical-tree structural decomposition.  This function contains no
runtime atom, ground comparator, or encoding convention; the relation above
remains its independent specification. -/
def canonicalDecomposeTree :
    Tree → Tree → Option (List (LogicVar × Tree))
  | .variable source, .variable target =>
      if source = target then some []
      else some [(source, .variable target)]
  | .variable source, value =>
      some [(source, value)]
  | value, .variable target =>
      some [(target, value)]
  | .node leftSymbol leftChildren, .node rightSymbol rightChildren =>
      if leftSymbol = rightSymbol then
        canonicalDecomposeTrees leftChildren rightChildren
      else none

/-- Ordered-child companion to `canonicalDecomposeTree`. -/
def canonicalDecomposeTrees :
    List Tree → List Tree → Option (List (LogicVar × Tree))
  | [], [] => some []
  | left :: lefts, right :: rights =>
      match canonicalDecomposeTree left right,
          canonicalDecomposeTrees lefts rights with
      | some head, some tail => some (head ++ tail)
      | _, _ => none
  | _, _ => none

end

/-- Complete ordered-equation decomposition in the canonical tree algebra. -/
def canonicalDecomposeEquations :
    List TreeEquation → Option (List (LogicVar × Tree))
  | [] => some []
  | (left, right) :: equations =>
      match canonicalDecomposeTree left right,
          canonicalDecomposeEquations equations with
      | some head, some tail => some (head ++ tail)
      | _, _ => none

/-- A singleton equation decomposes exactly as its two trees. -/
@[simp] theorem canonicalDecomposeEquations_single
    (left right : Tree) :
    canonicalDecomposeEquations [(left, right)] =
      canonicalDecomposeTree left right := by
  simp only [canonicalDecomposeEquations]
  cases canonicalDecomposeTree left right <;> simp

/-- Decomposition of concatenated equation worklists composes their ordered
constraint results.  This is the monoidal law used to keep head-before-tail
order visible through repeated normalization. -/
theorem canonicalDecomposeEquations_append
    (first second : List TreeEquation) :
    canonicalDecomposeEquations (first ++ second) =
      match canonicalDecomposeEquations first,
          canonicalDecomposeEquations second with
      | some firstConstraints, some secondConstraints =>
          some (firstConstraints ++ secondConstraints)
      | _, _ => none := by
  induction first with
  | nil =>
      cases secondComputed :
          canonicalDecomposeEquations second <;>
        simp [canonicalDecomposeEquations, secondComputed]
  | cons equation equations inductionHypothesis =>
      rcases equation with ⟨left, right⟩
      simp only [List.cons_append, canonicalDecomposeEquations]
      rw [inductionHypothesis]
      cases canonicalDecomposeTree left right <;>
        cases canonicalDecomposeEquations equations <;>
        cases canonicalDecomposeEquations second <;>
        simp [List.append_assoc]

mutual

/-- Every relational tree decomposition computes the same canonical
constraint list. -/
theorem TreeDecomposes.to_function
    {left right : Tree} {constraints : List (LogicVar × Tree)}
    (decomposition : TreeDecomposes left right constraints) :
    canonicalDecomposeTree left right = some constraints := by
  cases decomposition with
  | reflexiveVariable identity =>
      simp [canonicalDecomposeTree]
  | bindLeft =>
      rename_i source different
      cases right with
      | «variable» identity =>
          have unequal : source ≠ identity := by
            intro equality
            subst identity
            exact different rfl
          simp [canonicalDecomposeTree, unequal]
      | node symbol children =>
          simp [canonicalDecomposeTree]
  | bindRight =>
      rename_i target notVariable
      cases left with
      | «variable» identity =>
          exact False.elim (notVariable identity rfl)
      | node symbol children =>
          simp [canonicalDecomposeTree]
  | node symbol children =>
      simp [canonicalDecomposeTree,
        TreesDecompose.to_function children]

/-- Ordered-list relational decomposition computes its canonical function. -/
theorem TreesDecompose.to_function
    {left right : List Tree}
    {constraints : List (LogicVar × Tree)}
    (decomposition : TreesDecompose left right constraints) :
    canonicalDecomposeTrees left right = some constraints := by
  cases decomposition with
  | nil => rfl
  | cons head tail =>
      simp [canonicalDecomposeTrees,
        TreeDecomposes.to_function head,
        TreesDecompose.to_function tail]

end

/-- Complete equation-worklist relational decomposition computes its
canonical function. -/
theorem TreeEquationsDecompose.to_function
    {equations : List TreeEquation}
    {constraints : List (LogicVar × Tree)}
    (decomposition :
      TreeEquationsDecompose equations constraints) :
    canonicalDecomposeEquations equations = some constraints := by
  cases decomposition with
  | nil => rfl
  | cons head tail =>
      simp [canonicalDecomposeEquations,
        TreeDecomposes.to_function head,
        TreeEquationsDecompose.to_function tail]

mutual

/-- Every successful canonical tree decomposition function result is
licensed by the independent relation. -/
theorem treeDecomposes_of_function :
    ∀ {left right : Tree} {constraints : List (LogicVar × Tree)},
      canonicalDecomposeTree left right = some constraints →
        TreeDecomposes left right constraints
  | .variable source, .variable target, constraints, computed => by
      by_cases same : source = target
      · subst target
        simp [canonicalDecomposeTree] at computed
        subst constraints
        exact .reflexiveVariable source
      · simp [canonicalDecomposeTree, same] at computed
        subst constraints
        exact .bindLeft source (.variable target) (by
          intro equality
          exact same (Tree.variable.inj equality).symm)
  | .variable source, .node symbol children, constraints, computed => by
      simp [canonicalDecomposeTree] at computed
      subst constraints
      exact .bindLeft source (.node symbol children) (by
        simp)
  | .node symbol children, .variable target, constraints, computed => by
      simp [canonicalDecomposeTree] at computed
      subst constraints
      exact .bindRight (.node symbol children) target (by
        intro identity equality
        cases equality)
  | .node leftSymbol leftChildren, .node rightSymbol rightChildren,
      constraints, computed => by
      by_cases same : leftSymbol = rightSymbol
      · subst rightSymbol
        simp [canonicalDecomposeTree] at computed
        exact .node leftSymbol
          (treesDecompose_of_function computed)
      · simp [canonicalDecomposeTree, same] at computed

/-- Ordered-list functional decomposition is licensed by the independent
relation. -/
theorem treesDecompose_of_function :
    ∀ {left right : List Tree}
      {constraints : List (LogicVar × Tree)},
      canonicalDecomposeTrees left right = some constraints →
        TreesDecompose left right constraints
  | [], [], constraints, computed => by
      simp [canonicalDecomposeTrees] at computed
      subst constraints
      exact .nil
  | [], _ :: _, _, computed => by
      simp [canonicalDecomposeTrees] at computed
  | _ :: _, [], _, computed => by
      simp [canonicalDecomposeTrees] at computed
  | left :: lefts, right :: rights, constraints, computed => by
      simp only [canonicalDecomposeTrees] at computed
      cases headComputed :
          canonicalDecomposeTree left right with
      | none =>
          simp [headComputed] at computed
      | some headConstraints =>
          cases tailComputed :
              canonicalDecomposeTrees lefts rights with
          | none =>
              simp [headComputed, tailComputed] at computed
          | some tailConstraints =>
              simp [headComputed, tailComputed] at computed
              subst constraints
              exact .cons
                (treeDecomposes_of_function headComputed)
                (treesDecompose_of_function tailComputed)

end

/-- Every successful canonical equation-worklist function result is
licensed by the independent relation. -/
theorem treeEquationsDecompose_of_function :
    ∀ {equations : List TreeEquation}
      {constraints : List (LogicVar × Tree)},
      canonicalDecomposeEquations equations = some constraints →
        TreeEquationsDecompose equations constraints
  | [], constraints, computed => by
      simp [canonicalDecomposeEquations] at computed
      subst constraints
      exact .nil
  | (left, right) :: equations, constraints, computed => by
      simp only [canonicalDecomposeEquations] at computed
      cases headComputed :
          canonicalDecomposeTree left right with
      | none =>
          simp [headComputed] at computed
      | some headConstraints =>
          cases tailComputed :
              canonicalDecomposeEquations equations with
          | none =>
              simp [headComputed, tailComputed] at computed
          | some tailConstraints =>
              simp [headComputed, tailComputed] at computed
              subst constraints
              exact .cons
                (treeDecomposes_of_function headComputed)
                (treeEquationsDecompose_of_function tailComputed)

/-- The independent relation is exactly the graph of the independent
canonical tree decomposition function. -/
theorem treeDecomposes_iff_function
    {left right : Tree} {constraints : List (LogicVar × Tree)} :
    TreeDecomposes left right constraints ↔
      canonicalDecomposeTree left right = some constraints :=
  ⟨TreeDecomposes.to_function, treeDecomposes_of_function⟩

/-- Ordered-child graph theorem. -/
theorem treesDecompose_iff_function
    {left right : List Tree}
    {constraints : List (LogicVar × Tree)} :
    TreesDecompose left right constraints ↔
      canonicalDecomposeTrees left right = some constraints :=
  ⟨TreesDecompose.to_function, treesDecompose_of_function⟩

/-- Ordered-equation graph theorem. -/
theorem treeEquationsDecompose_iff_function
    {equations : List TreeEquation}
    {constraints : List (LogicVar × Tree)} :
    TreeEquationsDecompose equations constraints ↔
      canonicalDecomposeEquations equations = some constraints :=
  ⟨TreeEquationsDecompose.to_function,
    treeEquationsDecompose_of_function⟩

/-- Canonical tree decomposition is deterministic because the independent
relation is exactly the graph of `canonicalDecomposeTree`. -/
theorem TreeDecomposes.deterministic
    {left right : Tree}
    {first second : List (LogicVar × Tree)}
    (one : TreeDecomposes left right first)
    (two : TreeDecomposes left right second) :
    first = second :=
  Option.some.inj (one.to_function.symm.trans two.to_function)

/-- Ordered child-list decomposition is deterministic. -/
theorem TreesDecompose.deterministic
    {left right : List Tree}
    {first second : List (LogicVar × Tree)}
    (one : TreesDecompose left right first)
    (two : TreesDecompose left right second) :
    first = second :=
  Option.some.inj (one.to_function.symm.trans two.to_function)

/-- Complete equation-worklist decomposition is deterministic. -/
theorem TreeEquationsDecompose.deterministic
    {equations : List TreeEquation}
    {first second : List (LogicVar × Tree)}
    (one : TreeEquationsDecompose equations first)
    (two : TreeEquationsDecompose equations second) :
    first = second :=
  Option.some.inj (one.to_function.symm.trans two.to_function)

/-- Two worklists are decomposition-equivalent when every successful
ordered constraint result for one is exactly a result for the other.  This
relation, rather than syntactic equation equality, is the congruence needed
to transport Robinson rounds across structural normalization. -/
def TreeDecompositionEquivalent
    (first second : List TreeEquation) : Prop :=
  ∀ constraints,
    TreeEquationsDecompose first constraints ↔
      TreeEquationsDecompose second constraints

/-- Functional equality is an exact decision procedure for relational
decomposition equivalence. -/
theorem treeDecompositionEquivalent_iff_function
    {first second : List TreeEquation} :
    TreeDecompositionEquivalent first second ↔
      canonicalDecomposeEquations first =
        canonicalDecomposeEquations second := by
  constructor
  · intro equivalent
    cases firstComputed :
        canonicalDecomposeEquations first with
    | none =>
        cases secondComputed :
        canonicalDecomposeEquations second with
        | none => rfl
        | some constraints =>
            have secondRel :
                TreeEquationsDecompose second constraints :=
              treeEquationsDecompose_of_function secondComputed
            have firstRel :=
              (equivalent constraints).2 secondRel
            exact False.elim (by
              rw [firstRel.to_function] at firstComputed
              cases firstComputed)
    | some constraints =>
        have firstRel :
            TreeEquationsDecompose first constraints :=
          treeEquationsDecompose_of_function firstComputed
        have secondRel :=
          (equivalent constraints).1 firstRel
        exact secondRel.to_function.symm
  · intro same constraints
    rw [treeEquationsDecompose_iff_function,
      treeEquationsDecompose_iff_function, same]

/-- Successful canonical Robinson rounds, indexed by the same fuel discipline
as the executable algorithm.  The state is an ordered substitution list;
freshness makes canonical cons coincide with executable `Subst.extend`.
There is deliberately no constructor for a rigid clash, an occurs failure,
or exhausted fuel with pending constraints. -/
inductive TreeUnifyRounds :
    Nat → List TreeEquation → TreeSubstitution →
      TreeSubstitution → Prop where
  | done (fuel : Nat) {equations : List TreeEquation}
      {base : TreeSubstitution}
      (decomposition : TreeEquationsDecompose equations []) :
      TreeUnifyRounds fuel equations base base
  | eliminate (fuel : Nat) {equations : List TreeEquation}
      {source : LogicVar} {replacement : Tree}
      {rest : List (LogicVar × Tree)}
      {base result : TreeSubstitution}
      (decomposition :
        TreeEquationsDecompose equations
          ((source, replacement) :: rest))
      (fresh : source ∉ base.map Prod.fst)
      (absent : Tree.occurs source replacement = false)
      (avoids :
        TreeVariablesSatisfy
          (fun identity =>
            identity ∉ TreeSubstitution.keys base)
          replacement)
      (next :
        TreeUnifyRounds fuel
          (normalizeTreeConstraints source replacement rest)
          ((source, replacement) :: base) result) :
      TreeUnifyRounds (fuel + 1) equations base result

/-- Decomposition-equivalent initial worklists admit exactly the same round
derivations.  Recursive normalized worklists are unchanged; only the first
structural-decomposition premise is transported. -/
theorem TreeUnifyRounds.transport
    {fuel : Nat} {first second : List TreeEquation}
    {base result : TreeSubstitution}
    (equivalent : TreeDecompositionEquivalent first second)
    (rounds : TreeUnifyRounds fuel first base result) :
    TreeUnifyRounds fuel second base result := by
  cases rounds with
  | done fuel decomposition =>
      exact .done fuel ((equivalent []).1 decomposition)
  | eliminate fuel decomposition fresh absent avoids next =>
      exact .eliminate fuel
        ((equivalent _).1 decomposition) fresh absent avoids next

/-- Extra fuel cannot change or invalidate a successful independent round
derivation. -/
theorem TreeUnifyRounds.add_fuel
    {fuel : Nat} {equations : List TreeEquation}
    {base result : TreeSubstitution}
    (rounds : TreeUnifyRounds fuel equations base result)
    (extra : Nat) :
    TreeUnifyRounds (fuel + extra) equations base result := by
  induction rounds with
  | done fuel decomposition =>
      exact .done (fuel + extra) decomposition
  | eliminate fuel decomposition fresh absent avoids next
      inductionHypothesis =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (TreeUnifyRounds.eliminate (fuel + extra)
          decomposition fresh absent avoids inductionHypothesis)

/-- Order-theoretic form of `TreeUnifyRounds.add_fuel`. -/
theorem TreeUnifyRounds.mono
    {fuel larger : Nat} {equations : List TreeEquation}
    {base result : TreeSubstitution}
    (rounds : TreeUnifyRounds fuel equations base result)
    (enough : fuel ≤ larger) :
    TreeUnifyRounds larger equations base result := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le enough
  exact rounds.add_fuel extra

/-- Every successful flattened round preserves the stored elimination order.
The replacement-avoids-base premise on `eliminate` is load-bearing: without
it, a freshly prefixed source could point to a key later in the accumulated
association list, and sequential canonical application would not be a deep
normal form. -/
theorem TreeUnifyRounds.result_topological
    {fuel : Nat} {equations : List TreeEquation}
    {base result : TreeSubstitution}
    (rounds : TreeUnifyRounds fuel equations base result)
    (baseTopological : TreeSubstitutionTopological base) :
    TreeSubstitutionTopological result := by
  induction rounds with
  | done _ =>
      exact baseTopological
  | @eliminate fuel equations source replacement rest base result
      decomposition fresh absent avoids next inductionHypothesis =>
      have singletonTopological :
          TreeSubstitutionTopological [(source, replacement)] :=
        TreeSubstitutionTopological.singleton source replacement absent
      have singletonAvoids :
          TreeSubstitutionVariablesSatisfy
            (fun identity =>
              identity ∉ TreeSubstitution.keys base)
            [(source, replacement)] := by
        intro entry member
        simp only [List.mem_singleton] at member
        subst entry
        exact ⟨fresh, avoids⟩
      have nextBaseTopological :
          TreeSubstitutionTopological
            ((source, replacement) :: base) := by
        simpa using
          baseTopological.append singletonTopological singletonAvoids
      exact inductionHypothesis nextBaseTopological

mutual

/-- Every canonical tree decomposes reflexively to no constraints. -/
theorem TreeDecomposes.reflexive :
    ∀ tree, TreeDecomposes tree tree []
  | .variable identity => .reflexiveVariable identity
  | .node symbol children =>
      .node symbol (TreesDecompose.reflexive children)

/-- Ordered reflexive decomposition companion. -/
theorem TreesDecompose.reflexive :
    ∀ trees, TreesDecompose trees trees []
  | [] => .nil
  | tree :: trees => by
      simpa using
        (TreesDecompose.cons
          (TreeDecomposes.reflexive tree)
          (TreesDecompose.reflexive trees))

end

/-- Applying one singleton substitution to an equation-list cons exposes
exactly one pair of one-pass replacements and preserves the tail worklist. -/
@[simp] theorem applyEquations_singleton_cons
    (source : LogicVar) (replacement left right : Tree)
    (equations : List TreeEquation) :
    TreeSubstitution.applyEquations [(source, replacement)]
        ((left, right) :: equations) =
      (Tree.instantiateOne source replacement left,
        Tree.instantiateOne source replacement right) ::
      TreeSubstitution.applyEquations
        [(source, replacement)] equations :=
  rfl

private def orientationWitnessX : LogicVar := .source "$orientation_x"
private def orientationWitnessY : LogicVar := .source "$orientation_y"
private def orientationWitnessZ : LogicVar := .source "$orientation_z"

private def orientationWitnessF (identity : LogicVar) : Tree :=
  .node (.compound "$orientation_f") [.variable identity]

/-- Exact syntactic decomposition does not commute with an earlier
substitution: a valid right-oriented constraint reverses the later rigid
equation.  The two residual worklists have the same unifiers, but their
deterministic constraint spellings are `X ↦ Z` and `Z ↦ X`.  This witness
rules out using syntactic decomposition equality to bridge the independent
ordered MGU and the flattened executable algorithm. -/
theorem exact_decomposition_commutation_is_false :
    TreeEquationsDecompose
        [(orientationWitnessF orientationWitnessX,
          .variable orientationWitnessY)]
        [(orientationWitnessY,
          orientationWitnessF orientationWitnessX)] ∧
    canonicalDecomposeEquations
        (TreeSubstitution.applyEquations
          [(orientationWitnessY,
            orientationWitnessF orientationWitnessZ)]
          [(orientationWitnessF orientationWitnessX,
            .variable orientationWitnessY)]) =
      some [(orientationWitnessX,
        .variable orientationWitnessZ)] ∧
    canonicalDecomposeEquations
        (normalizeTreeConstraints orientationWitnessY
          (orientationWitnessF orientationWitnessZ)
          [(orientationWitnessY,
            orientationWitnessF orientationWitnessX)]) =
      some [(orientationWitnessZ,
        .variable orientationWitnessX)] ∧
    ([(orientationWitnessX, .variable orientationWitnessZ)] :
        List (LogicVar × Tree)) ≠
      [(orientationWitnessZ, .variable orientationWitnessX)] := by
  constructor
  · simpa [orientationWitnessF] using
      (TreeEquationsDecompose.cons
        (TreeDecomposes.bindRight
          (orientationWitnessF orientationWitnessX)
          orientationWitnessY (by
            intro identity equality
            cases equality))
        TreeEquationsDecompose.nil)
  · simp [TreeSubstitution.applyEquations, TreeSubstitution.apply,
      Tree.instantiateOne, Trees.instantiateOne,
      canonicalDecomposeTree,
      canonicalDecomposeTrees, normalizeTreeConstraints,
      orientationWitnessF, orientationWitnessX,
      orientationWitnessY, orientationWitnessZ]

/-! ## Semantic decomposition equivalence -/

/-- Read flattened Robinson constraints back as ordinary oriented
equations. -/
def treeConstraintEquations
    (constraints : List (LogicVar × Tree)) : List TreeEquation :=
  constraints.map fun item => (.variable item.1, item.2)

/-- Constraint normalization is exactly singleton substitution over the
corresponding equation worklist. -/
theorem normalizeTreeConstraints_eq_applyEquations
    (source : LogicVar) (replacement : Tree)
    (constraints : List (LogicVar × Tree)) :
    normalizeTreeConstraints source replacement constraints =
      TreeSubstitution.applyEquations [(source, replacement)]
        (treeConstraintEquations constraints) :=
  by
    simp [normalizeTreeConstraints, treeConstraintEquations,
      TreeSubstitution.applyEquations, List.map_map,
      Function.comp_def, TreeSubstitution.apply]

/-- Worklists are semantically equivalent when every finite-tree
substitution unifies one exactly when it unifies the other. -/
def TreeUnificationEquivalent
    (first second : List TreeEquation) : Prop :=
  ∀ binding,
    TreeUnifiesEquations binding first ↔
      TreeUnifiesEquations binding second

/-- Semantic worklist equivalence transports a unifier in either direction. -/
theorem TreeUnificationEquivalent.unifies_iff
    {first second : List TreeEquation}
    (equivalent : TreeUnificationEquivalent first second)
    (binding : TreeSubstitution) :
    TreeUnifiesEquations binding first ↔
      TreeUnifiesEquations binding second :=
  equivalent binding

/-- Semantic worklist equivalence preserves the complete MGU property, not
merely satisfiability. -/
theorem TreeUnificationEquivalent.isMgu_iff
    {first second : List TreeEquation}
    (equivalent : TreeUnificationEquivalent first second)
    (binding : TreeSubstitution) :
    TreeIsMgu binding first ↔ TreeIsMgu binding second := by
  constructor
  · rintro ⟨unifies, mostGeneral⟩
    refine ⟨(equivalent binding).1 unifies, ?_⟩
    intro candidate candidateUnifies
    exact mostGeneral candidate
      ((equivalent candidate).2 candidateUnifies)
  · rintro ⟨unifies, mostGeneral⟩
    refine ⟨(equivalent binding).2 unifies, ?_⟩
    intro candidate candidateUnifies
    exact mostGeneral candidate
      ((equivalent candidate).1 candidateUnifies)

/-- MGUs of semantically equivalent worklists factor through each other.
This is the orientation-insensitive invariant needed for residual aliases;
association-list equality is deliberately not claimed. -/
theorem TreeUnificationEquivalent.mgus_mutually_factor
    {first second : List TreeEquation}
    (equivalent : TreeUnificationEquivalent first second)
    {firstMgu secondMgu : TreeSubstitution}
    (firstMostGeneral : TreeIsMgu firstMgu first)
    (secondMostGeneral : TreeIsMgu secondMgu second) :
    TreeFactorsThrough secondMgu firstMgu ∧
      TreeFactorsThrough firstMgu secondMgu := by
  constructor
  · exact firstMostGeneral.2 secondMgu
      ((equivalent secondMgu).2 secondMostGeneral.1)
  · exact secondMostGeneral.2 firstMgu
      ((equivalent firstMgu).1 firstMostGeneral.1)

/-- Pointwise unification distributes over ordered worklist append. -/
theorem treeUnifiesEquations_append_iff
    (binding : TreeSubstitution)
    (first second : List TreeEquation) :
    TreeUnifiesEquations binding (first ++ second) ↔
      TreeUnifiesEquations binding first ∧
        TreeUnifiesEquations binding second := by
  constructor
  · intro unifies
    constructor
    · intro equation member
      exact unifies equation (List.mem_append_left second member)
    · intro equation member
      exact unifies equation (List.mem_append_right first member)
  · rintro ⟨firstUnifies, secondUnifies⟩ equation member
    rcases List.mem_append.mp member with member | member
    · exact firstUnifies equation member
    · exact secondUnifies equation member

/-- Unifying an already-substituted worklist is the same as unifying its
source with the candidate composed after that substitution. -/
theorem treeUnifiesEquations_applyEquations_iff
    (candidate extension : TreeSubstitution)
    (equations : List TreeEquation) :
    TreeUnifiesEquations candidate
        (TreeSubstitution.applyEquations extension equations) ↔
      TreeUnifiesEquations (candidate ++ extension) equations := by
  constructor
  · intro unifies equation member
    have mappedMember :
        (TreeSubstitution.apply extension equation.1,
          TreeSubstitution.apply extension equation.2) ∈
          TreeSubstitution.applyEquations extension equations := by
      exact List.mem_map_of_mem member
    have exactEquation := unifies _ mappedMember
    simpa [TreeSubstitution.apply_append] using exactEquation
  · intro unifies mapped mappedMember
    simp only [TreeSubstitution.applyEquations, List.mem_map]
      at mappedMember
    obtain ⟨equation, member, rfl⟩ := mappedMember
    have exactEquation := unifies equation member
    simpa [TreeSubstitution.apply_append] using exactEquation

mutual

/-- Structural decomposition preserves exactly the finite substitutions
that unify one tree equation.  The right-oriented constructor uses equality
symmetry, explaining why syntactic constraint orientation cannot be the
bridge invariant. -/
theorem TreeDecomposes.unifies_iff
    (binding : TreeSubstitution)
    {left right : Tree}
    {constraints : List (LogicVar × Tree)}
    (decomposition : TreeDecomposes left right constraints) :
    TreeSubstitution.apply binding left =
        TreeSubstitution.apply binding right ↔
      TreeUnifiesEquations binding
        (treeConstraintEquations constraints) := by
  cases decomposition with
  | reflexiveVariable =>
      simp [treeConstraintEquations, TreeUnifiesEquations]
  | bindLeft =>
      rename_i source different
      simp only [treeConstraintEquations,
        List.map_cons, List.map_nil]
      rw [TreeUnifiesEquations.cons_iff]
      constructor
      · intro exactEquation
        exact ⟨exactEquation, by
          intro equation member
          simp at member⟩
      · rintro ⟨exactEquation, _⟩
        exact exactEquation
  | bindRight =>
      rename_i target notVariable
      simp only [treeConstraintEquations,
        List.map_cons, List.map_nil]
      rw [TreeUnifiesEquations.cons_iff]
      constructor
      · intro exactEquation
        exact ⟨exactEquation.symm, by
          intro equation member
          simp at member⟩
      · rintro ⟨exactEquation, _⟩
        exact exactEquation.symm
  | node symbol children =>
      simpa [treeConstraintEquations,
        TreeSubstitution.apply_node] using
          (children.unifies_iff binding)

/-- Ordered-child companion to `TreeDecomposes.unifies_iff`. -/
theorem TreesDecompose.unifies_iff
    (binding : TreeSubstitution)
    {left right : List Tree}
    {constraints : List (LogicVar × Tree)}
    (decomposition : TreesDecompose left right constraints) :
    TreeSubstitution.applyTrees binding left =
        TreeSubstitution.applyTrees binding right ↔
      TreeUnifiesEquations binding
        (treeConstraintEquations constraints) := by
  cases decomposition with
  | nil =>
      simp [treeConstraintEquations, TreeUnifiesEquations]
  | @cons leftHead rightHead leftTail rightTail
      headConstraints tailConstraints head tail =>
      rw [show
        treeConstraintEquations (headConstraints ++ tailConstraints) =
          treeConstraintEquations headConstraints ++
            treeConstraintEquations tailConstraints by
              simp [treeConstraintEquations]]
      rw [treeUnifiesEquations_append_iff,
        ← head.unifies_iff binding,
        ← tail.unifies_iff binding]
      simp [TreeSubstitution.applyTrees_cons]

end

/-- Complete ordered structural decomposition preserves exactly the
finite-tree unifier set of the source worklist. -/
theorem TreeEquationsDecompose.unifies_iff
    (binding : TreeSubstitution)
    {equations : List TreeEquation}
    {constraints : List (LogicVar × Tree)}
    (decomposition :
      TreeEquationsDecompose equations constraints) :
    TreeUnifiesEquations binding equations ↔
      TreeUnifiesEquations binding
        (treeConstraintEquations constraints) := by
  cases decomposition with
  | nil =>
      simp [treeConstraintEquations, TreeUnifiesEquations]
  | @cons left right equations headConstraints tailConstraints head tail =>
      rw [TreeUnifiesEquations.cons_iff]
      rw [show
        treeConstraintEquations (headConstraints ++ tailConstraints) =
          treeConstraintEquations headConstraints ++
            treeConstraintEquations tailConstraints by
              simp [treeConstraintEquations]]
      rw [treeUnifiesEquations_append_iff,
        head.unifies_iff binding, tail.unifies_iff binding]

/-- The correct commuting law: substituting before structural decomposition
and normalizing the exposed constraints may orient residual aliases
differently, but they preserve exactly the same unifier set. -/
theorem TreeEquationsDecompose.instantiateOne_unificationEquivalent
    (source : LogicVar) (replacement : Tree)
    {equations : List TreeEquation}
    {constraints : List (LogicVar × Tree)}
    (decomposition :
      TreeEquationsDecompose equations constraints) :
    TreeUnificationEquivalent
      (TreeSubstitution.applyEquations
        [(source, replacement)] equations)
      (normalizeTreeConstraints source replacement constraints) := by
  intro binding
  rw [normalizeTreeConstraints_eq_applyEquations,
    treeUnifiesEquations_applyEquations_iff,
    treeUnifiesEquations_applyEquations_iff,
    decomposition.unifies_iff]

/-! ## Constructive structural-decomposition existence -/

mutual

/-- Any finite substitution that identifies two canonical trees licenses a
successful structural decomposition. -/
theorem treeDecomposes_exists_of_unifier
    (binding : TreeSubstitution) :
    ∀ left right,
      TreeSubstitution.apply binding left =
        TreeSubstitution.apply binding right →
      ∃ constraints, TreeDecomposes left right constraints
  | .variable source, .variable target, exactEquation => by
      by_cases same : source = target
      · subst target
        exact ⟨[], .reflexiveVariable source⟩
      · exact ⟨[(source, .variable target)],
          .bindLeft source (.variable target) (by
            intro equality
            exact same (Tree.variable.inj equality).symm)⟩
  | .variable source, .node symbol children, _ =>
      ⟨[(source, .node symbol children)],
        .bindLeft source (.node symbol children) (by
          intro equality
          cases equality)⟩
  | .node symbol children, .variable target, _ =>
      ⟨[(target, .node symbol children)],
        .bindRight (.node symbol children) target (by
          intro identity equality
          cases equality)⟩
  | .node leftSymbol leftChildren,
      .node rightSymbol rightChildren, exactEquation => by
      simp only [TreeSubstitution.apply_node, Tree.node.injEq]
        at exactEquation
      rcases exactEquation with ⟨symbolExact, childrenExact⟩
      subst rightSymbol
      obtain ⟨constraints, children⟩ :=
        treesDecompose_exists_of_unifier binding
          leftChildren rightChildren childrenExact
      exact ⟨constraints, .node leftSymbol children⟩

/-- Ordered-child companion to
`treeDecomposes_exists_of_unifier`. -/
theorem treesDecompose_exists_of_unifier
    (binding : TreeSubstitution) :
    ∀ left right,
      TreeSubstitution.applyTrees binding left =
        TreeSubstitution.applyTrees binding right →
      ∃ constraints, TreesDecompose left right constraints
  | [], [], _ => ⟨[], .nil⟩
  | [], _ :: _, exactEquation => by
      simp at exactEquation
  | _ :: _, [], exactEquation => by
      simp at exactEquation
  | left :: lefts, right :: rights, exactEquation => by
      simp only [TreeSubstitution.applyTrees_cons, List.cons.injEq]
        at exactEquation
      obtain ⟨headConstraints, head⟩ :=
        treeDecomposes_exists_of_unifier binding
          left right exactEquation.1
      obtain ⟨tailConstraints, tail⟩ :=
        treesDecompose_exists_of_unifier binding
          lefts rights exactEquation.2
      exact ⟨headConstraints ++ tailConstraints, .cons head tail⟩

end

/-- Every finitely unifiable ordered equation worklist has a successful
structural decomposition. -/
theorem treeEquationsDecompose_exists_of_unifier
    (binding : TreeSubstitution) :
    ∀ equations,
      TreeUnifiesEquations binding equations →
      ∃ constraints, TreeEquationsDecompose equations constraints
  | [], _ => ⟨[], .nil⟩
  | equation :: equations, unifies => by
      rcases equation with ⟨left, right⟩
      have split :=
        (TreeUnifiesEquations.cons_iff binding (left, right) equations).1
          unifies
      obtain ⟨headConstraints, head⟩ :=
        treeDecomposes_exists_of_unifier binding
          left right split.1
      obtain ⟨tailConstraints, tail⟩ :=
        treeEquationsDecompose_exists_of_unifier binding
          equations split.2
      exact ⟨headConstraints ++ tailConstraints, .cons head tail⟩

/-- Every flattened constraint emitted by structural decomposition is
non-reflexive in its stored orientation. -/
def TreeConstraintsIrreflexive
    (constraints : List (LogicVar × Tree)) : Prop :=
  ∀ constraint, constraint ∈ constraints →
    constraint.2 ≠ .variable constraint.1

mutual

theorem TreeDecomposes.constraints_irreflexive
    {left right : Tree}
    {constraints : List (LogicVar × Tree)}
    (decomposition : TreeDecomposes left right constraints) :
    TreeConstraintsIrreflexive constraints := by
  cases decomposition with
  | reflexiveVariable =>
      intro constraint member
      simp at member
  | bindLeft source value different =>
      intro constraint member
      simp only [List.mem_singleton] at member
      subst constraint
      exact different
  | bindRight value target notVariable =>
      intro constraint member
      simp only [List.mem_singleton] at member
      subst constraint
      exact notVariable target
  | node symbol children =>
      exact children.constraints_irreflexive

theorem TreesDecompose.constraints_irreflexive
    {left right : List Tree}
    {constraints : List (LogicVar × Tree)}
    (decomposition : TreesDecompose left right constraints) :
    TreeConstraintsIrreflexive constraints := by
  cases decomposition with
  | nil =>
      intro constraint member
      simp at member
  | @cons leftHead rightHead leftTail rightTail
      headConstraints tailConstraints head tail =>
      intro constraint member
      rcases List.mem_append.mp member with member | member
      · exact head.constraints_irreflexive constraint member
      · exact tail.constraints_irreflexive constraint member

end

theorem TreeEquationsDecompose.constraints_irreflexive
    {equations : List TreeEquation}
    {constraints : List (LogicVar × Tree)}
    (decomposition :
      TreeEquationsDecompose equations constraints) :
    TreeConstraintsIrreflexive constraints := by
  cases decomposition with
  | nil =>
      intro constraint member
      simp at member
  | @cons left right equations headConstraints tailConstraints head tail =>
      intro constraint member
      rcases List.mem_append.mp member with member | member
      · exact head.constraints_irreflexive constraint member
      · exact tail.constraints_irreflexive constraint member

/-! ## Finite support decreases across elimination -/

/-- Every key and replacement variable in a flattened constraint worklist
satisfies one support predicate. -/
def TreeConstraintsVariablesSatisfy
    (predicate : LogicVar → Prop)
    (constraints : List (LogicVar × Tree)) : Prop :=
  ∀ constraint, constraint ∈ constraints →
    predicate constraint.1 ∧
      TreeVariablesSatisfy predicate constraint.2

mutual

/-- Structural decomposition cannot invent a variable outside the supports
of its two source trees. -/
theorem TreeDecomposes.constraints_variablesSatisfy
    {predicate : LogicVar → Prop}
    {left right : Tree}
    {constraints : List (LogicVar × Tree)}
    (decomposition : TreeDecomposes left right constraints)
    (leftSupported : TreeVariablesSatisfy predicate left)
    (rightSupported : TreeVariablesSatisfy predicate right) :
    TreeConstraintsVariablesSatisfy predicate constraints := by
  cases decomposition with
  | reflexiveVariable =>
      intro constraint member
      simp at member
  | bindLeft source value different =>
      intro constraint member
      simp only [List.mem_singleton] at member
      subst constraint
      exact ⟨leftSupported, rightSupported⟩
  | bindRight value target notVariable =>
      intro constraint member
      simp only [List.mem_singleton] at member
      subst constraint
      exact ⟨rightSupported, leftSupported⟩
  | node symbol children =>
      exact children.constraints_variablesSatisfy
        leftSupported rightSupported

/-- Ordered-child support companion. -/
theorem TreesDecompose.constraints_variablesSatisfy
    {predicate : LogicVar → Prop}
    {left right : List Tree}
    {constraints : List (LogicVar × Tree)}
    (decomposition : TreesDecompose left right constraints)
    (leftSupported : TreesVariablesSatisfy predicate left)
    (rightSupported : TreesVariablesSatisfy predicate right) :
    TreeConstraintsVariablesSatisfy predicate constraints := by
  cases decomposition with
  | nil =>
      intro constraint member
      simp at member
  | @cons leftHead rightHead leftTail rightTail
      headConstraints tailConstraints head tail =>
      intro constraint member
      rcases List.mem_append.mp member with member | member
      · exact head.constraints_variablesSatisfy
          leftSupported.1 rightSupported.1 constraint member
      · exact tail.constraints_variablesSatisfy
          leftSupported.2 rightSupported.2 constraint member

end

/-- Whole-worklist structural decomposition preserves finite support. -/
theorem TreeEquationsDecompose.constraints_variablesSatisfy
    {predicate : LogicVar → Prop}
    {equations : List TreeEquation}
    {constraints : List (LogicVar × Tree)}
    (decomposition :
      TreeEquationsDecompose equations constraints)
    (supported :
      TreeEquationsVariablesSatisfy predicate equations) :
    TreeConstraintsVariablesSatisfy predicate constraints := by
  cases decomposition with
  | nil =>
      intro constraint member
      simp at member
  | @cons left right equations headConstraints tailConstraints head tail =>
      have headSupported := supported (left, right) (by simp)
      have tailSupported :
          TreeEquationsVariablesSatisfy predicate equations := by
        intro equation member
        exact supported equation (by simp [member])
      intro constraint member
      rcases List.mem_append.mp member with member | member
      · exact head.constraints_variablesSatisfy
          headSupported.1 headSupported.2 constraint member
      · exact tail.constraints_variablesSatisfy
          tailSupported constraint member

/-- One occurs-safe elimination removes its source from every remaining
normalized equation's finite support. -/
theorem normalizeTreeConstraints_variablesSatisfy_erase
    (allowed : List LogicVar)
    (source : LogicVar) (replacement : Tree)
    (rest : List (LogicVar × Tree))
    (replacementSupported :
      TreeVariablesSatisfy (fun identity => identity ∈ allowed)
        replacement)
    (absent : Tree.occurs source replacement = false)
    (restSupported :
      TreeConstraintsVariablesSatisfy
        (fun identity => identity ∈ allowed) rest) :
    TreeEquationsVariablesSatisfy
      (fun identity => identity ∈ allowed.erase source)
      (normalizeTreeConstraints source replacement rest) := by
  have replacementOutside :
      TreeVariablesSatisfy (fun identity => identity ≠ source)
        replacement :=
    treeVariablesSatisfy_ne_of_occurs_false source absent
  have replacementErased :
      TreeVariablesSatisfy
        (fun identity => identity ∈ allowed.erase source)
        replacement :=
    TreeVariablesSatisfy.mono
      (fun identity supported =>
        (List.mem_erase_of_ne supported.2).2 supported.1)
      (TreeVariablesSatisfy.and
        replacementSupported replacementOutside)
  intro equation member
  simp only [normalizeTreeConstraints, List.mem_map] at member
  obtain ⟨constraint, constraintMember, rfl⟩ := member
  have constraintSupported :=
    restSupported constraint constraintMember
  have liftSupport :
      ∀ {tree : Tree},
        TreeVariablesSatisfy
            (fun identity => identity ∈ allowed) tree →
          TreeVariablesSatisfy
            (fun identity =>
              identity = source ∨ identity ∈ allowed.erase source) tree := by
    intro tree supported
    exact TreeVariablesSatisfy.mono
      (fun identity identityAllowed => by
        by_cases same : identity = source
        · exact Or.inl same
        · exact Or.inr
            ((List.mem_erase_of_ne same).2 identityAllowed))
      supported
  constructor
  · apply treeVariablesSatisfy_instantiateOne_eliminate source
      replacementErased
    exact liftSupport (tree := .variable constraint.1)
      constraintSupported.1
  · apply treeVariablesSatisfy_instantiateOne_eliminate source
      replacementErased
    exact liftSupport constraintSupported.2

/-- An already-realizing finite substitution still realizes every remaining
constraint after one occurs-safe singleton normalization. -/
theorem treeUnifies_normalizeTreeConstraints
    (binding : TreeSubstitution)
    (source : LogicVar) (replacement : Tree)
    (rest : List (LogicVar × Tree))
    (identifies :
      TreeSubstitution.apply binding (.variable source) =
        TreeSubstitution.apply binding replacement)
    (realizes :
      TreeUnifiesEquations binding
        (treeConstraintEquations rest)) :
    TreeUnifiesEquations binding
      (normalizeTreeConstraints source replacement rest) := by
  intro equation member
  simp only [normalizeTreeConstraints, List.mem_map] at member
  obtain ⟨constraint, constraintMember, rfl⟩ := member
  have exactConstraint :
      TreeSubstitution.apply binding (.variable constraint.1) =
        TreeSubstitution.apply binding constraint.2 :=
    realizes (.variable constraint.1, constraint.2) (by
      simpa [treeConstraintEquations] using constraintMember)
  calc
    TreeSubstitution.apply binding
        (Tree.instantiateOne source replacement
          (.variable constraint.1)) =
        TreeSubstitution.apply binding (.variable constraint.1) :=
      TreeSubstitution.apply_instantiateOne_of_unifier
        binding source replacement identifies (.variable constraint.1)
    _ = TreeSubstitution.apply binding constraint.2 := exactConstraint
    _ = TreeSubstitution.apply binding
        (Tree.instantiateOne source replacement constraint.2) :=
      (TreeSubstitution.apply_instantiateOne_of_unifier
        binding source replacement identifies constraint.2).symm

/-- The accumulated substitution has no key still listed in the current
finite equation support. -/
def TreeBaseFreshFor
    (allowed : List LogicVar) (base : TreeSubstitution) : Prop :=
  ∀ source, source ∈ allowed → source ∉ base.map Prod.fst

/-- Extending by the selected source preserves freshness for the strictly
smaller erased support. -/
theorem TreeBaseFreshFor.cons_erase
    {allowed : List LogicVar} {base : TreeSubstitution}
    (fresh : TreeBaseFreshFor allowed base)
    (allowedNodup : allowed.Nodup)
    (source : LogicVar) (replacement : Tree) :
    TreeBaseFreshFor (allowed.erase source)
      ((source, replacement) :: base) := by
  intro identity member
  have different : identity ≠ source :=
    (allowedNodup.mem_erase_iff.mp member).1
  have oldMember : identity ∈ allowed :=
    List.mem_of_mem_erase member
  simp only [List.map_cons, List.mem_cons, not_or]
  exact ⟨different, fresh identity oldMember⟩

mutual

/-- Variable occurrences of one canonical tree, in structural order. -/
def treeLogicVariables : Tree → List LogicVar
  | .variable identity => [identity]
  | .node _ children => treesLogicVariables children

/-- Ordered-child variable occurrences. -/
def treesLogicVariables : List Tree → List LogicVar
  | [] => []
  | tree :: trees =>
      treeLogicVariables tree ++ treesLogicVariables trees

end

/-- Variable occurrences of a complete equation worklist. -/
def treeEquationsLogicVariables :
    List TreeEquation → List LogicVar
  | [] => []
  | (left, right) :: equations =>
      treeLogicVariables left ++ treeLogicVariables right ++
        treeEquationsLogicVariables equations

mutual

/-- The occurrence list of a tree supports every variable in that tree. -/
theorem treeLogicVariables_supported :
    ∀ tree,
      TreeVariablesSatisfy
        (fun identity => identity ∈ treeLogicVariables tree) tree
  | .variable identity => by
      simp [treeLogicVariables, TreeVariablesSatisfy]
  | .node symbol children =>
      treesLogicVariables_supported children

/-- Ordered-child companion. -/
theorem treesLogicVariables_supported :
    ∀ trees,
      TreesVariablesSatisfy
        (fun identity => identity ∈ treesLogicVariables trees) trees
  | [] => trivial
  | tree :: trees => by
      constructor
      · exact TreeVariablesSatisfy.mono
          (fun identity member =>
            List.mem_append_left _ member)
          (treeLogicVariables_supported tree)
      · exact TreesVariablesSatisfy.mono
          (fun identity member =>
            List.mem_append_right _ member)
          (treesLogicVariables_supported trees)

end

/-- The finite occurrence list of a worklist supports every equation. -/
theorem treeEquationsLogicVariables_supported
    (equations : List TreeEquation) :
    TreeEquationsVariablesSatisfy
      (fun identity =>
        identity ∈ treeEquationsLogicVariables equations) equations := by
  intro equation member
  induction equations with
  | nil => simp at member
  | cons head equations inductionHypothesis =>
      rcases head with ⟨left, right⟩
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · constructor
        · exact TreeVariablesSatisfy.mono
            (fun identity identityMember =>
              List.mem_append_left _
                (List.mem_append_left _ identityMember))
            (treeLogicVariables_supported left)
        · exact TreeVariablesSatisfy.mono
            (fun identity identityMember =>
              List.mem_append_left _
                (List.mem_append_right _ identityMember))
            (treeLogicVariables_supported right)
      · have tailSupported := inductionHypothesis member
        constructor
        · exact TreeVariablesSatisfy.mono
            (fun identity identityMember =>
              List.mem_append_right _ identityMember)
            tailSupported.1
        · exact TreeVariablesSatisfy.mono
            (fun identity identityMember =>
              List.mem_append_right _ identityMember)
            tailSupported.2

/-- Deduplicating the structural occurrence list gives a finite,
duplicate-free support for the whole equation worklist. -/
theorem treeEquationsLogicVariables_dedup_supported
    (equations : List TreeEquation) :
    TreeEquationsVariablesSatisfy
      (fun identity =>
        identity ∈
          (treeEquationsLogicVariables equations).eraseDups)
      equations := by
  have supported :=
    treeEquationsLogicVariables_supported equations
  intro equation member
  have equationSupported := supported equation member
  exact
    ⟨TreeVariablesSatisfy.mono
        (fun identity identityMember =>
          List.mem_eraseDups.mpr identityMember)
        equationSupported.1,
      TreeVariablesSatisfy.mono
        (fun identity identityMember =>
          List.mem_eraseDups.mpr identityMember)
        equationSupported.2⟩

/-- Deduplication of finite canonical-variable supports is genuinely
duplicate-free. -/
theorem logicVar_eraseDups_nodup :
    ∀ support : List LogicVar, support.eraseDups.Nodup
  | [] => by simp
  | head :: tail => by
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · intro member
        rw [List.mem_eraseDups] at member
        simp at member
      · exact logicVar_eraseDups_nodup
          (tail.filter (fun identity => !identity == head))
termination_by support => support.length
decreasing_by
  have lengthBound :=
    List.length_filter_le
      (fun identity : LogicVar => !identity == head) tail
  simp only [List.length_cons]
  omega

mutual

/-- Variable occurrences are bounded by canonical structural weight. -/
theorem treeLogicVariables_length_le_weight :
    ∀ tree : Tree,
      (treeLogicVariables tree).length ≤ tree.weight
  | .variable identity => by
      simp [treeLogicVariables, Tree.weight]
  | .node symbol children => by
      have childrenBound :=
        treesLogicVariables_length_le_weight children
      simp only [treeLogicVariables, Tree.weight]
      omega

/-- Ordered-child companion. -/
theorem treesLogicVariables_length_le_weight :
    ∀ trees : List Tree,
      (treesLogicVariables trees).length ≤ Trees.weight trees
  | [] => by
      simp [treesLogicVariables, Trees.weight]
  | tree :: trees => by
      have headBound := treeLogicVariables_length_le_weight tree
      have tailBound := treesLogicVariables_length_le_weight trees
      simp only [treesLogicVariables, List.length_append,
        Trees.weight]
      omega

end

/-- Additive canonical equation weight. -/
def treeEquationsWeight : List TreeEquation → Nat
  | [] => 0
  | (left, right) :: equations =>
      left.weight + right.weight + treeEquationsWeight equations

/-- Equation-variable occurrences are bounded by additive equation weight. -/
theorem treeEquationsLogicVariables_length_le_weight :
    ∀ equations : List TreeEquation,
      (treeEquationsLogicVariables equations).length ≤
        treeEquationsWeight equations
  | [] => by
      simp [treeEquationsLogicVariables, treeEquationsWeight]
  | (left, right) :: equations => by
      have leftBound := treeLogicVariables_length_le_weight left
      have rightBound := treeLogicVariables_length_le_weight right
      have tailBound :=
        treeEquationsLogicVariables_length_le_weight equations
      simp only [treeEquationsLogicVariables, List.length_append,
        treeEquationsWeight]
      omega

/-- Deduplication cannot enlarge a finite canonical-variable support. -/
theorem logicVar_eraseDups_length_le :
    ∀ support : List LogicVar,
      support.eraseDups.length ≤ support.length
  | [] => by simp
  | head :: tail => by
      rw [List.eraseDups_cons]
      have inductionHypothesis :=
        logicVar_eraseDups_length_le
          (tail.filter (fun identity => !identity == head))
      have filterBound :=
        List.length_filter_le
          (fun identity : LogicVar => !identity == head) tail
      simp only [List.length_cons]
      omega
termination_by support => support.length
decreasing_by
  have filterBound :=
    List.length_filter_le
      (fun identity : LogicVar => !identity == head) tail
  simp only [List.length_cons]
  omega

/-- Every supported canonical tree is no larger than its executable
encoding.  List and partial-value encodings add administrative cons cells,
so the inequality is intentionally one-way. -/
theorem CanonicalRuntimeAgrees.weight_le_size
    {alpha : List (LogicVar × String)}
    {tree : Tree} {atom : Atom}
    (agreement : CanonicalRuntimeAgrees alpha tree atom) :
    tree.weight ≤ atom.size := by
  induction agreement with
  | «variable» | atom | trueAtom | falseAtom |
      integer | float | string | nil =>
      simp [Tree.weight, Trees.weight, Atom.size, nilA]
  | partialValue arguments inductionHypothesis =>
      simp [Tree.weight, Trees.weight, Atom.size, partialC, partialTagA] at *
      omega
  | cons head tail headInduction tailInduction =>
      simp [Tree.weight, Trees.weight, Atom.size,
        consC] at *
      omega

/-- Shared source/runtime equation agreement bounds canonical variable
occurrences by the executable atoms' structural sizes. -/
theorem SharedAlphaEquationsAgree.logicVariables_length_le_runtime_sizes
    {alpha : List (LogicVar × String)}
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms) :
    (treeEquationsLogicVariables
        (denoteEquations equations)).length ≤
      (leftAtoms.map Atom.size).sum +
        (rightAtoms.map Atom.size).sum := by
  induction agreement with
  | nil =>
      simp [denoteEquations, treeEquationsLogicVariables]
  | @cons leftTerm rightTerm leftAtom rightAtom equations
      leftAtoms rightAtoms left right tail inductionHypothesis =>
      have leftVariableBound :=
        treeLogicVariables_length_le_weight
          (Term.denote leftTerm)
      have rightVariableBound :=
        treeLogicVariables_length_le_weight
          (Term.denote rightTerm)
      have leftRuntimeBound :=
        PLeaTTa.PrologMguDirectSimulation.CanonicalRuntimeAgrees.weight_le_size
          (AlphaTermAgrees.canonicalRuntimeAgrees left)
      have rightRuntimeBound :=
        PLeaTTa.PrologMguDirectSimulation.CanonicalRuntimeAgrees.weight_le_size
          (AlphaTermAgrees.canonicalRuntimeAgrees right)
      have tailBound :
          (treeEquationsLogicVariables
            (List.map
              (fun equation =>
                (Term.denote equation.1, Term.denote equation.2))
              equations)).length ≤
            (leftAtoms.map Atom.size).sum +
              (rightAtoms.map Atom.size).sum := by
        simpa [denoteEquations] using inductionHypothesis
      simp only [denoteEquations, List.map_cons,
        treeEquationsLogicVariables, List.length_append,
        List.sum_cons]
      omega

/-- The executable top-level fuel is at least the number of distinct
canonical equation variables. -/
theorem SharedAlphaEquationsAgree.canonical_fuel_le_runtime_fuel
    {alpha : List (LogicVar × String)}
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms) :
    (treeEquationsLogicVariables
        (denoteEquations equations)).eraseDups.length ≤
      (.expr leftAtoms : Atom).size + (.expr rightAtoms : Atom).size := by
  have dedupBound :=
    logicVar_eraseDups_length_le
      (treeEquationsLogicVariables (denoteEquations equations))
  have runtimeBound :=
    PLeaTTa.PrologMguDirectSimulation.SharedAlphaEquationsAgree.logicVariables_length_le_runtime_sizes
      agreement
  simp only [Atom.size]
  omega

/-- The independent flattened Robinson algorithm is constructively complete
whenever `fuel` covers a duplicate-free finite support of all remaining
equation variables.  No executable success result is assumed. -/
theorem treeUnifyRounds_complete_of_unifier
    (fuel : Nat) (allowed : List LogicVar)
    (equations : List TreeEquation)
    (base witness : TreeSubstitution)
    (allowedNodup : allowed.Nodup)
    (supported :
      TreeEquationsVariablesSatisfy
        (fun identity => identity ∈ allowed) equations)
    (fuelEnough : allowed.length ≤ fuel)
    (baseFresh : TreeBaseFreshFor allowed base)
    (unifies : TreeUnifiesEquations witness equations) :
    ∃ result, TreeUnifyRounds fuel equations base result := by
  induction fuel generalizing allowed equations base with
  | zero =>
      have allowedEmpty : allowed = [] := by
        exact List.eq_nil_of_length_eq_zero (by omega)
      obtain ⟨constraints, decomposition⟩ :=
        treeEquationsDecompose_exists_of_unifier witness equations unifies
      have constraintsSupported :=
        decomposition.constraints_variablesSatisfy supported
      have constraintsEmpty : constraints = [] := by
        cases constraints with
        | nil => rfl
        | cons constraint rest =>
            have sourceAllowed :=
              (constraintsSupported constraint (by simp)).1
            rw [allowedEmpty] at sourceAllowed
            contradiction
      subst constraints
      exact ⟨base, .done 0 decomposition⟩
  | succ fuel inductionHypothesis =>
      obtain ⟨constraints, decomposition⟩ :=
        treeEquationsDecompose_exists_of_unifier witness equations unifies
      have constraintsSupported :=
        decomposition.constraints_variablesSatisfy supported
      cases constraints with
      | nil =>
          exact ⟨base, .done (fuel + 1) decomposition⟩
      | cons constraint rest =>
          rcases constraint with ⟨source, replacement⟩
          have headSupported :=
            constraintsSupported (source, replacement) (by simp)
          have restSupported :
              TreeConstraintsVariablesSatisfy
                (fun identity => identity ∈ allowed) rest := by
            intro item member
            exact constraintsSupported item (by simp [member])
          have realized :
              TreeUnifiesEquations witness
                (treeConstraintEquations
                  ((source, replacement) :: rest)) :=
            (decomposition.unifies_iff witness).1 unifies
          have realizedSplit :
              TreeSubstitution.apply witness (.variable source) =
                  TreeSubstitution.apply witness replacement ∧
                TreeUnifiesEquations witness
                  (treeConstraintEquations rest) := by
            apply (TreeUnifiesEquations.cons_iff witness
              (.variable source, replacement)
              (treeConstraintEquations rest)).1
            simpa [treeConstraintEquations] using realized
          have different :
              replacement ≠ .variable source :=
            decomposition.constraints_irreflexive
              (source, replacement) (by simp)
          have absent : Tree.occurs source replacement = false := by
            cases present : Tree.occurs source replacement with
            | false => rfl
            | true =>
                exact False.elim
                  ((Tree.no_finite_unifier_of_occurs_true witness
                    source replacement present different)
                    realizedSplit.1)
          have replacementAvoidsBase :
              TreeVariablesSatisfy
                (fun identity =>
                  identity ∉ TreeSubstitution.keys base)
                replacement :=
            TreeVariablesSatisfy.mono
              (fun identity identityAllowed =>
                baseFresh identity identityAllowed)
              headSupported.2
          have sourceAllowed : source ∈ allowed := headSupported.1
          have nextSupported :
              TreeEquationsVariablesSatisfy
                (fun identity => identity ∈ allowed.erase source)
                (normalizeTreeConstraints source replacement rest) :=
            normalizeTreeConstraints_variablesSatisfy_erase
              allowed source replacement rest
              headSupported.2 absent restSupported
          have nextNodup : (allowed.erase source).Nodup :=
            allowedNodup.erase source
          have nextFuelEnough :
              (allowed.erase source).length ≤ fuel := by
            have shorter :
                (allowed.erase source).length < allowed.length := by
              have positive : 0 < allowed.length :=
                List.length_pos_of_mem sourceAllowed
              rw [List.length_erase_of_mem sourceAllowed]
              omega
            omega
          have nextFresh :
              TreeBaseFreshFor (allowed.erase source)
                ((source, replacement) :: base) :=
            baseFresh.cons_erase allowedNodup source replacement
          have nextUnifies :
              TreeUnifiesEquations witness
                (normalizeTreeConstraints source replacement rest) :=
            treeUnifies_normalizeTreeConstraints
              witness source replacement rest
              realizedSplit.1 realizedSplit.2
          obtain ⟨result, nextRounds⟩ :=
            inductionHypothesis
              (allowed.erase source)
              (normalizeTreeConstraints source replacement rest)
              ((source, replacement) :: base)
              nextNodup nextSupported nextFuelEnough
              nextFresh nextUnifies
          exact ⟨result, .eliminate fuel decomposition
            (baseFresh source sourceAllowed) absent
            replacementAvoidsBase nextRounds⟩

/-- Every finitely unifiable canonical worklist has a successful flattened
round derivation at the exact size of its deduplicated structural variable
support. -/
theorem treeUnifyRounds_exists_of_unifier
    (equations : List TreeEquation)
    (witness : TreeSubstitution)
    (unifies : TreeUnifiesEquations witness equations) :
    ∃ result,
      TreeUnifyRounds
        (treeEquationsLogicVariables equations).eraseDups.length
        equations [] result := by
  let allowed :=
    (treeEquationsLogicVariables equations).eraseDups
  have allowedNodup : allowed.Nodup :=
    logicVar_eraseDups_nodup _
  have supported :
      TreeEquationsVariablesSatisfy
        (fun identity => identity ∈ allowed) equations := by
    exact treeEquationsLogicVariables_dedup_supported equations
  have baseFresh : TreeBaseFreshFor allowed [] := by
    intro source member
    simp
  exact treeUnifyRounds_complete_of_unifier
    allowed.length allowed equations [] witness
      allowedNodup supported (Nat.le_refl _)
      baseFresh unifies

/-- In particular, every independently selected ordered canonical MGU
constructs a successful flattened round derivation; its final spelling is
not asserted equal to the ordered MGU because the orientation anti-witness
above proves that claim false. -/
theorem OrderedTreeMgu.treeUnifyRounds_exists
    {equations : List TreeEquation}
    {canonical : TreeSubstitution}
    (derivation : OrderedTreeMgu equations canonical) :
    ∃ result,
      TreeUnifyRounds
        (treeEquationsLogicVariables equations).eraseDups.length
        equations [] result :=
  treeUnifyRounds_exists_of_unifier
    equations canonical derivation.isMostGeneral.1

/-- Successful flattened rounds compute an MGU extension independently of
their accumulated base.  The final association list is exactly that
extension followed by the old base.  This relative form is the induction
invariant needed by repeated elimination: the next round receives the
previous singleton binding as accumulated state, while its newly computed
extension remains an MGU of the normalized residual worklist. -/
theorem TreeUnifyRounds.extension_isMostGeneral
    {fuel : Nat} {equations : List TreeEquation}
    {base result : TreeSubstitution}
    (rounds : TreeUnifyRounds fuel equations base result) :
    ∃ extension,
      result = extension ++ base ∧
        TreeIsMgu extension equations := by
  induction rounds with
  | @done fuel equations base decomposition =>
      have equivalent :
          TreeUnificationEquivalent equations [] := by
        intro binding
        simpa [treeConstraintEquations, TreeUnifiesEquations] using
          (decomposition.unifies_iff binding)
      refine ⟨[], by simp, ?_⟩
      exact (equivalent.isMgu_iff []).2 tree_empty_is_mgu
  | @eliminate fuel equations source replacement rest base result
      decomposition fresh absent avoids next inductionHypothesis =>
      obtain ⟨extension, resultEq, extensionMgu⟩ :=
        inductionHypothesis
      have tailMgu :
          TreeIsMgu extension
            (TreeSubstitution.applyEquations
              [(source, replacement)]
              (treeConstraintEquations rest)) := by
        rw [← normalizeTreeConstraints_eq_applyEquations]
        exact extensionMgu
      have constraintsMgu :
          TreeIsMgu
            (extension ++ [(source, replacement)])
            (treeConstraintEquations
              ((source, replacement) :: rest)) := by
        simpa [treeConstraintEquations] using
          (tree_singleton_variable_is_mgu source replacement absent).compose_append
            tailMgu
      have equivalent :
          TreeUnificationEquivalent equations
            (treeConstraintEquations
              ((source, replacement) :: rest)) := by
        intro binding
        exact decomposition.unifies_iff binding
      refine
        ⟨extension ++ [(source, replacement)], ?_,
          (equivalent.isMgu_iff _).2 constraintsMgu⟩
      simpa [List.append_assoc] using resultEq

/-- At the empty initial base, every successful flattened round result is a
most-general unifier of the original ordered equation worklist. -/
theorem TreeUnifyRounds.isMostGeneral
    {fuel : Nat} {equations : List TreeEquation}
    {result : TreeSubstitution}
    (rounds : TreeUnifyRounds fuel equations [] result) :
    TreeIsMgu result equations := by
  obtain ⟨extension, resultEq, extensionMgu⟩ :=
    rounds.extension_isMostGeneral
  have exactResult : result = extension := by
    simpa using resultEq
  subst result
  simpa using extensionMgu

mutual

/-- Decomposing one independent tree against itself cannot manufacture a
constraint.  This is a property of the independent relation, not of the
executable algorithm. -/
theorem TreeDecomposes.same_constraints_nil
    {tree : Tree} {constraints : List (LogicVar × Tree)}
    (decomposition : TreeDecomposes tree tree constraints) :
    constraints = [] := by
  cases decomposition with
  | reflexiveVariable => rfl
  | bindLeft _ _ different => exact False.elim (different rfl)
  | bindRight _ _ notVariable => exact False.elim (notVariable _ rfl)
  | node _ children =>
      exact TreesDecompose.same_constraints_nil children

/-- Ordered-list companion to
`TreeDecomposes.same_constraints_nil`. -/
theorem TreesDecompose.same_constraints_nil
    {trees : List Tree} {constraints : List (LogicVar × Tree)}
    (decomposition : TreesDecompose trees trees constraints) :
    constraints = [] := by
  cases decomposition with
  | nil => rfl
  | cons head tail =>
      rw [head.same_constraints_nil, tail.same_constraints_nil]
      rfl

end

/-- Empty independent child lists can only decompose against another empty
list and produce no constraints. -/
theorem TreesDecompose.left_nil
    {right : List Tree} {constraints : List (LogicVar × Tree)}
    (decomposition : TreesDecompose [] right constraints) :
    right = [] ∧ constraints = [] := by
  cases decomposition
  exact ⟨rfl, rfl⟩

/-- Inversion of an exact two-child decomposition, retaining the ordered
head-before-tail concatenation explicitly. -/
theorem TreesDecompose.two
    {leftHead leftTail rightHead rightTail : Tree}
    {constraints : List (LogicVar × Tree)}
    (decomposition :
      TreesDecompose [leftHead, leftTail] [rightHead, rightTail]
        constraints) :
    ∃ headConstraints tailConstraints,
      TreeDecomposes leftHead rightHead headConstraints ∧
      TreeDecomposes leftTail rightTail tailConstraints ∧
      constraints = headConstraints ++ tailConstraints := by
  cases decomposition with
  | cons head tail =>
      cases tail with
      | cons second rest =>
          cases rest
          exact ⟨_, _, head, second, by simp⟩

/-- Source atom leaves can decompose only when their names coincide, and
then produce no variable constraints. -/
theorem TreeDecomposes.atom_leaf
    {left right : String} {constraints : List (LogicVar × Tree)}
    (decomposition :
      TreeDecomposes
        (.node (.atom left) []) (.node (.atom right) []) constraints) :
    left = right ∧ constraints = [] := by
  cases decomposition with
  | node _ children =>
      cases children
      exact ⟨rfl, rfl⟩

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

/-! ## Exact source-guided structural decomposition -/

/-- A runtime variable spelling can only denote an independent variable.
This is intentionally source-guided: the converse is false for rigid
runtime spellings such as `True` and `#nil`, which each admit two canonical
readings. -/
theorem CanonicalRuntimeAgrees.of_runtime_variable
    {alpha : List (LogicVar × String)}
    {tree : Tree} {name : String}
    (agreement : CanonicalRuntimeAgrees alpha tree (.var name)) :
    ∃ identity, tree = .variable identity ∧ (identity, name) ∈ alpha := by
  cases agreement with
  | «variable» linked => exact ⟨_, rfl, linked⟩

/-- A distinct alpha-related canonical value cannot collapse to the same
runtime variable as the source. -/
theorem CanonicalRuntimeAgrees.runtime_ne_source_variable
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {source : LogicVar} {name : String}
    (linked : (source, name) ∈ alpha)
    {value : Tree} {target : Atom}
    (agreement : CanonicalRuntimeAgrees alpha value target)
    (different : value ≠ .variable source) :
    target ≠ .var name := by
  intro equality
  subst target
  obtain ⟨identity, rfl, identityLinked⟩ :=
    CanonicalRuntimeAgrees.of_runtime_variable agreement
  exact different (congrArg Tree.variable
    (shared.backward identityLinked linked))

/-- Executable left-variable decomposition chooses the expected singleton
whenever the right atom is not that same variable. -/
theorem decomposeEqWith_variable_left
    (groundEq : Metta.Ground → Metta.Ground → Bool)
    (name : String) (target : Atom)
    (different : target ≠ .var name) :
    Metta.Unify.decomposeEqWith groundEq (.var name) target =
      some [(name, target)] := by
  cases target <;> simp_all [Metta.Unify.decomposeEqWith]
  exact fun equality => different equality.symm

/-- Executable right-variable decomposition keeps its right-variable
orientation when the left atom is rigid. -/
theorem decomposeEqWith_variable_right
    (groundEq : Metta.Ground → Metta.Ground → Bool)
    (source : Atom) (name : String)
    (notVariable : ∀ candidate, source ≠ .var candidate) :
    Metta.Unify.decomposeEqWith groundEq source (.var name) =
      some [(name, source)] := by
  cases source <;> simp_all [Metta.Unify.decomposeEqWith]

mutual

/-- Every independent source-guided decomposition is realized by the
executable structural decomposer, with exactly the same ordered constraint
worklist up to the shared alpha graph. -/
theorem TreeDecomposes.runtime
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {leftTree rightTree : Tree}
    {canonical : List (LogicVar × Tree)}
    {leftAtom rightAtom : Atom}
    (leftAgreement : CanonicalRuntimeAgrees alpha leftTree leftAtom)
    (rightAgreement : CanonicalRuntimeAgrees alpha rightTree rightAtom)
    (decomposition :
      TreeDecomposes leftTree rightTree canonical) :
    ∃ runtime : List (String × Atom),
      Metta.Unify.decomposeEqWith PLeaTTa.prologGroundIdentical
          leftAtom rightAtom =
        some runtime ∧
      AlphaTreeConstraintsAgree alpha canonical runtime := by
  cases decomposition with
  | reflexiveVariable identity =>
      cases leftAgreement with
      | «variable» leftLinked =>
          cases rightAgreement with
          | «variable» rightLinked =>
              have namesEqual := shared.forward leftLinked rightLinked
              exact
                ⟨[], by
                    simp [Metta.Unify.decomposeEqWith, namesEqual],
                  .nil⟩
  | bindLeft source value different =>
      cases leftAgreement with
      | @«variable» _ name linked =>
          refine ⟨[(name, rightAtom)], ?_, ?_⟩
          · exact decomposeEqWith_variable_left
              PLeaTTa.prologGroundIdentical _ _
              (PLeaTTa.PrologMguDirectSimulation.CanonicalRuntimeAgrees.runtime_ne_source_variable
                shared linked rightAgreement different)
          · exact .cons ⟨linked, rightAgreement⟩ .nil
  | bindRight value target notVariable =>
      cases rightAgreement with
      | @«variable» _ name linked =>
          have sourceNotVariable :
              ∀ candidate, leftAtom ≠ .var candidate := by
            intro candidate equality
            subst leftAtom
            obtain ⟨identity, equality, _⟩ :=
              CanonicalRuntimeAgrees.of_runtime_variable leftAgreement
            exact notVariable identity equality
          refine ⟨[(name, leftAtom)], ?_, ?_⟩
          · exact decomposeEqWith_variable_right
              PLeaTTa.prologGroundIdentical _ _ sourceNotVariable
          · exact .cons ⟨linked, leftAgreement⟩ .nil
  | node symbol children =>
      cases leftAgreement with
      | atom notTrue notFalse =>
          obtain ⟨rfl, rfl⟩ := children.left_nil
          exact
            ⟨[],
              CanonicalRuntimeAgrees.decomposeEqWith_same
                shared
                  (CanonicalRuntimeAgrees.atom notTrue notFalse)
                  rightAgreement,
              .nil⟩
      | trueAtom =>
          obtain ⟨rfl, rfl⟩ := children.left_nil
          exact
            ⟨[],
              CanonicalRuntimeAgrees.decomposeEqWith_same
                shared CanonicalRuntimeAgrees.trueAtom rightAgreement,
              .nil⟩
      | falseAtom =>
          obtain ⟨rfl, rfl⟩ := children.left_nil
          exact
            ⟨[],
              CanonicalRuntimeAgrees.decomposeEqWith_same
                shared CanonicalRuntimeAgrees.falseAtom rightAgreement,
              .nil⟩
      | integer value =>
          obtain ⟨rfl, rfl⟩ := children.left_nil
          exact
            ⟨[],
              CanonicalRuntimeAgrees.decomposeEqWith_same
                shared (CanonicalRuntimeAgrees.integer value)
                  rightAgreement,
              .nil⟩
      | float value =>
          obtain ⟨rfl, rfl⟩ := children.left_nil
          exact
            ⟨[],
              CanonicalRuntimeAgrees.decomposeEqWith_same
                shared (CanonicalRuntimeAgrees.float value)
                  rightAgreement,
              .nil⟩
      | string value =>
          obtain ⟨rfl, rfl⟩ := children.left_nil
          exact
            ⟨[],
              CanonicalRuntimeAgrees.decomposeEqWith_same
                shared (CanonicalRuntimeAgrees.string value)
                  rightAgreement,
              .nil⟩
      | @partialValue head argumentsTree encodedArguments arguments =>
          cases rightAgreement with
          | @partialValue _ rightArgumentsTree rightEncodedArguments
              rightArguments =>
              obtain
                ⟨headConstraints, argumentConstraints, headDecomposition,
                  argumentDecomposition, canonicalExact⟩ :=
                children.two
              obtain ⟨headNamesEqual, headEmpty⟩ :=
                headDecomposition.atom_leaf
              subst head
              subst headConstraints
              simp only [List.nil_append] at canonicalExact
              subst canonical
              obtain
                ⟨runtime, runtimeExact, runtimeAgreement⟩ :=
                argumentDecomposition.runtime
                  shared arguments rightArguments
              refine ⟨runtime, ?_, runtimeAgreement⟩
              simp [partialC, partialTagA,
                Metta.Unify.decomposeEqWith,
                Metta.Unify.decomposeListWith, runtimeExact]
      | nil =>
          obtain ⟨rfl, rfl⟩ := children.left_nil
          exact
            ⟨[],
              CanonicalRuntimeAgrees.decomposeEqWith_same
                shared CanonicalRuntimeAgrees.nil rightAgreement,
              .nil⟩
      | @cons leftHeadTree leftTailTree leftHeadAtom leftTailAtom
          leftHead leftTail =>
          cases rightAgreement with
          | @cons rightHeadTree rightTailTree rightHeadAtom rightTailAtom
              rightHead rightTail =>
              obtain
                ⟨headConstraints, tailConstraints, headDecomposition,
                  tailDecomposition, canonicalExact⟩ :=
                children.two
              subst canonical
              obtain
                ⟨runtimeHead, headExact, headAgreement⟩ :=
                headDecomposition.runtime shared leftHead rightHead
              obtain
                ⟨runtimeTail, tailExact, tailAgreement⟩ :=
                tailDecomposition.runtime shared leftTail rightTail
              refine
                ⟨runtimeHead ++ runtimeTail, ?_,
                  List.rel_append headAgreement tailAgreement⟩
              simp [consC, Metta.Unify.decomposeEqWith,
                Metta.Unify.decomposeListWith, headExact, tailExact]

/-- Ordered-list companion to `TreeDecomposes.runtime`. -/
theorem TreesDecompose.runtime
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {leftTrees rightTrees : List Tree}
    {canonical : List (LogicVar × Tree)}
    {leftAtoms rightAtoms : List Atom}
    (leftAgreement :
      List.Forall₂ (CanonicalRuntimeAgrees alpha) leftTrees leftAtoms)
    (rightAgreement :
      List.Forall₂ (CanonicalRuntimeAgrees alpha) rightTrees rightAtoms)
    (decomposition :
      TreesDecompose leftTrees rightTrees canonical) :
    ∃ runtime : List (String × Atom),
      Metta.Unify.decomposeListWith PLeaTTa.prologGroundIdentical
          leftAtoms rightAtoms =
        some runtime ∧
      AlphaTreeConstraintsAgree alpha canonical runtime := by
  cases decomposition with
  | nil =>
      cases leftAgreement
      cases rightAgreement
      exact ⟨[], rfl, .nil⟩
  | cons head tail =>
      cases leftAgreement with
      | cons leftHead leftTail =>
          cases rightAgreement with
          | cons rightHead rightTail =>
              obtain ⟨runtimeHead, headExact, headAgreement⟩ :=
                head.runtime shared leftHead rightHead
              obtain ⟨runtimeTail, tailExact, tailAgreement⟩ :=
                tail.runtime shared leftTail rightTail
              refine ⟨runtimeHead ++ runtimeTail, ?_, ?_⟩
              · simp [Metta.Unify.decomposeListWith,
                  headExact, tailExact]
              · exact List.rel_append
                  headAgreement tailAgreement

end

/-- Whole-worklist exactness: independent ordered decomposition and the
executable comparator-parametric decomposer produce alpha-related
constraints in the same order. -/
theorem TreeEquationsDecompose.runtime
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {canonicalEquations : List TreeEquation}
    {canonicalConstraints : List (LogicVar × Tree)}
    {runtimeEquations : List (Atom × Atom)}
    (equationsAgreement :
      AlphaTreeEquationsAgree alpha canonicalEquations runtimeEquations)
    (decomposition :
      TreeEquationsDecompose canonicalEquations canonicalConstraints) :
    ∃ runtimeConstraints : List (String × Atom),
      Metta.Unify.decomposeAllWith PLeaTTa.prologGroundIdentical
          runtimeEquations =
        some runtimeConstraints ∧
      AlphaTreeConstraintsAgree alpha
        canonicalConstraints runtimeConstraints := by
  cases decomposition with
  | nil =>
      cases equationsAgreement
      exact ⟨[], rfl, .nil⟩
  | cons head tail =>
      cases equationsAgreement with
      | cons equationAgreement tailAgreement =>
          obtain ⟨runtimeHead, headExact, headAgreement⟩ :=
            head.runtime shared
              equationAgreement.left equationAgreement.right
          obtain ⟨runtimeTail, tailExact, runtimeTailAgreement⟩ :=
            tail.runtime shared tailAgreement
          refine
            ⟨runtimeHead ++ runtimeTail, ?_,
              List.rel_append headAgreement runtimeTailAgreement⟩
          simp [Metta.Unify.decomposeAllWith,
            headExact, tailExact]

/-- A shared source/runtime equation family gives pointwise canonical-tree
agreement with the executable zipped worklist. -/
theorem SharedAlphaEquationsAgree.alphaTreeEquationsAgree_zip
    {alpha : List (LogicVar × String)}
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms) :
    AlphaTreeEquationsAgree alpha
      (denoteEquations equations) (List.zip leftAtoms rightAtoms) := by
  induction agreement with
  | nil =>
      exact .nil
  | cons left right tail inductionHypothesis =>
      exact .cons
        ⟨AlphaTermAgrees.canonicalRuntimeAgrees left,
          AlphaTermAgrees.canonicalRuntimeAgrees right⟩
        inductionHypothesis

/-- A shared equation family has equal executable arities.  Keeping this
fact attached to the source-guided relation avoids admitting the malformed
`List.zip` truncation case at the top-level executable bridge. -/
theorem SharedAlphaEquationsAgree.runtime_lengths
    {alpha : List (LogicVar × String)}
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms) :
    leftAtoms.length = rightAtoms.length := by
  induction agreement with
  | nil =>
      rfl
  | cons left right tail inductionHypothesis =>
      simp only [List.length_cons, Nat.succ.injEq]
      exact inductionHypothesis

/-- Zipping equal-length atom lists exposes exactly the same structural
constraints as direct ordered-list decomposition. -/
theorem decomposeAllWith_zip_eq_decomposeListWith
    (groundEq : Metta.Ground → Metta.Ground → Bool) :
    ∀ {left right : List Atom}, left.length = right.length →
      Metta.Unify.decomposeAllWith groundEq (List.zip left right) =
        Metta.Unify.decomposeListWith groundEq left right
  | [], [], _ => rfl
  | [], _ :: _, lengths => by
      simp at lengths
  | _ :: _, [], lengths => by
      simp at lengths
  | left :: lefts, right :: rights, lengths => by
      have tailLengths : lefts.length = rights.length := by
        simpa only [List.length_cons, Nat.succ.injEq] using lengths
      simp only [List.zip_cons_cons, Metta.Unify.decomposeAllWith,
        Metta.Unify.decomposeListWith]
      rw [decomposeAllWith_zip_eq_decomposeListWith
        groundEq tailLengths]

/-- The one-expression top-level worklist and its pointwise zipped form run
the same executable elimination loop at every fuel and base state. -/
theorem unifyRoundsWith_expression_eq_zip
    (groundEq : Metta.Ground → Metta.Ground → Bool)
    (fuel : Nat) (left right : List Atom) (base : Subst)
    (lengths : left.length = right.length) :
    Metta.Unify.unifyRoundsWith groundEq fuel
        [(.expr left, .expr right)] base =
      Metta.Unify.unifyRoundsWith groundEq fuel
        (List.zip left right) base := by
  have decomposed :
      Metta.Unify.decomposeAllWith groundEq
          [(.expr left, .expr right)] =
        Metta.Unify.decomposeAllWith groundEq
          (List.zip left right) := by
    simp only [Metta.Unify.decomposeAllWith,
      Metta.Unify.decomposeEqWith]
    rw [decomposeAllWith_zip_eq_decomposeListWith groundEq lengths]
    cases Metta.Unify.decomposeListWith groundEq left right <;> simp
  cases fuel <;>
    simp [Metta.Unify.unifyRoundsWith, decomposed]

/-! ## Exact repeated elimination -/

/-- Canonical key freshness transports to the runtime association list.
Inverse alpha functionality is load-bearing: without it, a distinct
canonical key could reuse the executable name being inserted. -/
theorem AlphaTreeSubstitutionAgrees.runtime_key_not_mem
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {source : LogicVar} {name : String}
    (linked : (source, name) ∈ alpha)
    {canonical : TreeSubstitution} {runtime : Subst}
    (agreement :
      AlphaTreeSubstitutionAgrees alpha canonical runtime)
    (fresh : source ∉ canonical.map Prod.fst) :
    name ∉ runtime.map Prod.fst := by
  induction agreement with
  | nil =>
      simp
  | @cons identity runtimeName tree atom canonical runtime
      identityLinked replacement tail inductionHypothesis =>
      simp only [List.map_cons, List.mem_cons, not_or] at fresh ⊢
      constructor
      · intro namesEqual
        subst runtimeName
        have identitiesEqual : identity = source := by
          exact shared.backward identityLinked linked
        exact fresh.1 identitiesEqual.symm
      · exact inductionHypothesis fresh.2

/-- Filtering a runtime substitution by a key absent from its complete key
list is the identity. -/
theorem substErase_eq_self_of_key_not_mem
    (runtime : Subst) (name : String)
    (fresh : name ∉ runtime.map Prod.fst) :
    Metta.Subst.erase runtime name = runtime := by
  induction runtime with
  | nil => rfl
  | cons entry runtime inductionHypothesis =>
      rcases entry with ⟨key, value⟩
      simp only [List.map_cons, List.mem_cons, not_or] at fresh
      have keep : (key != name) = true := by
        simp [Ne.symm fresh.1]
      unfold Metta.Subst.erase at inductionHypothesis ⊢
      simp only [List.filter_cons, keep, if_true]
      rw [inductionHypothesis fresh.2]

/-- The executable comparator-parametric round loop realizes every
successful independent canonical round derivation with the same fuel,
ordered worklist, base substitution, and final association-list shape up to
the shared alpha graph. -/
theorem TreeUnifyRounds.runtime
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {fuel : Nat}
    {canonicalEquations : List TreeEquation}
    {canonicalBase canonicalResult : TreeSubstitution}
    {runtimeEquations : List (Atom × Atom)}
    {runtimeBase : Subst}
    (equationsAgreement :
      AlphaTreeEquationsAgree alpha canonicalEquations runtimeEquations)
    (baseAgreement :
      AlphaTreeSubstitutionAgrees alpha canonicalBase runtimeBase)
    (rounds :
      TreeUnifyRounds fuel canonicalEquations
        canonicalBase canonicalResult) :
    ∃ runtimeResult : Subst,
      Metta.Unify.unifyRoundsWith PLeaTTa.prologGroundIdentical
          fuel runtimeEquations runtimeBase =
        some runtimeResult ∧
      AlphaTreeSubstitutionAgrees alpha
        canonicalResult runtimeResult := by
  induction rounds generalizing runtimeEquations runtimeBase with
  | done fuel decomposition =>
      obtain ⟨runtimeConstraints, decomposed, constraintsAgreement⟩ :=
        decomposition.runtime shared equationsAgreement
      cases constraintsAgreement
      refine ⟨runtimeBase, ?_, baseAgreement⟩
      cases fuel <;>
        simp [Metta.Unify.unifyRoundsWith, decomposed]
  | @eliminate fuel equations source replacement rest base result
      decomposition fresh absent avoids next inductionHypothesis =>
      obtain ⟨runtimeConstraints, decomposed, constraintsAgreement⟩ :=
        decomposition.runtime shared equationsAgreement
      cases constraintsAgreement with
      | @cons canonicalHead runtimeHead canonicalTail runtimeTail
          headAgreement tailAgreement =>
          rcases runtimeHead with ⟨name, target⟩
          have runtimeAbsent :
              Metta.Subst.occurs name target = false := by
            rw [←
              PLeaTTa.PrologMguDirectSimulation.CanonicalRuntimeAgrees.occurs_eq
                shared headAgreement.key headAgreement.replacement]
            exact absent
          have runtimeFresh :
              name ∉ runtimeBase.map Prod.fst :=
            PLeaTTa.PrologMguDirectSimulation.AlphaTreeSubstitutionAgrees.runtime_key_not_mem
              shared headAgreement.key baseAgreement fresh
          have erased :
              Metta.Subst.erase runtimeBase name = runtimeBase :=
            substErase_eq_self_of_key_not_mem
              runtimeBase name runtimeFresh
          have nextEquationsAgreement :
              AlphaTreeEquationsAgree alpha
                (normalizeTreeConstraints source replacement rest)
                (runtimeTail.map fun item =>
                  (Metta.Subst.apply [(name, target)] (.var item.1),
                    Metta.Subst.apply [(name, target)] item.2)) :=
            PLeaTTa.PrologMguDirectSimulation.AlphaTreeConstraintsAgree.instantiateOne
              shared headAgreement.key headAgreement.replacement
                tailAgreement
          have nextBaseAgreement :
              AlphaTreeSubstitutionAgrees alpha
                ((source, replacement) :: base)
                ((name, target) :: runtimeBase) :=
            .cons headAgreement.key headAgreement.replacement baseAgreement
          obtain ⟨runtimeResult, nextExact, resultAgreement⟩ :=
            inductionHypothesis
              nextEquationsAgreement nextBaseAgreement
          refine ⟨runtimeResult, ?_, resultAgreement⟩
          simp [Metta.Unify.unifyRoundsWith, decomposed,
            runtimeAbsent, Metta.Subst.extend, erased, nextExact]

/-- Every independently selected ordered canonical MGU forces the actual
top-level executable unifier to succeed at its real structural fuel.  The
returned association list agrees with a constructively produced flattened
canonical Robinson run.  It is deliberately not asserted equal to
`canonical`: equivalent MGU orientations can have different list spelling,
as witnessed by `exact_decomposition_commutation_is_false`. -/
theorem OrderedTreeMgu.unifyTopExact_exists_alpha
    {alpha : List (LogicVar × String)}
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    {canonical : TreeSubstitution}
    (shared : SharedRuntimeAlpha alpha)
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    (derivation :
      OrderedTreeMgu (denoteEquations equations) canonical) :
    ∃ flattened runtimeResult,
      TreeUnifyRounds
        ((.expr leftAtoms : Atom).size +
          (.expr rightAtoms : Atom).size)
        (denoteEquations equations) [] flattened ∧
      PLeaTTa.unifyTopExact
          (.expr leftAtoms) (.expr rightAtoms) =
        some runtimeResult ∧
      AlphaTreeSubstitutionAgrees alpha
        flattened runtimeResult := by
  obtain ⟨flattened, smallRounds⟩ :=
    PLeaTTa.PrologMguDirectSimulation.OrderedTreeMgu.treeUnifyRounds_exists
      derivation
  have rounds :
      TreeUnifyRounds
        ((.expr leftAtoms : Atom).size +
          (.expr rightAtoms : Atom).size)
        (denoteEquations equations) [] flattened :=
    smallRounds.mono
      (PLeaTTa.PrologMguDirectSimulation.SharedAlphaEquationsAgree.canonical_fuel_le_runtime_fuel
        agreement)
  have equationsAgreement :
      AlphaTreeEquationsAgree alpha
        (denoteEquations equations)
        (List.zip leftAtoms rightAtoms) :=
    PLeaTTa.PrologMguDirectSimulation.SharedAlphaEquationsAgree.alphaTreeEquationsAgree_zip
      agreement
  obtain ⟨runtimeResult, runtimeExact, runtimeAgreement⟩ :=
    rounds.runtime shared equationsAgreement
      (AlphaTreeSubstitutionAgrees.nil (alpha := alpha))
  refine ⟨flattened, runtimeResult, rounds, ?_, runtimeAgreement⟩
  unfold PLeaTTa.unifyTopExact Metta.Unify.unifyTopWith
  rw [unifyRoundsWith_expression_eq_zip
    PLeaTTa.prologGroundIdentical
    ((.expr leftAtoms : Atom).size +
      (.expr rightAtoms : Atom).size)
    leftAtoms rightAtoms []
    (PLeaTTa.PrologMguDirectSimulation.SharedAlphaEquationsAgree.runtime_lengths
      agreement)]
  exact runtimeExact

/-- The executable-success bridge also exposes the semantic invariant hidden
by association-list orientation: the independently ordered MGU and the
flattened runtime-guiding MGU factor through each other over every canonical
tree.  The flattened result is topological, its exact executable spelling is
acyclic, and the two give the same open valuation under the shared alpha
graph.  Thus residual aliases may be spelled differently without changing
the finite-tree solution space. -/
theorem OrderedTreeMgu.unifyTopExact_exists_alpha_mgu
    {alpha : List (LogicVar × String)}
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    {canonical : TreeSubstitution}
    (shared : SharedRuntimeAlpha alpha)
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    (derivation :
      OrderedTreeMgu (denoteEquations equations) canonical) :
    ∃ flattened runtimeResult,
      PLeaTTa.unifyTopExact
          (.expr leftAtoms) (.expr rightAtoms) =
        some runtimeResult ∧
      AlphaTreeSubstitutionAgrees alpha
        flattened runtimeResult ∧
      TreeSubstitutionTopological flattened ∧
      Nonempty (PLeaTTa.SubstTopological runtimeResult) ∧
      AlphaValuationAgrees alpha flattened runtimeResult ∧
      TreeIsMgu flattened (denoteEquations equations) ∧
      TreeFactorsThrough flattened canonical ∧
      TreeFactorsThrough canonical flattened := by
  obtain
    ⟨flattened, runtimeResult, rounds, runtimeExact,
      runtimeAgreement⟩ :=
    PLeaTTa.PrologMguDirectSimulation.OrderedTreeMgu.unifyTopExact_exists_alpha
      shared agreement derivation
  have flattenedMgu : TreeIsMgu flattened (denoteEquations equations) :=
    rounds.isMostGeneral
  have canonicalMgu : TreeIsMgu canonical (denoteEquations equations) :=
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
    ⟨flattened, runtimeResult, runtimeExact, runtimeAgreement,
      flattenedTopological, ⟨runtimeTopological⟩, flattenedValuation,
      flattenedMgu,
      canonicalMgu.2 flattened flattenedMgu.1,
      flattenedMgu.2 canonical canonicalMgu.1⟩

/-- Composition through the machine's carried binding preserves the complete
direct-simulation witness.  The generated component remains visible before
installation, while `installed` is pinned to the exact `unifyB` empty/nonempty
branch.  No claim about liveness trimming is folded into this theorem. -/
theorem OrderedTreeMgu.unifyB_exists_alpha_mgu
    (base : Subst)
    {alpha : List (LogicVar × String)}
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    {canonical : TreeSubstitution}
    (shared : SharedRuntimeAlpha alpha)
    (agreement :
      SharedAlphaEquationsAgree alpha equations
        (leftAtoms.map (PLeaTTa.subst base))
        (rightAtoms.map (PLeaTTa.subst base)))
    (derivation :
      OrderedTreeMgu (denoteEquations equations) canonical) :
    ∃ flattened generated installed,
      PLeaTTa.unifyTopExact
          (.expr (leftAtoms.map (PLeaTTa.subst base)))
          (.expr (rightAtoms.map (PLeaTTa.subst base))) =
        some generated ∧
      AlphaTreeSubstitutionAgrees alpha flattened generated ∧
      TreeSubstitutionTopological flattened ∧
      Nonempty (PLeaTTa.SubstTopological generated) ∧
      AlphaValuationAgrees alpha flattened generated ∧
      TreeIsMgu flattened (denoteEquations equations) ∧
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
    PLeaTTa.PrologMguDirectSimulation.OrderedTreeMgu.unifyTopExact_exists_alpha_mgu
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

/-- Direct repeated-elimination adequacy specialized to the real
suffix-freshened retained-clause activation.  The exact graph joins the
normalized query variables and the reserved clause-copy interval once, then
relates both the generated MGU and the installed `unifyB` result. -/
theorem FreshenedClauseAlphaAgrees.unifyB_exists_direct_alpha_mgu
    {queryAlpha : List (LogicVar × String)}
    {reference : LocalClause} {executablePredicate : String}
    {executable : PLeaTTa.Clause} {freshSeed : Nat}
    {argsv args : List Atom} {result : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst}
    {query : Atom} {seed barrier : Nat}
    (freshened :
      FreshenedClauseAlphaAgrees reference executablePredicate executable
        freshSeed argsv args result rest binding query seed barrier)
    (argsvEq : argsv = args.map (PLeaTTa.subst binding))
    (queryShared : SharedRuntimeAlpha queryAlpha)
    {queryTerms : List Term}
    (queryPayload :
      AlphaTermsAgree queryAlpha queryTerms
        (args.map (PLeaTTa.subst binding) ++
          [PLeaTTa.subst binding result]))
    (queryReferenceBelow :
      GeneratedBelow (reference.freshCopy freshSeed).firstFresh
        (queryAlpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ queryAlpha.map Prod.snd →
        name ∈ resolutionOccupiedVars argsv result rest binding query)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars argsv result rest binding query) ≤ seed)
    (lengths :
      queryTerms.length =
        (reference.freshCopy freshSeed).clause.arguments.length)
    {canonical : TreeSubstitution}
    (derivation :
      OrderedTreeMgu
        (denoteEquations
          (argumentEquations queryTerms
            (reference.freshCopy freshSeed).clause.arguments))
        canonical) :
    ∃ flattened generated installed,
      PLeaTTa.unifyTopExact
          (.expr ((args ++ [result]).map (PLeaTTa.subst binding)))
          (.expr
            (((freshenResolutionClause argsv args result rest binding query
                seed barrier executable).params ++
              [(freshenResolutionClause argsv args result rest binding query
                seed barrier executable).result]).map
              (PLeaTTa.subst binding))) =
        some generated ∧
      AlphaTreeSubstitutionAgrees
          (queryAlpha ++
            RuntimeAlpha.graph
              (referenceFreshTargets
                (reference.freshCopy freshSeed).firstFresh
                reference.variables)
              (executableFreshTargets
                (resolutionFreshSuffix argsv result rest binding query seed)
                reference.variables))
          flattened generated ∧
      TreeSubstitutionTopological flattened ∧
      Nonempty (PLeaTTa.SubstTopological generated) ∧
      AlphaValuationAgrees
          (queryAlpha ++
            RuntimeAlpha.graph
              (referenceFreshTargets
                (reference.freshCopy freshSeed).firstFresh
                reference.variables)
              (executableFreshTargets
                (resolutionFreshSuffix argsv result rest binding query seed)
                reference.variables))
          flattened generated ∧
      TreeIsMgu flattened
        (denoteEquations
          (argumentEquations queryTerms
            (reference.freshCopy freshSeed).clause.arguments)) ∧
      TreeFactorsThrough flattened canonical ∧
      TreeFactorsThrough canonical flattened ∧
      PLeaTTa.unifyB binding (.expr (args ++ [result]))
          (.expr
            ((freshenResolutionClause argsv args result rest binding query
                seed barrier executable).params ++
              [(freshenResolutionClause argsv args result rest binding query
                seed barrier executable).result])) =
        some installed ∧
      installed =
        match generated with
        | [] => binding
        | _ :: _ => Metta.Subst.compose generated binding := by
  have normalized :=
    PLeaTTa.PrologMguValuation.FreshenedClauseAlphaAgrees.normalizedSharedHeadEquations
      freshened argsvEq queryShared queryPayload queryReferenceBelow
      queryExecutableLive highWater lengths
  exact
    PLeaTTa.PrologMguDirectSimulation.OrderedTreeMgu.unifyB_exists_alpha_mgu
      binding normalized.1 normalized.2 derivation

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

private def decomposeWitnessLeft : LogicVar := .source "left"
private def decomposeWitnessRight : LogicVar := .source "right"
private def decomposeWitnessA : Tree := .node (.atom "a") []
private def decomposeWitnessB : Tree := .node (.atom "b") []
private def decomposeWitnessAlpha : List (LogicVar × String) :=
  [(decomposeWitnessLeft, "X"), (decomposeWitnessRight, "Y")]

private theorem decomposeWitnessShared :
    SharedRuntimeAlpha decomposeWitnessAlpha := by
  constructor <;>
    intro left right name leftMember rightMember <;>
    simp [decomposeWitnessAlpha, decomposeWitnessLeft,
      decomposeWitnessRight] at leftMember rightMember <;>
    rcases leftMember with leftMember | leftMember <;>
    rcases rightMember with rightMember | rightMember <;>
    simp_all

/-- A two-field cons witness pins the order of the independent constraints
and the executable worklist simultaneously.  Reversing child traversal
would change the displayed runtime list and falsify the theorem. -/
theorem structural_decomposition_preserves_left_to_right_order :
    let canonicalLeft : Tree :=
      .node .cons
        [.variable decomposeWitnessLeft,
         .variable decomposeWitnessRight]
    let canonicalRight : Tree :=
      .node .cons [decomposeWitnessA, decomposeWitnessB]
    let canonicalConstraints :=
      [(decomposeWitnessLeft, decomposeWitnessA),
       (decomposeWitnessRight, decomposeWitnessB)]
    let runtimeLeft := consC (.var "X") (.var "Y")
    let runtimeRight := consC (.sym "a") (.sym "b")
    let runtimeConstraints := [("X", .sym "a"), ("Y", .sym "b")]
    TreeDecomposes canonicalLeft canonicalRight canonicalConstraints ∧
      Metta.Unify.decomposeEqWith PLeaTTa.prologGroundIdentical
          runtimeLeft runtimeRight =
        some runtimeConstraints ∧
      AlphaTreeConstraintsAgree decomposeWitnessAlpha
        canonicalConstraints runtimeConstraints := by
  dsimp only
  have independent :
      TreeDecomposes
        (.node .cons
          [.variable decomposeWitnessLeft,
           .variable decomposeWitnessRight])
        (.node .cons [decomposeWitnessA, decomposeWitnessB])
        [(decomposeWitnessLeft, decomposeWitnessA),
         (decomposeWitnessRight, decomposeWitnessB)] := by
    apply TreeDecomposes.node .cons
    simpa using
      (TreesDecompose.cons
        (TreeDecomposes.bindLeft
          decomposeWitnessLeft decomposeWitnessA (by
            simp [decomposeWitnessA]))
        (TreesDecompose.cons
          (TreeDecomposes.bindLeft
            decomposeWitnessRight decomposeWitnessB (by
              simp [decomposeWitnessB]))
          TreesDecompose.nil))
  have leftAgreement :
      CanonicalRuntimeAgrees decomposeWitnessAlpha
        (.node .cons
          [.variable decomposeWitnessLeft,
           .variable decomposeWitnessRight])
        (consC (.var "X") (.var "Y")) :=
    .cons (.variable (by simp [decomposeWitnessAlpha]))
      (.variable (by simp [decomposeWitnessAlpha]))
  have rightAgreement :
      CanonicalRuntimeAgrees decomposeWitnessAlpha
        (.node .cons [decomposeWitnessA, decomposeWitnessB])
        (consC (.sym "a") (.sym "b")) :=
    .cons
      (.atom (by decide) (by decide))
      (.atom (by decide) (by decide))
  obtain ⟨runtime, runtimeExact, runtimeAgreement⟩ :=
    independent.runtime decomposeWitnessShared
      leftAgreement rightAgreement
  have runtimeValue :
      runtime = [("X", .sym "a"), ("Y", .sym "b")] := by
    symm
    simpa [consC, Metta.Unify.decomposeEqWith,
      Metta.Unify.decomposeListWith] using runtimeExact
  subst runtime
  exact ⟨independent, runtimeExact, runtimeAgreement⟩

/-- Two genuine elimination rounds pin both normalization and the
newest-first returned association-list order.  A one-round shortcut or a
reversed extension policy falsifies the exact executable result. -/
theorem repeated_elimination_preserves_normalization_and_result_order :
    let canonicalEquations : List TreeEquation :=
      [(.variable decomposeWitnessLeft,
          .variable decomposeWitnessRight),
       (.variable decomposeWitnessRight, decomposeWitnessA)]
    let canonicalResult : TreeSubstitution :=
      [(decomposeWitnessRight, decomposeWitnessA),
       (decomposeWitnessLeft, .variable decomposeWitnessRight)]
    let runtimeEquations : List (Atom × Atom) :=
      [(.var "X", .var "Y"), (.var "Y", .sym "a")]
    let runtimeResult : Subst :=
      [("Y", .sym "a"), ("X", .var "Y")]
    TreeUnifyRounds 2 canonicalEquations [] canonicalResult ∧
      Metta.Unify.unifyRoundsWith PLeaTTa.prologGroundIdentical
          2 runtimeEquations [] =
        some runtimeResult ∧
      AlphaTreeSubstitutionAgrees decomposeWitnessAlpha
        canonicalResult runtimeResult := by
  dsimp only
  have firstDecomposition :
      TreeEquationsDecompose
        [(.variable decomposeWitnessLeft,
            .variable decomposeWitnessRight),
         (.variable decomposeWitnessRight, decomposeWitnessA)]
        [(decomposeWitnessLeft, .variable decomposeWitnessRight),
         (decomposeWitnessRight, decomposeWitnessA)] := by
    simpa using
      (TreeEquationsDecompose.cons
        (TreeDecomposes.bindLeft
          decomposeWitnessLeft
          (.variable decomposeWitnessRight) (by
            simp [decomposeWitnessLeft, decomposeWitnessRight]))
        (TreeEquationsDecompose.cons
          (TreeDecomposes.bindLeft
            decomposeWitnessRight decomposeWitnessA (by
              simp [decomposeWitnessA]))
          TreeEquationsDecompose.nil))
  have secondDecomposition :
      TreeEquationsDecompose
        [(.variable decomposeWitnessRight, decomposeWitnessA)]
        [(decomposeWitnessRight, decomposeWitnessA)] := by
    simpa using
      (TreeEquationsDecompose.cons
        (TreeDecomposes.bindLeft
          decomposeWitnessRight decomposeWitnessA (by
            simp [decomposeWitnessA]))
        TreeEquationsDecompose.nil)
  have terminal :
      TreeUnifyRounds 0 []
        [(decomposeWitnessRight, decomposeWitnessA),
         (decomposeWitnessLeft, .variable decomposeWitnessRight)]
        [(decomposeWitnessRight, decomposeWitnessA),
         (decomposeWitnessLeft, .variable decomposeWitnessRight)] :=
    .done 0 TreeEquationsDecompose.nil
  have secondRound :
      TreeUnifyRounds 1
        [(.variable decomposeWitnessRight, decomposeWitnessA)]
        [(decomposeWitnessLeft, .variable decomposeWitnessRight)]
        [(decomposeWitnessRight, decomposeWitnessA),
         (decomposeWitnessLeft, .variable decomposeWitnessRight)] := by
    apply TreeUnifyRounds.eliminate 0 secondDecomposition
    · simp [decomposeWitnessLeft, decomposeWitnessRight]
    · simp [Tree.occurs, Trees.occurs, decomposeWitnessA]
    · exact True.intro
    · simpa [normalizeTreeConstraints,
        Tree.instantiateOne, Trees.instantiateOne] using terminal
  have rounds :
      TreeUnifyRounds 2
        [(.variable decomposeWitnessLeft,
            .variable decomposeWitnessRight),
         (.variable decomposeWitnessRight, decomposeWitnessA)]
        []
        [(decomposeWitnessRight, decomposeWitnessA),
         (decomposeWitnessLeft, .variable decomposeWitnessRight)] := by
    apply TreeUnifyRounds.eliminate 1 firstDecomposition
    · simp
    · simp [Tree.occurs,
        decomposeWitnessLeft, decomposeWitnessRight]
    · simp [TreeSubstitution.keys, TreeVariablesSatisfy]
    · simpa [normalizeTreeConstraints,
        Tree.instantiateOne, Trees.instantiateOne,
        decomposeWitnessA,
        decomposeWitnessLeft, decomposeWitnessRight] using secondRound
  have equationsAgreement :
      AlphaTreeEquationsAgree decomposeWitnessAlpha
        [(.variable decomposeWitnessLeft,
            .variable decomposeWitnessRight),
         (.variable decomposeWitnessRight, decomposeWitnessA)]
        [(.var "X", .var "Y"), (.var "Y", .sym "a")] :=
    .cons
      ⟨.variable (by simp [decomposeWitnessAlpha]),
        .variable (by simp [decomposeWitnessAlpha])⟩
      (.cons
        ⟨.variable (by simp [decomposeWitnessAlpha]),
          .atom (by decide) (by decide)⟩
        .nil)
  obtain ⟨runtime, runtimeExact, runtimeAgreement⟩ :=
    rounds.runtime decomposeWitnessShared
      equationsAgreement AlphaTreeSubstitutionAgrees.nil
  have runtimeValue :
      runtime = [("Y", .sym "a"), ("X", .var "Y")] := by
    have computed :
        Metta.Unify.unifyRoundsWith
            PLeaTTa.prologGroundIdentical 2
            [(.var "X", .var "Y"), (.var "Y", .sym "a")] [] =
          some [("Y", .sym "a"), ("X", .var "Y")] := by
      simp [Metta.Unify.unifyRoundsWith,
        Metta.Unify.decomposeAllWith,
        Metta.Unify.decomposeEqWith,
        Metta.Subst.occurs, Metta.Subst.apply,
        Metta.Subst.lookup, Metta.Subst.extend,
        Metta.Subst.erase]
    rw [computed] at runtimeExact
    exact Option.some.inj runtimeExact.symm
  subst runtime
  exact ⟨rounds, runtimeExact, runtimeAgreement⟩

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
