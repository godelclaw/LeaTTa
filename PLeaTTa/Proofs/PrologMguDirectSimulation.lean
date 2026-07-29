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
  TreeDecomposes.runtime,
  TreeEquationsDecompose.runtime,
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
      (canonical.map fun item =>
        (Tree.instantiateOne source replacement (.variable item.1),
          Tree.instantiateOne source replacement item.2))
      (runtime.map fun item =>
        (Metta.Subst.apply [(name, target)] (.var item.1),
          Metta.Subst.apply [(name, target)] item.2)) := by
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
              simp [chainOf, consC, nilA,
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
