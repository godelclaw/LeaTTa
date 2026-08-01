-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologMguVariantRenaming
Purpose: Turn finite-tree mutual instantiation into an explicit bijective
  variable renaming on each observed value.
Trusted boundary: none
Main exports: MutualInstanceRenaming,
  TreeSubstitutionVariants.apply_has_mutualInstanceRenaming
-/
import PLeaTTa.Proofs.PrologMguOpenAgreement
import PLeaTTa.Proofs.PrologMguVariant

namespace PLeaTTa.PrologMguVariantRenaming

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PrologMguOpenAgreement
open PrologMguVariant

mutual

/-- Pointwise variable renaming in the canonical finite-tree algebra. -/
def Tree.renameVariables (rename : LogicVar → LogicVar) : Tree → Tree
  | .variable identity => .variable (rename identity)
  | .node symbol children =>
      .node symbol (Trees.renameVariables rename children)

/-- Ordered child-list companion of `Tree.renameVariables`. -/
def Trees.renameVariables (rename : LogicVar → LogicVar) :
    List Tree → List Tree
  | [] => []
  | tree :: trees =>
      Tree.renameVariables rename tree ::
        Trees.renameVariables rename trees

end

/-!
# Finite mutual instances are variants

`TreeSubstitutionVariants` deliberately states residual-MGU equivalence by
mutual factorization.  A consumer observing one finite tree needs the more
concrete consequence: both images have the same rigid skeleton, and their
remaining variables are related by one finite bijection.

The derivation below records variable pairs in occurrence order.  Repeated
occurrences may repeat an exact pair; the two residual-image equations prove
that no left variable can pair with two right variables and vice versa.
Exact duplicate removal is therefore safe at the later runtime-alpha seam.
-/

mutual

/-- Same rigid tree skeleton with every variable occurrence paired. -/
inductive TreeRenamingDerivation :
    Tree → Tree → List (LogicVar × LogicVar) → Prop where
  | variable (left right : LogicVar) :
      TreeRenamingDerivation (.variable left) (.variable right)
        [(left, right)]
  | node (symbol : RigidSymbol) {left right : List Tree}
      {pairs : List (LogicVar × LogicVar)}
      (children : TreesRenamingDerivation left right pairs) :
      TreeRenamingDerivation (.node symbol left) (.node symbol right) pairs

/-- Ordered child-list companion of `TreeRenamingDerivation`. -/
inductive TreesRenamingDerivation :
    List Tree → List Tree → List (LogicVar × LogicVar) → Prop where
  | nil : TreesRenamingDerivation [] [] []
  | cons {leftHead rightHead : Tree} {leftTail rightTail : List Tree}
      {headPairs tailPairs : List (LogicVar × LogicVar)}
      (head : TreeRenamingDerivation leftHead rightHead headPairs)
      (tail : TreesRenamingDerivation leftTail rightTail tailPairs) :
      TreesRenamingDerivation (leftHead :: leftTail)
        (rightHead :: rightTail) (headPairs ++ tailPairs)

end


mutual

private theorem TreeVariablesSatisfy.weaken
    {first second : LogicVar → Prop}
    (included : ∀ identity, first identity → second identity) :
    ∀ {tree : Tree}, TreeVariablesSatisfy first tree →
      TreeVariablesSatisfy second tree
  | .variable identity, supported => included identity supported
  | .node _ _, supported =>
      TreesVariablesSatisfy.weaken included supported

private theorem TreesVariablesSatisfy.weaken
    {first second : LogicVar → Prop}
    (included : ∀ identity, first identity → second identity) :
    ∀ {trees : List Tree}, TreesVariablesSatisfy first trees →
      TreesVariablesSatisfy second trees
  | [], _ => trivial
  | _ :: _, supported =>
      ⟨TreeVariablesSatisfy.weaken included supported.1,
        TreesVariablesSatisfy.weaken included supported.2⟩

end


mutual

/-- A structural renaming derivation is eliminated by any pointwise map
which realizes every recorded right-to-left variable link. -/
theorem TreeRenamingDerivation.left_eq_rename_right
    {left right : Tree} {pairs : List (LogicVar × LogicVar)}
    (derivation : TreeRenamingDerivation left right pairs)
    (rename : LogicVar → LogicVar)
    (realizes :
      ∀ {leftIdentity rightIdentity},
        (leftIdentity, rightIdentity) ∈ pairs →
          rename rightIdentity = leftIdentity) :
    left = Tree.renameVariables rename right := by
  cases derivation with
  | «variable» leftIdentity rightIdentity =>
      simp only [Tree.renameVariables, Tree.variable.injEq]
      exact (realizes (by simp)).symm
  | node symbol children =>
      simp only [Tree.renameVariables, Tree.node.injEq, true_and]
      exact TreesRenamingDerivation.left_eq_rename_right
        children rename realizes

/-- Ordered child-list companion of
`TreeRenamingDerivation.left_eq_rename_right`. -/
theorem TreesRenamingDerivation.left_eq_rename_right
    {left right : List Tree} {pairs : List (LogicVar × LogicVar)}
    (derivation : TreesRenamingDerivation left right pairs)
    (rename : LogicVar → LogicVar)
    (realizes :
      ∀ {leftIdentity rightIdentity},
        (leftIdentity, rightIdentity) ∈ pairs →
          rename rightIdentity = leftIdentity) :
    left = Trees.renameVariables rename right := by
  cases derivation with
  | nil =>
      rfl
  | @cons leftHead rightHead leftTail rightTail headPairs tailPairs
      head tail =>
      simp only [Trees.renameVariables, List.cons.injEq]
      constructor
      · exact TreeRenamingDerivation.left_eq_rename_right
          head rename fun {_ _} member =>
          realizes (List.mem_append_left _ member)
      · exact TreesRenamingDerivation.left_eq_rename_right
          tail rename fun {_ _} member =>
          realizes (List.mem_append_right _ member)

end


mutual

/-- Every recorded right identity is an actual variable occurrence of the
right tree.  This rules out padding the graph with irrelevant links. -/
theorem TreeRenamingDerivation.right_pair_satisfies
    {left right : Tree} {pairs : List (LogicVar × LogicVar)}
    (derivation : TreeRenamingDerivation left right pairs)
    {predicate : LogicVar → Prop}
    (supported : TreeVariablesSatisfy predicate right)
    {leftIdentity rightIdentity : LogicVar}
    (member : (leftIdentity, rightIdentity) ∈ pairs) :
    predicate rightIdentity := by
  cases derivation with
  | «variable» left right =>
      simp only [List.mem_singleton] at member
      cases member
      exact supported
  | node symbol children =>
      exact TreesRenamingDerivation.right_pair_satisfies
        children supported member

/-- Ordered child-list companion of
`TreeRenamingDerivation.right_pair_satisfies`. -/
theorem TreesRenamingDerivation.right_pair_satisfies
    {left right : List Tree} {pairs : List (LogicVar × LogicVar)}
    (derivation : TreesRenamingDerivation left right pairs)
    {predicate : LogicVar → Prop}
    (supported : TreesVariablesSatisfy predicate right)
    {leftIdentity rightIdentity : LogicVar}
    (member : (leftIdentity, rightIdentity) ∈ pairs) :
    predicate rightIdentity := by
  cases derivation with
  | nil =>
      simp at member
  | @cons leftHead rightHead leftTail rightTail headPairs tailPairs
      head tail =>
      rcases List.mem_append.mp member with headMember | tailMember
      · exact TreeRenamingDerivation.right_pair_satisfies
          head supported.1 headMember
      · exact TreesRenamingDerivation.right_pair_satisfies
          tail supported.2 tailMember

end


mutual

/-- Every right-tree variable is represented by at least one recorded pair.
Together with `right_pair_satisfies`, the graph is exactly the occurrence
support up to duplicate occurrences. -/
theorem TreeRenamingDerivation.right_variables_linked
    {left right : Tree} {pairs : List (LogicVar × LogicVar)}
    (derivation : TreeRenamingDerivation left right pairs) :
    TreeVariablesSatisfy
      (fun rightIdentity =>
        ∃ leftIdentity, (leftIdentity, rightIdentity) ∈ pairs)
      right := by
  cases derivation with
  | «variable» leftIdentity rightIdentity =>
      exact ⟨leftIdentity, by simp⟩
  | node symbol children =>
      exact TreesRenamingDerivation.right_variables_linked children

/-- Ordered child-list companion of
`TreeRenamingDerivation.right_variables_linked`. -/
theorem TreesRenamingDerivation.right_variables_linked
    {left right : List Tree} {pairs : List (LogicVar × LogicVar)}
    (derivation : TreesRenamingDerivation left right pairs) :
    TreesVariablesSatisfy
      (fun rightIdentity =>
        ∃ leftIdentity, (leftIdentity, rightIdentity) ∈ pairs)
      right := by
  cases derivation with
  | nil =>
      trivial
  | @cons leftHead rightHead leftTail rightTail headPairs tailPairs
      head tail =>
      constructor
      · exact TreeVariablesSatisfy.weaken
          (fun rightIdentity witness => by
            rcases witness with ⟨leftIdentity, member⟩
            exact
              ⟨leftIdentity, List.mem_append_left _ member⟩)
          (TreeRenamingDerivation.right_variables_linked head)
      · exact TreesVariablesSatisfy.weaken
          (fun rightIdentity witness => by
            rcases witness with ⟨leftIdentity, member⟩
            exact
              ⟨leftIdentity, List.mem_append_right _ member⟩)
          (TreesRenamingDerivation.right_variables_linked tail)

end

/-- Duplicate removal retains complete right-tree support while discarding
only repeated occurrences of the same structural link. -/
theorem TreeRenamingDerivation.right_variables_in_unique_pairs
    {left right : Tree} {pairs : List (LogicVar × LogicVar)}
    (derivation : TreeRenamingDerivation left right pairs) :
    TreeVariablesSatisfy
      (fun rightIdentity =>
        rightIdentity ∈ pairs.eraseDups.map Prod.snd)
      right := by
  exact TreeVariablesSatisfy.weaken
    (fun rightIdentity witness => by
      rcases witness with ⟨leftIdentity, member⟩
      exact List.mem_map.mpr
        ⟨(leftIdentity, rightIdentity),
          List.mem_eraseDups.mpr member, rfl⟩)
    derivation.right_variables_linked


/-- A structural renaming together with the exact two residual images for
every recorded pair.  These equations are stronger than a naked skeleton:
they exclude `f(X,X)` versus `f(Y,Z)` even though the rigid shapes agree. -/
structure MutualInstanceRenaming
    (forward backward : TreeSubstitution)
    (pairs : List (LogicVar × LogicVar))
    (left right : Tree) : Prop where
  derivation : TreeRenamingDerivation left right pairs
  forwardImages :
    ∀ {leftIdentity rightIdentity},
      (leftIdentity, rightIdentity) ∈ pairs →
      TreeSubstitution.apply forward (.variable rightIdentity) =
        .variable leftIdentity
  backwardImages :
    ∀ {leftIdentity rightIdentity},
      (leftIdentity, rightIdentity) ∈ pairs →
      TreeSubstitution.apply backward (.variable leftIdentity) =
        .variable rightIdentity

/-- A finite tree-renaming graph is functional from left to right. -/
def TreeRenamingForwardFunctional
    (pairs : List (LogicVar × LogicVar)) : Prop :=
  ∀ {left right₁ right₂},
    (left, right₁) ∈ pairs → (left, right₂) ∈ pairs → right₁ = right₂

/-- A finite tree-renaming graph is functional from right to left. -/
def TreeRenamingBackwardFunctional
    (pairs : List (LogicVar × LogicVar)) : Prop :=
  ∀ {left₁ left₂ right},
    (left₁, right) ∈ pairs → (left₂, right) ∈ pairs → left₁ = left₂

/-- The two-sided finite functionality certificate exported to graph
composition. -/
structure SharedTreeRenaming
    (pairs : List (LogicVar × LogicVar)) : Prop where
  forward : TreeRenamingForwardFunctional pairs
  backward : TreeRenamingBackwardFunctional pairs

private theorem renamingPairs_eraseDups_nodup :
    ∀ pairs : List (LogicVar × LogicVar), pairs.eraseDups.Nodup
  | [] => by
      simp
  | head :: tail => by
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · intro member
        rw [List.mem_eraseDups] at member
        simp at member
      · exact renamingPairs_eraseDups_nodup
          (tail.filter (fun pair => !pair == head))
termination_by pairs => pairs.length
decreasing_by
  have lengthBound :=
    List.length_filter_le
      (fun pair : LogicVar × LogicVar => !pair == head) tail
  simp only [List.length_cons]
  omega

namespace SharedTreeRenaming

/-- Exact duplicate removal plus left-to-right functionality makes the left
projection a finite set. -/
theorem eraseDups_fst_nodup
    {pairs : List (LogicVar × LogicVar)}
    (shared : SharedTreeRenaming pairs) :
    (pairs.eraseDups.map Prod.fst).Nodup := by
  apply (renamingPairs_eraseDups_nodup pairs).map_on
  intro first firstMember second secondMember same
  rcases first with ⟨firstLeft, firstRight⟩
  rcases second with ⟨secondLeft, secondRight⟩
  simp only at same
  subst secondLeft
  have rightSame : firstRight = secondRight :=
    shared.forward
      (List.mem_eraseDups.mp firstMember)
      (List.mem_eraseDups.mp secondMember)
  subst secondRight
  rfl

/-- Exact duplicate removal plus right-to-left functionality makes the right
projection a finite set. -/
theorem eraseDups_snd_nodup
    {pairs : List (LogicVar × LogicVar)}
    (shared : SharedTreeRenaming pairs) :
    (pairs.eraseDups.map Prod.snd).Nodup := by
  apply (renamingPairs_eraseDups_nodup pairs).map_on
  intro first firstMember second secondMember same
  rcases first with ⟨firstLeft, firstRight⟩
  rcases second with ⟨secondLeft, secondRight⟩
  simp only at same
  subst secondRight
  have leftSame : firstLeft = secondLeft :=
    shared.backward
      (List.mem_eraseDups.mp firstMember)
      (List.mem_eraseDups.mp secondMember)
  subst secondLeft
  rfl

end SharedTreeRenaming

namespace MutualInstanceRenaming

/-- The residual equations make the occurrence graph functional in both
directions, including across different rigid branches. -/
theorem shared
    {forward backward : TreeSubstitution}
    {pairs : List (LogicVar × LogicVar)} {left right : Tree}
    (witness :
      MutualInstanceRenaming forward backward pairs left right) :
    SharedTreeRenaming pairs := by
  constructor
  · intro leftIdentity right₁ right₂ first second
    have firstImage := witness.backwardImages first
    have secondImage := witness.backwardImages second
    have variableEq :
        Tree.variable right₁ = Tree.variable right₂ :=
      firstImage.symm.trans secondImage
    exact Tree.variable.inj variableEq
  · intro left₁ left₂ rightIdentity first second
    have firstImage := witness.forwardImages first
    have secondImage := witness.forwardImages second
    have variableEq : Tree.variable left₁ = Tree.variable left₂ :=
      firstImage.symm.trans secondImage
    exact Tree.variable.inj variableEq

end MutualInstanceRenaming

mutual

/-- Two mutually instantiated finite trees admit one explicit structural
renaming whose links retain both residual image equations. -/
theorem Tree.exists_mutualInstanceRenaming
    (forward backward : TreeSubstitution) :
    (left right : Tree) →
      left = TreeSubstitution.apply forward right →
      right = TreeSubstitution.apply backward left →
      ∃ pairs,
        MutualInstanceRenaming forward backward pairs left right
  | .variable leftIdentity, .variable rightIdentity,
      leftEq, rightEq => by
      refine
        ⟨[(leftIdentity, rightIdentity)],
          { derivation := .variable leftIdentity rightIdentity
            forwardImages := ?_
            backwardImages := ?_ }⟩
      · intro candidateLeft candidateRight member
        simp only [List.mem_singleton] at member
        cases member
        exact leftEq.symm
      · intro candidateLeft candidateRight member
        simp only [List.mem_singleton] at member
        cases member
        exact rightEq.symm
  | .variable leftIdentity, .node symbol children,
      leftEq, _rightEq => by
      simp only [TreeSubstitution.apply_node] at leftEq
      cases leftEq
  | .node symbol children, .variable rightIdentity,
      _leftEq, rightEq => by
      simp only [TreeSubstitution.apply_node] at rightEq
      cases rightEq
  | .node leftSymbol leftChildren, .node rightSymbol rightChildren,
      leftEq, rightEq => by
      simp only [TreeSubstitution.apply_node, Tree.node.injEq] at leftEq rightEq
      have symbols : leftSymbol = rightSymbol := leftEq.1
      subst rightSymbol
      obtain
        ⟨pairs, childrenDerivation, childrenForward, childrenBackward⟩ :=
        Trees.exists_mutualInstanceRenaming forward backward
          leftChildren rightChildren leftEq.2 rightEq.2
      exact
        ⟨pairs,
          { derivation := .node leftSymbol childrenDerivation
            forwardImages := childrenForward
            backwardImages := childrenBackward }⟩

/-- Ordered child-list companion of
`Tree.exists_mutualInstanceRenaming`. -/
theorem Trees.exists_mutualInstanceRenaming
    (forward backward : TreeSubstitution) :
    (left right : List Tree) →
      left = TreeSubstitution.applyTrees forward right →
      right = TreeSubstitution.applyTrees backward left →
      ∃ pairs,
        (∃ _derivation : TreesRenamingDerivation left right pairs,
          (∀ {leftIdentity rightIdentity},
            (leftIdentity, rightIdentity) ∈ pairs →
            TreeSubstitution.apply forward (.variable rightIdentity) =
              .variable leftIdentity) ∧
          ∀ {leftIdentity rightIdentity},
            (leftIdentity, rightIdentity) ∈ pairs →
            TreeSubstitution.apply backward (.variable leftIdentity) =
              .variable rightIdentity)
  | [], [], _leftEq, _rightEq => by
      exact ⟨[], .nil, by simp, by simp⟩
  | [], rightHead :: rightTail, leftEq, _rightEq => by
      simp only [TreeSubstitution.applyTrees_cons] at leftEq
      cases leftEq
  | leftHead :: leftTail, [], _leftEq, rightEq => by
      simp only [TreeSubstitution.applyTrees_cons] at rightEq
      cases rightEq
  | leftHead :: leftTail, rightHead :: rightTail,
      leftEq, rightEq => by
      simp only [TreeSubstitution.applyTrees_cons, List.cons.injEq] at leftEq rightEq
      obtain ⟨headPairs, head⟩ :=
        Tree.exists_mutualInstanceRenaming forward backward
          leftHead rightHead leftEq.1 rightEq.1
      obtain ⟨tailPairs, tailDerivation, tailForward, tailBackward⟩ :=
        Trees.exists_mutualInstanceRenaming forward backward
          leftTail rightTail leftEq.2 rightEq.2
      refine
        ⟨headPairs ++ tailPairs,
          .cons head.derivation tailDerivation, ?_, ?_⟩
      · intro leftIdentity rightIdentity member
        rcases List.mem_append.mp member with headMember | tailMember
        · exact head.forwardImages headMember
        · exact tailForward tailMember
      · intro leftIdentity rightIdentity member
        rcases List.mem_append.mp member with headMember | tailMember
        · exact head.backwardImages headMember
        · exact tailBackward tailMember

end

namespace TreeSubstitutionVariants

/-- Specializing semantic residual variants to one observed finite tree
produces a structural variable-renaming witness.  Neither idempotence nor a
particular MGU association-list orientation is assumed. -/
theorem apply_has_mutualInstanceRenaming
    {first second : TreeSubstitution}
    (variants : TreeSubstitutionVariants first second)
    (tree : Tree) :
    ∃ forward backward pairs,
      MutualInstanceRenaming forward backward pairs
        (TreeSubstitution.apply first tree)
        (TreeSubstitution.apply second tree) := by
  rcases variants.1 with ⟨forward, firstFactors⟩
  rcases variants.2 with ⟨backward, secondFactors⟩
  obtain ⟨pairs, witness⟩ :=
    Tree.exists_mutualInstanceRenaming forward backward
      (TreeSubstitution.apply first tree)
      (TreeSubstitution.apply second tree)
      (firstFactors tree) (secondFactors tree)
  exact ⟨forward, backward, pairs, witness⟩

/-- A residual variant of a variable image is itself a variable image.

This is a structural consequence of mutual instantiation, not a choice of
association-list orientation.  It is the stable interface for later
sequential-MGU proofs: a selected representative may rename an unresolved
variable, but it cannot silently ground it or replace it by a rigid tree. -/
theorem apply_variable_exists_of_first
    {first second : TreeSubstitution}
    (variants : TreeSubstitutionVariants first second)
    (tree : Tree) {source : LogicVar}
    (firstExact :
      TreeSubstitution.apply first tree = .variable source) :
    ∃ target,
      TreeSubstitution.apply second tree = .variable target := by
  obtain ⟨forward, backward, pairs, witness⟩ :=
    PLeaTTa.PrologMguVariantRenaming.TreeSubstitutionVariants.apply_has_mutualInstanceRenaming
      variants tree
  generalize secondExact :
      TreeSubstitution.apply second tree = secondImage at witness
  rw [firstExact] at witness
  cases witness.derivation with
  | «variable» leftIdentity rightIdentity =>
      exact ⟨rightIdentity, rfl⟩

end TreeSubstitutionVariants

/-! ## Anti-vacuity: both factorization directions are load-bearing -/

private def splitLeft : LogicVar := .source "$variant_left"
private def splitRight₁ : LogicVar := .source "$variant_right_1"
private def splitRight₂ : LogicVar := .source "$variant_right_2"

private def repeatedLeftTree : Tree :=
  .node (.compound "f")
    [.variable splitLeft, .variable splitLeft]

private def splitRightTree : Tree :=
  .node (.compound "f")
    [.variable splitRight₁, .variable splitRight₂]

private def collapseSplitRight : TreeSubstitution :=
  [(splitRight₁, .variable splitLeft),
   (splitRight₂, .variable splitLeft)]

/-- One instance direction alone can collapse two distinct variables into
one repeated variable. -/
theorem split_sharing_has_forward_instance :
    repeatedLeftTree =
      TreeSubstitution.apply collapseSplitRight splitRightTree := by
  simp [repeatedLeftTree, splitRightTree, collapseSplitRight,
    TreeSubstitution.applyTrees, Tree.instantiateOne,
    Trees.instantiateOne, splitLeft,
    splitRight₁, splitRight₂]

/-- No finite substitution can reverse that sharing collapse: two
occurrences of one variable always receive the same image. -/
theorem split_sharing_has_no_backward_instance :
    ¬ ∃ backward : TreeSubstitution,
      splitRightTree =
        TreeSubstitution.apply backward repeatedLeftTree := by
  rintro ⟨backward, equality⟩
  simp only [repeatedLeftTree, splitRightTree,
    TreeSubstitution.apply_node, Tree.node.injEq, true_and,
    TreeSubstitution.applyTrees_cons, TreeSubstitution.applyTrees_nil,
    List.cons.injEq] at equality
  have same :
      Tree.variable splitRight₁ = Tree.variable splitRight₂ :=
    equality.1.trans equality.2.1.symm
  have impossible : splitRight₁ = splitRight₂ := Tree.variable.inj same
  simp [splitRight₁, splitRight₂] at impossible

end PLeaTTa.PrologMguVariantRenaming
