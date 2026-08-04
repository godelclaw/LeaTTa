-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologRetractOpenFactorRegression
Purpose: Force the retract open-factor bridge to preserve a residual alias
  after one independent value binding inside private reserved syntax.
Trusted boundary: none
[SPEC metta.pl:279-280]
-/
import PLeaTTa.Proofs.PrologRetractOpenFactor

namespace PLeaTTa.PrologRetractOpenFactorRegression

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PrologMguBridge
open PrologMguExecutableOpenFactor
open PrologPrefilterBridge
open PrologRetractEncodingBridge
open PrologRetractOpenFactor
open PrologStateBridge

private def queryX : LogicVar := .source "query-x"
private def queryY : LogicVar := .source "query-y"
private def clauseZ : LogicVar := .generated 4

private def alpha : List (LogicVar × String) :=
  [(queryX, "qx"), (queryY, "qy"), (clauseZ, "cz")]

private def leftTree : Tree :=
  .node (.compound "$goal.unify")
    [.variable queryX, .variable queryY]

private def rightTree : Tree :=
  .node (.compound "$goal.unify")
    [.node (.atom "a") [], .variable clauseZ]

private def leftAtom : Atom :=
  reservedSyntaxC "$goal.unify"
    (chainOf [.var "qx", .var "qy"])

private def rightAtom : Atom :=
  reservedSyntaxC "$goal.unify"
    (chainOf [.sym "a", .var "cz"])

private def canonical : TreeSubstitution :=
  [(queryY, .variable clauseZ),
    (queryX, .node (.atom "a") [])]

private theorem shared : SharedRuntimeAlpha alpha := by
  constructor
  · intro identity left right leftMember rightMember
    simp [alpha, queryX, queryY, clauseZ] at leftMember rightMember
    rcases leftMember with leftMember | leftMember | leftMember <;>
      rcases rightMember with rightMember | rightMember | rightMember <;>
      simp_all
  · intro left right name leftMember rightMember
    simp [alpha, queryX, queryY, clauseZ] at leftMember rightMember
    rcases leftMember with leftMember | leftMember | leftMember <;>
      rcases rightMember with rightMember | rightMember | rightMember <;>
      simp_all

private theorem leftAgreement :
    RetractSyntaxRuntimeAgrees alpha leftTree leftAtom := by
  exact .goalUnify
    (.variable (by simp [alpha]))
    (.variable (by simp [alpha]))

private theorem rightAgreement :
    RetractSyntaxRuntimeAgrees alpha rightTree rightAtom := by
  exact .goalUnify
    (.atom (by decide) (by decide))
    (.variable (by simp [alpha]))

private theorem canonicalDerivation :
    OrderedTreeMgu [(leftTree, rightTree)] canonical := by
  apply OrderedTreeMgu.cons leftTree rightTree [] canonical []
  · unfold leftTree rightTree canonical
    apply TreeMgu.node (.compound "$goal.unify")
      [.variable queryX, .variable queryY]
      [.node (.atom "a") [], .variable clauseZ]
    · simp
    · apply TreesMgu.cons
        (.variable queryX) (.node (.atom "a") [])
        [.variable queryY] [.variable clauseZ]
        [(queryX, .node (.atom "a") [])]
        [(queryY, .variable clauseZ)]
      · exact .bindLeft queryX (.node (.atom "a") [])
          (by simp) (by simp [Tree.occurs, Trees.occurs])
      · simpa [TreeSubstitution.applyTrees,
          Tree.instantiateOne, Trees.instantiateOne,
          queryX, queryY, clauseZ] using
          (TreesMgu.cons
            (.variable queryY) (.variable clauseZ) [] []
            [(queryY, .variable clauseZ)] []
            (TreeMgu.bindLeft queryY (.variable clauseZ)
              (by simp [queryY, clauseZ])
              (by simp [Tree.occurs, queryY, clauseZ]))
            TreesMgu.nil)
  · exact .nil

private theorem actualResult :
    PLeaTTa.unifyTopExact leftAtom rightAtom =
      some [("qy", .var "cz"), ("qx", .sym "a")] := by
  have decomposed0 :
      Metta.Unify.decomposeAllWith PLeaTTa.prologGroundIdentical
          [(leftAtom, rightAtom)] =
        some [("qx", .sym "a"), ("qy", .var "cz")] := by
    rfl
  unfold PLeaTTa.unifyTopExact Metta.Unify.unifyTopWith
  have fuelEq : leftAtom.size + rightAtom.size = 20 := by
    simp [leftAtom, rightAtom, reservedSyntaxC, reservedSyntaxTagA,
      chainOf, consC, nilA, Atom.size]
  rw [fuelEq]
  change
    Metta.Unify.unifyRoundsWith PLeaTTa.prologGroundIdentical 20
        [(leftAtom, rightAtom)] [] =
      some [("qy", .var "cz"), ("qx", .sym "a")]
  rw [Metta.Unify.unifyRoundsWith, decomposed0]
  simp only [Metta.Subst.occurs, Bool.false_eq_true, ↓reduceIte,
    List.map, Metta.Subst.apply, Metta.Subst.lookup, Option.getD,
    Metta.Subst.extend, Metta.Subst.erase, List.filter]
  change
    Metta.Unify.unifyRoundsWith PLeaTTa.prologGroundIdentical 19
        [(.var "qy", .var "cz")] [("qx", .sym "a")] =
      some [("qy", .var "cz"), ("qx", .sym "a")]
  have decomposed1 :
      Metta.Unify.decomposeAllWith PLeaTTa.prologGroundIdentical
          [(.var "qy", .var "cz")] =
        some [("qy", .var "cz")] := by
    rfl
  rw [Metta.Unify.unifyRoundsWith, decomposed1]
  have occurs1 : Metta.Subst.occurs "qy" (.var "cz") = false := by
    simp [Metta.Subst.occurs]
  change
    (if Metta.Subst.occurs "qy" (.var "cz") = true then none
      else
        Metta.Unify.unifyRoundsWith PLeaTTa.prologGroundIdentical 18 []
          (Metta.Subst.extend [("qx", .sym "a")] "qy" (.var "cz"))) =
      some [("qy", .var "cz"), ("qx", .sym "a")]
  rw [occurs1]
  change
    Metta.Unify.unifyRoundsWith PLeaTTa.prologGroundIdentical 18 []
        [("qy", .var "cz"), ("qx", .sym "a")] =
      some [("qy", .var "cz"), ("qx", .sym "a")]
  rfl

/-- The concrete reserved-syntax run binds `queryX` to `a` while retaining
the independent `queryY`/clause-variable alias as the live runtime variable
`cz`.  The open-factor theorem therefore cannot be satisfied by a grounded
representative. -/
theorem selected_binding_and_residual_alias_are_both_preserved :
    OpenAlphaResultFactors alpha canonical
        [("qy", .var "cz"), ("qx", .sym "a")] ∧
      PLeaTTa.subst
          [("qy", .var "cz"), ("qx", .sym "a")]
          (.var "qx") = .sym "a" ∧
      PLeaTTa.subst
          [("qy", .var "cz"), ("qx", .sym "a")]
          (.var "qy") = .var "cz" ∧
      PLeaTTa.subst
          [("qy", .var "cz"), ("qx", .sym "a")]
          (.var "cz") = .var "cz" := by
  refine ⟨?_, ?_, ?_, ?_⟩
  exact unifyTopExact_open_factor_of_ordered_retract
    shared leftAgreement rightAgreement canonicalDerivation actualResult
  all_goals simp [PLeaTTa.subst, PLeaTTa.substN, Metta.Subst.lookup]

end PLeaTTa.PrologRetractOpenFactorRegression
