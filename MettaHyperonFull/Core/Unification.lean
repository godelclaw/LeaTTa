-- SPDX-FileCopyrightText: 2026 MesTTo
-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Core.Unification
Layer: Core
Purpose: First-order syntactic unification of atoms, returning a most-general unifier when one exists.
  Each equation is decomposed structurally into variable constraints (a head clash or arity mismatch
  fails), then the main loop eliminates one variable per round under an occurs-check. The loop is
  fuel-bounded by the total term size, an upper bound on the number of distinct variables, so the
  function is total. Grounded atoms with custom matching are handled in Matching.lean.
Imports: MettaHyperonFull.Core.Substitution
Trusted boundary: none
Main exports: Unify.decomposeEqWith, Unify.decomposeListWith,
  Unify.decomposeAllWith, Unify.unifyRoundsWith, Unify.unifyTopWith,
  Unify.decomposeEq, Unify.decomposeList, Unify.decomposeAll,
  Unify.unifyRounds, Unify.unifyTop
Open obligations: none
-/
import MettaHyperonFull.Core.Substitution

namespace Metta

namespace Unify

mutual

/-- Comparator-parametric structural decomposition of a single equation.
The ground comparator is consulted at every recursive leaf, including leaves
exposed only after a previous unification round substitutes a variable. -/
def decomposeEqWith (groundEq : Ground → Ground → Bool) :
    Atom → Atom → Option (List (VarName × Atom))
  | Atom.var x, Atom.var y => if x == y then some [] else some [(x, Atom.var y)]
  | Atom.var x, t => some [(x, t)]
  | t, Atom.var x => some [(x, t)]
  | Atom.sym a, Atom.sym b => if a == b then some [] else none
  | Atom.gnd a, Atom.gnd b => if groundEq a b then some [] else none
  | Atom.expr xs, Atom.expr ys => decomposeListWith groundEq xs ys
  | _, _ => none

/-- Pointwise comparator-parametric companion to `decomposeEqWith`. -/
def decomposeListWith (groundEq : Ground → Ground → Bool) :
    List Atom → List Atom → Option (List (VarName × Atom))
  | [], [] => some []
  | x :: xs, y :: ys =>
      match decomposeEqWith groundEq x y,
          decomposeListWith groundEq xs ys with
      | some c₁, some c₂ => some (c₁ ++ c₂)
      | _, _ => none
  | _, _ => none

end

mutual
/-- Structurally decompose a single equation using Hyperon's ordinary ground
equivalence.  Its equations remain explicit because the metatheory relies on
their definitional reduction; `decomposeEqWith` is the comparator-parametric
counterpart used by dialects with a different ground identity. -/
def decomposeEq : Atom → Atom → Option (List (VarName × Atom))
  | Atom.var x, Atom.var y => if x == y then some [] else some [(x, Atom.var y)]
  | Atom.var x, t => some [(x, t)]
  | t, Atom.var x => some [(x, t)]
  | Atom.sym a, Atom.sym b => if a == b then some [] else none
  | Atom.gnd a, Atom.gnd b => if Ground.equiv a b then some [] else none
  | Atom.expr xs, Atom.expr ys => decomposeList xs ys
  | _, _ => none

def decomposeList : List Atom → List Atom → Option (List (VarName × Atom))
  | [], [] => some []
  | x :: xs, y :: ys =>
      match decomposeEq x y, decomposeList xs ys with
      | some c₁, some c₂ => some (c₁ ++ c₂)
      | _, _ => none
  | _, _ => none
end

/-- Comparator-parametric decomposition of every equation in a worklist. -/
def decomposeAllWith (groundEq : Ground → Ground → Bool) :
    List (Atom × Atom) → Option (List (VarName × Atom))
  | [] => some []
  | (a, b) :: rest =>
      match decomposeEqWith groundEq a b, decomposeAllWith groundEq rest with
      | some c₁, some c₂ => some (c₁ ++ c₂)
      | _, _ => none

/-- Hyperon's ordinary worklist decomposition, kept definitionally stable for
the existing metatheory. -/
def decomposeAll : List (Atom × Atom) → Option (List (VarName × Atom))
  | [] => some []
  | (a, b) :: rest =>
      match decomposeEq a b, decomposeAll rest with
      | some c₁, some c₂ => some (c₁ ++ c₂)
      | _, _ => none

/-- The unification main loop, recursing structurally on `fuel`. Each round fully decomposes the
    worklist, then eliminates one variable: it substitutes `x ↦ t` into the remaining constraints
    and records the binding. Because every round removes one distinct variable from the problem,
    the number of rounds is bounded by the number of distinct variables, so `unifyTop` supplies a
    `fuel` (the total term size) that exceeds that bound; if the `fuel = 0` clause is reached with
    constraints still pending, it returns `none`. -/
def unifyRoundsWith (groundEq : Ground → Ground → Bool) :
    Nat → List (Atom × Atom) → Subst → Option Subst
  | 0, eqs, s =>
      match decomposeAllWith groundEq eqs with
      | none => none
      | some [] => some s
      | some (_ :: _) => none
  | fuel + 1, eqs, s =>
      match decomposeAllWith groundEq eqs with
      | none => none
      | some [] => some s
      | some ((x, t) :: rest) =>
          if Subst.occurs x t then none
          else
            let sub : Subst := [(x, t)]
            let rest' := rest.map fun p => (Subst.apply sub (Atom.var p.1), Subst.apply sub p.2)
            unifyRoundsWith groundEq fuel rest' (Subst.extend s x t)

/-- Hyperon's ordinary unification loop, definitionally stable for its
existing proof layer. -/
def unifyRounds : Nat → List (Atom × Atom) → Subst → Option Subst
  | 0, eqs, s =>
      match decomposeAll eqs with
      | none => none
      | some [] => some s
      | some (_ :: _) => none
  | fuel + 1, eqs, s =>
      match decomposeAll eqs with
      | none => none
      | some [] => some s
      | some ((x, t) :: rest) =>
          if Subst.occurs x t then none
          else
            let sub : Subst := [(x, t)]
            let rest' := rest.map fun p =>
              (Subst.apply sub (Atom.var p.1), Subst.apply sub p.2)
            unifyRounds fuel rest' (Subst.extend s x t)

/-- First-order syntactic unification of two atoms, returning a most-general unifier when one
    exists. Grounded atoms with custom matching are handled by `Matching.lean`, since the spec
    allows custom ground matchers. Total: decomposition is structural and elimination is bounded by
    the term size (an upper bound on the number of distinct variables). -/
def unifyTopWith (groundEq : Ground → Ground → Bool) (a b : Atom) :
    Option Subst :=
  unifyRoundsWith groundEq (Atom.size a + Atom.size b) [(a, b)] []

/-- Hyperon's ordinary top-level unifier. -/
def unifyTop (a b : Atom) : Option Subst :=
  unifyRounds (Atom.size a + Atom.size b) [(a, b)] []

/-! The legacy Hyperon entry points retain their definitional equations for
the existing metatheory.  These equations pin them extensionally to the new
comparator-parametric core, preventing the two presentations from drifting. -/

mutual

theorem decomposeEqWith_groundEquiv :
    ∀ left right,
      decomposeEqWith Ground.equiv left right = decomposeEq left right
  | .var _, .var _ => rfl
  | .var _, .sym _ => rfl
  | .var _, .gnd _ => rfl
  | .var _, .expr _ => rfl
  | .sym _, .var _ => rfl
  | .sym _, .sym _ => rfl
  | .sym _, .gnd _ => rfl
  | .sym _, .expr _ => rfl
  | .gnd _, .var _ => rfl
  | .gnd _, .sym _ => rfl
  | .gnd _, .gnd _ => rfl
  | .gnd _, .expr _ => rfl
  | .expr _, .var _ => rfl
  | .expr _, .sym _ => rfl
  | .expr _, .gnd _ => rfl
  | .expr left, .expr right =>
      decomposeListWith_groundEquiv left right

theorem decomposeListWith_groundEquiv :
    ∀ left right,
      decomposeListWith Ground.equiv left right = decomposeList left right
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | left :: lefts, right :: rights => by
      simp only [decomposeListWith, decomposeList]
      rw [decomposeEqWith_groundEquiv left right,
        decomposeListWith_groundEquiv lefts rights]

end

theorem decomposeAllWith_groundEquiv (equations) :
    decomposeAllWith Ground.equiv equations = decomposeAll equations := by
  induction equations with
  | nil => rfl
  | cons equation rest induction =>
      rcases equation with ⟨left, right⟩
      simp only [decomposeAllWith, decomposeAll]
      rw [decomposeEqWith_groundEquiv left right, induction]

theorem unifyRoundsWith_groundEquiv :
    ∀ fuel equations generated,
      unifyRoundsWith Ground.equiv fuel equations generated =
        unifyRounds fuel equations generated
  | 0, equations, generated => by
      simp only [unifyRoundsWith, unifyRounds]
      rw [decomposeAllWith_groundEquiv]
  | fuel + 1, equations, generated => by
      simp only [unifyRoundsWith, unifyRounds]
      rw [decomposeAllWith_groundEquiv]
      cases decomposed : decomposeAll equations with
      | none => rfl
      | some constraints =>
          cases constraints with
          | nil => rfl
          | cons constraint rest =>
              rcases constraint with ⟨name, target⟩
              by_cases occurs : Subst.occurs name target = true
              · simp [occurs]
              · have occursFalse : Subst.occurs name target = false := by
                  cases value : Subst.occurs name target with
                  | false => rfl
                  | true => exact False.elim (occurs value)
                simp only [occursFalse, Bool.false_eq_true, if_false]
                exact unifyRoundsWith_groundEquiv fuel
                  (rest.map fun pair =>
                    (Subst.apply [(name, target)] (Atom.var pair.1),
                      Subst.apply [(name, target)] pair.2))
                  (Subst.extend generated name target)

theorem unifyTopWith_groundEquiv (left right : Atom) :
    unifyTopWith Ground.equiv left right = unifyTop left right := by
  unfold unifyTopWith unifyTop
  exact unifyRoundsWith_groundEquiv _ _ _

end Unify

end Metta
