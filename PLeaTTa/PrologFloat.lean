-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.PrologFloat
Purpose: Exact SWI-Prolog float term identity, separate from IEEE arithmetic
  equality.
Trusted boundary: none
Main exports: PrologFloatIdentity, PrologFloatIdentity.ofFloat,
  prologGroundIdentical
-/
import MettaHyperonFull.Core.Atom

namespace PLeaTTa

/-- Identity of a float as an SWI-Prolog term.  SWI has one NaN term even
though IEEE 754 admits payload and sign variants.  Every other float is
identified by its exact bits, so `0.0` and `-0.0` remain distinct terms.

This is term identity for unification and `==/2`, not arithmetic equality:
arithmetic continues to use IEEE comparison and therefore rejects NaN
reflexivity. -/
inductive PrologFloatIdentity where
  | nan
  | bits (value : UInt64)
deriving Repr, Inhabited, DecidableEq

/-- Canonical float identities use decidable propositional equality rather
than runtime IEEE equality. -/
instance : BEq PrologFloatIdentity where
  beq left right := decide (left = right)

/-- Project one runtime float into exact SWI-Prolog term identity. -/
def PrologFloatIdentity.ofFloat (value : Float) : PrologFloatIdentity :=
  if value.isNaN then .nan else .bits value.toBits

/-- Boolean equality of canonical float identities agrees with
propositional equality.  This is stated explicitly because runtime `Float`
equality is not lawful on NaN, even though this canonical key is. -/
theorem PrologFloatIdentity.beq_eq_true_iff
    (left right : PrologFloatIdentity) :
    (left == right) = true ↔ left = right := by
  simp [BEq.beq]

/-- The explicit Prolog key has reflexive decidable equality even when the
runtime IEEE value used to construct it is NaN. -/
@[simp] theorem PrologFloatIdentity.beq_self :
    ∀ identity : PrologFloatIdentity, (identity == identity) = true
  | identity => PrologFloatIdentity.beq_eq_true_iff identity identity |>.2 rfl

/-- Exact identity of grounded values after they cross into PeTTa's Prolog
dialect.  Unlike Hyperon's `Ground.equiv`, this never coerces an integer to a
float.  Float identity is the canonical SWI key above: all NaNs coincide,
while signed zeroes remain distinct. -/
def prologGroundIdentical : Metta.Ground → Metta.Ground → Bool
  | .int left, .int right => left == right
  | .float left, .float right =>
      PrologFloatIdentity.ofFloat left == PrologFloatIdentity.ofFloat right
  | .str left, .str right => left == right
  | .bool left, .bool right => left == right
  | .unit, .unit => true
  | .error left, .error right => left == right
  | .external leftTag leftPayload, .external rightTag rightPayload =>
      leftTag == rightTag && leftPayload == rightPayload
  | _, _ => false

/-- Canonical identity key for one runtime ground at the SWI-Prolog term
boundary.  In particular, the key keeps integer and float constructors
separate while identifying every IEEE NaN payload with the single Prolog
`nan` identity. -/
inductive PrologGroundIdentity where
  | integer (value : Int)
  | floating (value : PrologFloatIdentity)
  | string (value : String)
  | boolean (value : Bool)
  | unit
  | error (value : String)
  | external (tag payload : String)
deriving Repr, DecidableEq

/-- Project a runtime ground into its exact SWI-Prolog term-identity key. -/
def PrologGroundIdentity.ofGround : Metta.Ground → PrologGroundIdentity
  | .int value => .integer value
  | .float value => .floating (.ofFloat value)
  | .str value => .string value
  | .bool value => .boolean value
  | .unit => .unit
  | .error value => .error value
  | .external tag payload => .external tag payload

/-- The executable comparator is exactly equality of the canonical Prolog
ground keys.  This formulation exposes the equivalence relation used by the
comparator without pretending that distinct IEEE NaN payloads are equal as
Lean `Float` values. -/
theorem prologGroundIdentical_eq_true_iff (left right : Metta.Ground) :
    prologGroundIdentical left right = true ↔
      PrologGroundIdentity.ofGround left =
        PrologGroundIdentity.ofGround right := by
  cases left <;> cases right <;>
    simp [prologGroundIdentical, PrologGroundIdentity.ofGround, beq_iff_eq]

/-- Prolog term identity is reflexive for every executable ground payload,
including NaN. -/
@[simp] theorem prologGroundIdentical_self :
    ∀ ground : Metta.Ground,
      prologGroundIdentical ground ground = true
  | .int value => by simp [prologGroundIdentical]
  | .float value => by
      simp [prologGroundIdentical]
  | .str value => by simp [prologGroundIdentical]
  | .bool value => by simp [prologGroundIdentical]
  | .unit => rfl
  | .error value => by simp [prologGroundIdentical]
  | .external tag payload => by simp [prologGroundIdentical]

/-- Exact Prolog ground identity is symmetric. -/
theorem prologGroundIdentical_symm {left right : Metta.Ground}
    (identical : prologGroundIdentical left right = true) :
    prologGroundIdentical right left = true := by
  rw [prologGroundIdentical_eq_true_iff] at identical ⊢
  exact identical.symm

/-- Exact Prolog ground identity is transitive. -/
theorem prologGroundIdentical_trans {first second third : Metta.Ground}
    (firstSecond : prologGroundIdentical first second = true)
    (secondThird : prologGroundIdentical second third = true) :
    prologGroundIdentical first third = true := by
  rw [prologGroundIdentical_eq_true_iff] at firstSecond secondThird ⊢
  exact firstSecond.trans secondThird

end PLeaTTa
