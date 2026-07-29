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
deriving Repr, Inhabited, DecidableEq, BEq

/-- Project one runtime float into exact SWI-Prolog term identity. -/
def PrologFloatIdentity.ofFloat (value : Float) : PrologFloatIdentity :=
  if value.isNaN then .nan else .bits value.toBits

/-- The explicit Prolog key has reflexive decidable equality even when the
runtime IEEE value used to construct it is NaN. -/
@[simp] theorem PrologFloatIdentity.beq_self :
    ∀ identity : PrologFloatIdentity, (identity == identity) = true
  | .nan => rfl
  | .bits value => by exact beq_self_eq_true value

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

/-- Prolog term identity is reflexive for every executable ground payload,
including NaN. -/
@[simp] theorem prologGroundIdentical_self :
    ∀ ground : Metta.Ground,
      prologGroundIdentical ground ground = true
  | .int value => by simp [prologGroundIdentical]
  | .float value => by
      simp [prologGroundIdentical, PrologFloatIdentity.beq_self]
  | .str value => by simp [prologGroundIdentical]
  | .bool value => by simp [prologGroundIdentical]
  | .unit => rfl
  | .error value => by simp [prologGroundIdentical]
  | .external tag payload => by simp [prologGroundIdentical]

end PLeaTTa
