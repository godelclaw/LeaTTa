-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.GroundModel
Layer: Proofs
Purpose: The engine's own DECLARATIVE ground semantics (Track 3, T3.1): a
  least-fixpoint model `leastModelP` over the equality-rule reduction, mirroring
  the logic-programming least-Herbrand model (Tarski's lfp of an
  immediate-consequence operator) but SELF-CONTAINED — it imports only the
  executable core, never the Mettapedia LP tree (the dependency arrow). The
  executable reducer gains nothing; this is proof-layer material (the zero-bog
  rule). `leastModelP` is the object the coincidence theorem (T3.2) relates to
  operational reduction, and the object the math-side SLD-agreement theorem
  (T3.3b) will vendor and pin.
Imports: MettaHyperonFull.Operational.Semantics, Mathlib.Order.FixedPoints
Trusted boundary: human-reviewed spec (the model definition); its lattice
  properties are fully proved via Mathlib's lfp API.
Main exports: TPeq, TPeqMono, leastModelP, leastModelP_fixpoint,
  leastModelP_least, TPeq_le_leastModelP
Open obligations: the coincidence theorem (T3.2) and ground-instantiation
  soundness (T3.3a) live in sibling Proofs modules.
-/
import MettaHyperonFull.Operational.Semantics
import Mathlib.Order.FixedPoints

namespace Metta

/-- One ground reduction step: `r` is an equality-rule reduct of `a`. This is
the pure rule-application core (the definite-clause fragment); grounded
operators are extensional facts, an orthogonal extension point. -/
def StepR (kb : Space) (a r : Atom) : Prop := r ∈ equalityReductions kb a

/-- Immediate-consequence operator on the set of `(input, value)` pairs. A pair
enters either because `a` is irreducible and is its own value (a normal-form
fact), or because some one-step reduct `r` of `a` already reaches the value.
Monotone in the interpretation `I`, so Tarski gives a least fixpoint. -/
def TPeq (kb : Space) (I : Set (Atom × Atom)) : Set (Atom × Atom) :=
  { p | (equalityReductions kb p.1 = [] ∧ p.1 = p.2)
        ∨ (∃ r, StepR kb p.1 r ∧ (r, p.2) ∈ I) }

theorem TPeqMono (kb : Space) : Monotone (TPeq kb) := by
  intro I J hIJ p hp
  rcases hp with hfact | ⟨r, hstep, hmem⟩
  · exact Or.inl hfact
  · exact Or.inr ⟨r, hstep, hIJ hmem⟩

/-- The operator as a bundled `OrderHom`, for Mathlib's `lfp`. -/
def TPeqHom (kb : Space) : Set (Atom × Atom) →o Set (Atom × Atom) :=
  ⟨TPeq kb, TPeqMono kb⟩

/-- **The engine's least model** (Tarski's lfp of the immediate-consequence
operator) — the declarative, logic-programming reading of the ground rewriting
semantics, self-contained in the engine repo. -/
def leastModelP (kb : Space) : Set (Atom × Atom) := OrderHom.lfp (TPeqHom kb)

/-- `leastModelP` is a fixpoint of the immediate-consequence operator. -/
theorem leastModelP_fixpoint (kb : Space) :
    TPeq kb (leastModelP kb) = leastModelP kb :=
  OrderHom.map_lfp (TPeqHom kb)

/-- `leastModelP` is the LEAST pre-fixpoint: any interpretation closed under the
operator contains it (the "least" in least model). -/
theorem leastModelP_least (kb : Space) (I : Set (Atom × Atom))
    (hI : TPeq kb I ⊆ I) : leastModelP kb ⊆ I :=
  OrderHom.lfp_le (TPeqHom kb) hI

/-- One unfolding: the operator applied to the model lands in the model. -/
theorem TPeq_le_leastModelP (kb : Space) :
    TPeq kb (leastModelP kb) ⊆ leastModelP kb :=
  (leastModelP_fixpoint kb).le

/-- Normal forms are their own values in the model (the reflexive facts). -/
theorem leastModelP_nf (kb : Space) (a : Atom)
    (h : equalityReductions kb a = []) : (a, a) ∈ leastModelP kb := by
  rw [← leastModelP_fixpoint]
  exact Or.inl ⟨h, rfl⟩

/-- One-step lift: if `a` reduces to `r` and `r` reaches `v` in the model, then
`a` reaches `v` in the model (the clause-firing facts). -/
theorem leastModelP_step (kb : Space) {a r v : Atom}
    (hstep : StepR kb a r) (hrv : (r, v) ∈ leastModelP kb) :
    (a, v) ∈ leastModelP kb := by
  rw [← leastModelP_fixpoint]
  exact Or.inr ⟨r, hstep, hrv⟩

end Metta
