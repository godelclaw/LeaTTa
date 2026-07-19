-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.Coincidence
Layer: Proofs
Purpose: **The coincidence theorem** (Track 3, T3.2): the engine's operational
  equality-rule reduction and its declarative least-fixpoint model
  (`leastModelP`) are the SAME semantics. Concretely, `(a, v) ∈ leastModelP kb`
  iff `v` is a normal form reachable from `a` by ground reduction steps. This is
  the van Emden–Kowalski / Henkin result — the operational reduction *computes*
  the declarative least model — mirrored for the PeTTa rewriting engine, and the
  precise content of "the rewriting engine and the logic engine are one
  semantics." Proof-layer only (zero-bog); self-contained (dependency arrow).
Imports: MettaHyperonFull.Proofs.GroundModel, Mathlib.Logic.Relation
Trusted boundary: none (fully proved)
Main exports: ReachesNF, coincidence, coincidence_sound, coincidence_complete
Open obligations: the LP-model *interpretation* (leastModelP = the least
  Herbrand model) and the SLD-agreement theorem are math-side (T3.3b); the
  coincidence itself is unconditional (holds for all atoms), a stronger outcome
  than the ground/definite scope the plan anticipated.
-/
import MettaHyperonFull.Proofs.GroundModel
import Mathlib.Logic.Relation

namespace Metta

/-- `v` is a normal form reachable from `a` by equality-rule reduction steps:
the operational reading of "`a` evaluates to `v`". -/
def ReachesNF (kb : Space) (a v : Atom) : Prop :=
  Relation.ReflTransGen (StepR kb) a v ∧ equalityReductions kb v = []

/-- **Soundness of the model** (`leastModelP ⊆ ReachesNF`): every pair in the
declarative least model is an operational reduction-to-normal-form. Proved by
least-ness — `ReachesNF` is closed under the immediate-consequence operator. -/
theorem coincidence_sound (kb : Space) {a v : Atom}
    (h : (a, v) ∈ leastModelP kb) : ReachesNF kb a v := by
  have hclosed : TPeq kb {p | ReachesNF kb p.1 p.2} ⊆ {p | ReachesNF kb p.1 p.2} := by
    rintro ⟨a', v'⟩ hp
    rcases hp with ⟨hnf, heq⟩ | ⟨r, hstep, hreach⟩
    · exact ⟨heq ▸ Relation.ReflTransGen.refl, heq ▸ hnf⟩
    · exact ⟨Relation.ReflTransGen.head hstep hreach.1, hreach.2⟩
  exact leastModelP_least kb _ hclosed h

/-- **Completeness of the model** (`ReachesNF ⊆ leastModelP`): every operational
reduction-to-normal-form is captured by the declarative least model. Proved by
induction on the reduction chain, using the model's fact/step lemmas. -/
theorem coincidence_complete (kb : Space) {a v : Atom}
    (h : ReachesNF kb a v) : (a, v) ∈ leastModelP kb := by
  obtain ⟨hchain, hvnf⟩ := h
  induction hchain using Relation.ReflTransGen.head_induction_on with
  | refl => exact leastModelP_nf kb v hvnf
  | head hstep _ ih => exact leastModelP_step kb hstep ih

/-- **The coincidence theorem.** The declarative least-fixpoint model and the
operational reduction-to-normal-form relation coincide: for all atoms,
`(a, v) ∈ leastModelP kb ↔ v` is a normal form reachable from `a`. The
rewriting engine and the logic model are one semantics.

Scope note: the coincidence holds unconditionally (all atoms). The further
identification `leastModelP = the least Herbrand model` — and the SLD-computed
agreement — is the math-side theorem (BRIDGE-DESIGN §6, T3.3b), stated over
ground definite queries where the logic-programming model is the intended
reading. -/
theorem coincidence (kb : Space) (a v : Atom) :
    (a, v) ∈ leastModelP kb ↔ ReachesNF kb a v :=
  ⟨coincidence_sound kb, coincidence_complete kb⟩

end Metta
