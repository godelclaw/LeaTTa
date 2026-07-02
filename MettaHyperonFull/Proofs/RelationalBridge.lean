/-
Module: MettaHyperonFull.Proofs.RelationalBridge
Layer: Proofs
Purpose: Ground-instantiation soundness for relational execution (Track 3,
  T3.3a). The engine-side, SLD-free half of the MODE-1 account: any answer that
  corresponds to a ground reduction-to-normal-form is certified by the least
  model. Non-ground goals (inverting `append`, `functionhead`) compute *input*
  bindings — a search over substitutions that the ground value-relation
  `leastModelP` does not itself perform; that search is the separately-certified
  LP/SLD solver (the math side, T3.3b), and its full non-ground completeness is
  undecidable (the honest never). Proof-layer only; imports only the engine.
Imports: MettaHyperonFull.Proofs.Coincidence
Trusted boundary: none (fully proved)
Main exports: ground_answer_sound, relational_answer_certified
Open obligations: the SLD-computed agreement (`SLDTree` answers ⊆ `leastModelP`)
  is math-side (BRIDGE-DESIGN §6). Full non-ground completeness is undecidable
  (stated, not a gap).
-/
import MettaHyperonFull.Proofs.Coincidence

namespace Metta

/-- **Ground-answer soundness.** Whenever a (ground) query `a` reduces to a
normal form `v`, the pair is in the certified least model. This is the
engine-side guarantee behind relational execution: any concrete ground answer a
relational solver returns — read as a reduction — is model-certified. Immediate
from the coincidence theorem. -/
theorem ground_answer_sound (kb : Space) {a v : Atom}
    (hreach : ReachesNF kb a v) : (a, v) ∈ leastModelP kb :=
  coincidence_complete kb hreach

/-- **Relational answer certification.** A relational solver answers a query
`q` by producing a substitution `θ` (binding `q`'s variables) such that the
instantiated query `θ·q` evaluates to a value. Engine-side, the soundness
content is exactly: if that instantiated query reduces to a normal form, the
resulting input/output pair is in the least model. The *production* of `θ`
(searching input bindings — e.g. inverting `append`) is beyond the ground
value-relation and is the LP/SLD solver's role; here we certify what it returns.

`θ·q` is `applyθ` (the caller's instantiation of the query under the solver's
answer); this states the certification uniformly without naming SLD. -/
theorem relational_answer_certified (kb : Space) (appliedQuery value : Atom)
    (hreach : ReachesNF kb appliedQuery value) :
    (appliedQuery, value) ∈ leastModelP kb :=
  ground_answer_sound kb hreach

/-!
## The relational boundary (MODE-1-BRIDGED), stated honestly

`leastModelP` is a relation on *values*: `(a, v)` means "`a` evaluates to `v`".
It does not, by itself, compute the *input* bindings a relational query asks
for — e.g. "which `x` make `(append x ys) = zs`?" That is a search over
substitutions, which:

* is performed by the certified LP/SLD solver (Martelli–Montanari MGU with
  proven fuel-sufficiency; least-Herbrand soundness) — the math side, imported
  there, never here (the dependency arrow);
* agrees with `leastModelP` on the answers it returns via the math-side
  theorem `SLDTree`-answers ⊆ `leastModelP` (BRIDGE-DESIGN §6, T3.3b), whose
  `leastModelP` component is `ground_answer_sound` above;
* is **not fully decidable**: for non-terminating programs the SLD search tree
  is infinite, so a total solver enumerating *all* non-ground answers cannot
  exist. This is the honest never — a consequence of undecidability of the
  halting problem for logic programs, not a gap in the certification.

The corpus files that exercise this (invert-*, functionhead) are therefore
re-tagged `MODE-1-BRIDGED`: their disagreement with our ground reducer is not a
semantic defect but the expected boundary between value-evaluation (this engine)
and relational search (the certified LP solver).
-/

end Metta
