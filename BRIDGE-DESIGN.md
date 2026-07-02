# BRIDGE-DESIGN — LeaTTa-petta ↔ the logic-programming model (Track 3)

## §1 Governing architecture (two rules)

**Rule 1 — the dependency arrow: math imports engine, engine never imports
math.** LeaTTa-petta is the engine artifact: self-contained, dependency-light,
and it takes **no cross-tree Lean dependency** on Mettapedia. We may READ the
Mettapedia LP/SLD/PeTTaEval formalization for alignment; we never `import` it.
Any theorem that must *name* `SLDTree` (or other math-side objects) is authored
on the math side (Mettapedia, where LP/SLD already lives and LeaTTa is already
an `externals/` dependency), later — see §6.

**Rule 2 — zero-bog (the mm-lean4 pattern).** The executable core — the
`Operational` reducer (`Semantics.lean`, `SemanticsP.lean`), the `Minimal`
kernel + stdlib, and `Main` — carries **no proof-theory weight** and stays
100% efficient. Every Track-3 model, relation, and theorem lives under
`Proofs/`, importing the core. The core gains nothing but is depended upon.

*Housekeeping flag (not a milestone):* `Operational/NormalizeP.lean` currently
holds the `CtxStepP` Prop-relation (proof-theory) alongside the `normalizeP`
def. It is off the production hot path (`Main` never calls it), so it is not an
efficiency defect, but for strict Rule-2 hygiene its Prop content should
eventually move to `Proofs/`. Deferred; recorded here.

## §2 The correspondence map

Three views of the same ground semantics:

| View | Object | Where |
|---|---|---|
| **Operational (ours)** | `equalityReductions` / `reduceAtomP pettaProfile` — a rule `(lhs,rhs)` fires by `matchAtoms lhs a` → `instantiate b rhs` | LeaTTa-petta `Operational/` (executable) |
| **Declarative (ours, new)** | `leastModelP` — least fixpoint of an immediate-consequence operator over ground reduction | LeaTTa-petta `Proofs/GroundModel.lean` (T3.1) |
| **Logic-programming (math-side)** | `leastHerbrandModel` via `OrderHom.lfp` + `T_P_LP`; `PeTTaEval` inductive relation | Mettapedia `Logic/LP/Semantics.lean`, `Languages/MeTTa/PeTTa/Eval.lean` |

Mettapedia's `Eval.lean` already asserts the target thesis in prose:
*"PeTTa's ruleApp ≡ LP's leastHerbrandModel ≡ MeTTa metta_call — all three
agree."* Track 3 makes the **engine-side half** of that a machine-checked
theorem (`leastModelP` = our reduction), and hands the **SLD-named half** to
the math side (§6). We mirror the LP model's *shape* (Tarski lfp of a `TP`
operator over `Set (ground Atom)`) without importing it — a minimal,
self-contained redo, per Rule 1.

## §3 Definite-clause check (the T3.0 stop-rule question) — **VERDICT: GO**

Are the in-fragment equality rules definite-clause-shaped? **Yes.**

- Each `(= lhs rhs)` reads as the Horn clause
  `Val(a, V) :- Match(lhs, a, θ), Val(θ·rhs, V)` — one positive head literal,
  positive body, **no negation**.
- Grounded operators (`+`, `car-atom`, …) are extensional facts / an oracle —
  positive, definite.
- `noMatchEmpty` (PeTTa goal failure) is **absence from the least model**, not
  negation-in-a-body — exactly the closed-world reading the least Herbrand
  model already provides. It does not break definiteness.
- Nondeterminism (`superpose`, multiple matching rules) is a **set-valued**
  model (several members), which a least fixpoint over `Set` handles natively.
- The only things that *would* break definiteness — negation-as-failure in a
  rule body, higher-order rule heads — are precisely the out-of-fragment
  families (MODE-1 higher-order, TYPES, effects). In-fragment: clean.

So the coincidence theorem keeps its intended shape; the stop rule is not
triggered.

## §4 The coincidence theorem (T3.2), stated

Scope: **ground** queries, **definite** in-fragment rules, `pettaProfile`.

> For a ground atom `a` and a ground normal form `v`:
> `v` is reachable from `a` by `equalityReductions` (its reflexive-transitive
> reduction) **iff** `(a, v) ∈ leastModelP kb`.

`leastModelP` (T3.1) is the least fixpoint of `TPeq`, the immediate-consequence
operator: `TPeq I` adds `(a, v)` when either `a = v` is inert, or some rule
`(lhs,rhs)` matches `a` under a ground `θ` with `(θ·rhs, v) ∈ I`. This is the
van Emden–Kowalski / Henkin result, mirrored for our reducer: the operational
reduction *computes* the declarative least model.

On resistance (stop rule): prove **soundness** alone —
`v` reachable ⇒ `(a,v) ∈ leastModelP` (the `TP`-closure direction, the easy
half) — and ledger completeness with the precise obstruction.

## §5 Relational execution (T3.3a) and the honest never

Non-ground goals (invert-`append`, `functionhead`) are the **relational
extension** the ground model does not reach: they compute *input* bindings, not
just outputs. Engine-side, expressible without SLD:

> Every ground **instantiation** of a non-ground answer lands in `leastModelP`
> (a statement about `leastModelP` + substitution; the substitution lemma is
> already in-tree).

The full non-ground **solver** is the separately-certified LP/SLD stack (audit:
real Martelli–Montanari MGU, `unifyFuel_exists_of_unifies` making fuel honest,
completeness scoped where decidable). Full non-ground **completeness** is
**undecidable** (SLD trees for non-terminating programs are infinite) — stated
as the honest never, not a gap. Re-tag the affected corpus family
`MODE-1 → MODE-1-BRIDGED`.

## §6 T3.3b handoff (math-side, BANKED — not this repo)

The theorem *"`SLDTree`-computed answers agree with `leastModelP`"* is authored
in Mettapedia: it imports LeaTTa as an external and **vendors the pinned
`leastModelP` spec** — provenance header naming the LeaTTa-petta commit it
mirrors, plus a `defs-equal` check so the two trees cannot silently drift while
the theorem claims agreement. Queue behind the SR seal.

## Go / no-go

**GO — confidence 82%.** Definite-clause shape confirmed (§3); the LP model
shape is a clean Tarski-lfp mirror (§2); T3.1 is a screenful; the T3.2
soundness direction is low-risk and the completeness direction is the only real
proof-risk (stop rule covers it). The architecture rules (§1) keep the engine
clean and the deep SLD theorem where the math lives.
