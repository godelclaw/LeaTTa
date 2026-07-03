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


## §7 Three-tier reorganization (the pristine format for LP/SLD/Prolog) — **LANDED**

The executable Prolog/SLD material lives in its OWN tier, not buried in the heavy
theory nor bolted onto a pure engine. Three tiers, one arrow:

```
ENGINES     LeaTTa / LeaTTa-petta / CeTTa / PeTTa
            rewriting-only, self-contained, import NOTHING (unchanged).
                 ▲ process boundary only (harness runs binaries)
ALGORITHMS  the standalone verified-executable package `algos-lp`, in the SAME
            namespace `Mettapedia.Logic.LP`: Core (types), Substitution,
            Unification (unifyFuel, Martelli-Montanari), SLDCompute (executable
            DFS: sldSearch/sldQuery). CORE-LEAN ONLY, no Mathlib, builds
            sub-second, ships `grandfather`.
                 ▲ Lake dependency (math imports algos -- the arrow)
METTAPEDIA  the theory: SLDTree, least Herbrand, unification/SLD completeness,
            the Track-3 coincidence + T3.3b agreement -- Mathlib-powered,
            proves things ABOUT the algos code (goal: no vendored copy).
```

**Status (landed, verified):** `algos-lp` exists in the godelclaw MeTTapedia repo
under `lean/algos-lp`, builds Mathlib-free sub-second, and `lake exe grandfather`
resolves `grandfather(Abe, Z)` -> `Z = Bart` through the certified SLD solver --
the exact relational query the rewriting engine declines. The method is a **move,
not a fork**: the executable defs are carried *verbatim*
under the *same* namespace `Mettapedia.Logic.LP`, so the eventual math re-point is
import-lines-only; every theorem and every Mathlib-flavored def stays in the math
tier untouched; each file carries a provenance header. The prior straight-copy
`lp-engine` mirror was pure replication and is removed. Gates verified: 0 Mathlib
imports; grandfather runs; no third def site; all math theorems still resolve;
provenance + defs-equal spot-check (algos `unifyFuel` byte-identical to math's
modulo `N`/`Nat`).

**Remaining for zero-replication (Gate 6, the reconciliation tranche):** the math
tier still carries its own proof-side copies of the executable defs. Re-pointing
it to `import` this package (so each exec def lives in exactly one place) is now
**unblocked** -- the math tier and `algos-lp` are both on Lean 4.31 and share the
namespace, so the re-point is import-lines-only. It is held as its own tranche
because the math `Logic/LP` tree is hot (active proof lanes) and touching it is a
significant, confirm-first change -- not a rider on the split.

**Why**: the relational residue (implicit `(, g1 g2)` SLD conjunction, `?`/
reduce resolution) is a PeTTa-dialect EXECUTION MODEL, not a rewriting-engine
defect (HE/CeTTa/LeaTTa/ours all decline it identically; only PeTTa runs it,
being swipl underneath). So the certified relational account is: run the
fragment through `lp-engine` (compileExpr + SLDCompute + the meTTaPrologOracle
calling back into the rewriting engine for grounded/functional parts). No
second resolver is ever written; the engine stays pure.

**The carve-out is a de-tangling, not a move** (aimama-side, read-only here —
this is the executable spec for that work): `SLDCompute`/`UnificationMGU`
import no Mathlib directly but pull it transitively via `FunctionFreeEvaluation`
(3) and `Core` (5). Factor defs-from-proofs in ~4-6 files: executable defs ->
`lp-engine` on core-Lean-only imports; interleaved proofs stay in Mettapedia and
re-point. Bounded classic work; its own tranche.

**Sequencing**: do the carve-out BEFORE T3.3b so the agreement theorem is
written once against the final layout. Home it in `lean/standalone/` beside
mm-lean4. This is the natural first job for the SR-side agent after the seal
(it merges with the already-banked T3.3b -- one tranche). Verify-don't-assume
when it lands: soundness (coincidence+T3.3b) guarantees answers are in the
model, but exact PLN-numeric agreement (STV arithmetic through resolution) is an
EMPIRICAL check -- the oracle must run the grounded ops faithfully mid-resolution.

**Efficiency**: `lp-engine` is the CERTIFIED oracle, verification-grade, not
production-fast (Lean SLD << swipl). Production PLN runs on PeTTa/CeTTa. Same
Level-1/Level-2 split as the rest of the stack. An FFI-to-SWI fast lane is
possible but pointless -- it re-plumbs PeTTa, which already ships as its own
binary the harness tests against.


## §8 swipl finds, Lean checks (the certificate architecture — **BUILT, demonstrated**)

> Status update: `checkAnswer` + the s-expr adapter + the swipl meta-interpreter
> (`prolog/mi.pl`) are live in `algos-lp`. End-to-end verified: swipl solves
> grandfather -> `checktrace` certifies `Z = bart`; four tamper classes (lied
> answer, wrong clause index, corrupted binding, forged fact) all REJECTED.
> LAMBDA demonstrated the same way: defunctionalized `apply/3` with a
> partial-application closure `addpair(K)`; higher-order `map` certified.
> Remaining for corpus routing: the MeTTa->clause compile step + harness verdict
> classes; the checker soundness theorem is math-tier work.

This supersedes §7's "FFI-to-SWI fast lane is pointless" line. There is a fast
lane worth building, but not as a faster *solver* — as a *checker*. The move is
the LCF / de Bruijn / ATP discipline: **untrusted search, checked results.**

**The asymmetry that makes it work.** SLD's positive answers are cheap to
*certify* even when they were expensive to *find*:

- When swipl returns an answer substitution (`Z = Bart`, or a derived PLN fact),
  the certified `algos-lp` engine does not redo the search. It only *checks* the
  answer: apply the substitution and re-verify the derivation (linear in the
  supplied resolution trace, or a bounded re-derivation of a ground fact against
  `leastModelP`). Checking is orders of magnitude cheaper than finding. So every
  answer that is actually *used* ends up certified, at swipl speed. Trust moves
  from per-query (take-it-or-leave-it) to **per-result**.
- What cannot be certified this way is swipl saying **"no"**: failure and
  exhaustiveness claims have no finite certificate. That is the undecidability
  (infinite SLD trees) living exactly where it should. So the honest trust line
  is one sentence: **positive answers = certified; negative/completeness claims =
  trusted-with-label.** No fudging.

**Concrete shape.** The swipl adapter returns `answer + (optional) resolution
trace`. `algos-lp` gains one small entry point — a *checker*, strictly simpler
than the solver it already ships:

```
checkAnswer : Program σ → Atom σ → Subst σ → (trace : List Step) → Bool
-- applies the substitution, replays each resolution step against the program's
-- clauses (each step must unify), bottoming out in facts / bounded re-derivation.
```

Its soundness theorem (`checkAnswer = true → answer ∈ leastModelP`) is the same
van Emden-Kowalski content as the Track-3 coincidence, read in *verify* mode, and
lands in the math tier over the algos `checkAnswer`.

**The payoff (the reason this is load-bearing).** PeTTaChainer forward-chains,
emitting a *stream of positive derived facts* — each one exactly the checkable
object above. So: **chainer runs on swipl at production speed, every derived fact
certificate-checked by the Lean core = certified PLN chaining at Prolog speed.**
That is what the three tiers were quietly building toward: the rewriting engine
for rewriting, swipl for search, `algos-lp` as the checker that makes the search
output trustworthy, and Mettapedia proving the checker correct.

**Scoreboard verdict classes** (diffbench): `DELEGATED-CHECKED` (positive answer,
certificate verified — counts as certified) vs `DELEGATED-TRUSTED` (a "no"/
exhaustiveness claim, labeled, uncertified by construction).

**Sequencing.** This is its OWN probe-first tranche, landing after the tier split
(now done). It extends `compileExpr` and the solver's atom model (higher-order
`call/N` for `(partial f args)` / `|->` lambdas is the same layer — see the
LAMBDA note), *not* the SLD loop. One tranche at a time — that discipline is what
keeps each one perfect.
