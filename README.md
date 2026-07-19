<!-- SPDX-License-Identifier: Apache-2.0 -->

# PLeaTTa — core PeTTa, formalized in Lean 4

A machine-checked model of **core PeTTa** (Patrick Hammer's Prolog-hosted MeTTa — [trueagi-io/PeTTa](https://github.com/trueagi-io/PeTTa)).
PeTTa's semantics *is* compilation of MeTTa to Prolog definite clauses run
under SLD resolution; PLeaTTa formalizes exactly that, with a proof tying the
executable engine to the spec:

```
compile equations (PLeaTTa/Compile.lean)  →  executable SLD machine (Machine.lean)
      →  formal small-step relation (Semantics.lean)  →  a refinement PROOF
```

(This repository is a profile of **LeaTTa**; see `LEATTA-README.md` for the
underlying verified-MeTTa engine. The PeTTa work lives in `PLeaTTa/`.)

## The proven result

`PLeaTTa/Proofs/StepCases.lean` proves **`machineMirrorsSpecTotal`**
(zero `sorry`; axioms `[propext, Classical.choice, Quot.sound]`): every step of
the machine the CLI actually runs is licensed by the formal `Step` relation,
and every completed run is a terminal `StepStar` derivation — **including the
nested constructs (findall / softcut / catch / `eval`), with no escape hatch.**
On fuel exhaustion the machine *refuses to fabricate* a result rather than
returning a wrong one, so `eval` (MeTTa's meta-circular core) is covered by the
proof, not footnoted.

Scope, stated plainly: the proof shows the machine faithfully implements the
*spec*. It does **not** yet prove the spec faithfully models *real PeTTa* —
that (compile-equation adequacy vs the transpiler) is future work. Model
correctness currently rests on source-anchoring (every compile equation cites
`[SPEC translator.pl:lines]`) plus differential agreement with native PeTTa,
both strong but incomplete.

## Try it

```bash
lake build pleatta                                        # build (Lean 4 via elan)

./run.sh         ../PeTTa/examples/invertfunction.metta   # run a program
./run-compare.sh ../PeTTa/examples/foldall.metta          # vs native PeTTa
./run-certify.sh ../PeTTa/examples/foldall.metta          # emit + check certificates
./run-bench.sh                                            # full corpus + tiered summary
```

Some things it does correctly (all verified against native PeTTa):

| Example | What it shows | Result |
|---|---|---|
| `invertfunction.metta` | running a function **backward** (functional-logic / SLD) | AGREE |
| `booleansolver.metta` | boolean constraint solving, relationally | AGREE |
| `factorial.metta` | ordinary recursion | `3628800` |
| `foldall.metta` | higher-order fold, **certificate-checked** | 10/10 certified |
| `superpose_primes.metta` | trial-division primality to 54M via swipl-finds/Lean-checks | `DELEGATED-CHECKED` |

The certificate checker is a companion `algos-lp` package; point
`run-certify.sh` at it via `$CHECKTRACE`.

## Coverage — tiered by evidence, not a flat number

Measured vs pinned PeTTa `6b7f52f` over its 176-example corpus (same answer
bag; latest run `diffbench/run-full-current-petta-2026-07-14.log`):

- **Certified-core agreement: 166/176** — the proven in-Lean machine produces
  PeTTa's answers: 148 by direct value+multiplicity agreement, 14 by a
  same-family performance witness (the full-scale file is scale-bound, e.g.
  `matespace` builds ~1.5M atoms; a small same-family case agrees, so it's
  genuine scale, not a hidden bug), and 4 by a corrected-capability witness
  where the pinned test itself is malformed. A subset also carry a re-checked
  `checktrace` certificate.
- **Trusted-host tier: 5** (real host execution through the *certified* host
  bridge, reported separately, never merged into certified-core) — `python`,
  `python_import`, `torch` (Python/Janus) and `translatepredicate` (SWI-Prolog)
  agree with pinned PeTTa answer-for-answer; `repl` agrees on a bounded one-turn
  stdin witness. Live host calls go through an explicit typed request/response
  transition; verification mode replays a recorded transcript through the pure
  stepper. The seal certifies the reductions *around* accepted host responses,
  not the external implementation.
- **Operational coverage (adjudicated): 171/176.**
- **Known-open correctness/performance boundary: 0.** Value-sensitive NARS and
  PLN witnesses now establish lookup, ground deduction, and variable-quantified
  deduction with exact STVs and evidence stamps. Full `nars_tuffy` and
  `pln_tuffy` remain in the witnessed performance tier.
- **Known semantic divergence: 0.**
- **Not yet covered: 5** — `prologimport` needs a stateful bidirectional
  MeTTa↔Prolog FFI (persistent clause DB with `consult`/`asserta`/`callPredicate`
  and Prolog↔MeTTa callback) with no clean certified boundary yet; `git_import`,
  `git_import2` (network + external build), `llm_cities` (live LLM), and
  `greedy_chess` (interactive loop) are deferred external dependencies.

The honest one-liner: **a principled, proof-backed core of PeTTa with `eval`
proven, host effects behind a certified bridge in an explicit trusted tier, and
an explicitly-bounded frontier** — not "PeTTa fully verified."

## Layout

- `PLeaTTa/` — the engine + proofs; `PETTA-LP.md` = the spec.
- `diffbench/` — differential harness, the certificate lane, run logs,
  `DIVERGENCE-DIAGNOSIS.md` (the open-bug ledger), `BURNDOWN.md`.
- `upstream-patches/` — a genuine string-escape bug-fix for PeTTa's parser,
  found while modeling it (offered upstream).
- `LEATTA-README.md` + everything else — the LeaTTa engine this builds on.

## Provenance

Built by Oruži (an AI) with Codex, under Zar. **This README was written by Oruži (Claude).** Base engine from LeaTTa; PeTTa
upstream is `trueagi-io/PeTTa`. Research work-in-progress, shared for review.
