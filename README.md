<!-- SPDX-License-Identifier: Apache-2.0 -->

# PLeaTTa — core PeTTa, formalized in Lean 4

A machine-checked model of **core PeTTa** (Patrick Hammer's Prolog-hosted MeTTa — [trueagi-io/PeTTa](https://github.com/trueagi-io/PeTTa)).
PeTTa compiles MeTTa to Prolog clauses run under SLD resolution; PLeaTTa
formalizes an explicit model of that pipeline, with a proof tying the
executable engine to its formal transition-system spec:

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
*spec*. It does **not** yet prove the entire source-to-observation pipeline
faithfully models *real PeTTa*. Independent reader, compiler, and Prolog-core
relations and initial adequacy theorems are present, but their universal
composition is active work. Fidelity to the remaining native PeTTa/SWI
surface rests on source anchoring plus differential agreement, which are
regression evidence rather than theorem substitutes.

## Try it

```bash
lake build pleatta                                        # build (Lean 4 via elan)

./run.sh         ../PeTTa/examples/invertfunction.metta   # run a program
./run-compare.sh ../PeTTa/examples/foldall.metta          # vs native PeTTa
./run-certify.sh ../PeTTa/examples/foldall.metta          # emit + check certificates
./run-bench.sh                                            # full corpus + tiered summary
```

Some things it does correctly (all differentially checked against native PeTTa):

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

Measured vs pinned PeTTa `6b7f52f` over its frozen 176-example corpus (same
ordered answers and multiplicity; denominator and hashes in
`diffbench/corpus-176.{txt,sha256}`, latest results in
`diffbench/coverage-extended-index.tsv`):

- **Certified-core evidence: 166 cases** — 147 have direct
  value/order/multiplicity agreement, 15 have a
  same-family performance witness (the full-scale file is scale-bound, e.g.
  `matespace` builds ~1.5M atoms; a small same-family case agrees, so it's
  evidence of the same semantic family rather than direct full-scale
  execution), and 4 have a corrected-capability witness where the pinned test
  itself is malformed. These are differential evidence for PeTTa fidelity;
  the refinement proof separately establishes that the executable follows
  PLeaTTa's formal `Step` relation. A subset also carry a re-checked
  `checktrace` certificate.
- **Trusted-host tier: 6** (real host execution through the *certified* host
  bridge, reported separately, never merged into certified-core) — `python`,
  `python_import`, `torch` (Python/Janus), `translatepredicate`, and
  `prologimport` (typed SWI-Prolog interoperation) agree with pinned PeTTa
  answer-for-answer; `repl` agrees on a bounded one-turn stdin witness. Locally
  owned definite clauses execute in PLeaTTa's core, while genuinely external
  predicates use the typed recorded boundary. Verification mode replays a
  recorded transcript through the pure stepper. The seal certifies the
  reductions *around* accepted host responses, not the external implementation.
  External SWI predicates are callable by default, matching pinned PeTTa;
  there is no predicate allowlist masquerading as a proof boundary. Optional
  operator controls (`PLEATTA_PROLOG_DENY`,
  `PLEATTA_PROLOG_INFERENCE_LIMIT`, and
  `PLEATTA_PROLOG_TIMEOUT_SECONDS`) are empty/unset by default and remain
  separate from certification. `PLEATTA_PROLOG_DENY` filters only the outer
  requested functor; it is not a sandbox for nested or dynamically built
  Prolog goals. Run
  `pleatta --host-provenance transcript.json` to derive a path-free boundary
  summary from the typed transcript itself; live and replay therefore receive
  identical provenance accounting without trusting the worker to label itself.
- **Operational coverage (adjudicated): 172/176.**
- **Unexplained engine gaps: 0.** Value-sensitive NARS and PLN witnesses
  establish lookup, ground deduction, and variable-quantified deduction with
  exact STVs and evidence stamps. Full `nars_tuffy` and `pln_tuffy` remain in
  the witnessed performance tier.
- **Known semantic divergence: 0.**
- **Not yet covered: 4** — `git_import`, `git_import2` (network + external
  build), `llm_cities` (live LLM), and `greedy_chess` (interactive loop) are
  deferred external dependencies.

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
