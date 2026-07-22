<!-- SPDX-License-Identifier: Apache-2.0 -->

# PLeaTTa — core PeTTa, formalized in Lean 4

A machine-checked model of **core PeTTa** (Patrick Hammer's Prolog-hosted MeTTa, [trueagi-io/PeTTa](https://github.com/trueagi-io/PeTTa)).
PeTTa's semantics *is* compilation of MeTTa to Prolog definite clauses run
under SLD resolution; PLeaTTa formalizes exactly that, the LeaTTa way:

```
compile equations (Compile.lean)  →  executable SLD machine (Machine.lean)
        →  formal small-step relation (Semantics.lean)  →  a refinement PROOF
```

## The proven result

`PLeaTTa/Proofs/StepCases.lean` proves **`machineMirrorsSpecTotal`** (zero
`sorry`, axioms `[propext, Classical.choice, Quot.sound]`): every step of the
executable machine the CLI runs (`stepClean`/`runClean`) is licensed by the
formal `Step` relation, and every completed run is a terminal `StepStar`
derivation — **including nested runs (findall / softcut / catch / eval), with
no escape hatch.** On fuel exhaustion the machine refuses to fabricate a
result rather than returning a wrong one. So `eval` (MeTTa's meta-circular
core) is covered by the proof, not footnoted.

What the proof does *and does not* say: it proves the machine faithfully
implements the spec. It does **not** yet prove the spec faithfully models real
PeTTa — that (compile-equation adequacy vs the transpiler) is future work.
Correctness of the *model* rests on source-anchoring (every compile equation
cites `[SPEC translator.pl:lines]`) plus corpus agreement, both strong but
incomplete.

## Coverage — tiered by evidence, never a flat number

Measured against native PeTTa over its 176-example corpus (same answer bag):

- **Certified-core agreement: 166/176** — the proven in-Lean machine produces
  PeTTa's answers: **148** by direct value+multiplicity agreement, **14** by a
  same-family performance witness (the full-scale file is scale-bound — e.g.
  `matespace` builds ~1.5M atoms — while a small same-family case *agrees*, so
  the semantics are right and it is genuinely scale, not a masked bug), and
  **4** by a corrected-capability witness where the pinned test itself is
  malformed (both engines agree it is). A subset also carry a re-checked
  `checktrace` certificate (`superpose_primes`, 54M-scale primality, via the
  swipl-finds/Lean-checks delegation lane).
- **Trusted-host tier: 5** — real host execution through the *certified* host
  bridge, reported separately and **never** merged into the certified-core
  count. `python`, `python_import`, `torch` (Python/Janus) and
  `translatepredicate` (SWI-Prolog) agree with pinned PeTTa answer-for-answer;
  `repl` agrees on a bounded one-turn stdin witness. Live execution goes through
  an explicit typed request/response transition, and verification mode replays a
  recorded transcript through the pure stepper — the seal certifies the PeTTa
  reductions *around* accepted host responses, not the external implementation.
- **Operational coverage (adjudicated): 171/176.**
- **Known-open correctness/performance boundary: 0.** NARS lookup, ground-rule
  deduction, variable-quantified `==>` deduction, and the corresponding PLN
  deduction return the exact expected STVs and evidence stamps in both engines.
  Full `nars_tuffy` and `pln_tuffy` remain performance-disqualified.
- **Known semantic divergence: 0.**
- **Not yet covered: 5.** `prologimport` needs a stateful, bidirectional
  MeTTa↔Prolog FFI (a persistent clause database with `consult`/`asserta`/
  `callPredicate` plus Prolog↔MeTTa callback) with no clean certified boundary
  yet; `git_import`/`git_import2` (network clone + external build), `llm_cities`
  (live LLM), and `greedy_chess` (interactive loop) are deferred external
  dependencies.

The honest one-liner: *a principled, proof-backed core of PeTTa with `eval`
proven, host effects handled through a certified bridge in an explicit trusted
tier, and an explicitly-bounded frontier* — not "PeTTa fully verified."

## Run it

```bash
lake build pleatta            # build (Lean 4 via elan; toolchain pinned)
./run.sh         FILE.metta   # evaluate, print answers
./run-certify.sh FILE.metta   # evaluate + emit & verify certificates
./run-compare.sh FILE.metta   # side-by-side vs native PeTTa (needs swipl)
./run-bench.sh                # full-corpus differential + tiered summary
```
The certificate checker lives in a companion `algos-lp` package
(`$CHECKTRACE` / `ALGOS_LP_DIR` to point at it).

## Layout

- `PLeaTTa/` — the engine + proofs. `PETTA-LP.md` = the spec.
- `diffbench/` — differential harness, the certificate lane, run logs,
  `DIVERGENCE-DIAGNOSIS.md` (the honest open-bug ledger), `BURNDOWN.md`.
- `upstream-patches/` — a genuine string-escape bug-fix for PeTTa's parser,
  found while modeling it (offered upstream, not committed to PeTTa's repo).

## Provenance

Base MeTTa/Hyperon engine + tooling from LeaTTa (this repository's own
codebase); PeTTa upstream is `trueagi-io/PeTTa`. Research work-in-progress —
shared for review, not a finished release.
