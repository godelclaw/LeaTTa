# BURNDOWN — LeaTTa-petta sorry ledger and known-issue register

Rule: nothing in this repo is called "certified" for the PeTTa profile while
this ledger has open entries. Sorries are special-permission: a scoped window
was granted by the maintainer (2026-07-02) for M2/M3 special-form arms, on exactly that
condition. Current `sorry` count in `MettaHyperonFull/`: **0**.

## Open — profile axes not yet modeled

- **ORDER-1 (evaluation order / one-pass)**: PeTTa's eagerness is a
  compile-time evaluation-point commitment (WAM-style), not a runtime flag on
  the HE machine loop. Symptom already probed: `!(quote (+ 1 2))` → PeTTa
  returns `(+ 1 2)` *unevaluated* (results are not re-driven), while the
  four-register machine re-reduces workspace reducts to fixpoint. The
  `quoteStrips` flag therefore over-reduces `(quote <redex>)` day-one (will
  show as scoreboard DIFFs). Plan: model the order dimension Strategy-style
  (`MeTTaIL/Semantics/Strategy.lean` is the proven-sound template), not as a
  Bool. Expected to be the paper-grade structural finding.
- **ERR-1 (error surface)**: PROBED 2026-07-02: native PeTTa on
  `!(+ 1 nonnumber)` raises a FATAL Prolog `is/2` arithmetic error — the
  whole file run aborts (no subsequent directives execute). Not empty, not
  inert, not a structured error atom: a crash. The profile leaves such
  atoms inert (HE-style noReduce), so error-probe files diverge by design
  until an error-semantics axis is modeled. Distinct from noMatchEmpty —
  no conflation observed.
- **MODE-1 (relational/invertible execution)**: PeTTa runs equality rules
  as Prolog clauses, in ANY instantiation mode — `functionhead.metta` /
  `invertfunction.metta` invert `append` through unbound arguments. A
  rewriting kernel evaluates left-to-right on ground(ish) terms and cannot
  do this without narrowing. This is a structural finding about PeTTa
  semantics (functional-LOGIC, not just functional): attribution family in
  the scoreboard, out of scope for the dialect profile.

## Fidelity audit (chainer/PLN workload, 2026-07-03) — the real DIFF-COUNT content

Probed against native PeTTa (pin 700707a68053). The chainer slice (50% baseline)
exposed that the residual multiplicity divergence is NOT "branch-local failure"
(that was fixed in Track 2 and is correct) but three distinct causes:

- **CONTROL-1 — `cut` / `progn` MISSING (critical, unmodeled).** Probe:
  `(= (pick $x) (progn (cut) first))` + `(= (pick $x) second)`;
  `(collapse (pick anything))` → native `(first)` (cut commits, prunes clause 2);
  ours `((progn (cut) first) second)` (neither grounded; both clauses fire
  unreduced). `cut` is committed choice — it prunes the answer multiset; PLN's
  `=>` operator relies on it. This is control-flow / the Prolog-execution layer,
  NOT pure rewriting — it belongs with the relational/SLD layer or must be
  explicitly scoped out; a rewriting kernel cannot fake cut honestly.
- **BIND-1 — `find` / `reduce` primitives MISSING (fixable, in-fragment-ish).**
  `spaces_find`: `(find &self (friend $a $b))` yields 4 UNBOUND
  `(FoundChain $a $b $c)` instead of bound `(FoundChain a b c)` +
  `(MissedSecondPiece)`. `find`/`reduce` (force-eval-to-answer, bind vars) are
  lib primitives we do not ground; PLN's `(? $term)` uses `(reduce $term)`.
  Real bug, addable.
- **PERF-1 — fuel too shallow for deep arithmetic.** `hyperpose_primes`
  StackOverflows on `find-divisor` recursing to sqrt(n); swipl computes it.
  Config artifact, not semantics; raise fuel or tag PERF.

Mutation-visibility (logical-update view) probe: **PASS** — `add-atom` during an
open match enumeration is not seen by that enumeration (native `(1 2)`; ours
`(1 2)`), seen by the next call (both `(1 2 100 100)`). The chainer heartbeat is
faithful.

Verdict: the pure rewriting + spaces core is faithful (mutation view correct,
tutorials mostly agree). "Chainer-grade" is premature: real PLN leans on `cut`
(committed choice) and `find`/`reduce`, which we do not model. The single
biggest fidelity lever is `cut` — and it is control-flow, so it lands with the
relational layer, not a rewriting-profile arm.

## Fidelity audit

## Track-3 status (the Prolog bridge)

- **MODE-1 → MODE-1-BRIDGED (T3.3a, DONE engine-side)**: relational execution
  is accounted for. `ground_answer_sound`/`relational_answer_certified`
  (RelationalBridge.lean) certify that any answer read as a ground reduction is
  in `leastModelP`; the input-binding SEARCH is the certified LP/SLD solver
  (math side). Full non-ground completeness = undecidable (honest never).
- **T3.1/T3.2/T3.3a DONE (engine-side, zero sorry, audited)**: `leastModelP`
  (Tarski lfp); the **coincidence theorem** (`leastModelP` = reduction-to-normal
  -form, unconditional); `ground_answer_sound` (relational answers certified).
- **T3.3b (BANKED, math-side)**: `SLDTree`-answers ⊆ `leastModelP`, authored in
  Mettapedia with a pinned+defs-equal vendored `leastModelP`. Behind SR seal.
- **Genuinely-never (a theorem, not a gap)**: full non-ground completeness =
  undecidable (infinite SLD trees for non-terminating programs).

## Track-2 obligations from Track-1 kernel changes

- **OBL-1 — DISCHARGED (T2.1)**: spec-side `stepAddAtomP`/`stepRemAtomP`
  with `successAtomP` added (`SemanticsP.lean`); HE regressions proven by
  `rfl`; audited in `Proofs/AxiomAuditP.lean`.

## Open — normalizer program (post-C2.3)

- **NORM-1**: completeness of `normalizeP` (every `CtxStepP`-normal form is
  produced given sufficient fuel) — converse of the proven star-soundness.
- **NORM-2**: normalizer ⇔ kernel-driver correspondence (the minimal
  interpreter's argMask/returnsAtom evaluation vs `normalizeP stratAll` at
  the petta profile) — the full ORDER/NONDET formal closure.
- **C3.1 — DISCHARGED**: `definedHeadK_eq_definedHead_dyn` generalizes the
  no-match trichotomy to arbitrary `selfExtra` (imports + runtime rules);
  the `World.empty` theorem is now its corollary. Audited.

## T1.3 pre-work: native space-semantics probes (2026-07-02, 6 probes)

- `add-atom`/`remove-atom` return `true` in native PeTTa (LeaTTa returns
  `()` — DIV-006 surface family; needs a profile-side result-shape switch).
- Runtime rules fire immediately after `add-atom &self (= ...)`; `match`
  works over rule and non-rule atoms alike.
- **Definedness is dynamic**: after `remove-atom` deletes the last rule for a
  head, calls to it revert to INERT (undefined), not empty. The kernel's
  `definedHeadK` over `candidatesW` (which consults `selfExtra`) already has
  the right shape; the spec-side correspondence is stated at `World.empty`
  and will need a dynamic-KB restatement in Track 2.
- Named spaces: `bind! &kb (new-space)` + `add-atom`/`match`/`get-atoms &kb`
  behave as in HE modulo the `true` result shape.

## Known LeaTTa artifacts (NOT profile deltas — pre-ledgered so the M0
baseline is not misread)

- **LEATTA-1 (collapse bare tuple)**: fixed at `b851427` ("stdlib: collapse
  yields a bare tuple, matching HE 0.2.10"), which is this branch's base
  commit — VERIFIED PRESENT, no pollution expected.
- **LEATTA-2 (size-atom meta-type violation)**: LeaTTa's `size-atom`
  evaluates its Expression-typed argument; HE/CeTTa pass it unreduced.
  Documented upstream divergence, unfixed. Any scoreboard DIFF on files using
  `size-atom` must be attributed here first, not to the PeTTa profile.

## Harness approximations (diffbench/diff.py)

- `(test A B)` / `(assertEqual A B)` rewritten to `(== A B)` for
  cross-engine comparability (PeTTa's checkmark printer vs LeaTTa's stdlib).
- PeTTa side-effect prints (`println!`) interleave with result lines in the
  extractor; comparison is multiset-based, and files whose agreement hinges
  on print side-effects need per-file review before counting as semantic
  DIFFs.
- `definedHead` uses head-symbol + arity (Prolog functor indexing). The
  cross-arity case (rules exist at other arity only) is unprobed on native
  PeTTa — probe before M3 closes.
