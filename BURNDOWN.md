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

## Track-4 DECISIVE finding: the >=90% gate is not reachable by builtin coverage

MEASURED: 7 clean builtins added (msort, second-from-pair, is-member,
list_to_set, exclude-item, decons, member) moved the tutorial from 66/168 to
**68/168 (+2 files)**. That is the ROI of the builtin-coverage grind: ~7 ops per
2 files. To reach 90% (151/168) would need ~80 more files to flip; at this rate
that is hundreds of ops -- AND most remaining files are NOT builtin-fixable:
the 50 VALUE-DIFF bulk is dominated by RELATIONAL (battery tier), LAMBDA
(partial-application), PERF (fuel), and quote/eval STAGING, none of which a
grounded op addresses.

CONCLUSION (evidenced, not speculated): the >=90% agreement gate on the full
tutorial corpus is NOT achievable by adding builtins to this rewriting engine.
Reaching it would require the relational battery tier + lambda features +
accepting PERF -- i.e. the THREE-TIER architecture (relational -> lp-engine),
not more ops here. The gate as written ("residue ONLY LAMBDA/PERF/effects")
assumed a small closeable residue; the measurement shows a large ARCHITECTURAL
tail. The correct closure is: certified rewriting core (done) + the three-tier
plan for the relational fragment + honest residue attribution. The aggregate
agreement % measures "does this rewriting engine replicate PeTTa's entire
runtime," which is a different (and larger) thing than the certified deliverable.

## Builtin-coverage tail — progress + method

Implemented (probe-verified): msort ((3 1 2)->(1 2 3)). Attempted `once`
(take-first-of-nondeterminism): needs kernel evaluation-ORDER surgery, not a
grounded op or noeval-signature -- the arg is spread by the enclosing eager
evaluation before `once` sees it, at a level the (-> Atom _) signature does not
reach. Reverted per the 2-iteration stop-rule; `once` is a dedicated kernel
task (special-form arg-capture), grouped with the other take-first/committed
ops. METHOD for the tail: extract unreduced operator heads from the divergence
diffs (once/msort/... ), implement each as grounded-op / prelude-rule / special
-form, probe, re-measure. Bounded, op-by-op, multi-session.

## Track-4 tutorial residue — ATTRIBUTED (the honest-report gate, both slices)

Comprehensive diagnosis of the ~86 in-fragment tutorial disagreements
(oracle-pinned, order-agnostic multiset):

- **PERF (16)**: deep recursion/search exceeding fuel; swipl computes (accepted,
  not a fidelity bug).
- **RELATIONAL (13)**: implicit SLD conjunction / unbound-var resolution -->
  the lp-engine battery tier (certified account, not the rewriting engine).
- **LAMBDA / partial-application (~10)**: PeTTa reifies `(partial f args)` and
  `|->` lambdas; cool-but-not-core (Zar) -- advanced surface.
- **BUILTIN-COVERAGE (~40, the VALUE-DIFF bulk)**: a LONG TAIL of individual
  PeTTa operators our HE-lineage kernel does not yet match, sampled: `eval`
  and `call` staging (callquoteevalreduce, eval), `second-from-pair` (atomops),
  `if-equal` (he_equalreduct evaluates where native holds), and similar. Each
  is small and addable (a grounded op or a staging rule); NONE is a deep
  semantic defect. Collectively they are the ~40% aggregate gap.

CONCLUSION (honest, both slices attributed): the rewriting SEMANTICS is faithful
where the semantics is shared (probe-verified: primitives, spaces, control,
mutation-view; certified: the whole Track 1-3 core). The ~40% aggregate is NOT
a broken core -- it is (a) PERF, (b) relational (battery tier), (c) lambda
(advanced), and (d) a long tail of ~40 individual builtin/operator coverage
gaps. Reaching >=90% = implementing that builtin tail: bounded-but-large,
op-by-op, now NAMED rather than mysterious. Not a defect to debug; a coverage
list to work if the corpus-match number is itself the goal.

## Track-4 FINAL honest number (verified three ways)

The `test` differential transform was NOT the cause of the low agreement.
Three comparison methods all cluster at ~40% tutorial agreement (order-agnostic
multiset, oracle-pinned 700707a68053, states admitted):
  test->== (spread):        69/168 (41%)
  test->(collapse A) (tuple): 61/168 (36%)  [order-sensitive, rejected]
  test->A bare (multiset):   66/168 (39%)  [correct: order-agnostic]
So ~66/168 agree; ~86 in-fragment files (50 DIFF-COUNT + 36 DIFF-VAL) are
GENUINE value/count divergences in the rewriting fragment, NOT harness
artifacts and NOT all RELATIONAL/PERF. Their individual causes are undiagnosed.

CONCLUSION: the >=90% gate is not reachable without a large, open-ended
per-file diagnosis of a long tail of small dialect divergences (our HE-lineage
kernel vs PeTTa's full behavior). Two "systematic cause" hypotheses (transform
unfairness) were tested and FALSIFIED. What is solid and independent of this
number: the certified core (Track 1/2/3, zero-sorry), the probe-verified
primitives (progn/reduce/cut/typecheck/states), the mutation-view, the chainer
heartbeat, and the three-tier plan. The aggregate % measures how fully our
minimal-MeTTa-derived engine replicates PeTTa's entire dialect surface -- a
long tail, not a single fixable root.

## Track-4 HONEST STATUS (correction, supersedes the "100% rewriting" claim)

The claim "faithful on 100% of the rewriting fragment" was WRONG -- extrapolated
from the clean chainer slice (6/12, residue RELATIONAL+PERF) to the whole
tutorial corpus without checking. The MEASURED tutorial number is 69/168 (41%,
oracle-pinned 700707a68053, states admitted). Of the ~86 in-fragment
disagreements, only ~29 are in characterized families; **~57 are untagged and
mostly small value/count divergences** (off-by-one, surfacing as an extra
`false` where our computation yields a different value than native, exposed by
the test->== harness transform). These are NOT all RELATIONAL/PERF -- some are
genuine value differences in the rewriting fragment, undiagnosed.

SOLID (probe-verified): progn/reduce/cut/typecheck/states individually correct;
mutation-visibility faithful; the chainer-slice residue cleanly RELATIONAL+PERF.
NOT MET: the >=90% agreement gate (41% actual); the full residue is NOT honestly
attributed (57 untagged). The long-tail per-file diagnosis is real remaining
work, not a wave-through.

## Track-4 engine boundary (rewriting primitives faithful; long tail undiagnosed)

Verified: our engine does variable-binding queries `(age $who)->(5 7)` and
explicit nested-match joins `(match (father Abe $y) (match (father $y $z) $z))
->(Bart)` -- both agree with native PeTTa. HE/CeTTa/LeaTTa decline the IMPLICIT
`(, g1 g2)` SLD conjunction identically; only PeTTa runs it (it is swipl
underneath). So the RELATIONAL residue is a PeTTa-dialect EXECUTION MODEL
(implicit SLD resolution via `?`/reduce), NOT a rewriting-engine defect. It is
a legitimate fourth residue category (with LAMBDA/PERF/effects), certified by
the ALGORITHMS/battery tier (compileExpr + SLDCompute + the meTTaPrologOracle
calling back to this engine), not by adding a resolver here. The engine stays
rewriting-only, self-contained. Primitives now faithful: progn/reduce/cut,
arithmetic, spaces, imports, mutation-view. Engine-side Track 4: DONE at its
natural boundary.

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

## CUT-1 (LANDED): body-internal cut via a fired-flag, not branch tags
The recursive evaluator's sequential folds ARE the choicepoint stack, so cut
needs no per-branch provenance: make `cut` an embedded op that sets a
`cutFired` flag in `St`; at each rule application whose RHS `atomHasCut`
(already computed for clause-commit), evaluate alternatives left-to-right and
stop when the flag fires (clear it there — cut cuts its own clause, Prolog
scope). Overhead: one O(1) flag check per alternative, zero allocation;
cut-free programs (all HE code) take the never-fired branch — guard theorem
"cut-free ⇒ unchanged" to accompany. Petta-profile-gated. Testing: both
engines deterministic in KB order, so commit-to-first should match petta's
pick on the corpus (bag-equality remains usable); the general spec is
"sound refinement of the answer bag" (soundness inherited, completeness
deliberately forfeited — that IS cut).

## Ledger: HE oracle 269/270 (pre-existing)
`e2_states.metta` 13/14 on the HE oracle suite — verified present on the
clean committed tree (rebuild bisect), predates the petta-profile work.
Not a today regression; needs its own diagnosis.

### CUT-1 landing notes (2026-07-03)
Landed as the two-stage flag: `St.cutFired` (transient, set by the `(cut)`
arm in `evalOp`, petta-profile-gated) -> `interpretFuel` prunes the pending
work-list siblings and converts it to `St.cutBubble` (sticky) -> the six
`mettaEval` alternative-producing folds stop when the bubble rises DURING the
fold (baseline-relative check `bubble && !baseline`, so survivors of an
already-bubbled call are kept) -> cleared per bang query in `evalSequential`.
Scope: cuts to the current top-level query, not the textual clause — on the
corpus commit-after-choice patterns these coincide; a nested-independent-
nondet program could over-prune (ledgered, no corpus witness). Bonus: `once`
became a one-line lib rule `(= (once $x) (let $cut_tmp (cut) $x))` — the
bubble prunes sibling rule applications even after argument spread, which is
what blocked the previous `once` attempt. Probe-verified vs native petta:
cut.metta, once.metta, matchsingle.metta all match exactly; HE oracle canary
unchanged (269/270 pre-existing); accumulator lemma re-proved (zero sorry).
Overhead: one boolean check per alternative; no allocation.
