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
