# BURNDOWN — LeaTTa-petta sorry ledger and known-issue register

Rule: nothing in this repo is called "certified" for the PeTTa profile while
this ledger has open entries. Sorries are special-permission: a scoped window
was granted by Zar (2026-07-02) for M2/M3 special-form arms, on exactly that
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
- **ERR-1 (error surface)**: no-match axis case (c): a partial grounded
  predicate applied to unexpected input can raise a real Prolog error in
  PeTTa (vs HE structured `BadType` atoms vs empty). Unmodeled; needs native
  probes before any field is added.

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
