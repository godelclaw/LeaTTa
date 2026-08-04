# Archived PLeaTTa custom compiler/SLD lane

This branch preserves the experimental PLeaTTa implementation introduced by
`747153b` and all subsequent compiler, machine, independent-semantics, proof,
test, and work-in-progress material through 2026-08-04.  Its pre-diversion
parent is `8be8fac`.

The branch is a historical and empirical reference.  It is not the foundation
for continued PLeaTTa verification, and its proof modules must not be imported,
cherry-picked, or treated as inherited evidence in the replacement design.

## Reason for archival

The lane independently implemented both halves of pinned PeTTa:

1. a Lean compiler restating the behavior of `translator.pl`; and
2. a custom SLD-like machine for the resulting private goal language.

It did not execute pinned `translator.pl`, reuse the generic LP SLD kernel, or
make the existing Prolog control layer a real extension of that kernel.  A
later independent Prolog trace/goal semantics then created a second PLeaTTa
model in order to justify the first.  The resulting bridge work multiplied
representations and proof obligations without closing the universal
source-to-observation theorem.

Continued work should instead establish one shared executable LP/Prolog layer,
interpret or mechanically compile pinned PeTTa's Prolog source into that layer,
and keep unsupported SWI facilities behind an explicit boundary.

## Material worth mining as requirements or evidence

Mine behavior, test cases, and independently reusable ideas only.  Reimplement
them against the shared LP/Prolog types rather than retaining dependencies on
this branch.

### Empirical assets

- pinned-PeTTa and SWI runners;
- differential corpus infrastructure and ordered-output normalization;
- source-shaped fuzz generation and minimized counterexamples;
- compiler and Prolog obligation ledgers;
- host fixtures, typed transcripts, replay checks, and provenance summaries;
- exact source anchors into `translator.pl` and `metta.pl`.

### Behavioral regressions to preserve

- `findall/3` copies residual variables once per solution, preserving sharing
  within a solution and separation between solutions;
- catch streams preceding answers and selects catchers using throw-time
  bindings while reconstructing recovery from the entry environment;
- soft cut, case, and ordinary cut preserve pinned clause and answer order;
- logical-update snapshots retain clauses visible at call entry while
  assert/retract effects survive backtracking;
- retract scans in source order and uses unification rather than exact syntax;
- float identity, including NaN, follows the pinned Prolog behavior;
- source `#nil`, proper lists, partial values, and reserved internal compounds
  remain distinct;
- Predicate values do not accidentally register executable functions;
- captured partial applications retain their closure environment;
- `eval` and `translatePredicate` preserve pinned argument staging and runtime
  value provenance;
- host calls remain provenance-visible and replayable without an allowlist
  being confused with a proof boundary.

### Semantic ideas to reconsider generically

- demand-driven, finite-prefix observations that distinguish exhaustion,
  exception, and an open/divergent continuation;
- explicit ordered answer multiplicity and effect order;
- structurally distinct cut, exception, and collection delimiters;
- persistent state outside backtrackable search state;
- logical-update generations and call-start clause snapshots;
- globally fresh clause and `copy_term` allocation with sharing and separation
  theorems;
- exception unwinding that prunes discarded cursor resources exactly once;
- provider interfaces that cannot manufacture locally certified answers;
- anti-vacuity witnesses that reject answer reordering, fair interleaving,
  wrong cut scope, stale freshness, eager collection, and restored world state.

### Process lessons

- A machine-to-Step theorem is not language adequacy when the Step relation
  shares the machine's helper functions.
- Source anchoring and differential agreement are evidence, not a compiler
  refinement theorem.
- A producer repeatedly proving facts that packaging erases is evidence that
  the representation boundary is wrong, not a reason to add another carrier.
- Local PASS counts are not completion percentages.  Work must be governed by
  the top-level theorem and by executable reference parity.
- When a language is implemented as a Prolog program, first attempt to execute
  that program in the shared verified Prolog layer; do not paraphrase it into a
  language-specific machine without a demonstrated need and a refinement plan.

## Material not to carry into the replacement

- PLeaTTa-specific bridge and carrier modules;
- the custom compiler equations as the authoritative translator;
- the custom alternative-bank machine as the verified runtime foundation;
- duplicated resolver, MGU, term, substitution, or clause representations;
- proof ledgers whose PASS rows certify only the archived representations;
- generated theorem counts or coverage summaries as inherited progress.

The replacement may cite this branch to locate a test or counterexample.  Its
proof starts again from the shared LP/Prolog foundation.
