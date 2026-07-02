# A Certified Dialect Profile for a Prolog-Hearted MeTTa

**STATUS: internal draft. NOT for publication until reviewed.** Consolidates
PROFILE.md, BURNDOWN.md, ORDER1-DESIGN.md, TYPES-DESIGN.md, and the diffbench
scoreboard series. Companion to the prior architectural autopsy
(leatta-vs-leanpetta): where that paper argued *verify the semantics, not the
machine*, this one applies the rule to a second dialect and reports what the
dialect's semantics turned out to be.

## Abstract

Starting from a zero-sorry verified minimal MeTTa (a relation-first core with
an executable indexed kernel proven equal to its specification), we ask
whether a *different* MeTTa dialect — native PeTTa, a functional-logic engine
compiled to Prolog — can be certified in the same shape without forking the
core. Our answer is an `EvalProfile`: a small structure of measured semantic
switches through which one parametric reducer certifies both dialects. The
HE-conformance result is preserved by a regression theorem (`reduceAtomP_he`);
the PeTTa dialect is validated empirically against the upstream engine on 176
programs and formally by a machine-checked no-match trichotomy, an import
theorem, and a Strategy-parametric normalizer with star-soundness. Along the
way the differential harness forced the dialect's semantics into the open:
the switches that *could* be data (no-match failure, quote, arity, success
shape, nondeterminism spread) and the ones that *could not* (relational
execution, evaluation order in general), the latter being the paper's
findings about what "Prolog-hearted" means precisely.

## 1. The profile

`EvalProfile` fields, each justified by a live probe against the upstream
engine (the sole oracle; a prior compat-lane divergence registry served only
as a hypothesis catalog):

- `noMatchEmpty` — a defined head with no matching clause fails to the empty
  result (Prolog goal failure) rather than staying inert.
- `ifArity2` — two-argument `if` with an empty failure branch.
- `quoteStrips` — `(quote x)` reduces to `x`, its result NOT re-evaluated
  (realized via the kernel's existing `(-> Atom Atom)` no-re-drive typing,
  not an evaluation-order hack — the elegant reuse of the paper).
- `successTrue` — space mutations return `true`, not unit.

The regression theorem `reduceAtomP heProfile = reduceAtom` (proved) keeps
the original HE certification untouched: additive modules only, the guard
theorem unconditional.

## 2. Two validations

**Empirical.** A differential harness runs each of 176 native programs
through the upstream engine and through the certified core under the PeTTa
profile, comparing result multisets after presentation-only normalization.
Never is the certified core's own output asserted as ground truth. A fragment
classifier reports what fraction is *core PeTTa* (pure rewriting + spaces,
excluding FFI): after admitting imports and dynamic spaces, **93% of the
corpus is in-fragment**, of which a rising fraction agrees exactly as dialect
arms land.

**Formal.** Machine-checked, zero sorry, standard axioms only:
- the no-match **trichotomy** (undefined-inert / defined-fail / reduces),
  against the indexed kernel's dead-branch condition, generalized to dynamic
  knowledge bases (imports and runtime `add-atom`);
- the **import theorem**: runtime `&self` imports fire exactly as
  concatenated rules would — "import is rule-space concatenation" as a
  theorem;
- a **Strategy-parametric normalizer** capturing innermost, quote-guarded,
  branch-local-failure evaluation, with star-soundness (the scheduler is
  bookkeeping over the named rewriting relation) and a recovery anchor to the
  certified head-step at the trivial strategy.

## 3. What the differential harness discovered

The value was as much in what *resisted* becoming a profile flag. Residual
disagreements, attributed by family:

- **MODE-1 (relational execution)** — PeTTa runs equality rules as Prolog
  clauses in ANY instantiation mode; corpus programs invert `append` through
  unbound arguments. A rewriting kernel cannot do this without narrowing.
  This is the core meaning of "Prolog-hearted": PeTTa is functional-*logic*,
  not merely functional. Certifiable only atop a Prolog/SLD layer (the
  in-tree oracle contract is the entry point) — the sequel campaign.
- **NONDET-1 (branch-local failure)** — `superpose` spreads its *raw* tuple
  and evaluates each element in its own backtracking branch, so an
  empty-yielding element kills only its branch. This one *did* become data (a
  quote-args + typing arm) and is now part of the certified normalizer.
- **ORDER (evaluation commitment)** — probed to be normalize-once, innermost,
  quote-guarded; the kernel already realizes this through type-directed
  descent, so "ORDER-1" dissolved on inspection into NONDET-1 plus noeval
  aggregators. The normalizer is its formal account.
- **TYPECHECK-1 (leniency)** — the HE kernel enforces argument type-checking;
  PeTTa is permissive. A pending one-field dialect switch.
- **TRANSLATOR / LAMBDA / PERF** — implementation-specific surfaces
  (specializer, `|->` lambdas, deep-recursion cost) at or beyond the language
  boundary.

The honest ceiling, stated: we certify PeTTa-the-rewriting-semantics nearly
completely and the effects boundary never. Everything the harness could not
turn into a flag is itself a characterization of the dialect.

## 4. Method note (the reusable part)

The `EvalProfile` discipline — *make every measured divergence either a data
switch with a probe or a named finding with an obstruction* — is the
transferable contribution. It converts "dialect A differs from dialect B"
from folklore into a checkable structure plus a residue that is itself the
research map.

---

*Appendices (to assemble): the probe log; the scoreboard series; the full
theorem list with axiom-audit output; the BURNDOWN as an honest limitations
section.*
