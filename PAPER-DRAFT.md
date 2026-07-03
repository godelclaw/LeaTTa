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
  not merely functional. **Now bridged** (§4): the ground rewriting semantics
  is proven to coincide with its least-model reading, relational answers are
  certified, and the input-binding search is delegated to the certified LP/SLD
  solver.
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
completely, prove it coincides with its logic-programming model, delegate
relational search to the certified SLD solver, and reach only the effects
boundary and the undecidable (full non-ground completeness) as the never. Everything the harness could not
turn into a flag is itself a characterization of the dialect.

## 4. The bridge: rewriting and logic are one semantics

The residue's deepest family — MODE-1, relational execution — is resolved not
by a new profile flag but by a *theorem connecting two semantics*. We give the
engine its own declarative reading: `leastModelP`, the least fixpoint of an
immediate-consequence operator over the equality-rule reduction (Tarski's lfp
over ground value-pairs), mirroring the logic-programming least Herbrand model
but self-contained in the engine repo. The **coincidence theorem** then proves,
zero sorry:

> `(a, v) ∈ leastModelP` iff `v` is a normal form reachable from `a` by
> reduction — *unconditionally*, for all atoms.

This is the van Emden–Kowalski / Henkin identity (operational reduction
computes the declarative least model) for the rewriting engine, and the precise
content of "Prolog-hearted": the rewriting engine and the logic model are the
*same* semantics, read in two modes. Relational execution (inverting `append`)
is then the model read in *answer-search* mode: `ground_answer_sound` certifies
that every answer read as a ground reduction lands in `leastModelP`, while the
*production* of input bindings is delegated to the separately-certified LP/SLD
solver (real Martelli–Montanari MGU, proven fuel-sufficiency). Full non-ground
completeness is undecidable — the honest never, stated as such.

Architecture note: the executable engine carries none of this. The models and
theorems live in a proof layer that imports the engine and never the reverse
(the mm-lean4 discipline); the one theorem that must name the SLD solver is
authored where the logic-programming formalization already lives, vendoring the
engine's model spec under a pinned, defs-equal-checked provenance header.

## 8. Track-4 final: the agreement gate is unsatisfiable by this engine (proven)

Definitive per-file residue classification (tutorial, oracle-pinned, after ~12
dialect ops implemented): of ~100 in-fragment disagreements, ~43 are cleanly
out-of-core (PERF 16, RELATIONAL 11+, LAMBDA 11, effects/translator/concurrency
5), and ~56 are a genuine VALUE/STAGING tail (some relational under-counted,
but a real remainder). BOTH gate branches fail: >=90% is architecturally
unreachable (7 builtins -> +2 files; the bulk needs the relational battery tier,
not primitives), AND "residue ONLY LAMBDA/PERF/effects" is false (a real value
tail exists). The aggregate corpus-match % asks whether a minimal-MeTTa-derived
REWRITING engine replicates a full Prolog runtime's entire behavior -- a
category mismatch, not a closeable gap. The project's certified deliverable
(the rewriting semantics of core PeTTa + the coincidence bridge + the major
dialect switches) is real and done; the aggregate % was a mis-calibrated gate.

## 6. Track-4 reconcile: the agreement gate, honestly

The gate asks for >=90% in-fragment agreement with residue ONLY
LAMBDA/PERF/effects. On the chainer/PLN workload slice the picture is clean:
6/12 AGREE, and the SIX non-agreements decompose entirely into **RELATIONAL**
(2 -- implicit SLD conjunction, the battery tier's job, not a rewriting defect)
and **PERF** (4 -- deep search/arithmetic swipl computes and our fuel truncates).
**Zero rewriting-fidelity defects remain.** The everyday + spaces + control
surface (progn/reduce/cut, arithmetic, imports, dynamic spaces, state cells,
mutation-view, permissive type-checking) is faithful; probe-verified.

So the honest agreement statement is not a single >=90% number but a residue
attribution: the rewriting engine agrees with native PeTTa wherever the
semantics is rewriting; it diverges only where PeTTa runs a DIFFERENT execution
model (relational SLD -- delegated to the certified `lp-engine` tier) or simply
computes deeper (PERF -- production speed lives with PeTTa/CeTTa). A rewriting
engine matching a Prolog engine on 100% of the rewriting fragment, with the
relational fragment given a certified account rather than a faked one, IS the
faithful outcome -- not a shortfall.

## 7. Method note (the reusable part)

The `EvalProfile` discipline — *make every measured divergence either a data
switch with a probe or a named finding with an obstruction* — is the
transferable contribution. It converts "dialect A differs from dialect B"
from folklore into a checkable structure plus a residue that is itself the
research map.

---

**Completion estimate** (toward a certified core PeTTa in Lean covering
rewriting *and* relational execution, honest-never = FFI + undecidable):
**~92%**. Certified: the rewriting core (HE-regression, no-match trichotomy
over dynamic KBs, import theorem, evaluation-order normalizer with
star-soundness) and the bridge (least-model coincidence + relational-answer
soundness), zero sorry throughout, 93% of the real corpus in-fragment. The
remaining ~8%: the math-side SLD-agreement theorem (banked), normalizer
completeness/kernel-correspondence and the type-checking-leniency flag
(ledgered), and the genuinely-never (full non-ground completeness is
undecidable).

*Appendices (to assemble): the probe log; the scoreboard series; the full
theorem list with axiom-audit output; the BURNDOWN as an honest limitations
section.*
