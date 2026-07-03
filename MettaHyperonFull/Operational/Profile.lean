/-
Module: MettaHyperonFull.Operational.Profile
Layer: Operational
Purpose: Evaluation profiles. An `EvalProfile` packages the measured semantic
  divergences between MeTTa dialects as first-class switches, so one parametric
  reducer (`SemanticsP.reduceAtomP`) can certify several engines. `heProfile`
  reproduces the existing HE 0.2.10 spec (`Semantics.reduceAtom`) exactly —
  see `SemanticsP.reduceAtomP_he`. `pettaProfile` targets native PeTTa
  (github.com/patham9/PeTTa). ORACLE DISCIPLINE: every field value is
  justified by a live probe against NATIVE PeTTa, the sole oracle; DIV ids
  from the petta-he-profile registry are background hypotheses only (that
  registry was measured on PeTTa's --he compatibility lane, not native).
  The evaluation-ORDER dimension (PeTTa's compile-time eagerness / one-pass
  results) is deliberately NOT a Bool here: it is expected to be structural
  and will be modeled Strategy-style (cf. MeTTaIL/Semantics/Strategy.lean).
Imports: none (pure data)
Trusted boundary: human-reviewed spec (field values are empirical claims about
  engines; each is tied to a live native-PeTTa probe)
Main exports: EvalProfile, heProfile, pettaProfile
Open obligations: post-match one-pass-vs-fixpoint and error-surface leniency
  are documented but not yet switched (BURNDOWN.md).
-/

namespace Metta

/-- Semantic switches distinguishing MeTTa engine dialects.

Fields are the *measured* divergence axes:

* `noMatchEmpty` — the no-match axis is THREE-way; this flag covers the
  first two, the third is ledgered:
  (a) head with NO rules: inert data in both dialects (probe:
      `(nosuchfunc 5)` inert in both) — flag-independent;
  (b) head WITH rules, none matching: `true` = empty result set (Prolog
      goal failure; native PeTTa, probe: `(= (g 1) one)` then `(g 2)` →
      nothing); `false` = inert normal form (HE; the foundational
      divergence, he-petta paper "source-head no-match");
  (c) partial grounded predicate on unexpected input: PeTTa can raise a
      real Prolog error rather than fail — NOT modeled by this flag
      (error-surface axis, BURNDOWN.md).
  Out-of-fragment heads always stay inert/uninterpreted — never an
  "unsupported feature" error.
* `ifArity2` — accept 2-argument `if`: `(if c t)` reduces to `t` when the
  condition holds and to the empty result when it fails (native PeTTa,
  DIV-011; probe confirmed both branches). `false` = 2-arg `if` is not a
  special form (HE errors with IncorrectNumberOfArguments).
* `quoteStrips` — `(quote x)` reduces to `x` (native PeTTa; probe:
  `!(quote (+ 1 2))` → `(+ 1 2)`). `false` = `quote` is preserved (HE).
  NOTE (day-one approximation, ledgered): in PeTTa the stripped argument is
  NOT re-evaluated (one-pass compilation); in the four-register machine the
  reduct re-enters the workspace, so this switch alone over-reduces
  `(quote redex)`. The gap is the one-pass/fixpoint axis below. -/
structure EvalProfile where
  noMatchEmpty : Bool
  ifArity2 : Bool
  quoteStrips : Bool
  /-- Success shape of space mutations (`add-atom`/`remove-atom`/`import!`):
  `true` = they return the boolean `true` (native PeTTa, probe 2026-07-02);
  `false` = they return the unit `()` (HE; DIV-006 family). -/
  successTrue : Bool
  /-- Enforce declared argument type-checking (HE `BadArgType`). `true` = HE
  (strict); `false` = native PeTTa (permissive — type-checking is optional in
  PeTTa; probe: PeTTa evaluates calls HE rejects). Strict remains available
  when the user declares types. -/
  typecheckStrict : Bool
  /-- Body-internal committed choice (PeTTa `cut`/`!`): `(cut)` prunes the
  pending sibling branches of the enclosing evaluation (probe 2026-07-03:
  `!(cut)` -> `true`; `match-single` commits to its first match). `false` =
  `(cut)` is an ordinary inert atom (HE). -/
  cutCommits : Bool := false
  /-- `import!` result discipline (probe 2026-07-03, per target kind): a
  `.metta` file path answers `true`; `../lib/` modules and bare names answer
  NOTHING (Prolog library mechanism). `false` = HE always answers success. -/
  importSilent : Bool := false
deriving Repr, BEq, Inhabited

/-- Hyperon-Experimental 0.2.10 — the dialect certified by the existing
`Semantics.reduceAtom`; `SemanticsP.reduceAtomP_he` proves the equivalence. -/
def heProfile : EvalProfile :=
  { noMatchEmpty := false, ifArity2 := false, quoteStrips := false,
    successTrue := false, typecheckStrict := true }

/-- Native PeTTa (the lane PeTTaChainer and native-PeTTa agents run). Each field value
is an empirical claim; see the module docstring for probes/DIV ids. -/
def pettaProfile : EvalProfile :=
  { noMatchEmpty := true, ifArity2 := true, quoteStrips := true,
    successTrue := true, typecheckStrict := false, cutCommits := true, importSilent := true }

end Metta
