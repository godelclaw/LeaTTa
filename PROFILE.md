# PROFILE — what PeTTa semantics is, versus HE (the crux document)

This repo extends LeaTTa with a profile-parametric spec reducer
(`MettaHyperonFull/Operational/{Profile,SemanticsP}.lean`). The formal answer
to "what is native PeTTa, semantically, relative to HE 0.2.10" is the
`EvalProfile` structure plus the ledgered structural axes in `BURNDOWN.md`.

## The two engines in one sentence each

- **HE** is a rewriting engine: unmatched applications stay inert as data,
  post-match templates re-reduce to fixpoint, `quote` is preserved, arities
  are strict.
- **Native PeTTa** is a functional-logic engine compiled to Prolog: a defined
  head with no matching clause fails to the empty result, evaluation points
  are fixed at compile time (results are not re-driven), `quote` strips, 2-arg
  `if` is lenient with an empty failure branch.

## Field-by-field, probe-by-probe

| Axis | HE | native PeTTa | Evidence (native lane) |
|---|---|---|---|
| defined head, no clause matches | inert | empty | probe `(= (g 1) one)`; `!(g 2)` → no result |
| undefined head | inert | inert | probe `!(nosuchfunc 5)` → `(nosuchfunc 5)` both |
| `quote` | preserved | strips (result NOT re-evaluated) | probe `!(quote (+ 1 2))` → `(+ 1 2)` |
| 2-arg `if` | arity error | then-branch / empty | probes `!(if (== 1 1) yes)` → `yes`; false → nothing |
| argument evaluation before match | eager (minimal-MeTTa) | eager | probe `(f (z))` → `matched-zero` on BOTH — a shared behavior, not a divergence |
| result re-driving (one-pass vs fixpoint) | fixpoint | one-pass | structural — NOT a flag; see BURNDOWN ORDER-1 |
| error surface on bad grounded input | structured error atoms | can be Prolog error | unmodeled — BURNDOWN ERR-1 |

Oracle discipline: the sole oracle for pettaProfile is live native PeTTa
(`~/repos/PeTTa`, `test_runner.sh` lane). The petta-he-profile DIV registry is
a hypothesis catalog measured on the `--he` lane — background reading only.

## Theorems

- `reduceAtomP_he / reduceArgsP_he` (`SemanticsP.lean`): at `heProfile` the
  parametric reducer is EQUAL to the certified original `reduceAtom` —
  proven, zero sorry. The HE certification is untouched (original modules
  unmodified; new modules additive).
- `dialectStep_he`: no dialect arm fires at the HE profile (non-recursive).

## Governance

- Local branch `petta-profile`; no push without the maintainer's approval.
- **Upstreaming condition (SR-bridge compatibility):** a sibling effort's
  ~28.8k-line SR bridge imports `MettaHyperonFull.*`. If LeaTTa-petta is ever
  upstreamed to zariuq/LeaTTa: `heProfile` must remain the default and
  definitionally equal to the original semantics (`reduceAtomP_he` is the
  guard theorem — it must never become conditional), or the SR arc takes a
  ripple.
- Sorry policy: see BURNDOWN.md header. Nothing is "certified" for the PeTTa
  profile while the ledger is open.
- Scoreboard: `diffbench/scoreboard.tsv`, appended per run; out-of-fragment
  and parser-gap files are counted, never dropped.
