# ORDER-1 design note — PeTTa's evaluation-order commitment (T2.3 spike)

## (a) Probe battery (native PeTTa, 2026-07-02, 7 probes)

| Program | Result | Commitment revealed |
|---|---|---|
| `(= (h1) (+ 1 2))` → `!(h1)` | `3` | grounded calls in rule bodies evaluate |
| `(= (h2) (wrapX (+ 1 2)))` | `(wrapX 3)` | args evaluate even under UNDEFINED constructor heads |
| `(= (h4) (quote (+ 1 2)))` | `(+ 1 2)` | `quote` guards its argument from evaluation |
| `(= (mk) (pairX (f1) (+ 2 2)))`, `(= (f1) alpha)` | `(pairX alpha 4)` | defined calls and grounded ops both evaluate inside constructors |
| `(= (b1) (bx (a2)))`, `(= (a2) done)` | `(bx done)` | nested defined call evaluates; constructor shell survives |
| `(= (add2 $x $y) (+ $x $y))` → `!(add2 1)` | `(partial add2 (1))` | under-application reifies as a partial object (MODE/currying axis, not order) |
| `(= (deep) (outerX (innerX (+ 3 4))))` | `(outerX (innerX 7))` | evaluation descends through arbitrarily NESTED constructors |

**The model**: PeTTa evaluation is *normalize-once, innermost, quote-guarded*.
Every subterm evaluates bottom-up (call-by-value), regardless of whether the
enclosing head is defined — the only shields are `quote`-style noeval
positions. What makes it "one-pass" is WHEN: subterm evaluation is fixed at
clause compilation (each call becomes a Prolog goal); results are final and
never re-scanned. Contrast: the HE four-register machine re-drives workspace
reducts outermost-to-fixpoint; the minimal kernel evaluates args by TYPE mask
(`argMask`: skip `Atom`-typed positions) and suppresses re-driving only for
`(-> ... Atom)` returns (`returnsAtom`).

## (b) Strategy-style mechanism, mapped

The order dimension is exactly the GSLT `Strategy` shape
(`MeTTaIL/Semantics/Strategy.lean`: `Label → Nat → Bool`, proven-sound hook):
a position-permission predicate deciding where evaluation may descend.

- **PeTTa instance**: `fun label _pos => label ∉ noevalHeads` where
  `noevalHeads` = `quote` + the stdlib's `(-> ... Atom ...)`-argument
  positions — i.e., permission almost-everywhere. Plus the one-pass
  discipline: treat EVERY result as final (`returnsAtom ≡ true` globally).
- **HE instance**: the existing type-directed `argMask`/`returnsAtom` pair —
  already a strategy in disguise. This is the design's key economy: the
  kernel ALREADY routes evaluation-order decisions through two small
  functions; ORDER-1 = making those two functions profile-parametric
  (strategy as data), not rebuilding the driver.
- **Spec side**: a `Strategy`-parametric innermost normalizer
  `normalizeOnceP (strat) (cfg kb) : Atom → Atom` (structural recursion:
  normalize children where permitted, then apply one head step, no re-scan),
  with (i) `he`-instance theorem recovering the current machine behavior on
  the shared fragment (the `oneStepStrat_all` pattern), and (ii) the petta
  instance stated against the trichotomy theorems we already have.

What stays data: `noevalHeads` (a list), the profile fields. What becomes a
verified parameter: the descent predicate + the re-drive switch.

## (c) Predicted scoreboard conversions

ORDER-1-tagged files expected to flip on the kernel arm alone:
`casenew`, `caseconstrain`, `foldall`, `forall`, `hyperpose_primes`,
`myinterpreter`, `nestedcons`, `supercollapse`, `superpose_nested`,
`callquoteevalreduce2` (10 files), plus likely knock-on wins in DIFF-COUNT
files whose multiplicity divergence stems from re-driving (est. 3–6 more).
Predicted in-fragment agreement after the kernel arm: ~55% → ~65% of the
expanded (165-file) fragment. NOT converted: MODE-1 (relational), TYPES,
TRANSLATOR, ERR — different axes.

## (d) Go/no-go

**GO — confidence ~80%.** The commitment IS Strategy-shaped (probe (b2/d4)
wrinkles from the DIV registry are subsumed by innermost-once + quote-guard).
Effort: kernel arm (argMask/returnsAtom profile branches + scoreboard) ≈ 1–2
sessions; spec-side normalizer + he-recovery theorem + petta correspondence ≈
1–2 weeks of proof work (the correspondence against the four-register machine
is the long pole — scope it to the reduct core first, as Correspondence.lean
did). Risk (the 20%): the partial-application reification (probe 6) leaks
into order-sensitive corpus files, coupling ORDER-1 to the MODE/currying
axis; mitigation: keep `(partial f args)` reification as a separate profile
arm if it surfaces.

Recommended next chunk: kernel arm first (measured win, small), spec
normalizer second, correspondence third.


## ADDENDUM (C2.1 re-diagnosis, same day) — the tag was hiding two families

Executing the kernel arm triggered the stop rule in the best way: probing
showed the kernel ALREADY implements innermost-descend + quote-guard (6/7
probe shapes agreed before any change — the type-directed argMask/returnsAtom
machinery was the strategy all along). The "ORDER-1" scoreboard family
decomposed under per-file diffs into:

- **NONDET-1** (the real finding): PeTTa's nondeterminism is Prolog
  backtracking with BRANCH-LOCAL failure. `superpose` spreads its RAW tuple
  elements (probe: `(superpose (collapse (f)))` spreads literally, yielding
  the `collapse` symbol) and evaluates each in its own branch — an
  empty-yielding element kills only itself (probe: `(superpose ((dead) 7))`
  → `7`). Strict CBV tuple evaluation instead poisons the whole superpose.
  Fix shipped: `superpose`/`hyperpose` as quoteArgs + `(-> Atom _)` sigs in
  the petta profile (raw spread; the driver evaluates each item per-branch).
- **Noeval aggregators**: `foldall`/`forall` are PeTTa TRANSLATOR-level
  special forms (compiled to Prolog `foldall`/`forall` over the generator
  GOAL — call-by-name). Shipped as prelude rules with `Atom`-typed generator
  positions + `collapse`, mirroring the translator's findall semantics.

Remaining genuinely-ORDER content: none identified at kernel level; the
one-pass/fixpoint distinction is observationally covered by the type-directed
mechanism on the corpus. The spec-side Strategy normalizer (C2.2) remains
worthwhile as the FORMAL account of that mechanism, with the addendum that
its petta instance must also carry the NONDET-1 branch-local-failure
semantics (spread-raw superpose) to be faithful.
