<!-- SPDX-License-Identifier: Apache-2.0 -->

# Divergence diagnosis — the "genuine divergent" rows (2026-07-05, advisor)

> **DEFINITIVE (2026-07-14) — quantified NARS/PLN boundary closed.**
> `diffbench/nars_witnesses.py` runs against a clean archive of current pinned
> PeTTa commit `6b7f52f064bd` and checks concrete values rather than accepting
> identical unreduced terms:
>
> - one-belief lookup: exact stored `((stv 1.0 0.9) (10))` in both engines;
> - two-belief ground deduction: exact `((stv 0.6 0.486) (2 10))` in both;
> - variable-quantified `==>` NARS deduction: exact
>   `((stv 0.6 0.486) (2 10))` in both;
> - variable-quantified PLN deduction: exact `((stv 0.6 0.81) (2 10))` in both.
>
> Root cause: PeTTa `==` is Prolog term identity and must run on open terms;
> PLeaTTa incorrectly delayed it until every nested variable was ground. Adding
> `==` to the machine's term-level non-strict operations closes both witnesses.
> Full `nars_tuffy.metta` and `pln_tuffy.metta` remain performance-disqualified.
> All older NARS notes below are superseded provenance.

> **DEFINITIVE (2026-07-06) — supersedes every NARS/PLN note below.**
> Two separate things were tangled together in the entries under this header;
> both are now resolved and verified side-by-side against native PeTTa.
>
> **(A) Real bug — the `isGround` builtin gate was too strict.** Structural
> list ops (`car-atom`, `cdr-atom`, `last`, `size-atom`, `decons-atom`,
> `list_to_set`, `exclude-item`, `unique-atom`, `msort`) act on the list
> *spine*, not its elements, but the machine only fired them when *all* args
> were ground. So on a list holding a free-variable element they returned
> empty where native returns the element/list — e.g.
> `!(car-atom ((Sentence ($z (stv 0.9 0.9)) (1))))` → native
> `(Sentence ($_ (stv 0.9 0.9)) (1))`, PLeaTTa (old) `[]`. **Fixed** by moving
> these ops to `nonstrictOps` (Machine.lean); seal re-elaborates green
> (`machineMirrorsSpecTotal_proved`, axioms `propext/Classical.choice/
> Quot.sound`, zero sorry); full corpus 140/176 AGREE, **0 regressions**.
>
> **(B) NOT a bug — nars_tuffy / pln_tuffy are a PERFORMANCE frontier.** The
> earlier "`==>`-with-variable inference doesn't terminate / runs away" framing
> is **wrong**. The inference is correct: `nars_direct` / `pln_direct` AGREE,
> and every isolated piece (`|-` both directions, `BestCandidate`, the
> derivations-collapse) matches native. The full `NARS.Query` derivation loop
> (maxsteps=100 over the 10-sentence kb) is simply far too expensive for the
> spec-grade machine: **native finishes in 0.3 s (`true,true`); PLeaTTa does
> not finish in 4.5 min at 150 M fuel.** Key tell: whenever the diff harness's
> native timeout is short, *native itself returns the raw unreduced
> `(NARS.Query …)` term — and PLeaTTa returns the identical raw term (they
> AGREE)*; native only yields the STV once given enough wall-clock. So this is
> the matespace/patrick class (correct semantics, spec-machine too slow), not a
> `==>` correctness defect. Witness caveat honestly stated: I could not exhibit
> a *small* full-loop case that both completes in PLeaTTa **and** returns a
> non-raw answer — every real-answer configuration is already past PLeaTTa's
> practical fuel — so (B) rests on isolated-piece agreement + the native-also-
> raw tell, not on a completing end-to-end witness.
>
> Everything under this line is the (partly superseded) investigation trail.

Ran each vs native PeTTa with minimal repros. Result: 4 real semantic roots
(5 files), and 2 files that are actually FUEL-LIMITED (reclassify), not bugs.

## ROOT 5 (CORRECTED) — MISSING builtins list_to_set / exclude-item -> nars_tuffy, pln_tuffy
Initially I mislabeled these "just performance (fuel)". A WITNESS TEST
disproved that: even a 1-sentence kb + maxsteps=1 exhausts fuel, while native
is instant. Isolated root:
    !(list_to_set (1 2 2 3))   native: (1 2 3)   PLeaTTa: (list_to_set (1 2 2 3)) [inert]
    !(exclude-item 2 (1 2 3))  native: (1 3)      PLeaTTa: (exclude-item 2 (1 2 3)) [inert]
Both are absent from pleattaTable (registered funs in PeTTa's metta.pl:303-307
list_to_set / exclude-item). NARS.Derive prunes its task queue every step via
`(LimitSize (exclude-item ... (list_to_set (append $Tasks $derivations))) ...)`;
with these inert, the task-list TERM grows unboundedly across the derivation
recursion -> fuel exhaustion. So nars/pln_tuffy are GENUINE divergences
(missing builtins), NOT performance. Fix: add list_to_set (dedup, order-
preserving) and exclude-item (remove all equal to arg) to pleattaTable; also
verify LimitSize/append evaluate. Lesson: the clean machine's "fuel exhausted"
message can mask a semantic bug (unevaluated op causing unbounded growth) —
always witness-test before calling something performance.

## ROOT 1 — callDyn cannot dispatch COMPILE-TIME SPECIAL FORMS as HOF args
Files: roman_test (cons), he_evaluation (println!). Highest value (2 files).
Repro (no lib needed):
    (= (apply2 $f $x $y) ($f $x $y))
    !(apply2 cons 1 (2 3))
  native:  (1 2 3)      PLeaTTa: (cons 1 (2 3))   [inert]
Why: `cons` is a compile-time special form (Compile.lean:99 special set, :148
`("cons",[h,t])`), NOT a pleattaTable grounding. Bare `!(cons 1 (2 3))` works
(compiled statically). But under `callDyn` (hd=$f resolves to `cons` at
runtime), the dispatch is: defined-clause? no. `lookup gt "cons"`? none (it's
not a table op) -> falls to DATA. So `(cons x y)` stays inert.
Fix direction: callDyn's symbol path must ALSO recognize the special-form
head symbols (cons, println!, decons, if, let, ... the compile special set)
and route them to the same lowering the compiler uses — i.e. re-enter
compileApp/compileExpr on `(f args)` at runtime, not just check the grounding
table. (roman_test also uses map-flat/fold with `+` which works, confirming
only the special-form heads break.)

## ROOT 2 — catch / if-error / return-on-error produce NO answer
File: he_error. Repro (in examples/, so ../lib resolves):
    !(import! &self ../lib/lib_he)
    !(let $r (catch (+ 40 2)) (if-error $r Error $r))
    !(return-on-error 5 6)
  native:  true, 42, 6      PLeaTTa: True only  (the two error bangs vanish)
Why: the catch/if-error/return-on-error lib_he pipeline yields no answer
(branch dies) rather than the value. Likely `catch` (translator.pl:293-301)
or the Error-term shape the lib matches on is not what PLeaTTa's catch/eval
produces, so `if-error`/`return-on-error`'s match arms never fire. Debug the
Error-value representation catch returns vs what lib_he pattern-matches.

## ROOT 3 — `find` match bindings do not propagate out of an `if` condition
File: spaces_find. Repro:
    !(import! &self ../lib/lib_spaces)
    (friend a b)
    !(collapse (if (find &self (friend $a $b)) (Found $a $b) None))
  native:  ((Found a b))     PLeaTTa: ((Found $a $b))   [vars UNBOUND]
Why: `find` (lib_spaces, wraps match) succeeds, but the substitution binding
$a=a,$b=b does not reach the THEN branch. The `if` condition's bindings must
flow into the then-goals; PLeaTTa evaluates the condition for truth but drops
its unifier. Check the `if`/ifTE compile: the condition's bindings have to be
kept when the True branch runs (not re-fresh the branch).

## ROOT 4 — `unquote` over-reduces outside a quote context
File: he_quoting. Repro:
    !(import! &self ../lib/lib_he)
    !(repr (unquote 42))
  native:  "(unquote 42)"    PLeaTTa: "42"
Why: PLeaTTa reduces `(unquote X) -> X` unconditionally; native keeps
`(unquote …)` inert unless inside a `quote`/eval context. Narrow: make
unquote inert as data outside quote (it is a marker consumed by quote, not a
standalone reducer).

## Priority for Codex
Root 1 (HOF special-form dispatch) — 2 files, clean fix, highest value.
Root 3 (if-condition binding propagation) — 1 file, likely small + important
(binding flow is core). Root 2 (error pipeline) and Root 4 (unquote) are
narrower. nars/pln_tuffy — reclassify, don't debug as bugs.


## UPDATE (2026-07-05) — Root 5 was PARTIAL; a DEEPER NARS bug remains
list_to_set/exclude-item are fixed and AGREE in isolation. But the NARS
INFERENCE mini-case still fails, verified after the fix:
- 2-sentence kb, single rule deduction, maxsteps=1: exhausts fuel even at
  40M budget (a single deduction cannot legitimately need >40M steps ->
  RUNAWAY, not performance).
- 1-belief lookup `(NARS.Query ((Sentence ((--> Edward smokes) stv) (10)))
  (--> Edward smokes) 1)` -> PLeaTTa `()` (empty, WRONG); native returns the
  belief `((stv 1.0 0.9) (10))`.
So NARS.Query/NARS.Derive has a second bug beyond the missing builtins: the
belief-matching/derivation step either loops or fails to bind. Next probe:
isolate NARS.Derive's single-step body (the `superpose $Beliefs` + `|-` rule
+ collapse) on a 1-belief input and find which sub-goal returns empty / never
terminates. The witness that must go green: the 1-belief lookup returning the
stored stv, THEN the 2-sentence deduction.

## PRE-PUBLISH BUG INVENTORY (2026-07-05, witness audit of the perf frontier)
perf_witnesses.py ran a small same-family witness per performance-frontier
file. Result: the "performance" bucket was NOT all honest.

MASKED BUGS (witness FAILS even small — reclassify from perf to BUG):
- hyperpose_primes: witness LEATTA-NOOUT (0 answers) — masked bug.
- invertpeanoplus: witness LEATTA-TIMEOUT at target 2 — runaway even tiny
  (inverted/moded Peano plus).
- patrick_iterate_quad: witness DIFF-VAL — WRONG value at small n
  (lib_patrick iterate + dynamic step function).
- pln_roman: witness LEATTA-NOOUT (native 2, PLeaTTa 0) — same PLN inference
  bug family as pln_tuffy.
GENUINE PERFORMANCE (witness AGREES — semantics correct, just scale): fib,
fibadd, he_minimalmetta, holbenchmark, matespace{,2,fast}, peano{,fast},
permutations, scale, tilepuzzle (12 files). These are honest frontier.

So the correctness bugs remaining before publish:
1. NARS/PLN inference (nars_tuffy, pln_tuffy, pln_roman): NARS.Query filter /
   PLN.Query path — NARS.Derive itself is CORRECT (1-belief agrees); bug is
   the wrapper filter (empty) + rule-application runaway.
2. hyperpose_primes: NOOUT even small.
3. invertpeanoplus: runaway even at target 2 (inverse arithmetic).
4. patrick_iterate_quad: wrong value small (dynamic step fn).
The 5 fixed this session (he_error/he_evaluation/he_quoting/spaces_find/
roman_test) are AGREE. Everything else is genuine perf, deferred (specializer/
FFI), or out-of-scope (repl/mutex).

## UPDATE (2026-07-05, Codex/Oruzi) — masked pre-publish bugs fixed or reclassified

The witness failures listed above are no longer current:
- `invertpeanoplus.metta`: original file now `AGREE` (5/5). Root fix:
  function-clause resolution now narrows input arguments and the output slot
  together at clause entry, matching native `f(args..., Out) :- Body`; unknown
  constructor-like heads are data instead of delayed dynamic calls.
- `hyperpose_primes.metta`: small computed-list and evaluated-branch
  hyperpose witnesses now `AGREE`; original prime row is an honest timeout.
- `patrick_iterate_quad.metta`: small `quad-sum 20` witness now `AGREE`.
  Root fix: `last` is a real tuple builtin; original `n=1000` row is an
  honest timeout.
- `pln_roman.metta`: explicit small `PLN.Query ... 2 4 4` witness now
  `AGREE`. Root fix: `case` arms and rule heads use structural pattern
  compilation instead of ordinary expression compilation, so nested variables
  such as `$Term`/`$TV` bind.
- `nars_tuffy.metta` / `pln_tuffy.metta`: small NARS existing-belief,
  one-step deduction query, and PLN query witnesses now `AGREE`; full Tuffy
  rows remain timeouts.

Focused regression status after this update: the prior five fixed rows
(`he_evaluation`, `roman_test`, `he_quoting`, `spaces_find`, `he_error`) still
`AGREE`; `invertpeanoplus` is now `AGREE`; the remaining large rows above are
performance-frontier, not masked correctness bugs.


## VERIFY (2026-07-06 advisor) — masked-bug cleanup status
CONFIRMED FIXED (full file AGREE): invertpeanoplus (let-pattern narrowing),
plus the earlier 5 (he_error/he_evaluation/he_quoting/spaces_find/roman_test).
CONFIRMED GENUINE PERF (small witness agrees at appropriate scale):
patrick_iterate_quad, pln_roman, hyperpose_primes (op fixed; ~100-prime tests
AGREE; only ~1000-prime test fuel-limited — the audit witness picked primes too
big).
CLOSED 2026-07-14 — this historical blocker was the strict `==` scheduling
bug described at the top of this file. Ground and variable-quantified NARS/PLN
deductions now return exact values; only the full target-scale files time out.


## PRECISION (2026-07-06; superseded 2026-07-14) — NARS boundary
The ground deduction worked while variable-quantified implication did not complete.
The later clean-profiler trace identified a delayed open-term `==`, and the
term-identity scheduling fix closed the variable NARS and PLN witnesses.
