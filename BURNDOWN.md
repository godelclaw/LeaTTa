<!-- SPDX-License-Identifier: Apache-2.0 -->

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

## PLeaTTa 95% tranche — Family A PERF evidence (2026-07-04)

Baseline from `diffbench/run-p19.log`: all 15 Family-A files are in-fragment
and still `LEATTA-TIMEOUT`: `fib`, `fibadd`, `holbenchmark`,
`hyperpose_primes`, `invertpeanoplus`, `matespace`, `matespace2`,
`matespacefast`, `patrick_iterate_quad`, `peano`, `peanofast`,
`permutations`, `scale`, `tabling_fib`, `tilepuzzle`.

Crux probes (`peano`, `peanofast`, `tabling_fib`) all bucketed as timeout with
native answers present. Source anchors for the Peano crux: `translator.pl`
compiles `collapse` as `findall` and `once` as Prolog `once/1`; `match`
dispatches to `spaces.pl`'s dynamic predicate call. The first retained fix is
therefore `match` branch pruning: skip self-space atoms whose pattern is
syntactically impossible to unify, mirroring Prolog predicate indexing while
leaving the unification goal as the checked branch body.

Measured `peano` scaled profile, deep-step counter:

- Before pruning: K=25 11,982 steps / 0.20s; K=50 56,432 / 3.10s; K=75
  149,007 / 15.31s; K=100 305,332 / 48.13s; K=150+ timed out.
- After retained `match` pruning: K=25 9,057 / 0.30s; K=50 34,332 / 2.73s;
  K=75 75,857 / 14.21s; K=100 133,632 / 43.25s; K=150+ still timed out.

Rejected attempts:

- Substitution-chain rewrite: timed out at K=100 where the prior machine
  completed; reverted.
- Parallel exact-key list for `&self`: no step reduction and no wall
  improvement (K=50 remained 34,332 steps; K=100 remained 133,632 steps);
  reverted.

Status: no coverage gain claimed yet. The pruning is a real source-anchored
mechanism and reduces search, but it is not enough to flip Family A. The next
Family-A pass should target the remaining over-enumeration / committed-choice
shape in the compiled Peano path, not add oracle leaves or per-file cases.

Follow-up attempts before applying the family stop-rule:

- No-default `case` now follows the native translation shape
  (`Gk, KeyGoal, IfGoal` rather than eager scrutinee collection). This is kept:
  K=50 improved 34,332 → 31,732 steps; K=100 improved 133,632 → 123,432
  steps. K=150 and K=300 still time out.
- Lazy `match` choicepoint via `Alt` looked source-faithful but did not reduce
  measured Peano steps and worsened wall time; reverted.
- Changed-flag substitution loop and package-level `-O3` rebuild did not
  improve K=100 wall time; reverted.

Stop-rule applied for now: Family A has yielded real source-grounded cleanup
but no file flips. Resume later only with sharper evidence for substitution
dominance or a clearly non-counted performance-proxy design; next tranche
should move to Family B.

### PERF revisit p26 — substitution hot path only (2026-07-04)

Profile-before-design evidence on `peano`:

- Native PeTTa completes the original K=300 file in ~1.5s.
- PLeaTTa with the p25 executable completes K=80 in ~20s and K=100 in
  ~45-52s; K=150+ hits the wrapper ceiling. This is not an oracle slowness
  issue for `peano`.
- Retained micro-optimization: `substN` now stops when an intermediate
  substitution result is ground. This avoids reapplying the whole
  substitution over a closed term just to rediscover that it is stable.
- Rejected after measurement: a `once (match ...)` fast path that searched
  for the first successful space unification directly. It reduced counted
  steps on K=80/K=100 but did not improve wall time enough and widened the
  Step surface, so it was reverted.
- Full p26 sweep (`diffbench/run-p26-subst.log`): 176 rows, 122 agreements,
  exactly matching p25. No gains, no regressions, no changed rows.

## PLeaTTa 95% tranche — Family B Specializer evidence (2026-07-04)

Read `specializer.pl` in full. The real mechanism is compile-time
higher-order partial evaluation: `maybe_specialize_call/4` copies meta-clauses,
binds higher-order/head-position variables to concrete call-site operands,
creates a `Name_Spec_[...]` predicate, copies type declarations into `&self`,
and asserts translated specialized clauses. Translator rules are separate:
`add-translator-rule!` registers a head so later translation calls that MeTTa
function at compile time.

Landed source-grounded cleanup:

- `specializer.pl` prints `Not specialized ...` diagnostics with `format/2`
  when a specialization attempt fails. These are native compile diagnostics,
  not MeTTa answers; `diffbench` now filters just those lines. Result:
  `specializecyclic.metta` now agrees.
- `repra/2` is a native builtin (`metta.pl:30,306`) and is now in
  `pleattaTable`; `specializefunctiontypes.metta` now returns `42` for the
  first bang, with only the missing specialization type facts left.

Earlier rejected cleanup, now resolved in the eval/self tranche:

- PeTTa's loader adds user function/type forms to `&self` before translating
  them (`filereader.pl` + `spaces.pl`), and the earlier PLeaTTa attempt
  compiled the internal prelude and user atoms as one event stream. A direct
  rule/type seeding pass on that stream also exposed internal
  prelude rules and regressed `spaces3.metta`; that version was reverted.
  The retained p30 implementation keeps the internal prelude callable but
  invisible to user atomspace enumeration, while user-file declarations remain
  visible through `&self`.

Remaining Family-B obstruction: the full specializer and translator-rule
machinery. A one-off `f_Spec_[g]` fact generator would be a half-model, so it
was not implemented. Remaining files need a real Compile.lean specializer pass
or an explicit ledgered translator boundary.

## PLeaTTa 95% tranche — Family C Types v2 evidence (2026-07-04)

Landed:

- Tuple `get-type` now enumerates the cartesian product of element type
  alternatives instead of taking only the first alternative per element.
  Source anchor: `metta.pl:160-180` (`maplist('get-type', X, T)` can
  backtrack per element). Result: `recursive_types.metta` now agrees.
- Space-based `unify` is now distinct from equality-unify for literal
  `&self`, following `lib/lib_he.metta:24-31`: match the pattern in the
  space; evaluate the selected branch. This fixes the branch semantics, but
  `test_unify_eval_branches.metta` remains `DIFF-COUNT` because the import
  bang answer still differs from native PeTTa. Broad import-answer and
  import-base harness changes caused regressions and were reverted.

Full p22 sweep, measured against p19: 176 rows both runs, 168 in-fragment both
runs, 119 agreements vs 117 baseline; new agreements are `recursive_types.metta`
and `specializecyclic.metta`; zero regressions and zero class changes.

Still open:

- `types_nondet.metta`: PLeaTTa compiles a whole file with all later type
  declarations already visible; native PeTTa processes top-level forms
  sequentially, so the first `T3in` query must not see the later
  `(: T3in Type2)`. This is a sequential top-level state issue, not a
  `getTypeP` local bug.
- `parametric_types.metta`: parametric function-type unification still
  returns an extra fresh variable / `true` trace in the harness and misses the
  final `Bool` result.

## PLeaTTa 95% tranche — Sequential top-level state (2026-07-04)

Landed source-grounded sequential top-level compilation/execution:
`filereader.pl:16-28` parses all forms first (registering function heads),
then `process_form/3` runs forms strictly in order. PLeaTTa now compiles a
top-level event stream: facts, type declarations, and clauses become live in
source order; bangs run immediately against the current world. Function heads
are still collected up front, matching PeTTa's parse pass.

Focused diagnosis before the change:

- `types_nondet.metta`: native `T1out,T2out,Tdefault`; PLeaTTa had an extra
  `Tdefault` because the later `(: T3in Type2)` declaration was visible to the
  earlier bang.
- `parametric_types.metta`: still a parametric type-return issue (`Bool` vs
  `true,$v1`), not solved by top-level ordering.
- `test_unify_eval_branches.metta`: branch evaluation now matches, but the
  file still differs by the import bang answer (`true` on native only).

Verification:

- Focused three-file check: `types_nondet.metta` now `AGREE`; the other two
  remain `DIFF-COUNT` for the reasons above.
- Regression spot (`curry`, `plntest`, `state`, `functionhead`, `foldall`,
  `matchsingle`) all stayed `AGREE`.
- Full p23 sweep (`diffbench/run-p23-seq.log`): 176 rows, 120 agreements vs
  p22's 119; only changed verdict is `types_nondet.metta` from `DIFF-COUNT`
  (3/4) to `AGREE` (3/3); zero regressions.

Follow-up import-answer fix:

- `test_unify_eval_branches.metta` used `!(import! &self lib/lib_he)`.
  Native PeTTa resolves `lib/...` against its process working directory
  (`metta.pl:284-301`) and answers `true` when the import succeeds. PLeaTTa
  was resolving the transformed temp file's relative path instead, so it
  skipped the import answer. The import preloader now resolves `lib/...`
  through the configured PeTTa lib root, and `expandImports` emits the
  successful import answer for that same form. This intentionally does not
  change `../lib/...` imports.
- Focused import spot: `test_unify_eval_branches`, `he_evaluation`,
  `library`, `spaces_find`, `fibsmartimport`, and `types_nondet` all agree.
- Full p24 sweep (`diffbench/run-p24-seq-import.log`): 176 rows, 121
  agreements vs p22's 119; changed verdicts are `types_nondet.metta` and
  `test_unify_eval_branches.metta`, both `DIFF-COUNT` -> `AGREE`; zero
  regressions.

## PLeaTTa 95% tranche — `(call ...)` staging equation (2026-07-04)

Landed the bounded manual-dispatch compile equation for symbol-headed
`(call (f args...))`, anchored to `translator.pl:271-276`: translate the
embedded expression's arguments, then emit a direct predicate call
`f(args..., Out)`. The old unsupported-form guard for `(call ` was removed.

Verification:

- Focused eval/staging check: `callquoteevalreduce2.metta` is now `AGREE`.
  `callquoteevalreduce.metta` now compiles and runs but remains `DIFF-VAL`;
  its remaining crux is separate quote/automatic-dispatch staging inside
  `compilefib` (`within (fib 5)` should stay data there, while PLeaTTa still
  reduces it to `within 5`).
- Regression spot (`curry`, `plntest`, `state`, `functionhead`, `foldall`,
  `matchsingle`, plus the two newly covered files from the prior tranche)
  stayed `AGREE`.
- Full p25 sweep (`diffbench/run-p25-call.log`): 176 rows, 122 agreements vs
  p22's 119 and p24's 121. New p25 agreement is
  `callquoteevalreduce2.metta`; zero regressions. `callquoteevalreduce.metta`
  moved from `LEATTA-NOOUT` to `DIFF-VAL`, which is progress in diagnosis but
  not coverage.
- `lake build PLeaTTa` green.

## PLeaTTa 95% tranche — parser/string canary attempt (2026-07-04)

Landed the one canary-gated parser/string attempt:

- `diffbench`'s symmetric `(test A B) -> A` transform now respects quoted
  strings while finding the test form and first argument. Non-expression first
  arguments are routed through prelude `id`, because native PeTTa does not
  answer a bare literal bang such as `!"x"`.
- Shared parser string tokenization now treats `\"` and `\\` as escapes
  instead of ending the string at the escaped quote, and string tokens are
  unescaped on parse.
- Shared pretty-printing now escapes quotes and backslashes in string atoms.
  `repr` now returns the pretty surface of a string atom, so the result is
  printed once by the normal string printer instead of manually embedding
  backslashes.
- Parser tokens containing `_` stay symbols; Lean's numeric parser accepts
  underscores, but native PeTTa keeps `2025_12_12` as a symbol.

Canary:

- `./scripts/run-oracle.sh` stayed at the known baseline: 269/270 assertions,
  with only `e2_states.metta` mismatching.

Verification:

- Focused parser rows: `string.metta`, `parse.metta`, and `repr.metta` are
  now `AGREE`.
- `test_string_comments.metta` remains open. Original native PeTTa handles
  the file, but the harness-transformed file with `!(id "quote: \"")` hits a
  native syntax error, so this is ledgered rather than normalized away.
- Full p27 sweep (`diffbench/run-p27-parser.log`): 176 rows, 125 agreements
  vs p26's 122. Gains: `string.metta`, `parse.metta`, `repr.metta`. Zero
  regressions.

## PLeaTTa 95% tranche — partial/misc cleanup (2026-07-04)

Landed three source-anchored cleanups:

- Static partial arity compilation now mirrors `translator.pl:20-29` and
  `translator.pl:336-345`: known heads with mismatched arity compile to a
  partial value, and a rule whose RHS is such a partial expands its own head
  with the remaining arguments. Query compilation sees compiled live arities
  as well as source-registered arities. This fixes `partialdef.metta`.
- `diffbench` now rewrites inline `(println! X)` to `true`, extending the
  existing top-level print stripping. Source anchor: native `println!/2` in
  `metta.pl:199-200` prints `X` via host stdout and returns `true`; the
  differential surface is answer values, not host stdout. This fixes
  `myinterpreter.metta` while preserving `he_evaluation.metta`.
- `is-alpha-member` now uses alpha-equivalence first and then native-observed
  structural unification membership, with the native exception that a whole
  query variable does not match a ground collection element. Direct probes:
  `=alpha (1 $x) (1 2)` is false, but
  `is-alpha-member (1 $x) ((1 2) (3 4))` is true; `is-alpha-member $x (a b c)`
  is false; variable collection elements can match. This fixes
  `is_alpha_member_test.metta`.

Verification:

- `lake build PLeaTTa` green after the compile/builtin changes.
- `lake build pleatta` green.
- Focused regression spot (`curry`, `plntest`, `state`, `functionhead`,
  `foldall`, `matchsingle`, parser rows, `smartdispatch`, `he_evaluation`)
  stayed green.
- Full p28 sweep (`diffbench/run-p28-misc.log`): 176 rows, 128 covered vs
  p27's 125 (127 exact `AGREE` + 1 `AGREE-ORD`). Gains:
  `partialdef.metta`, `myinterpreter.metta`, `is_alpha_member_test.metta`.
  Zero regressions.

## PLeaTTa 95% tranche — eval/self source visibility (2026-07-04)

Landed source visibility for user-file rule and type forms in `&self`, with an
internal-prelude boundary:

- Native source anchors: `filereader.pl:35-43` calls `add_sexp(Space, Term)`
  for function forms before translating/asserting the clause; `spaces.pl:10-18`
  does the same for `add-atom` rule forms; `metta.pl:245-246` defines `eval`
  by translating the runtime value and calling the resulting goals.
- Sequential top-level events now carry the original rule source atom, so user
  clauses add both the compiled clause and the source `(= head body)` atom to
  `&self`. Type declarations similarly add their source `(: subject type)`
  atom while updating the type table.
- Runtime `add-atom`/`remove-atom` for rule forms now updates both the live
  clause database and the visible source atom, matching native assert/retract
  discipline.
- Internal PLeaTTa prelude rules are compiled into `progClauses` but not
  exposed as user `selfAtoms`. This preserves native-style user atomspace
  enumeration: the first attempted source-visibility patch exposed all prelude
  rules and regressed `spaces3.metta`; the retained prelude/user split restores
  `spaces3.metta` while keeping `eval.metta` covered.

Verification:

- `lake build PLeaTTa` green.
- `lake build pleatta` green.
- Focused rows: `eval.metta` is now `AGREE` (2/2); `spaces3.metta` remains
  `AGREE` (7/7); `myinterpreter.metta`, `partialdef.metta`, and
  `is_alpha_member_test.metta` remain `AGREE`.
- `he_atomspace.metta` moved from `DIFF-COUNT` 7/5 to 7/6 but remains open.
  This is a real spaces/import semantics gap (`get-type-space` and `unify`
  still differ), not a normalization candidate.
- Full p30 sweep (`diffbench/run-p30-eval-self-prelude.log`): 176 rows, 129
  covered (128 exact `AGREE` + 1 `AGREE-ORD`) vs p28's 128. Gain:
  `eval.metta`. Zero regressions. Against the discarded p29 attempt, the only
  recovered coverage item is `spaces3.metta`.

## PLeaTTa 95% tranche — named spaces and succeedsPredicate (2026-07-04)

Landed source-grounded named-space behavior:

- `PWorld` now keeps `&self` atoms separately from other named spaces. The
  compiler encodes the target space into the existing `Goal.smatch` payload,
  so the sealed goal shape did not grow; the executable machine and
  `Step.smatch` both use the shared `smatchAlts` helper.
- `add-atom` and `remove-atom` now carry their space argument through
  `Goal.wact`, so `&s1` and `&s2` no longer share one global atom list.
  Source anchor: `spaces.pl:2-7` constructs dynamic predicates from the
  explicit `Space` argument.
- `(get-atoms $space)` now enumerates atoms from that named space. Source
  anchor: `spaces.pl:66-69`, where `get-atoms/2` enumerates `Space/Arity`
  predicates and returns their atom payloads.
- `succeedsPredicate` has a bounded compile equation for the library's
  translator-rule behavior: a space predicate expression succeeds once per
  matching atom and returns `False` if no proof exists. Source anchors:
  `lib_spaces.metta`'s `succeedsPredicate` definition and
  `translator.pl:101-105,264-267` for translator-rule dispatch into
  `translatePredicate`.

Native probes used before the `succeedsPredicate` equation:

- No fact: `!(succeedsPredicate (&self friend tim tom))` returns `false`.
- One fact: `(friend a b)` plus
  `!(succeedsPredicate (&self friend $a $b))` returns `true`.
- Two facts in an `if` branch return `(a b)` and `(c d)`, one per proof.

Verification:

- `lake build PLeaTTa` green after the machine/semantics/proof change.
- `lake build pleatta` green.
- Focused rows: `metta4_streams.metta`, `spaces_removeallatoms.metta`, and
  `spaces_succeedspredicate.metta` are now `AGREE`; `spaces3.metta` and
  `spaces_find.metta` stayed `AGREE`; the standard regression spot
  (`curry`, `plntest`, `state`, `functionhead`, `foldall`, `matchsingle`)
  stayed `AGREE`.
- Full p31 sweep (`diffbench/run-p31-spaces.log`): 176 rows, 132 covered
  (131 exact `AGREE` + 1 `AGREE-ORD`) vs p30's 129. Gains:
  `metta4_streams.metta`, `spaces_removeallatoms.metta`,
  `spaces_succeedspredicate.metta`. Zero regressions.
- `he_atomspace.metta` remains open at `DIFF-COUNT` 7/6. Its remaining gap is
  still the mixed `../lib/lib_he` import / direct lib_he equation boundary,
  not named-space enumeration.
- Certification ride-along (`diffbench/trace-sweep-p31.tsv`): script summary
  `covered=133 pleatta=81 lane=28 union=84`. The three new spaces files are
  trace-partial (`metta4_streams` 2/5, `spaces_removeallatoms` 2/5,
  `spaces_succeedspredicate` 2/3), not fully trace-certified.

## PLeaTTa 95% tranche — Patrick `for` translator macro (2026-07-04)

Landed the bounded `for` translator-rule macro from `lib_patrick.metta`:

- Source anchor: `lib_patrick.metta:14-18` defines
  `(for $var $collection $body)` as a quoted
  `(let $var (superpose $collection) $body)` and registers `for` as a
  translator rule.
- PLeaTTa now compiles `(for v xs body)` directly as
  `(let v (superpose xs) body)`, matching the native translator-rule effect
  without implementing the whole translator-rule system in this tranche.

Verification:

- `lake build PLeaTTa` green.
- `lake build pleatta` green.
- Focused row: `patrick_test.metta` is now `AGREE` (4/4).
- The spaces rows from p31 and the standard regression spot stayed `AGREE`.
- Full p32 sweep (`diffbench/run-p32-patrick-for.log`): 176 rows, 133
  covered (132 exact `AGREE` + 1 `AGREE-ORD`) vs p31's 132. Gain:
  `patrick_test.metta`. Zero regressions.
- Certification ride-along for the new file
  (`diffbench/trace-sweep-p32-patrick.tsv`): `patrick_test.metta` is
  `PLEATTA-CERTIFIED` (`TRACED` 4/4, `CHECKED` 4, trusted=1).

## PLeaTTa 95% tranche — data-term staging for rule bodies (2026-07-04)

Landed the rule-translation staging distinction needed by
`callquoteevalreduce.metta`:

- Native source anchors: `translator.pl:302-326` distinguishes known function
  calls, known non-function atom data, plain data lists, and runtime
  `reduce/2` dispatch; `translator.pl:366-373` evaluates function-headed
  sublists inside data terms only when the head is already a registered
  function at translation time.
- `CEnv` now records whether unknown atom heads may use runtime dynamic
  dispatch. Top-level bangs keep dynamic dispatch so previous `add-atom`
  effects can be seen when a query runs. Rule bodies are compiled with
  `dynamicUnknown := false`, because native PeTTa translates a rule at assert
  time; unknown atom heads are data at that point.
- Compound-headed data terms whose head is an unknown non-function data tuple
  now remain data instead of becoming a future dynamic call. This preserves
  `(within (fib 5))` in `compilefib` even after the rule body first asserts
  `fib`.

Native probes:

- A rule `maker` returning `((within (fib 5)))` stays `((within (fib 5)))`
  even after a later runtime `add-atom` asserts `fib`.
- If `fib` is defined before `maker` is translated, the same data term becomes
  `((within 5))`.
- Builtin-headed sublists inside data terms still evaluate: `((+ 1 2))`
  returns `(3)`.

Verification:

- `lake build PLeaTTa` green.
- `lake build pleatta` green.
- Focused rows: `callquoteevalreduce.metta`, `callquoteevalreduce2.metta`,
  p31 spaces rows, `patrick_test.metta`, and the standard regression spot all
  stayed or became `AGREE`.
- Full p33 sweep (`diffbench/run-p33-staging-data.log`): 176 rows, 134
  covered (133 exact `AGREE` + 1 `AGREE-ORD`) vs p32's 133. Gain:
  `callquoteevalreduce.metta`. Zero regressions.
- Certification ride-along for the new file
  (`diffbench/trace-sweep-p33-callquote.tsv`): `callquoteevalreduce.metta`
  is `NOTRACE` (`TRACED` 0/4), so this is coverage-only for now.

## PLeaTTa 95% tranche — parametric type dispatch (2026-07-04)

Landed the remaining `parametric_types.metta` mismatch:

- Native source anchors: `src/metta.pl:166-181` computes application types by
  matching a function's declared arrow against argument `get-type` results;
  `src/translator.pl:310-317` emits typed-call branches whenever declarations
  exist; `src/translator.pl:354-363` type-checks non-`Expression` arguments
  using `get-type(V,T) *-> true ; get-metatype(V,T)`.
- `getTypeP` now drops arrow candidates whose parameter types do not unify
  with inferred argument types, instead of returning the uninstantiated result
  variable. This removes the bogus `$ty` type for `(apply not False)`.
- Compound type values emitted by `get-type` now use PLeaTTa's internal tuple
  representation. This lets a syntactic arrow pattern in `let` unify with a
  declared arrow type and bind the result type variable.
- Typed dispatch now covers a single declared chain when an argument type is
  compound, which is enough for `apply : (-> (-> $tx $ty) $tx $ty)` while
  avoiding the known dependent-type extension gap where user-defined
  `(= (get-type ...))` rules are not yet consulted by `getTypeP`.

Verification:

- `lake build PLeaTTa` green.
- `lake build pleatta` green.
- Focused type and spot rows: `parametric_types.metta`, `types.metta`,
  `types_dependent.metta`, `types_nondet.metta`, `recursive_types.metta`,
  `recursive_types2.metta`, `functiontypes.metta`, `builin_types.metta`,
  `he_types.metta`, `curry.metta`, `plntest.metta`, `state.metta`,
  `functionhead.metta`, `foldall.metta`, and `matchsingle.metta` all `AGREE`.
- Full p34 sweep (`diffbench/run-p34-parametric-types.log`): 176 rows, 135
  covered (134 exact `AGREE` + 1 `AGREE-ORD`) vs p33's 134. Gain:
  `parametric_types.metta`. Zero regressions.
- Certification ride-along for the new file
  (`diffbench/trace-sweep-p34-parametric.tsv`): `parametric_types.metta` is
  `NOTRACE` (`TRACED` 0/1), so this is coverage-only for now.

## PLeaTTa 95% tranche — freshened space matching and inert new-space (2026-07-04)

Landed the `nilbc.metta` unblock:

- Native source anchors: `src/metta.pl:240` defines `bind!` only for
  `(new-state ...)`, while `src/metta.pl:303` still registers `bind!` as a
  function. Therefore `!(bind! &x (new-space))` has no answer, and
  `!(new-space)` itself is just inert data. PLeaTTa now mirrors that narrow
  behavior instead of rejecting `(new-space)` at the guard.
- Native source anchor: `src/spaces.pl:60-63` calls an asserted Prolog
  predicate for `match`; asserted variables are fresh on each call. PLeaTTa's
  `smatch` now freshens each stored atom candidate with the machine counter
  before unification. This fixes variable capture in the `nilbc` backward
  chainer.
- Native source anchor: `src/spaces.pl:5-7` removes atoms via `retractall`.
  PLeaTTa space removal now drops atoms that unify with the removal pattern,
  not only atoms structurally equal to it. This preserves `remove-all-atoms`
  after match freshening.

Verification:

- `lake build PLeaTTa` green, including `PLeaTTa.Proofs.StepCases`.
- `lake build pleatta` green.
- Focused rows stayed green after the shared `smatch`/removal change:
  `nilbc.metta`, `parametric_types.metta`, the covered type rows, covered
  spaces rows, `functionremoval.metta`, `functionremovalspec.metta`, covered
  match rows, `state.metta`, and the standard spot checks.
- Full p35 sweep (`diffbench/run-p35-newspace-freshmatch.log`): 176 rows, 136
  covered (135 exact `AGREE` + 1 `AGREE-ORD`) vs p34's 135. Gain:
  `nilbc.metta`. Zero regressions.
- Certification ride-along for the new file
  (`diffbench/trace-sweep-p35-nilbc.tsv`): `nilbc.metta` is `TRACE-FAIL`
  (`TRACED` 0/0) due a trace-mode internal OOM, so this is coverage-only for
  now.

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

## IMPORT-RESULT discipline (landed) + the one honest residue
Probe-pinned per target kind: `.metta` file paths and `(library lib)` answer
`true`; `../lib/` module paths and bare names answer NOTHING (Prolog library
mechanism). First probe was WRONG (cwd-relative import failed silently ->
inferred blanket silence -> broke 18 files for one run; re-probed per kind
and corrected). Residue: git_import2 imports `(library lib_faiss)` whose
FFI build (git-import! + build.sh) petta requires at load; petta answers
nothing on that failure. Our loader resolves the stub, so we answer true —
distinguishing "resolves but its FFI build is missing" is effects-boundary
territory. One file, ledgered, not chased.

## PLeaTTa (2026-07-03): the re-founding — semantics-first, measured
The whack-a-mole diagnosis was accepted: PeTTa is compile-to-clauses + SLD,
not HE-with-switches. PLeaTTa/ is that semantics done the LeaTTa way:
PETTA-LP.md (spec) -> Compile.lean (the equations, definitional) ->
Machine.lean (fuel-total executable) -> Semantics.lean (Step/StepStar
relation; machineMirrorsSpec stated, proof queued). Values are cons-chains
(tuples ARE Prolog lists; narrowing structural). One day from first line to:

  pleatta solo:  99/176 agree (56%) — vs the switch-kernel's best 85
  union (kernel ∪ pleatta ∪ certified delegation): 105/176 (59%)

Remaining ladder: 17 timeouts (mostly genuine PERF — tree-fib/peano at
verification-grade speed; a machine perf pass may recover several),
45 DIFF tail (staging/call family + per-file probes), bind!/state (2),
5 NOOUT. The six kernel-only files (matchnested2, plntest, smartdispatch,
state, superpose_primes) are each diagnosed. Fresh-probe discipline held
throughout (two bad probes caught by regression, corrected per-kind).

## PLeaTTa Phase 0 progress (2026-07-03, cont.)
Solo 99->106/176 (60%), union 105->109/176 (61%). Landed, source-anchored:
- 0a first-argument indexing (shared resolveAlts, machine+relation one def);
- 0b named state cells [metta.pl:240-242] (bind!/get-state/change-state! —
  the numeric-handle State was an unanchored invention, removed); state.metta.
- 0c partial: conjunctive match (relational join; matchnested2), 2-arg match
  partial value (test_match_simple), parse, is-alpha-member, repr string
  escaping, typed-call dispatch for multiply-declared heads (types_nondet).
Ledgered obstructions (v2, not yet fixed):
- typed-check uses builtin get-type; does NOT consult user `(= (get-type ..) ..)`
  rules (types_dependent needs it — narrowed dispatch to >=2 chains to avoid
  regressing it).
- full meta-circular eval [metta.pl:245] for eval/myinterpreter/selfprog/curry.
- specializer.pl (partial evaluation) family unmodeled: specialize*,
  translatorrule*, smartdispatch, partialdef — decide model-vs-boundary.
- repr string escaping still imperfect on edge quotes.
- 17 TIMEOUT = deep compute (fib/peano/matespace/tilepuzzle/...) -> delegation
  lane per PERF policy; permutations+tilepuzzle went VALUE->TIMEOUT under
  indexing (explore more, still slow). 2 PETTA-TIMEOUT (petta itself hangs).

## Phase 0 cont. — meta-eval + the partial-application story (source-anchored)
- Meta-circular eval [metta.pl:245]: runtime translate-and-call (unchainify
  value -> compileExpr against live world -> splice renamed goals). Fixes
  myinterpreter, selfprog.
- Unified partial-application to partial(Base,Bound) [translator.pl:58-64,
  253-254, 328-339]: under-applied defined calls yield a partial value;
  |-> closures use partial(F,FreeVars); callDyn appends to a partial's bound
  and re-dispatches. Compound-headed applications (E a..) route through
  callDyn (runtime apply-or-data, mirrors translate_expr on [H|T]). Fixes
  curry (5/5, incl. repr of partials). maplist prelude rule.
Ledgered:
- lambda.metta 4/5: a deeply nested partial-closure capture
  (partial(myfunc,(42)) captured as a lambda free var then applied) does not
  fully reduce — the closure/partial interaction at depth. v2.
- eval.metta needs function DEFINITIONS matchable as (= head body) atoms in
  &self (match against a compiled clause) — definitions-as-atoms; deeper.

## PHASE 0 COVERAGE GATE CLEARED (2026-07-03) — union 66%
Two stable runs (p16=p17, 115 solo/176), union (kernel ∪ pleatta ∪ certified
delegation) 117/176 (66%) >= the 64% floor. Zero sorry. HE canary 269/270
(pre-existing e2_states, unchanged). The partial-application unification
(partial(Base,Bound), one root) cascaded to +6 files — the anti-whack-a-mole
principle paying off.

### Honest gate debt (Phase 1's first task, NOT yet done)
This session added machine arms WITHOUT their Step rules while racing to the
coverage gate: meta-circular evalg (replaced the old apply-or-data evalg, so
Semantics' evalg_call/evalg_id are now stale), .call zero-clause->data and
under-application->partial, .bin builtin-partial, callDyn partial-dispatch +
compound-headed routing. => Semantics.lean LAGS Machine.lean. The surface is
NOT yet frozen: Phase 1 must first re-sync every Step rule to the current
machine, THEN prove machineMirrorsSpec. (The correspondence gate was honored
for 0a's resolveAlts but slipped during 0b-0c — recorded, to be paid.)

### Historical divergent inventory after Phase 0 (35 in-fragment), classified
PERF/TIMEOUT (17): fib,fibadd,holbenchmark,hyperpose_primes,invertpeanoplus,
  matespace{,2,fast},patrick_iterate_quad,peano{,fast},permutations,
  plntestdirect,scale,superpose_primes,tabling_fib,tilepuzzle -> delegation
  lane (PERF policy); some certify-DIFF in the lane, need lane equation ports.
PETTA-TIMEOUT (2): he_minimalmetta,repl -> petta itself hangs; honest exclude.
Specializer (6): specialize{,cyclic,functiontypes},translatorrule{,_fib,_for}
  -> read specializer.pl; model-vs-boundary decision (don't half-model).
Meta/staging (5): eval (defs-as-(=)-atoms matchable in &self),
  callquoteevalreduce{,2} (needs `call` op + staging), lambda (deep nested
  partial-closure capture), myinterpreter/nilbc (recheck under transform).
NAL/PLN (5): nars_tuffy,nars_direct,pln_direct,plntest,test_backward_v01.
Types (4): parametric_types,types_nondet,recursive_types,
  test_unify_eval_branches (user get-type + output checks, v2).
Spaces (5): he_atomspace,metta4_streams,spaces_removeallatoms,
  spaces_succeedspredicate (translatePredicate boundary),mutex_and_transaction
  (thread ops -> honest never).
String/repr (4): repr (escape+underscore-number parse), string, parse,
  test_string_comments (parser edges, shared w/ LeaTTa -> canary after).
Small (3): partialdef,patrick_test,he_error.

## Phase 1 progress (2026-07-03, cont.) — the Step relation
Semantics.lean re-synced to the machine AND extended: 23 -> 37 constructors,
zero sorry, both builds green (lib + exe). Now formally covers the FULL
control + resolution + bin dispatch: pull/answer/eq/cut/call{data,partial,
resolve}/bin{partial,gettype,getmetatype,nonstrict-ok/fail,ok,mode,fail,
delay,flounder}/ite/amb/spread/smatch/callDyn{call,bin,symdata,partial,data}/
evalg{ok,err}/softcut{some,none}/onceg/findall/wact_ok. Each mirrors its
machine arm; oracle-shaped builtins reference callGrounded/getTypeP directly
(the LeaTTa oracle discipline — not circular).
REMAINING for the Phase-1 gate (machineMirrorsSpec zero-sorry):
  1. wact assert/retract rules (rule-form add/remove-atom compile a clause at
     runtime via compileRule + α-key match — intricate premises).
  2. THE PROOF: machineMirrorsSpec by cases on `step`. Most non-nested cases
     unfold (machine + relation share pull/resolveAlts/cutTo/unifyB); the
     nested cases (findall/softcut/onceg) need run->StepStar by fuel
     induction. This is a dedicated interactive-proving session (use the
     lean-lsp MCP tools), NOT a tail-of-session task — attempting it under
     time pressure risks sorries, which the standing rules forbid.
Phases 2-5 (sunset, certificates, math-tier, 95% stretch) follow the seal.

## Phase 1 proof — STARTED (2026-07-03)
PLeaTTa/Proofs/StepCases.lean: 6 machineMirrorsSpec case-lemmas proven, zero
sorry, green (step_eq/pull/answer/cutAt/amb/smatch). Pattern: `unfold step;
rw [cur-hyp]; simp only [inner-match lemmas]` reduces the machine to exactly
the Step constructor's output. REMAINING (dedicated interactive session):
ite (BEq-reduce condition, close with rfl after simp only [hc, trueA]),
spread/callDyn/call/bin branch cases, then nested findall/softcut/onceg via a
`run -> StepStar` fuel-induction lemma; finally assemble machineMirrorsSpec.
Note: `lean_goal` on this file returns ~15KB (full step unfolds) — budget the
proof session accordingly; each case is small but the context is large.

## PHASE 1 GATE CLOSED (2026-07-03, Fable) — machineMirrorsSpec PROVEN
Zero sorry; axioms [propext, Classical.choice, Quot.sound]; full build green;
corpus p18 = p17 = 115/176 exactly (the wactDispatch machine refactor is
behavior-preserving); HE canary 269/270 (baseline). 40 Step constructors, 15
case lemmas + assembly (PLeaTTa/Proofs/StepCases.lean).
What the proof CAUGHT (the gate earning its keep):
- Atom BEq is unlawful in general (IEEE float payloads), so the relation's
  Prop-form ite premises are equivalent to the machine's Boolean test ONLY
  against a literal symbol — beq_symTrue_iff is the bridge; a hypothetical
  non-symbol dispatch would have been a real spec/machine divergence.
- Under-applied +/-/* can never reach the moded-arithmetic match (the
  partial-application test catches them first) — proven vacuous via hnp;
  the relation needed bin_mode_fail for the >2-arg case.
- callDyn_partial's bound premise had to be corrected to the machine's
  getD [] (a some-premise would have under-specified the none case).
Fuel-honesty boundary: findall/softcut (nestedRunHead) — the relation
licenses nested-run steps only for TERMINAL sub-runs. The conditional
run->StepStar adequacy lemma is optional future metatheory, not gate.
NEXT = PHASE 2 (sunset): pleatta must rederive the 2 remaining kernel-only
files (plntest, superpose_primes — or certify via delegation), then rip the
petta arms from the HE kernel (rg-negative for pettaProfile in Minimal/).

## PHASE 2 EXECUTED (2026-07-03 eve) — the switch-kernel is retired
Replay-before-retire held: p19 solo 117/176 (66%), pleatta ∪ certified
delegation 118/176 (67%), kernel-only set EMPTY (superpose_primes
DELEGATED-CHECKED after the lane repair; plntest/plntestdirect solo via
min/max). Removed: pettaProfile + its Minimal/ dialect surface (~230 lines:
petta prelude deltas, pettaGroundings table, preludeAtomsFor), the --petta
flag, petta_failure_iff/petta_inert_iff + their axiom audits. KEPT: the
proven-parametric EvalProfile machinery anchored at heProfile (reduceAtomP_he
regression theorem) — the interpreter's parametric arms are proof subjects
of the untouchable HE lane and stay. Gates: full build green, HE canary
269/270 (baseline), zero sorry, rg pettaProfile hits only sunset notes.
Old scoreboards kept as regression oracles (run-t51.log).
Lane repair credited here: mi.pl streaming serialization (the atom-building
serializers were O(n^2) on deep proofs — a 7000-deep spine hung 200s+; now
ms) + imod/idiv arithOracle leaves (floored mod = SWI semantics; idiv exact).
NEXT: Phase 3 (pleatta --trace certificates), Phase 4 (math-tier), Phase 5
(95% stretch; remaining divergent families ledgered above).

## Phase 3 opened (2026-07-03 late) — certified fraction measured + the design decision
Lane sweep over all 118 covered files (diffbench/lane-sweep-p19.tsv):
28 certified (22 CHECKED + 6 TRUSTED) = 23%; 49 NO-COMPILE (outside the
Python lane's pure-SLD fragment); 37 DELEGATED-DIFF (fragment gaps: missing
bool/float leaves, partials, import splicing); 3 UNCERTIFIED. Blocker
families among the 89 non-certified: superpose/collapse 28, match 26,
effects (add-atom/state) 14, let* 9, case 5.
DECISION (the crux, so the next session builds the right machine): do NOT
extend relcompile.py toward these — that is a second compiler and the
whack-a-mole shape. The right Phase-3 artifact is `pleatta --trace`: a
clause-only projection INSIDE the anchored Lean pipeline — Compile's own
clauses serialized to the algos-lp wire format with aux clauses for
ite/amb (relcompile's ifaux move, done once in Lean), Prog.facts as fact
clauses for smatch, collapse as trusted tnodes, cut/once via committed_pred
(cut-agnostic certificates: pruning affects which derivation is FOUND, not
its validity) — plus a machine-run trace recorder projecting each answer's
clause-application tree. Checker stays the OTHER lane's CheckAnswer
(consume, don't duplicate); richer grounded leaves go through its PARAMETRIC
oracle argument (grounded ops are definitional — the trust economy holds:
certificates eliminate the SEARCH, not the table). Effects files (14) are
the honest never-certify boundary; realistic gate ceiling ~88% — revisit the
90% wording against that when the emitter lands.
Lane repair shipped meanwhile: streaming mi.pl serialization (O(n^2)->O(n));
imod/idiv oracle leaves; int_eq; superpose_primes certified 3.5s.

## PHASE 3 GATE MET (2026-07-04 early) — `pleatta --trace` certified fraction measured

Fresh trace sweep artifact: `diffbench/trace-sweep-p2.tsv`.

Headline over the 118 covered files:
- pleatta-certified: 75/118.
- swipl lane-certified baseline: 28/118.
- union certified: 78/118 = 66.1%.
- Target met: yes (>=70/118). Stretch not met (90/118).

What changed in this tranche:
- `--trace` accepts an optional per-run budget argument; heavy files can now
  be capped honestly instead of chasing wrapper OOMs.
- Trusted collection emission now proves every listed positive collection
  member as an ordinary SLD subtree; collection exhaustiveness remains the
  trusted boundary.
- Grounded leaf coverage was mirrored on both sides for the cheap deterministic
  families: int/float arithmetic and comparisons, min/max, `is-var`, `=alpha`,
  boolean `beq`, chain/list atom operations, alpha uniqueness/membership,
  `msort`, and the basic math functions.
- `diffbench/trace_sweep.py` now measures TRACED and CHECKED separately and
  reports the certified union against the lane baseline.

Regression/gate evidence:
- `lake build pleatta` green.
- `lake build checktrace` green.
- `lake build PLeaTTa` green; it replayed the sealed proof target. The build
  still prints three linter warnings in the sealed StepCases proof file, which
  was not edited in this tranche.
- Tamper pair still rejects: clean `xor.metta` trace accepted; answer mutation
  rejected; root clause-index mutation rejected.
- HE canary remains 269/270. The script exits nonzero because it still expects
  `e2_states.metta` to be 14/0/14, but the required canary headline remains
  the established 269/270 baseline.
- Placeholder scan: no active `sorry`, `theorem_wanted`, or `_wanted` hits in
  the checker files; PLeaTTa hits are only existing "Zero sorry" prose comments.

Residual p2 categories among the covered files:
- 18 NOTRACE: mostly machine-oracle or honest never-certify boundaries such as
  type/meta-type and world/state/effect families.
- 15 PARTIAL: some answers trace/check, but not every answer in the file.
- 10 TRACE-FAIL: wrapper-contained OOM/timeout failures, recorded as per-file
  honest failures.
- Rejected traces remain concentrated in `spaces2.metta` and
  `test_match_simple.metta`; these are the highest-signal next stretch targets
  if Phase 3 is continued past the gate.

NEXT: Phase 4 math-tier and Phase 5 stretch. For any renewed certificate push,
start from p2 residuals rather than broadening the checker unsafely: the best
stretch candidates are the rejected space/match traces and the partial families
with already-checked siblings.

### Advisor review of the Phase-3 tranche (Oruzi, 2026-07-04)
VERIFIED independently: 75/28/78 recounted from the tsv; tamper pair
re-run by hand (answer-flip REJECT; clause-redirect REJECT — note the first
attempt was a vacuous sed, always `cmp` the tampered file); sealed proof
re-elaborates green; zero sorry; canary 269/270; engine `--file` behavior
spot-unchanged (curry/plntest/state/functionhead). No file- or
answer-specific special-casing found (clean of whack-a-mole). The
superpose_functions "anomaly" was a phantom — the file does not exist
(bad name from an earlier smoke test).
FLAGS (next tranche = DEEPER PROLOG GROUNDING, Zar's directive):
1. THREE COPIES of grounded-op semantics now exist: machine pleattaTable,
   tracer evalLeaf, checker evalOracle. Mirror drift = silent coverage loss
   (concretely: msort sorts by Pretty.atom in the tracer but by termKey in
   the checker — divergent keys reject honestly but lossily). Fix: tracer
   evalLeaf should CALL pleattaTable (one engine-side source); only the
   checker stays independent.
2. Oracle-growth where CLAUSE-growth was possible: car_c/cdr_c/cons_c and
   friends are definitional oracle leaves, but in Prolog they are pure
   clauses — `cons_c(H, T, '#c'(H, T)).` etc. Moving structural ops from
   the trusted oracle into the certified clause program shrinks the trust
   surface and is closer to the actual transpilation semantics. Same
   question for the set ops (member/append already ARE clauses).
3. Aux-clause shapes (amb{n}/ite{n}/sc{n}) are OUR names; translator.pl has
   its own if/case compilation shapes — consider aligning the projection
   with the transpiler's own clause forms (the "quasi-executable Prolog in
   Lean" direction).
4. Ledger nuances: pow int with negative exponent = a^0 both sides
   (consistent, wrong vs ideal math — reject-safe only if engines differ);
   trunc/ceil/floor/round via toInt64 wrap beyond 2^63; both are
   documented trust-boundary footnotes, not soundness holes (the oracle is
   the leaf spec).

## Deeper Prolog grounding of the certificate lane (2026-07-04, Oruzi)
Zar's directive: ground in the actual transpilation semantics; prefer
executable Prolog over trusted oracle. Executed, coverage-NEUTRAL by
construction (sweep p3 = p2 exactly: pleatta 75, union 78/118; zero
regressions), trust surface SMALLER:
1. CLAUSE-GROWTH: booleans (truth-table facts), car/cdr/cons (pure facts),
   size/index (recursive relations over arithmetic leaves), union-atom
   (= chain_append), min/max (two-clause relations over cmp leaves) moved
   OUT of the trusted oracle INTO the certified clause program. The checker
   REJECTS them as bnodes now (entries deleted) — they certify as ordinary
   resolution.
2. THIRD COPY ELIMINATED: the tracer's evalLeaf now DELEGATES to the
   engine's own pleattaTable (leafOp maps leaf rel -> table op) — the
   tracer cannot drift from the machine; only the checker's oracle is an
   independent implementation (as it must be).
3. Aux clauses cite their transpiler sources (sup{n} = superpose
   disjunction translator.pl:112-114, ifte{n} = the compiled if 156-162,
   sc/case 163-176+388-399, coll = collapse/findall 115-116, once 127-128).
Remaining oracle: arithmetic/comparisons/beq/is_var/alpha_eq + the set/sort
family (their Prolog forms need disequality/ordering — not positive-clause
expressible) + float math. Gates: builds green, sealed proof re-elaborates,
zero sorry, HE untouched, tamper pair rejects (cmp-verified non-vacuous).
Note: superpose_primes TRACE-FAILs in the tracer (60s ulimit; 7350-deep
re-derivation) — covered by the swipl lane certificate; union unaffected.

## PLeaTTa 95% tranche — catch/error term semantics (2026-07-04)

Landed `he_error.metta`:

- Source anchor: PeTTa's translator compiles `(catch E)` by translating `E`
  to goals, wrapping those goals in Prolog `catch/3`, returning normal
  answers, reifying Prolog exceptions as `['Error', ...]`, and preserving
  ordinary no-answer as failure (`src/translator.pl:293-300`).
- Source anchor: `lib/lib_he.metta:46-53` defines `if-error` and
  `return-on-error`, but the differential harness's temp-file execution of
  `../lib/lib_he` leaves those forms inert on native PeTTa. PLeaTTa already
  matched that import boundary; the missing piece was the `catch` subterm.
- Implementation: added a `Goal.catchg` compile equation for `(catch E)`.
  The machine handles the source-observed direct translated-builtin case by
  reifying builtin `incorrectArgument` as `(Error type_error ...)` and
  builtin `runtimeError` as `(Error runtime_error ...)`; other catch bodies
  run through the ordinary sub-run, so `(catch (empty))` still has no answer.
- Harness normalization: `diffbench/diff.py` now canonicalizes `(Error ...)`
  subterms symmetrically to `(Error <kind>)`, preserving the error kind while
  discarding host-specific Prolog context terms or Lean-side message strings.

Evidence:

- `lake build PLeaTTa` green, including the sealed `StepCases` proof target.
- `lake build pleatta` green.
- Focused row: `he_error.metta` moved from `DIFF-COUNT 5/4` to `AGREE 5/5`.
- Focused regression spot stayed green:
  `curry.metta`, `plntest.metta`, `state.metta`, `functionhead.metta`,
  `foldall.metta`, `matchsingle.metta`, plus prior p34/p35 rows
  `parametric_types.metta` and `nilbc.metta`.
- Full p36 sweep (`diffbench/run-p36-catch-error.log`): 176 rows, 137
  covered (136 exact `AGREE` + 1 `AGREE-ORD`) vs p35's 136. Zero regressions;
  the only changed row is `he_error.metta`.
- Trace ride-along (`diffbench/trace-sweep-p36-he-error.tsv`):
  `he_error.metta` is `PARTIAL` (`TRACED 2/3`, `CHECKED 2`), not certified;
  `catchg` is currently an unsupported trace leaf.

Current gate distance: 137/176 -> at least 150/176 needs 13 more files.

## PLeaTTa 95% tranche — Expression staging for runtime PLN/NARS rules (2026-07-04)

Profile-before-design PERF note:

- Rechecked `peano.metta` before attempting any PERF edit. Native PeTTa
  completes the original `demo-peano 300` in about 1.5s. PLeaTTa profile
  still shows structural growth: scaled `demo-peano 50` finished in 26,630
  steps and about 2s; `demo-peano 100` took 103,230 steps and about 40s;
  `demo-peano 120` hit the wrapper timeout. This confirms the p26 diagnosis:
  the current Peano family remains a structural PERF gap, not a native-oracle
  slowness issue. No PERF semantic edit was made.

Landed `nars_direct.metta` and `pln_direct.metta`:

- Source anchor: native `translate_args_by_type/4` leaves `Expression`
  arguments as data input (`src/translator.pl:354-363`). In PeTTa's Prolog
  runtime, that data is a list term; in PLeaTTa the corresponding value is a
  chain. Ordinary `Expression`-typed calls now pass `chainify a`, matching the
  already-existing typed-dispatch branch and allowing cons patterns such as
  `(cons , $args)` to narrow comma-headed expression data.
- Source anchor: native runtime implication rules assert compiled clauses
  whose bodies can call source-registered heads even when those heads become
  live later in the file. PLeaTTa now records source-known heads/arities in
  `PWorld` for runtime compilation only. `PWorld.clausesOf` still reads only
  live `progClauses`, preserving sequential top-level visibility.
- Source anchor: native `reduce/2` on a variable-bearing term binds variables
  inside that term back into the caller. PLeaTTa `evalg` now preserves caller
  variables when splicing runtime-compiled goals, tags any cuts, and advances
  to the compiler-returned fresh counter instead of blanket-renaming the term.

Evidence:

- `lake build PLeaTTa` green, including `PLeaTTa.Proofs.StepCases`.
- `lake build pleatta` green.
- Tiny source probes now match native:
  `(f (cons , $args))` over `!(f (, a b))` returns `first, second`, and the
  analogous `=>` skeleton returns `first, second`.
- NARS decomposition probes now match native for ground and variable queries:
  `? (grandfather a c)`, `? (grandfather $who c)`, and `? (old $who)`.
- Focused corpus rows:
  `nars_direct.metta` moved to `AGREE 7/7`;
  `pln_direct.metta` moved to `AGREE 7/7`.
- Full p37 sweep (`diffbench/run-p37-expression-runtime-heads.log`): 176
  rows, 139 covered in the 168-file in-fragment (138 exact `AGREE` + 1
  `AGREE-ORD`) vs p36's 137. Zero covered-row regressions.
- Changed rows vs p36:
  `nars_direct.metta` and `pln_direct.metta` became covered;
  `lambda.metta` changed from `DIFF-COUNT 7/5` to `DIFF-VAL 7/7`;
  `specialize.metta` remains divergent but changed from `DIFF-COUNT 11/6`
  to `DIFF-COUNT 11/8`.
- Trace ride-along (`diffbench/trace-sweep-p37-nal-pln.tsv`) is partial:
  both new rows are `TRACED 1/7`, `CHECKED 1`, not fully certified.

Current gate distance: 139/176 -> at least 150/176 needs 11 more files.

## PLeaTTa 95% tranche — captured lambda partial values (2026-07-04)

Landed `lambda.metta`:

- Source anchor: native lambda translation (`src/translator.pl:242-254`)
  computes free variables, compiles a fresh predicate over
  `FreeVars ++ Args`, and returns either the bare function symbol or
  `partial(F, FreeVars)`. Captures are values in the partial closure; they
  are not evaluated by a zero-argument dynamic call.
- Source anchor: native dynamic dispatch (`src/translator.pl:59-61`) applies
  a partial closure by appending new arguments to the bound list and reducing
  the base call.
- Implementation: captured `|->` values now use PLeaTTa's internal
  `partialValue` directly instead of a surface `(partial F (...))`
  expression. Internal `#c` chain values produced by the compiler now compile
  as data, not as dynamic calls to a source head named `#c`.

Evidence:

- `lake build PLeaTTa` green, including `PLeaTTa.Proofs.StepCases`.
- `lake build pleatta` green.
- Focused row: `lambda.metta` moved from `DIFF-VAL 7/7` to `AGREE 7/7`.
- Focused regression set stayed green:
  `eval.metta`, `myinterpreter.metta`, `callquoteevalreduce.metta`,
  `callquoteevalreduce2.metta`, `curry.metta`, `functionhead.metta`,
  `foldall.metta`, `nars_direct.metta`, `pln_direct.metta`, plus p34-p37
  spot checks.
- Full p38 sweep (`diffbench/run-p38-lambda-captured-partial.log`): 176
  rows, 140 covered in the 168-file in-fragment (139 exact `AGREE` + 1
  `AGREE-ORD`) vs p37's 139. Zero covered-row regressions. The only changed
  row is `lambda.metta`.
- Trace ride-along (`diffbench/trace-sweep-p38-lambda.tsv`) is partial:
  `lambda.metta` is `TRACED 5/7`, `CHECKED 5`, not fully certified.

Current gate distance: 140/176 -> at least 150/176 needs 10 more files.

## PLeaTTa 95% tranche — add-atom data semantics, no coverage delta (2026-07-04)

Landed a source-correct compile equation for ordinary `add-atom` and
`remove-atom` data arguments. This is a correctness cleanup, not a coverage
tranche.

Source/semantics rationale:

- Native PeTTa asserts non-rule atoms as data. Surrounding bindings are
  instantiated, but known or builtin subexpressions inside the asserted atom
  are not evaluated.
- Direct probes:
  - `!(add-atom &self (foo (+ 1 2)))` then matching `(foo $x)` returns
    `(+ 1 2)`, not `3`.
  - With `(= (bar $x) (+ $x 1))` in scope,
    `!(add-atom &self (foo (bar 1)))` then matching `(foo $x)` returns
    `(bar 1)`, not `2`.
  - `!(let $t Z (add-atom &self (num (M $t))))` stores `(M Z)`, so runtime
    substitution still happens.
- PLeaTTa now passes non-rule atom arguments syntactically to the world
  effect and lets the machine substitution instantiate variables. Rule forms
  still pass syntactically to `wactDispatch`, where asserted clauses are
  compiled.

Measured PERF attempts in the same pass:

- Scaled `matespacefast` remained time-per-step dominated. `K=7` stayed around
  51-54 seconds for 6,759 counted steps and 384 atoms after the `add-atom`
  data correction.
- Storing space atoms newest-first while exposing insertion order did not
  materially move `matespacefast K=7`; it is retained only as an internal
  order-preserving representation cleanup.
- A shallow rule-form guard in `wactDispatch` avoids deep rule-form decoding
  for atoms whose top-level chain head is not `=`, but it also did not move
  `matespacefast K=7`.
- A reverse-accumulator rewrite for `smatchAlts`/`resolveAlts` worsened the
  profile and was reverted.

Evidence:

- `lake build PLeaTTa` green, including `PLeaTTa.Semantics` and
  `PLeaTTa.Proofs.StepCases`.
- `lake build pleatta` green.
- Focused mutation/space regression rows stayed green:
  `spaces3.metta`, `spaces_find.metta`, `spaces_removeallatoms.metta`,
  `spaces_succeedspredicate.metta`, `functionremoval.metta`,
  `functionremovalspec.metta`, `state.metta`, `eval.metta`, `partialdef.metta`,
  `curry.metta`, `plntest.metta`, `functionhead.metta`, `foldall.metta`, and
  `matchsingle.metta`.
- Full p41 sweep (`diffbench/run-p41-add-atom-data.log`): 176 rows, 141
  covered in the 168-file in-fragment (140 exact `AGREE` + 1 `AGREE-ORD`),
  exactly matching p40. Changed rows: 0. Covered-row regressions: 0.
- Hygiene: `git diff --check`, Python compile for `diffbench`, and placeholder
  scan all passed; placeholder hits were prose-only.

Current gate distance: 141/176 -> at least 150/176 needs 9 more files.

## PLeaTTa 95% tranche — explicit tabled recursion (2026-07-04)

Landed source-backed handling for explicit `tabled` directives and covered
`tabling_fib.metta`.

Source anchor:

- `lib/lib_tabling.metta:7-11` defines `(tabled $call)` by constructing and
  injecting a SWI directive `:- table <name>/<arity>.`.
- Native `tabling_fib.metta` runs `!(tabled (fib $N))`, then defines `fib`,
  then tests `(fib 30)`. Native completes quickly and returns three true
  answers after the harness transform.

Implementation:

- Top-level `!(tabled (f ...))` now compiles to a sequential world event
  instead of executing the imported Prolog-injection body.
- `PWorld` records tabled heads/arities and a ground-call table cache.
- A ground call to a tabled head replays cached answers if present; otherwise
  it runs the tabled variant once with that key marked active, caches the
  answers, and replays them into the caller.
- The formal nested-run boundary now includes uncached tabled calls; cached
  table calls have a normal `Step` constructor. `lake build PLeaTTa`
  re-elaborates the sealed proof target.

Evidence:

- `lake build PLeaTTa` green, including `PLeaTTa.Semantics` and
  `PLeaTTa.Proofs.StepCases`.
- `lake build pleatta` green.
- Focused row: `tabling_fib.metta` moved from `LEATTA-TIMEOUT 3/` to
  `AGREE 3/3`.
- Focused regression set stayed green:
  `curry.metta`, `plntest.metta`, `state.metta`, `functionhead.metta`,
  `foldall.metta`, `matchsingle.metta`, `lambda.metta`, `spaces3.metta`,
  `spaces_succeedspredicate.metta`, `nars_direct.metta`, `pln_direct.metta`,
  `eval.metta`, `partialdef.metta`, `types_nondet.metta`, and
  `test_unify_eval_branches.metta`.
- Full p40 sweep (`diffbench/run-p40-tabled-fib.log`): 176 rows, 141
  covered in the 168-file in-fragment (140 exact `AGREE` + 1 `AGREE-ORD`)
  vs p39's 140. The only changed row is `tabling_fib.metta`. Covered-row
  regressions: 0.
- Trace ride-along (`diffbench/trace-sweep-p40-tabling.tsv`) is not
  certified for this row: trace projection fails under the current trace
  budget, so the row is oracle-covered but not trace-certified.

Current gate distance: 141/176 -> at least 150/176 needs 9 more files.

## PLeaTTa 95% tranche — substitution trim PERF groundwork (2026-07-04)

Landed a proof-sealed substitution hot-path improvement for the PERF family.
This did not flip a corpus row yet, so it is recorded as groundwork rather
than a coverage tranche.

Source/semantics rationale:

- Native Prolog does not keep dead clause-local variables observable after
  they are no longer reachable from the remaining goals or the query answer.
  PLeaTTa's branch substitution previously accumulated all renamed
  clause-local bindings throughout deep recursive calls.
- `subst` now resolves variable chains directly instead of repeatedly
  applying the whole substitution to the whole term.
- `unifyB` now layers the new unifier before the current substitution; the
  deep `subst` operation resolves the resulting chain.
- Successful equality steps now trim the branch substitution to variables
  reachable from the remaining goals and the query term. The formal `Step`
  relation was updated to use the same `trimFor` successor state.

Evidence:

- `lake build PLeaTTa` green, including `PLeaTTa.Semantics` and
  `PLeaTTa.Proofs.StepCases`.
- `lake build pleatta` green.
- Focused regression set stayed green:
  `curry.metta`, `plntest.metta`, `state.metta`, `functionhead.metta`,
  `foldall.metta`, `matchsingle.metta`, `lambda.metta`, `spaces3.metta`,
  `spaces_succeedspredicate.metta`, `nars_direct.metta`, `pln_direct.metta`,
  `eval.metta`, `partialdef.metta`, and `types_nondet.metta`.
- PERF profile evidence on scaled `fib`:
  `fib 18` improved from about 29.1s to about 5.2s at the same 83,610
  counted steps; `fib 20` now completes under profile in about 19.1s at
  218,910 counted steps instead of hitting the wrapper ceiling.
- Full p39 sweep (`diffbench/run-p39-subst-trim-perf.log`): 176 rows, 140
  covered in the 168-file in-fragment (139 exact `AGREE` + 1 `AGREE-ORD`),
  exactly matching p38. Changed rows: 0. Covered-row regressions: 0.

Still open:

- The original `fib.metta` workload remains timeout-class at corpus scale;
  this optimization improves time per step but is not sufficient for the
  full PERF band.
- `peanofast.metta` remains dominated by deep Peano-term growth; K=200 still
  takes about 14s under profile, so the K=2500 corpus row is not near the
  current machine path.
- `permutations.metta`, `matespace.metta`, and `superpose_primes.metta`
  remained timeout-class in longer focused probes, so they are not simple
  timeout-threshold rows.

Current gate distance: 140/176 -> at least 150/176 needs 10 more files.

## Honesty pass on the coverage tiers (2026-07-05, Oruzi audit + fixes)
The "native-agree" tier was overclaiming: it lumped 16 files the verified
engine OOMs on (matespace/fib/peano/...) together with files that merely
missed the import-bang answer. Corrected:
- VERIFIED = 134 in-Lean machine-agree + 1 delegated-cert (superpose_primes)
  = 135/176. That is the honest headline.
- PERFORMANCE-DISQUALIFIED = 16 (engine OOM/timeout; unverified swipl
  cross-check; NOT counted). `diffbench/performance-frontier.tsv`
  (retired native.tsv). matespace builds ~1.5M atoms — pure scale, every
  construct verified elsewhere; WAM race, not a semantic gap.
Fixes landed: (1) checker int_eq leaf restored (superpose_primes cert broke
in the evalOracle refactor); (2) import! emits True on resolve, matching
native petta (+5 machine-agree: builin_types/fibsmartimport/he_atomspace/
he_equalreduct/he_types), zero regressions (run-p48).
Remaining DIVERGENT (engine runs, disagrees): he_error, he_evaluation,
he_quoting, nars_tuffy, pln_tuffy, roman_test, spaces_find, test_backward_v01.
