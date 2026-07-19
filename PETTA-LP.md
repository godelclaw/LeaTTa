<!-- SPDX-License-Identifier: Apache-2.0 -->

# PETTA-LP — the operational semantics of core PeTTa, done right

PeTTa's semantics is not "Hyperon with dialect switches." PeTTa **compiles
MeTTa to Prolog clauses and runs SLD resolution** (eager, leftmost-innermost,
clause-ordered, backtracking, assert-survives-backtracking). This file is the
spec: a small set of compile equations plus one small-step machine. The
`PettaLP/` implementation follows it; every corpus divergence is to be fixed
HERE, as a compile rule or machine transition — never as an ad-hoc patch.

The empirical ground: every corpus file run through this semantics via the
external prototype (diffbench/relcompile.py + swipl) agreed with native PeTTa
exactly, certificate-checked. This document promotes that validated design to
the primary in-engine semantics for the petta profile.

## 1. Syntax classes

```
program form  F ::= (= (f p1..pn) rhs)      function rule
                  | (: x T)                  type declaration (stored)
                  | (head a1..an)            ground fact (stored in &self)
                  | !(e)                     query (bang)
value         v ::= symbol | number | string | ($x unbound) | (v1 .. vn)
```

## 2. Compile equations  C⟦e⟧ = (t, G)

`C⟦e⟧` yields a term `t` and a prefix goal list `G` (flattening; fresh
variables `R` are the classic functional-logic transform):

```
C⟦$x⟧            = ($x, [])
C⟦k⟧             = (k, [])                      k symbol/number/string
C⟦(f e1..en)⟧    = (R, G1++..++Gn ++ [f(t1..tn,R)])       f defined by rules
C⟦(g e1..en)⟧    = (R, G1++..++Gn ++ [g#(t1..tn,R)])      g grounded builtin
C⟦(e1..en)⟧      = ((t1..tn), G1++..++Gn)                 data tuple otherwise
```

Special forms (each an equation, not a machine case):

```
C⟦(if c t e)⟧    = (R, Gc ++ [ifTE(tc, <t-closure>, <e-closure>, R)])
                    -- dispatch on True/False; only the taken branch's goals run
C⟦(if c t)⟧      = (R, Gc ++ [tc = True] ++ Gt), R = tt
C⟦(let p v b)⟧   = (R, Gv ++ Gp ++ [tp ≐ tv] ++ Gb), R = tb
                    -- p may be a function-call pattern: narrowing via Gp
C⟦(case s arms)⟧ = aux clauses, one per arm (clause-ordered, nondet)
C⟦(collapse e)⟧  = (R, [findall(te, Ge, R)])              exhaustive collect
C⟦(superpose t)⟧ = (R, [amb(t, R')] ++ C⟦R'-elem⟧)
                    -- enumerate the SYNTACTIC elements; each evaluated in its
                    -- own branch (branch-local failure, NONDET-1)
C⟦(cut)⟧         = (True, [!])                            prune to clause barrier
C⟦(once e)⟧      = C⟦(let $t e (let $u (cut) $t))⟧
C⟦(quote e)⟧     = (e, [])                                syntactic, not re-run
C⟦(match sp p tmpl)⟧ = (R, [spaceMatch(sp, p)] ++ C⟦tmpl⟧)
C⟦(add-atom sp a)⟧ etc. = world-effect builtin goals, sequenced left-to-right
```

**Typed staging (the staging family as ONE rule):** in an application whose
head has a declared type, arguments in `Atom`-typed positions are passed
SYNTACTICALLY (no flattening, no goal). This is PeTTa's compile-time
evaluation-point commitment.

Rules: `(= (f p1..pn) rhs)` compiles to the clause
`f(P1..Pn, R) :- Gp1..Gpn, Grhs.` where function calls inside the PATTERNS
also flatten to prefix goals (head narrowing). Rules keep file order.

## 3. The machine

State: `⟨ goals | bindings | world | alternatives ⟩`, fuel-bounded DFS.

```
(resolve)  user goal f(ts,R): clauses tried in order (freshened); head
           unified (full unification, occurs-check); body ++ rest pushed;
           a CLAUSE BARRIER is recorded for cut.
(builtin)  grounded goal g#(ts,R): if the needed arguments are ground, run
           via the grounding table; each result is an alternative. If not
           ground, DELAY: requeue after the next goal (bounded); a goal
           delayed past the fuel bound fails the branch.
(cut)      ! : discard alternatives back to the innermost clause barrier.
(findall)  run the sub-goals to exhaustion, collect the template instances
           in order; the collection itself is one deterministic result.
(unify)    t1 ≐ t2 : syntactic unification or branch failure.
(space)    spaceMatch unifies the pattern against the world's atoms
           (facts + rule atoms); add-atom/remove-atom/state ops mutate the
           world IMMEDIATELY and are NOT undone on backtracking (Prolog
           assert discipline); an open spaceMatch does not see atoms added
           after it started (logical update view).
(answers)  a bang's answers are the machine's solutions for its R, in
           search order; the harness compares them as a bag.
```

## 4. What stays with the rewriting kernel (transitional)

Files whose forms the compiler does not yet cover fall back to the rewriting
kernel PER FILE, visibly counted in the scoreboard (`fallback` column). The
fallback set must shrink monotonically; a fallback is a missing compile
equation, i.e. a SPEC gap, and is fixed here first.

## 5. Correspondence obligations (math-tier, queued)

- machine soundness vs the certified SLD (algos tier): a PettaLP derivation
  is an SLD derivation over the compiled program (checkAnswer's trace format
  is the interchange).
- compile-equation adequacy: C⟦·⟧ preserves the surface semantics on the
  probed corpus (empirical now, theorem later).
- HE untouched: PettaLP is a separate evaluation path; `reduceAtomP_he` and
  the kernel correspondence are unaffected by construction.

## 6. Anchoring, gates, and sunset (the principled-operation rules)

**Anchoring.** Every compile equation models a location in PeTTa's actual
transpiler (`src/translator.pl`, 434 lines) or runtime (`src/metta.pl`), and
carries a `[SPEC file:lines]` citation at its implementation site. Verified
against source 2026-07-03: clause flattening (translator.pl:17-34), pattern
narrowing via constrain_args (2-14), cons = the Prolog list constructor (3-8
— the cons-chain value representation is source-fact, not design choice),
superpose as disjunction (112-114), collapse = findall (115-116), cut = `!`
answering true (117-118), once (127-128), progn/prog1 (141-149), if with
else-on-any-non-true (151-162), case as committed if-chain with `\+ KeyGoal`
default (163-176, 388-399), let = chain with UNIFY-FIRST goal order
(178-181), let* (378-379), lambda closure conversion with free-variable
capture and partial(F, FreeVars) values (237-254), runtime reduce's
apply-or-data (50-64), partial application by argument append (26-30,
328-339), Expression-typed staging (354-363), stream-op rewrites (74-89),
forall/foldall (187-216), add/remove-atom (256-258), match (259-262),
`#+`-family = CLP(FD) `#=` (metta.pl:53-60 — our when/2-coroutined moded
arithmetic models its determinate cases; full FD propagation ledgered),
eval = meta-circular translate-and-call (metta.pl:245): the runtime value is
unchained and re-run through compileExpr against the LIVE definitions, and
the compiled goals are spliced (Machine `.evalg`, Step.evalg_ok/err,
step_evalg proved). This is the full semantics, not an approximation. Its
executable adequacy inherits the ONE standing frontier below.

**The correspondence gate — SEALED.** `Semantics.lean` is the authority, the
machine its executable mirror, and this is now a THEOREM:
`machineMirrorsSpec_proved` (PLeaTTa/Proofs/StepCases.lean) shows every
machine step on a live configuration is licensed by the `Step` relation, by
cases on the goal (15 case lemmas + assembly; zero sorry; axioms = the three
standard ones). The one honest boundary: `findall`/`softcut` nest
fuel-bounded sub-runs, and the relation licenses those only when the sub-run
is TERMINAL (`nestedRunHead` marks the exclusion) — fuel truncation is
outside the relation, the same honesty as LeaTTa's kernel vs its spec. The
shared constructions (`resolveAlts`, `wactDispatch`, `pull`, `cutTo`,
`unifyB`) make the correspondence hold by construction at the two most
intricate dispatches. A machine change that breaks a rule no longer
compiles against the theorem.

**PERF policy (decided).** No per-file tuning. The structural answers, in
order: (1) deep or search-heavy computation belongs to the certified
delegation lane (swipl finds, checkAnswer certifies) — a verification-grade
machine owes reasonable, not fast; (2) if in-machine speed is needed, the one
sanctioned optimization is first-argument indexing at `resolve` (the WAM
move), implemented once, measured against the whole corpus.

**Sunset clause (the dual-semantics debt) — EXECUTED 2026-07-03.** The
switch-kernel petta profile was scaffolding; its retirement criteria were
met and the retirement performed: (1) replay-before-retire — every file the
kernel covered is rederived by PLeaTTa or certified delegation (p19: solo
117/176, ∪ delegation 118/176; kernel-only set EMPTY; old scoreboards kept
as regression oracles in diffbench/run-t51.log); (2) the petta arms are out
of the HE kernel — the pettaProfile instantiation, its Minimal/ dialect
surface (prelude deltas, petta grounding table, profile-specialized prelude),
the --petta flag, and the profile-instantiated trichotomy theorems are
removed; `rg pettaProfile` hits only sunset notes. LeaTTa-HE is pure (canary
269/270 baseline); PLeaTTa is the sole PeTTa semantics. bind!/state/spaces
were ported into PLeaTTa as probed rules, not inherited implementation.
