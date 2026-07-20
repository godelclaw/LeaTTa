-- SPDX-License-Identifier: Apache-2.0

import PLeaTTa.Compile

/-!
# Desugaring equations for the application compiler

Several PLeaTTa compiler branches re-dispatch a surface form to another head.
This file proves those re-dispatches as plain implementation equations.  Of
the forms below, only `trace!` is literally a pinned `rewrite_streamops` rule;
the others still need an independent semantic adequacy argument against their
pinned PeTTa definitions.

These equations are unfolding lemmas for later adequacy proofs; they do not
discharge any construct's semantic obligation.  No agreement relation is
involved and no constructor is added to `TranslatesExpr` or `GoalAgrees`;
these are statements about the compiler alone.

Every equation carries the side condition required to select PLeaTTa's
built-in branch: a `translatorRules` hook on the source head takes precedence
in `compileAppFuel`, so the unconditional implementation equation would be
false when that head is shadowed.  This condition must not be confused with a
claim about pinned priority.  Adequacy also has to account for hooks on the
re-dispatch target; pinned direct clauses do not necessarily consult them.
-/

namespace PLeaTTa

open Metta (Atom)

set_option maxHeartbeats 4000000 in
/-- PLeaTTa aliases `(#+ a b)` to `(+ a b)`.

Pinned PeTTa instead defines `#+/3` as a CLPFD predicate
([SPEC metta.pl:53,316]); this implementation equation alone does not prove
that the two operations agree. -/
theorem compileAppFuel_hashPlus_eq (fuel counter : Nat) (env : CEnv)
    (a b : Atom)
    (noHook : env.translatorRules.contains "#+" = false) :
    compileAppFuel (fuel + 2) env counter "#+" [a, b]
      = compileAppFuel fuel env counter "+" [a, b] := by
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  simp only [compileAppCoreFuel]

set_option maxHeartbeats 4000000 in
/-- PLeaTTa aliases `(#- a b)` to `(- a b)`.

Pinned PeTTa instead defines the arity-three `#-` relation as a CLPFD predicate
([SPEC metta.pl:54,316]); semantic adequacy is a separate obligation. -/
theorem compileAppFuel_hashMinus_eq (fuel counter : Nat) (env : CEnv)
    (a b : Atom)
    (noHook : env.translatorRules.contains "#-" = false) :
    compileAppFuel (fuel + 2) env counter "#-" [a, b]
      = compileAppFuel fuel env counter "-" [a, b] := by
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  simp only [compileAppCoreFuel]

set_option maxHeartbeats 4000000 in
/-- PLeaTTa implements `and-then` by re-dispatching to `if`.

Pinned PeTTa translates `and-then` directly
([SPEC translator.pl:177-180]); connecting this equation to that clause must
prove the short-circuit behavior and account for any translator hook on `if`. -/
theorem compileAppFuel_andThen_eq (fuel counter : Nat) (env : CEnv)
    (a b : Atom)
    (noHook : env.translatorRules.contains "and-then" = false) :
    compileAppFuel (fuel + 2) env counter "and-then" [a, b]
      = compileAppFuel fuel env counter "if" [a, b, Atom.sym "False"] := by
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  simp only [compileAppCoreFuel]

set_option maxHeartbeats 4000000 in
/-- PLeaTTa implements `or-else` by re-dispatching to `if`.

Pinned PeTTa translates `or-else` directly
([SPEC translator.pl:181-183]); semantic adequacy, including target-hook
priority, is not established by this equation. -/
theorem compileAppFuel_orElse_eq (fuel counter : Nat) (env : CEnv)
    (a b : Atom)
    (noHook : env.translatorRules.contains "or-else" = false) :
    compileAppFuel (fuel + 2) env counter "or-else" [a, b]
      = compileAppFuel fuel env counter "if" [a, Atom.sym "True", b] := by
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  simp only [compileAppCoreFuel]

set_option maxHeartbeats 4000000 in
/-- [SPEC translator.pl:74-75] `trace!` is a pinned stream rewrite to
`(progn (println! message) value)`.

Pinned rewriting occurs before translator-rule lookup.  The `noHook` premise
below is needed by PLeaTTa's current branch order and records a supported-state
restriction for the later adequacy theorem. -/
theorem compileAppFuel_trace_eq (fuel counter : Nat) (env : CEnv)
    (message value : Atom)
    (noHook : env.translatorRules.contains "trace!" = false) :
    compileAppFuel (fuel + 2) env counter "trace!" [message, value]
      = compileAppFuel fuel env counter "progn"
          [Atom.expr [Atom.sym "println!", message], value] := by
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  simp only [compileAppCoreFuel]

set_option maxHeartbeats 4000000 in
/-- PLeaTTa compiles an immediately quoted `unquote` as `eval`.

When `lib_he.metta` is imported, pinned PeTTa defines this as an ordinary
MeTTa rule with a committing `cut` ([SPEC lib/lib_he.metta:64-67]); without
that library it is not a translator builtin.  Equivalence to this unconditional
compiler shortcut remains a semantic adequacy obligation. -/
theorem compileAppFuel_unquoteQuote_eq (fuel counter : Nat) (env : CEnv)
    (source : Atom)
    (noHook : env.translatorRules.contains "unquote" = false) :
    compileAppFuel (fuel + 2) env counter "unquote"
        [Atom.expr [Atom.sym "quote", source]]
      = compileAppFuel fuel env counter "eval" [source] := by
  rw [compileAppFuel.eq_2]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  simp only [compileAppCoreFuel]

end PLeaTTa
