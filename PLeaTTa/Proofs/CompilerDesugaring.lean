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

Every ordinary redispatch equation carries the side condition required to
select PLeaTTa's built-in branch. `trace!` is the deliberate exception: pinned
stream rewriting precedes translator-rule lookup, and the executable now does
the same. Adequacy also has to account for hooks on a redispatch target; pinned
direct clauses do not necessarily consult them.
-/

namespace PLeaTTa

open Metta (Atom)

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
  rw [rewriteStreamOp_hashPlus_none]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_def]
  rfl

/-- PLeaTTa aliases `(#- a b)` to `(- a b)`.

Pinned PeTTa instead defines the arity-three `#-` relation as a CLPFD predicate
([SPEC metta.pl:54,316]); semantic adequacy is a separate obligation. -/
theorem compileAppFuel_hashMinus_eq (fuel counter : Nat) (env : CEnv)
    (a b : Atom)
    (noHook : env.translatorRules.contains "#-" = false) :
    compileAppFuel (fuel + 2) env counter "#-" [a, b]
      = compileAppFuel fuel env counter "-" [a, b] := by
  rw [compileAppFuel.eq_2]
  rw [rewriteStreamOp_hashMinus_none]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_def]
  rfl

/-- [SPEC translator.pl:74-75] `trace!` is a pinned stream rewrite to
`(progn (println! message) value)`.

Pinned rewriting occurs before translator-rule lookup, so this equation holds
even when a translator rule named `trace!` is registered. -/
theorem compileAppFuel_trace_eq (fuel counter : Nat) (env : CEnv)
    (message value : Atom) :
    compileAppFuel (fuel + 2) env counter "trace!" [message, value]
      = compileAppFuel fuel env counter "progn"
          [Atom.expr [Atom.sym "println!", message], value] := by
  rw [compileAppFuel.eq_2]
  rw [rewriteStreamOp_trace_pair]
  simp only
  rw [compileExprFuel.eq_7 (x_4 := by simp)]

/-- The complete expression compiler performs the same pinned `trace!`
source rewrite, with the two extra application-dispatch steps exposed in the
fuel index. -/
theorem compileExprFuel_trace_rewrite_eq (fuel counter : Nat) (env : CEnv)
    (message value : Atom) :
    compileExprFuel (fuel + 5) env counter
        (.expr [.sym "trace!", message, value]) =
      compileExprFuel (fuel + 3) env counter
        (.expr
          [.sym "progn", .expr [.sym "println!", message], value]) := by
  rw [show fuel + 5 = (fuel + 4) + 1 by omega]
  rw [compileExprFuel.eq_7 (x_4 := by simp)]
  rw [show fuel + 4 = (fuel + 2) + 2 by omega]
  rw [compileAppFuel_trace_eq (fuel + 2) counter env message value]
  rw [show fuel + 3 = (fuel + 2) + 1 by omega]
  rw [compileExprFuel.eq_7 (x_4 := by simp)]

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
  rw [rewriteStreamOp_unquote_none]
  simp only [noHook, Bool.false_eq_true, ↓reduceIte]
  rw [compileAppCoreFuel.eq_def]
  rfl

end PLeaTTa
