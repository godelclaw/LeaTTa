/-
Module: MettaHyperonFull.Operational.SemanticsP
Layer: Operational
Purpose: Profile-parametric one-step reducer. `reduceAtomP p` generalizes
  `Semantics.reduceAtom` over an `EvalProfile`: at `heProfile` it is proven
  equal to the original (`reduceAtomP_he`), so the HE certification is
  untouched; at `pettaProfile` it enables the measured native-PeTTa dialect
  switches (defined-head no-match -> empty, 2-arg `if`, `quote` stripping).
  `Semantics.lean` itself is deliberately left unmodified.
Imports: MettaHyperonFull.Operational.Semantics, MettaHyperonFull.Operational.Profile
Trusted boundary: human-reviewed spec (the profile arms); the he-regression is
  fully proved.
Main exports: definedHead, equalityStepP, symbolApplyP, reduceAtomP,
  reduceArgsP, reduceAtomP_he, reduceArgsP_he
Open obligations: PeTTa one-pass (no re-reduction of rule results) is not yet
  modeled — see BURNDOWN.md.
-/
import MettaHyperonFull.Operational.Semantics
import MettaHyperonFull.Operational.Profile

namespace Metta

/-- Does the head symbol of `a` carry at least one equality rule of the same
head and arity in `kb`? Distinguishes a *defined function* with no matching
clause (Prolog goal failure under `noMatchEmpty`) from plain constructor data
(inert in every dialect). Head-and-arity mirrors Prolog's predicate indexing,
which is what PeTTa compiles equality rules into. -/
def definedHead (kb : Space) : Atom → Bool
  | Atom.expr (Atom.sym op :: args) =>
      kb.equalityRules.any (fun pr =>
        match pr.fst with
        | Atom.expr (Atom.sym op' :: args') =>
            op' == op && args'.length == args.length
        | _ => false)
  | _ => false

/-- Profile-aware `equalityStep`: under `noMatchEmpty`, a defined head with no
matching rule reduces to the empty result set instead of being a normal form. -/
def equalityStepP (p : EvalProfile) (kb : Space) (a : Atom) : Option (List Atom) :=
  match equalityReductions kb a with
  | [] => if p.noMatchEmpty && definedHead kb a then some [] else none
  | reds => some reds

/-- Success atom of a space mutation under a profile (DIV-006 axis):
native PeTTa's boolean `true`, or HE's unit (probe 2026-07-02). -/
def successAtomP (p : EvalProfile) : Atom :=
  if p.successTrue then Atom.gnd (Ground.bool true) else Atom.unit

/-- Profile-parametric `stepAddAtom` (OBL-1): identical to the original except
for the dialect success shape. -/
def stepAddAtomP (p : EvalProfile) (s : State) (call a : Atom) : State :=
  let st := { s with input := Space.removeOne s.input call }
  State.pushOutput (State.addKb st a) (successAtomP p)

/-- Profile-parametric `stepRemAtom` (OBL-1). -/
def stepRemAtomP (p : EvalProfile) (s : State) (call a : Atom) : State :=
  let st := { s with input := Space.removeOne s.input call }
  State.pushOutput (State.remKb st a) (successAtomP p)

theorem successAtomP_he : successAtomP heProfile = Atom.unit := rfl

theorem stepAddAtomP_he (s : State) (call a : Atom) :
    stepAddAtomP heProfile s call a = stepAddAtom s call a := rfl

theorem stepRemAtomP_he (s : State) (call a : Atom) :
    stepRemAtomP heProfile s call a = stepRemAtom s call a := rfl

theorem equalityStepP_he (kb : Space) (a : Atom) :
    equalityStepP heProfile kb a = equalityStep kb a := by
  unfold equalityStepP equalityStep heProfile
  cases equalityReductions kb a <;> simp

mutual

/-- Dialect-specific special forms, factored out so the delta between engines
is a single inspectable function. Returns `some` only when the profile enables
a dialect arm; `dialectStep_he` proves it is `none` at the HE profile, so the
parametric reducer collapses to the original there. Out-of-dialect shapes fall
through (`none`) and are handled by the generic logic — never an error. -/
def dialectStep (p : EvalProfile) (cfg : RuntimeConfig) (kb : Space) :
    (op : String) → (args : List Atom) → Option (List Atom)
  | "quote", [x] =>
      -- Native PeTTa (probe-verified): (quote x) strips to x.
      if p.quoteStrips then some [x] else none
  | "if", [c, t] =>
      -- Native PeTTa 2-arg if (probe-verified): failure branch is empty.
      if p.ifArity2 then
        match c with
        | Atom.gnd (Ground.bool true) => some [t]
        | Atom.sym "True" => some [t]
        | Atom.gnd (Ground.bool false) => some []
        | Atom.sym "False" => some []
        | _ =>
            match reduceAtomP p cfg kb c with
            | some cs => some (cs.map fun c' => Atom.expr [Atom.sym "if", c', t])
            | none => none
      else none
  | _, _ => none

/-- Profile-parametric one-step reducer: arm-for-arm the original
`Semantics.reduceAtom`, except that the generic symbol-application arm first
consults `dialectStep` and uses `equalityStepP` for the no-match policy. -/
def reduceAtomP (p : EvalProfile) (cfg : RuntimeConfig) (kb : Space) :
    Atom → Option (List Atom)
  | Atom.expr [Atom.sym "transform", pattern, tmpl] => some (kb.transform pattern tmpl)
  | Atom.expr [Atom.sym "match", _, pattern, tmpl] => some (kb.transform pattern tmpl)
  | Atom.expr [Atom.sym "get-type", x] => some (kb.typeAssignments x)
  | Atom.expr [Atom.sym "if", c, t, e] =>
      match c with
      | Atom.gnd (Ground.bool true) => some [t]
      | Atom.sym "True" => some [t]
      | Atom.gnd (Ground.bool false) => some [e]
      | Atom.sym "False" => some [e]
      | _ =>
          match reduceAtomP p cfg kb c with
          | some cs => some (cs.map fun c' => Atom.expr [Atom.sym "if", c', t, e])
          | none => none
  | Atom.expr [Atom.sym "let", Atom.var x, v, body] =>
      match reduceAtomP p cfg kb v with
      | some vs => some (vs.map fun v' => Atom.expr [Atom.sym "let", Atom.var x, v', body])
      | none => some [Subst.apply [(x, v)] body]
  | Atom.expr [Atom.sym "superpose", Atom.expr xs] => some xs
  | Atom.expr (Atom.sym op :: args) =>
      let whole := Atom.expr (Atom.sym op :: args)
      match dialectStep p cfg kb op args with
      | some r => some r
      | none =>
          match cfg.groundings.lookup op with
          | none => equalityStepP p kb whole
          | some g =>
              let applyOp : Option (List Atom) :=
                match g.impl args with
                | ReduceResult.ok rs => some rs
                | ReduceResult.runtimeError msg =>
                    some [Atom.expr [Atom.sym "Error", whole, Atom.gnd (Ground.str msg)]]
                | _ => equalityStepP p kb whole
              match g.mode with
              | GroundMode.quoteArgs => applyOp
              | GroundMode.evalArgs =>
                  match reduceArgsP p cfg kb args with
                  | some argss => some (argss.map (fun args' => Atom.expr (Atom.sym op :: args')))
                  | none => applyOp
  | a => equalityStepP p kb a

/-- Profile-parametric `reduceArgs`. -/
def reduceArgsP (p : EvalProfile) (cfg : RuntimeConfig) (kb : Space) :
    List Atom → Option (List (List Atom))
  | [] => none
  | x :: xs =>
      match reduceAtomP p cfg kb x with
      | some rs => some (rs.map (fun r => r :: xs))
      | none =>
          match reduceArgsP p cfg kb xs with
          | some xss => some (xss.map (fun xs' => x :: xs'))
          | none => none

end

/-- At the HE profile no dialect arm fires. Non-recursive: the profile guards
short-circuit before any recursion. -/
theorem dialectStep_he (cfg : RuntimeConfig) (kb : Space) (op : String)
    (args : List Atom) : dialectStep heProfile cfg kb op args = none := by
  rw [dialectStep.eq_def]
  split <;> simp [heProfile]

mutual

/-- Regression: at the HE profile the parametric reducer IS the certified
original — `dialectStep` is `none` and `equalityStepP` collapses. -/
theorem reduceAtomP_he (cfg : RuntimeConfig) (kb : Space) (a : Atom) :
    reduceAtomP heProfile cfg kb a = reduceAtom cfg kb a := by
  rw [reduceAtomP.eq_def, reduceAtom.eq_def]
  match a with
  | Atom.expr [Atom.sym "transform", pattern, tmpl] => rfl
  | Atom.expr [Atom.sym "match", _, pattern, tmpl] => rfl
  | Atom.expr [Atom.sym "get-type", x] => rfl
  | Atom.expr [Atom.sym "if", c, t, e] =>
      have ih := reduceAtomP_he cfg kb c
      cases c <;> simp_all <;> rfl
  | Atom.expr [Atom.sym "let", Atom.var x, v, body] =>
      have ih := reduceAtomP_he cfg kb v
      simp_all <;> rfl
  | Atom.expr [Atom.sym "superpose", Atom.expr xs] => rfl
  | Atom.expr (Atom.sym op :: args) =>
      have ihArgs := reduceArgsP_he cfg kb args
      have ihElems : ∀ b ∈ args, reduceAtomP heProfile cfg kb b = reduceAtom cfg kb b :=
        fun b _ => reduceAtomP_he cfg kb b
      split <;> simp_all [dialectStep_he, equalityStepP_he] <;> rfl
  | Atom.sym s => simp [equalityStepP_he]
  | Atom.var v => simp [equalityStepP_he]
  | Atom.gnd g => simp [equalityStepP_he]
  | Atom.expr [] => simp [equalityStepP_he]
  | Atom.expr (Atom.var v :: rest) => simp [equalityStepP_he]
  | Atom.expr (Atom.gnd g :: rest) => simp [equalityStepP_he]
  | Atom.expr (Atom.expr e :: rest) => simp [equalityStepP_he]
termination_by sizeOf a
decreasing_by
  all_goals
    first
      | (simp_all; omega)
      | (have hmem := List.sizeOf_lt_of_mem (by assumption); simp_all; omega)

theorem reduceArgsP_he (cfg : RuntimeConfig) (kb : Space) (l : List Atom) :
    reduceArgsP heProfile cfg kb l = reduceArgs cfg kb l := by
  rw [reduceArgsP.eq_def, reduceArgs.eq_def]
  match l with
  | [] => rfl
  | x :: xs =>
      have ih1 := reduceAtomP_he cfg kb x
      have ih2 := reduceArgsP_he cfg kb xs
      simp_all <;> rfl
termination_by sizeOf l
decreasing_by all_goals (simp_all; omega)

end

end Metta
