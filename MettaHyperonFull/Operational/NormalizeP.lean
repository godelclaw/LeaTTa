-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Operational.NormalizeP
Layer: Operational
Purpose: The Strategy-parametric spec normalizer (ORDER-1/NONDET-1 formal
  account, C2.2). PeTTa's evaluation order — normalize-once, innermost,
  quote-guarded, with Prolog branch-local failure — is modeled as a
  bag-valued fuel-bounded normalizer `normalizeP` parameterized by an
  `EvalStrategy` (a position-permission predicate, the GSLT
  `Semantics/Strategy.lean` shape). Branch-local failure is native here: a
  head-step to `some []` (goal failure, `equalityStepP` under
  `noMatchEmpty`) contributes an EMPTY bag for that branch only, exactly the
  probe-verified `(superpose ((dead) 7))` → `7` behavior. The one-step
  content is the certified `reduceAtomP`; the strategy-gated context closure
  `CtxStepP` names the induced rewriting relation, and at the trivial
  strategy + HE profile it collapses to the certified head-step
  (`ctxStepP_stratNone_he`, the `oneStepStrat_all`-style recovery anchor).
Imports: MettaHyperonFull.Operational.SemanticsP
Trusted boundary: human-reviewed spec (the normalizer shape); the recovery
  theorem is fully proved.
Main exports: EvalStrategy, stratNone, stratAll, listProd, normalizeP,
  descendantsP, CtxStepP, ctxStepP_stratNone_he
Open obligations: star-soundness of `normalizeP` against
  `ReflTransGen (CtxStepP …)` and the kernel correspondence — C2.3.
-/
import MettaHyperonFull.Operational.SemanticsP

namespace Metta

/-- A strategy: may evaluation descend into argument position `i` (1-based)
of a head symbol? The GSLT `Strategy` shape, at the HE/PeTTa layer. -/
abbrev EvalStrategy := String → Nat → Bool

/-- No descent: head reduction only (the four-register machine's own view —
it never rewrites under constructors). -/
def stratNone : EvalStrategy := fun _ _ => false

/-- Native-PeTTa strategy: descend everywhere. The quote shield lives in the
dialect arm of `reduceAtomP` (`quoteStrips`), not in the strategy — quote's
argument is protected because the quote HEAD-step fires before any deeper
step is needed, mirroring the kernel's `(-> Atom Atom)` typing shield. -/
def stratAll : EvalStrategy := fun _ _ => true

/-- Cartesian product of child bags: every way to pick one normal form per
child. The empty bag of any child annihilates the product — a failed child
branch kills exactly the combinations that contain it. -/
def listProd : List (List Atom) → List (List Atom)
  | [] => [[]]
  | xs :: rest => xs.flatMap fun x => (listProd rest).map (x :: ·)

mutual

/-- Bag-valued, fuel-bounded, innermost normalizer. For each innermost-
normalized candidate: a head-step to `some reds` continues into the reducts
(rule bodies evaluate — but RESULTS are never re-scanned once inert, the
one-pass discipline); `none` means inert normal form; `some []` is goal
failure and kills the branch. -/
def normalizeP (p : EvalProfile) (strat : EvalStrategy) (cfg : RuntimeConfig)
    (kb : Space) : Nat → Atom → List Atom
  | 0, a => [a]
  | fuel + 1, a =>
      (descendantsP p strat cfg kb fuel a).flatMap fun a' =>
        match reduceAtomP p cfg kb a' with
        | none => [a']
        | some reds => reds.flatMap (normalizeP p strat cfg kb fuel)

/-- Innermost descent: normalize each strategy-permitted child, rebuild one
atom per combination of child normal forms. -/
def descendantsP (p : EvalProfile) (strat : EvalStrategy) (cfg : RuntimeConfig)
    (kb : Space) (fuel : Nat) : Atom → List Atom
  | Atom.expr (Atom.sym op :: args) =>
      let bags := (args.zipIdx 1).map fun (x, i) =>
        if strat op i then normalizeP p strat cfg kb fuel x else [x]
      (listProd bags).map fun args' => Atom.expr (Atom.sym op :: args')
  | a => [a]

end

/-- The strategy-gated context closure of the profile head-step: the
rewriting relation that `normalizeP` walks. `head` is one certified
`reduceAtomP` step on the whole atom; `congr` rewrites inside a permitted
argument position. -/
inductive CtxStepP (p : EvalProfile) (strat : EvalStrategy)
    (cfg : RuntimeConfig) (kb : Space) : Atom → Atom → Prop
  | head {a a' : Atom} {reds : List Atom} :
      reduceAtomP p cfg kb a = some reds → a' ∈ reds →
      CtxStepP p strat cfg kb a a'
  | congr {op : String} {args : List Atom} {i : Nat} {x' : Atom}
      (hi : i < args.length) :
      strat op (i + 1) = true →
      CtxStepP p strat cfg kb args[i] x' →
      CtxStepP p strat cfg kb (Atom.expr (Atom.sym op :: args))
        (Atom.expr (Atom.sym op :: args.set i x'))

/-- **Recovery anchor** (the `oneStepStrat_all` pattern, inverted to the
degenerate strategy): at the HE profile with NO descent permission, the
parametric context relation is exactly the certified original head-step —
the strategy machinery adds nothing that was not already certified. -/
theorem ctxStepP_stratNone_he {cfg : RuntimeConfig} {kb : Space}
    {a a' : Atom} :
    CtxStepP heProfile stratNone cfg kb a a' ↔
      ∃ reds, reduceAtom cfg kb a = some reds ∧ a' ∈ reds := by
  constructor
  · intro h
    cases h with
    | head hred hmem =>
        exact ⟨_, by rw [← reduceAtomP_he]; exact hred, hmem⟩
    | congr hi hstrat _ => simp [stratNone] at hstrat
  · rintro ⟨reds, hred, hmem⟩
    exact CtxStepP.head (by rw [reduceAtomP_he]; exact hred) hmem

end Metta
