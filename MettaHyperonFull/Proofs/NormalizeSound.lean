/-
Module: MettaHyperonFull.Proofs.NormalizeSound
Layer: Proofs
Purpose: Star-soundness of the Strategy-parametric normalizer (C2.3, scoped):
  every atom in `normalizeP`'s result bag is reachable from the input by the
  strategy-gated context relation `CtxStepP` — the fuelled innermost
  scheduler is bookkeeping over the named rewriting relation, the same scope
  discipline `Correspondence.lean` applies to QUERY. Completeness and the
  kernel-driver correspondence stay explicitly out of scope (BURNDOWN).
Imports: MettaHyperonFull.Operational.NormalizeP, Mathlib.Logic.Relation
Trusted boundary: none (fully proved)
Main exports: mem_listProd, ctxStep_lift_star, star_congr_suffix,
  descendantsP_sound, normalizeP_sound
Open obligations: completeness (every CtxStepP-normal form is produced given
  fuel) and normalizer-vs-kernel-driver correspondence — ledgered.
-/
import MettaHyperonFull.Operational.NormalizeP
import Mathlib.Logic.Relation

namespace Metta

variable {p : EvalProfile} {strat : EvalStrategy} {cfg : RuntimeConfig}
  {kb : Space}

/-! ### Self-contained list helpers -/

theorem set_middle (pre rest : List Atom) (r r' : Atom) :
    (pre ++ r :: rest).set pre.length r' = pre ++ r' :: rest := by
  induction pre with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem get_middle (pre rest : List Atom) (r : Atom)
    (h : pre.length < (pre ++ r :: rest).length) :
    (pre ++ r :: rest)[pre.length] = r := by
  induction pre with
  | nil => rfl
  | cons x xs ih => simpa using ih (by simpa using h)

/-- Membership in the cartesian product of bags, pointwise. -/
theorem mem_listProd {bags : List (List Atom)} {l : List Atom} :
    l ∈ listProd bags ↔
      l.length = bags.length ∧
      ∀ i (hi : i < bags.length) (hl : i < l.length), l[i] ∈ bags[i] := by
  induction bags generalizing l with
  | nil =>
      simp only [listProd, List.mem_singleton]
      constructor
      · rintro rfl; simp
      · rintro ⟨hlen, _⟩; exact List.eq_nil_of_length_eq_zero hlen
  | cons xs rest ih =>
      simp only [listProd, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨x, hx, t, ht, rfl⟩
        obtain ⟨hlen, hpt⟩ := ih.mp ht
        refine ⟨by simp [hlen], ?_⟩
        intro i hi hl
        match i with
        | 0 => simpa using hx
        | j + 1 => simpa using hpt j (by simpa using hi) (by simpa using hl)
      · rintro ⟨hlen, hpt⟩
        match l with
        | [] => simp at hlen
        | x :: t =>
            have h0 := hpt 0 (by simp) (by simp)
            simp only [List.getElem_cons_zero] at h0
            refine ⟨x, h0, t, ?_, rfl⟩
            refine ih.mpr ⟨by simpa using hlen, ?_⟩
            intro j hj hl
            have hj1 := hpt (j + 1) (by simpa using hj) (by simpa using hl)
            simpa only [List.getElem_cons_succ] using hj1

/-! ### Congruence lifting -/

/-- Lift a star at a permitted argument position `i` to a star on the
rebuilt expression. -/
theorem ctxStep_lift_star {op : String} {args : List Atom} {i : Nat}
    (hi : i < args.length) (hstrat : strat op (i + 1) = true)
    {y : Atom}
    (h : Relation.ReflTransGen (CtxStepP p strat cfg kb) args[i] y) :
    Relation.ReflTransGen (CtxStepP p strat cfg kb)
      (Atom.expr (Atom.sym op :: args))
      (Atom.expr (Atom.sym op :: args.set i y)) := by
  induction h with
  | refl => rw [List.set_getElem_self]
  | tail hstar hstep ih =>
      rename_i mid fin
      refine Relation.ReflTransGen.tail ih ?_
      have hi' : i < (args.set i mid).length := by simpa using hi
      have hmid : (args.set i mid)[i] = mid := List.getElem_set_self hi'
      have hc := CtxStepP.congr (p := p) (strat := strat) (cfg := cfg)
        (kb := kb) (op := op) (args := args.set i mid) (i := i) (x' := fin)
        hi' hstrat (by rw [hmid]; exact hstep)
      simpa [List.set_set] using hc

/-- Sequencing stars across positions: rebuild the suffix one child at a
time. `pre` is the already-rebuilt prefix. -/
theorem star_congr_suffix {op : String} :
    ∀ (pre rest rest' : List Atom),
      rest'.length = rest.length →
      (∀ i (h : i < rest.length) (h' : i < rest'.length),
        rest'[i] = rest[i] ∨
        (strat op (pre.length + i + 1) = true ∧
          Relation.ReflTransGen (CtxStepP p strat cfg kb) rest[i] rest'[i])) →
      Relation.ReflTransGen (CtxStepP p strat cfg kb)
        (Atom.expr (Atom.sym op :: (pre ++ rest)))
        (Atom.expr (Atom.sym op :: (pre ++ rest')))
  | _, [], [], _, _ => Relation.ReflTransGen.refl
  | _, [], _ :: _, hlen, _ => by simp at hlen
  | _, _ :: _, [], hlen, _ => by simp at hlen
  | pre, r :: rest, r' :: rest', hlen, hpt => by
      have h0 := hpt 0 (by simp) (by simp)
      have step1 : Relation.ReflTransGen (CtxStepP p strat cfg kb)
          (Atom.expr (Atom.sym op :: (pre ++ r :: rest)))
          (Atom.expr (Atom.sym op :: (pre ++ r' :: rest))) := by
        rcases h0 with heq | ⟨hs, hstar⟩
        · simp only [List.getElem_cons_zero] at heq
          rw [heq]
        · have hi : pre.length < (pre ++ r :: rest).length := by simp
          have hget := get_middle pre rest r hi
          have hlift := ctxStep_lift_star (p := p) (strat := strat)
            (cfg := cfg) (kb := kb) (op := op) hi
            (by simpa [Nat.add_comm] using hs)
            (y := r') (by rw [hget]; simpa using hstar)
          rwa [set_middle] at hlift
      refine Relation.ReflTransGen.trans step1 ?_
      have hrec := star_congr_suffix (pre ++ [r']) rest rest'
        (by simpa using hlen)
        (fun i h h' => by
          have := hpt (i + 1) (by simpa using h) (by simpa using h')
          simpa [Nat.add_right_comm, Nat.add_assoc] using this)
      simpa using hrec

/-! ### Soundness -/

/-- Every rebuilt atom from innermost descent is star-reachable, given
star-soundness of the child normalizer at this fuel. -/
theorem descendantsP_sound (fuel : Nat)
    (ihn : ∀ a b, b ∈ normalizeP p strat cfg kb fuel a →
      Relation.ReflTransGen (CtxStepP p strat cfg kb) a b) :
    ∀ a a', a' ∈ descendantsP p strat cfg kb fuel a →
      Relation.ReflTransGen (CtxStepP p strat cfg kb) a a' := by
  intro a a' ha'
  match a with
  | Atom.sym _ | Atom.var _ | Atom.gnd _ | Atom.expr []
  | Atom.expr (Atom.var _ :: _) | Atom.expr (Atom.gnd _ :: _)
  | Atom.expr (Atom.expr _ :: _) =>
      simp only [descendantsP, List.mem_singleton] at ha'
      subst ha'
      exact Relation.ReflTransGen.refl
  | Atom.expr (Atom.sym op :: args) =>
      simp only [descendantsP, List.mem_map] at ha'
      obtain ⟨args', hargs', rfl⟩ := ha'
      obtain ⟨hlen, hpt⟩ := mem_listProd.mp hargs'
      have hbagslen : ((args.zipIdx 1).map fun (x, i) =>
          if strat op i then normalizeP p strat cfg kb fuel x else [x]).length
          = args.length := by simp
      have hstar := star_congr_suffix (p := p) (strat := strat) (cfg := cfg)
        (kb := kb) (op := op) [] args args'
        (by rw [hlen, hbagslen])
        (fun i h h' => by
          have hib : i < ((args.zipIdx 1).map fun (x, j) =>
              if strat op j then normalizeP p strat cfg kb fuel x
              else [x]).length := by rw [hbagslen]; exact h
          have hmem := hpt i hib h'
          have hbag : ((args.zipIdx 1).map fun (x, j) =>
              if strat op j then normalizeP p strat cfg kb fuel x
              else [x])[i]
              = if strat op (i + 1) then normalizeP p strat cfg kb fuel args[i]
                else [args[i]] := by
            simp [List.getElem_zipIdx, Nat.add_comm]
          rw [hbag] at hmem
          by_cases hs : strat op (i + 1)
          · rw [if_pos hs] at hmem
            exact Or.inr ⟨by simpa using hs, by simpa using ihn args[i] args'[i] hmem⟩
          · rw [if_neg hs] at hmem
            exact Or.inl (by simpa using hmem))
      simpa using hstar

/-- **Star-soundness.** Every result of the fuelled innermost normalizer is
reachable from the input by the strategy-gated context relation: the
scheduler is bookkeeping over `CtxStepP`. -/
theorem normalizeP_sound :
    ∀ (fuel : Nat) (a b : Atom), b ∈ normalizeP p strat cfg kb fuel a →
      Relation.ReflTransGen (CtxStepP p strat cfg kb) a b := by
  intro fuel
  induction fuel with
  | zero =>
      intro a b hb
      simp only [normalizeP, List.mem_singleton] at hb
      subst hb
      exact Relation.ReflTransGen.refl
  | succ n ih =>
      intro a b hb
      simp only [normalizeP, List.mem_flatMap] at hb
      obtain ⟨a', ha', hb⟩ := hb
      have hstar1 := descendantsP_sound n ih a a' ha'
      cases hred : reduceAtomP p cfg kb a' with
      | none =>
          rw [hred] at hb
          simp only [List.mem_singleton] at hb
          subst hb
          exact hstar1
      | some reds =>
          rw [hred] at hb
          simp only [List.mem_flatMap] at hb
          obtain ⟨r, hr, hb⟩ := hb
          exact Relation.ReflTransGen.trans hstar1
            (Relation.ReflTransGen.trans
              (Relation.ReflTransGen.single (CtxStepP.head hred hr))
              (ih r b hb))

end Metta
