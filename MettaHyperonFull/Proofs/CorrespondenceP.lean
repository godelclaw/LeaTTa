-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.CorrespondenceP
Layer: Proofs
Purpose: PeTTa-profile addendum to the interpreter-to-specification
  correspondence. The reduct-set core (`kernel_query_eq_mops_query`,
  `KernelStep = MopsStep`) is profile-INDEPENDENT — no dialect switch changes
  which equality rules fire — so `Correspondence.lean` already covers both
  profiles on the positive side (`equalityStepP_pos` makes this explicit).
  What the PeTTa profile adds is a classification of the NO-reduct case:
  goal failure (defined head) versus inert data (undefined head). This file
  proves the spec-side classifier (`SemanticsP.definedHead`) and the kernel
  classifier (`Interpreter.definedHeadK`) agree on a static knowledge base,
  and derives the failure/inert dichotomy against the kernel's dead-branch
  condition.
Imports: MettaHyperonFull.Proofs.Correspondence, MettaHyperonFull.Operational.SemanticsP
Trusted boundary: none (fully proved)
Main exports: equalityStepP_pos, definedHeadK_eq_definedHead,
  petta_failure_iff, petta_inert_iff
Open obligations: scope matches Correspondence.lean (static KB: `selfExtra`
  runtime rule additions are outside `definedHeadK_eq_definedHead`, which is
  stated at `World.empty`).
-/
import MettaHyperonFull.Proofs.Correspondence
import MettaHyperonFull.Proofs.ImportConcat
import MettaHyperonFull.Operational.SemanticsP

namespace Metta
open Metta.Minimal

/-- On the positive side the profiles are indistinguishable: whenever any
equality rule fires, `equalityStepP` IS `equalityStep`, for every profile. -/
theorem equalityStepP_pos (p : EvalProfile) (kb : Space) (a : Atom)
    (h : equalityReductions kb a ≠ []) :
    equalityStepP p kb a = equalityStep kb a := by
  unfold equalityStepP equalityStep
  cases hE : equalityReductions kb a with
  | nil => exact absurd hE h
  | cons x xs => rfl

/-- The spec's equality rules of a plain space are the kernel's extracted rules. -/
theorem equalityRules_eq_extractRules (atoms : List Atom) :
    Space.equalityRules ⟨atoms⟩ = extractRules atoms := rfl

/-- **Definedness classifiers agree.** For a static knowledge base, the
kernel's index-based defined-head test (`definedHeadK` over `candidatesW` at
`World.empty`) computes exactly the specification's whole-space test
(`definedHead`): first-argument indexing loses no defining rule and invents
none, at the level of head-and-arity definedness. -/
theorem definedHeadK_eq_definedHead (atoms : List Atom) (gt : GroundingTable)
    (a : Atom) :
    definedHeadK (MinEnv.ofAtomsGT atoms gt) World.empty a
      = definedHead ⟨atoms⟩ a := by
  match a with
  | Atom.sym _ => rfl
  | Atom.var _ => rfl
  | Atom.gnd _ => rfl
  | Atom.expr [] => rfl
  | Atom.expr (Atom.var _ :: rest) => rfl
  | Atom.expr (Atom.gnd _ :: rest) => rfl
  | Atom.expr (Atom.expr _ :: rest) => rfl
  | Atom.expr (Atom.sym op :: args) =>
      simp only [definedHeadK, definedHead]
      have hw : candidatesW (MinEnv.ofAtomsGT atoms gt) World.empty
          (Atom.expr (Atom.sym op :: args))
          = (MinEnv.ofAtomsGT atoms gt).candidates (Atom.expr (Atom.sym op :: args)) := by
        simp [candidatesW, World.empty]
      rw [hw]
      have hc : (MinEnv.ofAtomsGT atoms gt).candidates (Atom.expr (Atom.sym op :: args))
          = (MinEnv.ofAtomsGT atoms gt).ruleIndex.getD op []
            ++ (MinEnv.ofAtomsGT atoms gt).varRules := by
        simp [MinEnv.candidates, headKey]
      rw [hc, ruleIndex_getD, ofAtomsGT_varRules, List.any_append,
          equalityRules_eq_extractRules]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, List.any_eq_true]
      constructor
      · rintro (⟨⟨lhs, rhs⟩, hpr, hf⟩ | ⟨⟨lhs, rhs⟩, hpr, hf⟩)
        · -- bucket side: a genuine rule; its head equals `op` by the filter.
          obtain ⟨hmem, hkey⟩ := List.mem_filter.mp hpr
          refine ⟨(lhs, rhs), hmem, ?_⟩
          cases lhs with
          | sym s => simp at hf
          | var v => simp at hf
          | gnd g => simp at hf
          | expr l2 =>
            cases l2 with
            | nil => simp at hf
            | cons hd tl =>
              cases hd with
              | sym h =>
                simp only [headKey] at hkey
                have hho : h = op := by simpa using hkey
                subst hho
                simpa using hf
              | var v => simp at hf
              | gnd g => simp at hf
              | expr e => simp at hf
        · -- varRules side: head-less lhs cannot pass the sym-headed test.
          obtain ⟨hmem, hkey⟩ := List.mem_filter.mp hpr
          exfalso
          cases lhs with
          | sym s => simp at hf
          | var v => simp at hf
          | gnd g => simp at hf
          | expr l2 =>
            cases l2 with
            | nil => simp at hf
            | cons hd tl =>
              cases hd with
              | sym h => simp [headKey] at hkey
              | var v => simp at hf
              | gnd g => simp at hf
              | expr e => simp at hf
      · rintro ⟨⟨lhs, rhs⟩, hmem, hg⟩
        cases lhs with
        | sym s => simp at hg
        | var v => simp at hg
        | gnd g => simp at hg
        | expr l2 =>
          cases l2 with
          | nil => simp at hg
          | cons hd tl =>
            cases hd with
            | sym h =>
              have hg' := hg
              simp only [] at hg'
              have hho : (h == op) = true ∧ (tl.length == args.length) = true := by
                simpa using hg
              left
              refine ⟨(Atom.expr (Atom.sym h :: tl), rhs),
                List.mem_filter.mpr ⟨hmem, ?_⟩, ?_⟩
              · simp [headKey, hho.1]
              · simpa using hho.2
            | var v => simp at hg
            | gnd g => simp at hg
            | expr e => simp at hg

/-- **Definedness classifiers agree, dynamically.** For ANY runtime state —
rules imported or `add-atom`ed into `&self` included — the kernel's test
computes the specification's test over the CONCATENATED knowledge base.
Probe-grounded: definedness in native PeTTa is dynamic (removing a head's
last rule reverts it to inert). The static component is the previous
theorem; only the `selfExtra` component is new. -/
theorem definedHeadK_eq_definedHead_dyn (atoms : List Atom)
    (gt : GroundingTable) (w : World) (a : Atom) :
    definedHeadK (MinEnv.ofAtomsGT atoms gt) w a
      = definedHead ⟨atoms ++ w.selfExtra⟩ a := by
  match a with
  | Atom.sym _ => rfl
  | Atom.var _ => rfl
  | Atom.gnd _ => rfl
  | Atom.expr [] => rfl
  | Atom.expr (Atom.var _ :: rest) => rfl
  | Atom.expr (Atom.gnd _ :: rest) => rfl
  | Atom.expr (Atom.expr _ :: rest) => rfl
  | Atom.expr (Atom.sym op :: args) =>
      have hstatic := definedHeadK_eq_definedHead atoms gt
        (Atom.expr (Atom.sym op :: args))
      simp only [definedHeadK, definedHead] at hstatic ⊢
      rw [show candidatesW (MinEnv.ofAtomsGT atoms gt) World.empty
            (Atom.expr (Atom.sym op :: args))
          = (MinEnv.ofAtomsGT atoms gt).candidates
            (Atom.expr (Atom.sym op :: args)) from by
        simp [candidatesW, World.empty]] at hstatic
      have hw : candidatesW (MinEnv.ofAtomsGT atoms gt) w
            (Atom.expr (Atom.sym op :: args))
          = (MinEnv.ofAtomsGT atoms gt).candidates
              (Atom.expr (Atom.sym op :: args))
            ++ w.selfExtra.filterMap (fun x => match x with
              | Atom.expr [Atom.sym "=", lhs, rhs] =>
                  match headKey lhs,
                      headKey (Atom.expr (Atom.sym op :: args)) with
                  | some k1, some k2 =>
                      if k1 == k2 then some (lhs, rhs) else none
                  | none, _ => some (lhs, rhs)
                  | _, _ => none
              | _ => none) := rfl
      rw [hw, List.any_append, equalityRules_eq_extractRules,
          extractRules_append, List.any_append]
      rw [equalityRules_eq_extractRules] at hstatic
      rw [hstatic]
      congr 1
      -- the selfExtra component: filter guarantees head agreement
      apply Bool.eq_iff_iff.mpr
      rw [List.any_eq_true, List.any_eq_true]
      constructor
      · rintro ⟨⟨lhs, rhs⟩, hpr, hf⟩
        obtain ⟨y, hy, hmatch⟩ := List.mem_filterMap.mp hpr
        have hshape : y = Atom.expr [Atom.sym "=", lhs, rhs] ∧
            (headKey lhs = some op ∨ headKey lhs = none) := by
          split at hmatch
          · refine ⟨?_, ?_⟩
            · split at hmatch <;> (try split at hmatch) <;> simp_all
            · split at hmatch <;> (try split at hmatch) <;> simp_all [headKey]
          · simp at hmatch
        refine ⟨(lhs, rhs), List.mem_filterMap.mpr ⟨y, hy, by simp [hshape.1]⟩, ?_⟩
        cases lhs with
        | sym s => simp at hf
        | var v => simp at hf
        | gnd g => simp at hf
        | expr l3 =>
          cases l3 with
          | nil => simp at hf
          | cons hd tl =>
            cases hd with
            | var v => simp at hf
            | gnd g => simp at hf
            | expr e => simp at hf
            | sym h =>
                have hop : h = op := by
                  rcases hshape.2 with hk | hk <;> simpa [headKey] using hk
                subst hop
                simpa using hf
      · rintro ⟨⟨lhs, rhs⟩, hpr, hg⟩
        obtain ⟨y, hy, hmatch⟩ := List.mem_filterMap.mp hpr
        have hshape : y = Atom.expr [Atom.sym "=", lhs, rhs] := by
          split at hmatch <;> simp_all
        subst hshape
        cases lhs with
        | sym s => simp at hg
        | var v => simp at hg
        | gnd g => simp at hg
        | expr l3 =>
          cases l3 with
          | nil => simp at hg
          | cons hd tl =>
            cases hd with
            | var v => simp at hg
            | gnd g => simp at hg
            | expr e => simp at hg
            | sym h =>
                have hho : (h == op) = true ∧
                    (tl.length == args.length) = true := by simpa using hg
                have hop : h = op := by simpa using hho.1
                refine ⟨(Atom.expr (Atom.sym h :: tl), rhs),
                  List.mem_filterMap.mpr ⟨_, hy, ?_⟩, by simpa using hho.2⟩
                simp only [headKey, hop, beq_self_eq_true, if_true]

/- SUNSET: the pettaProfile-instantiated trichotomy theorems
(petta_failure_iff / petta_inert_iff) retired with the profile; PLeaTTa's
machineMirrorsSpec (PLeaTTa/Proofs/StepCases.lean) is the PeTTa
correspondence now. -/

end Metta
