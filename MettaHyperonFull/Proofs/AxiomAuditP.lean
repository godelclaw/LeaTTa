-- SPDX-License-Identifier: Apache-2.0

/-
Module: MettaHyperonFull.Proofs.AxiomAuditP
Layer: Proofs
Purpose: Build-visible axiom audit for the PeTTa-profile theorem surface
  (EvalProfile regression, dialect arms, no-match trichotomy, definedness
  correspondence, OBL-1 machine steps). The output must contain only
  Lean/Mathlib's standard classical axioms — no project axiom, no sorry.
Imports: MettaHyperonFull.Proofs.CorrespondenceP
Trusted boundary: none
Main exports: (audit output only)
Open obligations: keep aligned with PROFILE.md's theorem table.
-/
import MettaHyperonFull.Proofs.CorrespondenceP
import MettaHyperonFull.Proofs.ImportConcat
import MettaHyperonFull.Operational.NormalizeP
import MettaHyperonFull.Proofs.NormalizeSound
import MettaHyperonFull.Proofs.GroundModel
import MettaHyperonFull.Proofs.Coincidence
import MettaHyperonFull.Proofs.RelationalBridge

#print axioms Metta.reduceAtomP_he
#print axioms Metta.reduceArgsP_he
#print axioms Metta.dialectStep_he
#print axioms Metta.equalityStepP_he
#print axioms Metta.definedHeadK_eq_definedHead
#print axioms Metta.equalityStepP_pos
#print axioms Metta.successAtomP_he
#print axioms Metta.stepAddAtomP_he
#print axioms Metta.stepRemAtomP_he

-- Import theorem surface (T2.2)
#print axioms Metta.import_concat_query
#print axioms Metta.import_concat_irreducible

-- Strategy normalizer surface (C2.2)
#print axioms Metta.ctxStepP_stratNone_he
#print axioms Metta.normalizeP_sound
#print axioms Metta.descendantsP_sound
#print axioms Metta.definedHeadK_eq_definedHead_dyn

-- Ground model surface (T3.1)
#print axioms Metta.leastModelP_fixpoint
#print axioms Metta.leastModelP_least
#print axioms Metta.leastModelP_step

-- The coincidence theorem (T3.2)
#print axioms Metta.coincidence
#print axioms Metta.coincidence_sound
#print axioms Metta.coincidence_complete

-- Relational bridge (T3.3a)
#print axioms Metta.ground_answer_sound
#print axioms Metta.relational_answer_certified
