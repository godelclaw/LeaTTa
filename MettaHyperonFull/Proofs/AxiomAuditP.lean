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

#print axioms Metta.reduceAtomP_he
#print axioms Metta.reduceArgsP_he
#print axioms Metta.dialectStep_he
#print axioms Metta.equalityStepP_he
#print axioms Metta.definedHeadK_eq_definedHead
#print axioms Metta.petta_failure_iff
#print axioms Metta.petta_inert_iff
#print axioms Metta.equalityStepP_pos
#print axioms Metta.successAtomP_he
#print axioms Metta.stepAddAtomP_he
#print axioms Metta.stepRemAtomP_he
