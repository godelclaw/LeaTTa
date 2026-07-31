-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologFindallClosedBankUnifyBridge
Purpose: Preserve the closed local findall bank through selected literal
  unification success and residual failure
Trusted boundary: none
Main exports:
  ClosedLiteralFindallReadyRelates.selectedUnifySuccess,
  ClosedLiteralFindallReadyRelates.selectedUnifyFailure,
  closed_success_bank_empty_iff_no_residual
-/
import PLeaTTa.Proofs.PrologFindallClosedBankBridge

namespace PLeaTTa.PrologFindallClosedBankUnifyBridge

open Metta (Atom Subst GroundingTable)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PrologAnswerResourceBridge
open PrologDisjunctionStepBridge
open PrologFindallClosedBankBridge
open PrologGoalAlpha
open PrologMguBridge
open PrologMguComposition
open PrologOrdinaryStepBridge
open PrologStateBridge
open DemandDrivenStep

/-!
# Closed-bank preservation through the selected literal equality

Scheduling a literal `amb` installs only generator-owned alternatives above
the older bank.  The preceding bridge proves that a real `findall/3` entry
fixes that older bank to `[]`.  This module spends that fact on the next
actual transition:

* successful equality keeps the complete same-order residual literal bank
  and removes the empty suffix from the post-state equation;
* failed equality with a residual branch atomically pulls that branch and
  returns another activation indexed by the same literal empty suffix.

The singleton failing case is already closed by
`PrologFindallDisjunctionExitBridge`; it terminates the private generator and
exits with the empty bag.  No new control relation is introduced here.
-/

namespace ClosedLiteralFindallReadyRelates

/-- A successful selected literal equality preserves the closed generator
bank exactly.

The returned bank equation has no arbitrary suffix: every executable
alternative is one residual source literal branch in the same order and with
the same duplicate multiplicity.  The length equation is included as a
closure projection: closed means "no outside bank", not "no local
alternatives".  Reachability comes from the input closed-ready certificate,
not from this list equation.

[SPEC translator.pl:112-116; metta.pl:251-256; SWI:findall/3] -/
theorem selectedUnifySuccess
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {session : Session} {scope : CutScopeId} {current result : Substitution}
    {referenceValue referenceOutput : Term}
    {remainingReferences referenceTail :
      List PeTTaSpec.PrologCore.Goal}
    {runtime : Metta.Subst} {executableValue executableOutput : Metta.Atom}
    {remainingExecutables : List (Metta.Atom × List PLeaTTa.Goal)}
    {executableTail : List PLeaTTa.Goal} {state : OpenConf}
    (closed :
      ClosedLiteralFindallReadyRelates freshFrontier alpha support barrier
        canonical referenceBase session current referenceOutput
        (.unify referenceValue referenceOutput :: remainingReferences)
        referenceTail runtime executableOutput
        ((executableValue, []) :: remainingExecutables)
        executableTail state)
    (valueSupported :
      AlphaTreeSupported alpha support (Term.denote referenceValue))
    (outputSupported :
      AlphaTreeSupported alpha support (Term.denote referenceOutput))
    (supportIncluded : ∀ pair, pair ∈ support → pair ∈ alpha)
    (runtimeAvoids : AlphaRuntimeNamesAvoid support runtime)
    (live :
      AlphaRuntimeNamesLive support executableTail state.control.qterm)
    (resolved :
      UnifyResolution current referenceValue referenceOutput result) :
    ∃ sourceExtension : TreeSubstitution,
      ∃ installed : Metta.Subst,
        let selected := literalAmbPulledSuccessor state executableOutput
          executableValue remainingExecutables executableTail runtime
        let after := PrologOrdinaryStepBridge.unifySuccessor selected
          executableTail installed
        PLeaTTa.unifyB runtime executableOutput executableValue =
            some installed ∧
          RawStep session
            (.task scope
              (.disjunction
                  (.unify referenceValue referenceOutput ::
                    remainingReferences) :: referenceTail)
              current)
            [] .none session
            (.running
              (Search.disjoin scope
                (.unify referenceValue referenceOutput ::
                  remainingReferences)
                referenceTail current)) ∧
          DemandDrivenCallStep.Step prog gt (.ready state)
            (.ready selected) ∧
          RawStep session
            (Search.disjoin scope
              (.unify referenceValue referenceOutput :: remainingReferences)
              referenceTail current)
            [] .none session
            (.running
              (selectedUnifySourceSuccessor scope remainingReferences
                referenceTail current result)) ∧
          DemandDrivenCallStep.Step prog gt (.ready selected)
            (.ready after) ∧
          TaskPayloadAgrees alpha support barrier
            (sourceExtension ++ canonical) referenceBase result
            (PLeaTTa.trimFor executableTail state.control.qterm installed)
            referenceTail executableTail ∧
          OrderedTaskChoicePayloadsAgree alpha support barrier canonical
            referenceBase current runtime referenceTail remainingReferences
            (remainingExecutables.map fun branch =>
              PLeaTTa.ambBranchGoals executableOutput branch ++
                executableTail) ∧
          after.control.alts =
            remainingExecutables.map (fun branch =>
              PLeaTTa.Alt.br
                (PLeaTTa.ambBranchGoals executableOutput branch ++
                  executableTail)
                runtime) ∧
          after.control.alts.length = remainingExecutables.length ∧
          SessionRelatesPersistent freshFrontier session after.persistent ∧
          after.frames = state.frames ∧ after.scopes = state.scopes := by
  obtain
    ⟨sourceExtension, installed, installedExact, sourceSchedule,
      fineSchedule, sourceUnify, fineUnify, nextPayload, residualPayloads,
      bankExact, persistent, frames, scopes⟩ :=
    literal_selected_unify_two_step_correspondence
      (prog := prog) (gt := gt) (scope := scope) closed.ready
      valueSupported outputSupported supportIncluded runtimeAvoids live
      resolved
  have closedBank :
      (PrologOrdinaryStepBridge.unifySuccessor
        (literalAmbPulledSuccessor state executableOutput executableValue
          remainingExecutables executableTail runtime)
        executableTail installed).control.alts =
        remainingExecutables.map (fun branch =>
          PLeaTTa.Alt.br
            (PLeaTTa.ambBranchGoals executableOutput branch ++
              executableTail)
            runtime) := by
    rw [closed.bank_empty, List.append_nil] at bankExact
    exact bankExact
  refine
    ⟨sourceExtension, installed, installedExact, sourceSchedule,
      fineSchedule, sourceUnify, fineUnify, nextPayload, residualPayloads,
      closedBank, ?_, persistent, frames, scopes⟩
  rw [closedBank, List.length_map]

/-- A failed selected equality with at least one residual literal branch
preserves the same closed-bank activation certificate after the executable's
atomic `eq_fail → pull` step.

Both source and executable steps are the real scheduler transitions.  The
empty suffix is obtained from the reachable entry certificate, not supplied
as a fresh premise.

[SPEC translator.pl:112-116; metta.pl:251-256; SWI:findall/3] -/
theorem selectedUnifyFailure
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {session : Session} {scope : CutScopeId} {current : Substitution}
    {referenceValue referenceOutput : Term}
    {nextReference : PeTTaSpec.PrologCore.Goal}
    {remainingReferences referenceTail :
      List PeTTaSpec.PrologCore.Goal}
    {runtime : Metta.Subst}
    {executableValue executableOutput nextExecutable : Metta.Atom}
    {remainingExecutables : List (Metta.Atom × List PLeaTTa.Goal)}
    {executableTail : List PLeaTTa.Goal} {state : OpenConf}
    (closed :
      ClosedLiteralFindallReadyRelates freshFrontier alpha support barrier
        canonical referenceBase session current referenceOutput
        (.unify referenceValue referenceOutput ::
          nextReference :: remainingReferences)
        referenceTail runtime executableOutput
        ((executableValue, []) ::
          (nextExecutable, []) :: remainingExecutables)
        executableTail state)
    (valueSupported :
      AlphaTreeSupported alpha support (Term.denote referenceValue))
    (outputSupported :
      AlphaTreeSupported alpha support (Term.denote referenceOutput))
    (aliasSafe :
      CurrentUnifyOperandsAliasSafe current referenceValue referenceOutput)
    (clash :
      ¬ ∃ result,
        UnifyResolution current referenceValue referenceOutput result) :
    let selected :=
      literalAmbPulledSuccessor state executableOutput executableValue
        ((nextExecutable, []) :: remainingExecutables)
        executableTail runtime
    let next :=
      literalAmbPulledSuccessor state executableOutput nextExecutable
        remainingExecutables executableTail runtime
    PLeaTTa.unifyB runtime executableOutput executableValue = none ∧
      RawStep session
        (.task scope
          (.disjunction
              (.unify referenceValue referenceOutput ::
                nextReference :: remainingReferences) :: referenceTail)
          current)
        [] .none session
        (.running
          (Search.disjoin scope
            (.unify referenceValue referenceOutput ::
              nextReference :: remainingReferences)
            referenceTail current)) ∧
      DemandDrivenCallStep.Step prog gt (.ready state) (.ready selected) ∧
      RawStep session
        (Search.disjoin scope
          (.unify referenceValue referenceOutput ::
            nextReference :: remainingReferences)
          referenceTail current)
        [] .none session
        (.running
          (Search.disjoin scope (nextReference :: remainingReferences)
            referenceTail current)) ∧
      DemandDrivenCallStep.Step prog gt (.ready selected) (.ready next) ∧
      ClosedLiteralDisjunctionActivationAgrees alpha support scope barrier
        canonical referenceBase current runtime
        (Search.disjoin scope (nextReference :: remainingReferences)
          referenceTail current)
        next.control.cur next.control.alts ∧
      SessionRelatesPersistent freshFrontier session next.persistent ∧
      next.frames = state.frames ∧ next.scopes = state.scopes := by
  obtain
    ⟨failed, sourceSchedule, fineSchedule, sourceFailure, fineFailure,
      activation, persistent, frames, scopes⟩ :=
    literal_selected_unify_failure_two_step_correspondence
      (prog := prog) (gt := gt) (scope := scope) closed.ready
      valueSupported outputSupported aliasSafe clash
  have closedActivation :
      TaskChoiceActivationAgrees alpha support scope barrier canonical
        referenceBase current runtime []
        (Search.disjoin scope (nextReference :: remainingReferences)
          referenceTail current)
        (literalAmbPulledSuccessor state executableOutput nextExecutable
          remainingExecutables executableTail runtime).control.cur
        (literalAmbPulledSuccessor state executableOutput nextExecutable
          remainingExecutables executableTail runtime).control.alts := by
    rw [closed.bank_empty] at activation
    exact activation
  exact
    ⟨failed, sourceSchedule, fineSchedule, sourceFailure, fineFailure,
      ⟨closedActivation⟩, persistent, frames, scopes⟩

end ClosedLiteralFindallReadyRelates

/-- Exact local closure does not mean an empty executable bank: after a
successful selected equality the bank is empty exactly when no residual
literal branch remains.

This is the list-level discriminator consumed by later ownership proofs; it
rules out treating "closed" as a synonym for "no backtracking". -/
theorem closed_success_bank_empty_iff_no_residual
    {state : OpenConf}
    {remainingExecutables : List (Metta.Atom × List PLeaTTa.Goal)}
    {executableOutput : Metta.Atom} {executableTail : List PLeaTTa.Goal}
    {runtime : Metta.Subst}
    (exactBank :
      state.control.alts =
        remainingExecutables.map (fun branch =>
          PLeaTTa.Alt.br
            (PLeaTTa.ambBranchGoals executableOutput branch ++ executableTail)
            runtime)) :
    state.control.alts = [] ↔ remainingExecutables = [] := by
  rw [exactBank]
  simp

end PLeaTTa.PrologFindallClosedBankUnifyBridge
