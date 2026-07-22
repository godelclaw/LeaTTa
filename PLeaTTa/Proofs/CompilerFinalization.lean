-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.CompilerFinalization
Purpose: Prove that source-facing compilation solves and erases every
  translation-time alias before executable goals are exposed.
Trusted boundary: none
-/
import PLeaTTa.Compile

namespace PLeaTTa

set_option maxHeartbeats 2000000 in
/-- Erasing one raw goal recursively removes every compiler-only alias marker
from the runtime goal that remains. -/
theorem eraseCompileAliasesGoal_aliasFree :
    ∀ goal runtimeGoal,
      eraseCompileAliasesGoal goal = some runtimeGoal →
      collectCompileAliasesGoal runtimeGoal = [] := by
  intro goal
  induction goal using Goal.rec
      (motive_2 := fun goals =>
        collectCompileAliasesGoals (eraseCompileAliasesGoals goals) = [])
      (motive_3 := fun branches =>
        collectCompileAliasesBranches
          (eraseCompileAliasesBranches branches) = [])
      (motive_4 := fun branch =>
        collectCompileAliasesGoals
          (eraseCompileAliasesGoals branch.2) = [])
  all_goals try simp_all [eraseCompileAliasesGoal,
    eraseCompileAliasesGoals, eraseCompileAliasesBranches,
    collectCompileAliasesGoal, collectCompileAliasesGoals,
    collectCompileAliasesBranches]
  case cons head tail headIH tailIH =>
    cases erased : eraseCompileAliasesGoal head with
    | none => simpa [eraseCompileAliasesGoals, erased] using tailIH
    | some runtimeGoal =>
        have headFree := headIH runtimeGoal erased
        simp [collectCompileAliasesGoals, headFree, tailIH]

/-- Alias erasure is complete over an arbitrary nested ordered goal list. -/
theorem eraseCompileAliasesGoals_aliasFree (goals : List Goal) :
    collectCompileAliasesGoals (eraseCompileAliasesGoals goals) = [] := by
  induction goals with
  | nil => rfl
  | cons goal goals inductionHypothesis =>
      cases erased : eraseCompileAliasesGoal goal with
      | none =>
          simpa [eraseCompileAliasesGoals, erased] using inductionHypothesis
      | some runtimeGoal =>
          have headFree :=
            eraseCompileAliasesGoal_aliasFree goal runtimeGoal erased
          simp [collectCompileAliasesGoals, eraseCompileAliasesGoals, erased,
            headFree, inductionHypothesis]

set_option maxHeartbeats 2000000 in
/-- Deep compile-time substitution preserves the absence of alias markers. -/
theorem substCompiledGoal_aliasFree (binding : Metta.Subst) :
    ∀ goal,
      collectCompileAliasesGoal goal = [] →
      collectCompileAliasesGoal (substCompiledGoal binding goal) = [] := by
  intro goal
  induction goal using Goal.rec
      (motive_2 := fun goals =>
        collectCompileAliasesGoals goals = [] →
        collectCompileAliasesGoals (substCompiledGoals binding goals) = [])
      (motive_3 := fun branches =>
        collectCompileAliasesBranches branches = [] →
        collectCompileAliasesBranches
          (substCompiledBranches binding branches) = [])
      (motive_4 := fun branch =>
        collectCompileAliasesGoals branch.2 = [] →
        collectCompileAliasesGoals
          (substCompiledGoals binding branch.2) = [])
  all_goals simp_all [substCompiledGoal, substCompiledGoals,
    substCompiledBranches, collectCompileAliasesGoal,
    collectCompileAliasesGoals, collectCompileAliasesBranches]

/-- Pointwise deep substitution preserves alias freedom of a goal list. -/
theorem substCompiledGoals_aliasFree (binding : Metta.Subst) :
    ∀ goals,
      collectCompileAliasesGoals goals = [] →
      collectCompileAliasesGoals (substCompiledGoals binding goals) = [] := by
  intro goals
  induction goals with
  | nil => simp [collectCompileAliasesGoals, substCompiledGoals]
  | cons goal goals inductionHypothesis =>
      simp only [collectCompileAliasesGoals, substCompiledGoals]
      simp_all only [List.append_eq_nil_iff]
      intro allowed
      exact ⟨substCompiledGoal_aliasFree binding goal allowed.1, trivial⟩

/-- Every successful expression finalization exposes only runtime goals. -/
theorem finalizeCompiledExpression_aliasFree
    {term : Metta.Atom} {goals : List Goal} {nextCounter : Nat}
    {result : Metta.Atom × List Goal × Nat}
    (finalized :
      finalizeCompiledExpression term goals nextCounter = .ok result) :
    collectCompileAliasesGoals result.2.1 = [] := by
  dsimp only [finalizeCompiledExpression] at finalized
  cases equation :
      resolveCompileAliases (collectCompileAliasesGoals goals) with
  | error message =>
      rw [equation] at finalized
      contradiction
  | ok binding =>
      rw [equation] at finalized
      injection finalized with resultEquation
      rw [← resultEquation]
      exact substCompiledGoals_aliasFree binding
        (eraseCompileAliasesGoals goals)
        (eraseCompileAliasesGoals_aliasFree goals)

/-- Every successful clause finalization exposes an alias-free runtime body. -/
theorem finalizeCompiledClause_aliasFree
    {clause result : Clause}
    (finalized : finalizeCompiledClause clause = .ok result) :
    collectCompileAliasesGoals result.body = [] := by
  dsimp only [finalizeCompiledClause] at finalized
  cases equation :
      resolveCompileAliases (collectCompileAliasesGoals clause.body) with
  | error message =>
      rw [equation] at finalized
      contradiction
  | ok binding =>
      rw [equation] at finalized
      injection finalized with resultEquation
      rw [← resultEquation]
      exact substCompiledGoals_aliasFree binding
        (eraseCompileAliasesGoals clause.body)
        (eraseCompileAliasesGoals_aliasFree clause.body)

/-- Source-facing expression compilation never leaks translation metadata to
the executable machine. -/
theorem compileExprFresh_aliasFree
    {env : CEnv} {counter : Nat} {source : Metta.Atom}
    {result : Metta.Atom × List Goal × Nat}
    (compiled : compileExprFresh env counter source = .ok result) :
    collectCompileAliasesGoals result.2.1 = [] := by
  dsimp only [compileExprFresh] at compiled
  cases equation : compileExpr env
      (compilerFreshCounterForAtom counter source) source with
  | error message =>
      rw [equation] at compiled
      contradiction
  | ok raw =>
      rcases raw with ⟨term, goals, nextCounter⟩
      rw [equation] at compiled
      exact finalizeCompiledExpression_aliasFree compiled

/-- Source-facing rule compilation never leaks translation metadata into a
compiled clause body. -/
theorem compileRuleFresh_aliasFree
    {env : CEnv} {counter : Nat} {params : List Metta.Atom}
    {rhs : Metta.Atom} {clause : Clause} {nextCounter : Nat}
    (compiled :
      compileRuleFresh env counter params rhs = .ok (clause, nextCounter)) :
    collectCompileAliasesGoals clause.body = [] := by
  dsimp only [compileRuleFresh] at compiled
  cases equation : compileRule env
      (compilerFreshCounterForAtoms counter (rhs :: params)) params rhs with
  | error message =>
      rw [equation] at compiled
      contradiction
  | ok raw =>
      rcases raw with ⟨rawClause, rawNextCounter⟩
      rw [equation] at compiled
      change (do
        let finalized ← finalizeCompiledClause rawClause
        .ok (finalized, rawNextCounter)) =
          .ok (clause, nextCounter) at compiled
      cases finalEquation : finalizeCompiledClause rawClause with
      | error message =>
          rw [finalEquation] at compiled
          contradiction
      | ok finalClause =>
          rw [finalEquation] at compiled
          change Except.ok (finalClause, rawNextCounter) =
            Except.ok (clause, nextCounter) at compiled
          have parts :
              finalClause = clause ∧ rawNextCounter = nextCounter :=
            Prod.mk.inj (Except.ok.inj compiled)
          rw [← parts.1]
          exact finalizeCompiledClause_aliasFree finalEquation

end PLeaTTa
