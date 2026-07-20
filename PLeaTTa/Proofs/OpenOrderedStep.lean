/-
Module: PLeaTTa.Proofs.OpenOrderedStep
Purpose: First concrete source-to-observation witness connecting the
  independent ordered open-substitution semantics to the sealed machine.
Trusted boundary: none
Main exports: aliasIf_translates, aliasIf_compiles,
  aliasIf_reference_runs, aliasIf_executable_steps,
  aliasIf_source_to_observation
-/
import PLeaTTa.PeTTaSpec.OpenOrdered
import PLeaTTa.Proofs.PrologCoreAdequacy
import PLeaTTa.Proofs.ObservationAgreement

namespace PLeaTTa.OpenOrderedStep

open Metta (Atom Subst GroundingTable)
open PLeaTTa.CompilerAdequacy
open PLeaTTa.ObservationAgreement
open PLeaTTa.PrologCoreAdequacy
open PLeaTTa.PeTTaSpec.PrologCore
open PLeaTTa.PeTTaSpec.PrologCore.OpenSubstitution
open PLeaTTa.PeTTaSpec.PrologCore.OpenOrdered

/-- The independent translator state with no source-defined translator
hooks. -/
def emptyTranslatorState : TranslatorState := ⟨fun _ => False⟩

/-- The executable compiler environment corresponding to an empty source
world. -/
def emptyCompilerEnv : CEnv := mkEnv (fun _ => false) [] [] []

/-- A two-argument `if` whose selected branch returns a locally bound
variable.  Pinned `build_branch/4` shares that variable with the surrounding
result before condition execution. -/
def aliasIfSource (value : Int) : Atom :=
  .expr [.sym "if", .gnd (.bool true),
    .expr [.sym "let", .var "x", .gnd (.int value), .var "x"]]

/-- Independent result identity allocated for `aliasIfSource`. -/
def aliasIfReferenceQuery : Term := .variable (.generated 0)

/-- Independent normalized target emitted for `aliasIfSource`. -/
def aliasIfReferenceGoals (value : Int) :
    List PeTTaSpec.PrologCore.Goal :=
  [.unify (.variable (.source "x")) aliasIfReferenceQuery,
   .ifThenElse (.identical (.atom "true") (.atom "true"))
     (.conjunction
       [.unify (.variable (.source "x")) (.integer value)])
     .fail]

/-- The ordered open substitution returned by the independent execution. -/
def aliasIfReferenceAnswer (value : Int) : Substitution :=
  [(.generated 0, .integer value),
   (.source "x", .variable (.generated 0))]

/-- Executable result variable allocated for `aliasIfSource`. -/
def aliasIfExecutableQuery : Atom := .var "_q0"

private def aliasIfThenGoals (value : Int) : List PLeaTTa.Goal :=
  [PLeaTTa.Goal.eq (.var "x") (.gnd (.int value))]

private def aliasIfElseGoals : List PLeaTTa.Goal :=
  [PLeaTTa.Goal.eq (.sym "True") (.sym "False")]

private def aliasIfConditional (value : Int) : PLeaTTa.Goal :=
  PLeaTTa.Goal.ite (.sym "True")
    (aliasIfExecutableQuery, aliasIfThenGoals value)
    (aliasIfExecutableQuery, aliasIfElseGoals)
    aliasIfExecutableQuery

private def aliasIfTail (value : Int) : List PLeaTTa.Goal :=
  [aliasIfConditional value]

/-- Exact executable goal stream produced by the public compiler. -/
def aliasIfExecutableGoals (value : Int) : List PLeaTTa.Goal :=
  PLeaTTa.Goal.eq (.var "x") aliasIfExecutableQuery :: aliasIfTail value

/-- The independent pinned translator relation derives the normalized alias
prefix and ordered conditional body. -/
theorem aliasIf_translates (value : Int) :
    TranslatesExpr emptyTranslatorState 0 (aliasIfSource value)
      aliasIfReferenceQuery (aliasIfReferenceGoals value) 1 := by
  simpa [emptyTranslatorState, aliasIfSource, aliasIfReferenceQuery,
    aliasIfReferenceGoals] using
    (translates_ifThen_variable_alias emptyTranslatorState 0 "x" value
      (by simp [emptyTranslatorState])
      (by simp [emptyTranslatorState]))

/-- The public executable compiler produces the exact goal stream related by
`aliasIf_translates`; this is not a proof-only compiler. -/
theorem aliasIf_compiles (value : Int) :
    compileExpr emptyCompilerEnv 0 (aliasIfSource value) =
      .ok (aliasIfExecutableQuery, aliasIfExecutableGoals value, 1) := by
  unfold compileExpr
  have fuelEq : compilerFuel (aliasIfSource value) + 64 = 640 := by
    simp [compilerFuel, aliasIfSource, Atom.size]
  rw [fuelEq]
  have conditionCompiled :
      compileExprFuel 637 emptyCompilerEnv 0 (.gnd (.bool true)) =
        .ok (.sym "True", [], 0) := by
    rw [show 637 = 636 + 1 by omega, compileExprFuel.eq_4]
    rfl
  have patternCompiled :
      compileExprFuel 634 emptyCompilerEnv 0 (.var "x") =
        .ok (.var "x", [], 0) := by
    rw [show 634 = 633 + 1 by omega, compileExprFuel.eq_2]
  have valueCompiled :
      compileExprFuel 634 emptyCompilerEnv 0 (.gnd (.int value)) =
        .ok (.gnd (.int value), [], 0) := by
    rw [show 634 = 633 + 1 by omega, compileExprFuel.eq_4]
    rfl
  have bodyCompiled :
      compileExprFuel 634 emptyCompilerEnv 0 (.var "x") =
        .ok (.var "x", [], 0) := patternCompiled
  have letCompiled :
      compileExprFuel 637 emptyCompilerEnv 0
          (.expr [.sym "let", .var "x", .gnd (.int value), .var "x"]) =
        .ok (.var "x", aliasIfThenGoals value, 0) := by
    exact compileExprFuel_let_eq 634 emptyCompilerEnv 0
      (.var "x") (.gnd (.int value)) (.var "x")
      (.var "x") (.gnd (.int value)) (.var "x")
      [] [] [] 0 0 0 (by rfl) patternCompiled valueCompiled bodyCompiled
  have branchCompiled :
      compileBranch aliasIfExecutableQuery (.var "x", aliasIfThenGoals value) =
        ([PLeaTTa.Goal.eq (.var "x") aliasIfExecutableQuery],
         (aliasIfExecutableQuery, aliasIfThenGoals value)) := by
    rfl
  have compiled := compileExprFuel_ifThen_eq 637 emptyCompilerEnv 0
    (.gnd (.bool true))
    (.expr [.sym "let", .var "x", .gnd (.int value), .var "x"])
    (.sym "True") (.var "x") [] (aliasIfThenGoals value)
    [PLeaTTa.Goal.eq (.var "x") aliasIfExecutableQuery]
    0 0 (aliasIfExecutableQuery, aliasIfThenGoals value)
    (by rfl) conditionCompiled letCompiled branchCompiled
  change compileExprFuel 640 emptyCompilerEnv 0 (aliasIfSource value) =
    .ok (aliasIfExecutableQuery, aliasIfExecutableGoals value, 1) at compiled
  exact compiled

/-- The independent result and ordered goal stream are related to the exact
public compiler output by the general adequacy relations. -/
theorem aliasIf_compiler_agrees (value : Int) :
    TermAgrees aliasIfReferenceQuery aliasIfExecutableQuery ∧
    GoalsAgree (aliasIfReferenceGoals value)
      (aliasIfExecutableGoals value) := by
  have environmentAgreement :
      EnvAgrees emptyTranslatorState emptyCompilerEnv := by
    refine ⟨?_⟩
    intro name
    simp [emptyTranslatorState, emptyCompilerEnv, mkEnv]
  obtain ⟨internal, executableGoals, compiled, termAgreement,
      goalsAgreement⟩ :=
    compileExpr_initial_sound emptyCompilerEnv environmentAgreement
      (aliasIf_translates value)
  have resultEquality :
      (internal, executableGoals, 1) =
        (aliasIfExecutableQuery, aliasIfExecutableGoals value, 1) :=
    Except.ok.inj (compiled.symm.trans (aliasIf_compiles value))
  cases resultEquality
  exact ⟨termAgreement, goalsAgreement⟩

/-- Ordered call-free execution of the independent normalized target.  The
answer bag retains the explicit alias and its later value binding. -/
theorem aliasIf_reference_runs (value : Int) :
    RunsAll NoCalls [] (aliasIfReferenceGoals value)
      [aliasIfReferenceAnswer value] := by
  let aliasState : Substitution :=
    [(.source "x", .variable (.generated 0))]
  let resultState : Substitution :=
    [(.generated 0, .integer value),
      (.source "x", .variable (.generated 0))]
  have aliasUnifies : Unifies []
      (.variable (.source "x")) (.variable (.generated 0)) aliasState :=
    unifies_empty_distinct_alias _ _
      (LogicVar.source_ne_generated "x" 0)
  have valueUnifies : Unifies aliasState
      (.variable (.source "x")) (.integer value) resultState :=
    unifies_alias_source_with_integer _ _ value
  have conditionRun : Runs NoCalls aliasState
      (.identical (.atom "true") (.atom "true")) [aliasState] :=
    .identicalSuccess aliasState _ _ (by rfl)
  have bodyAll : RunsAll NoCalls aliasState
      [.unify (.variable (.source "x")) (.integer value)] [resultState] := by
    exact .cons aliasState _ [] [resultState] [resultState]
      (.unifySuccess aliasState resultState _ _ valueUnifies)
      (.cons resultState [] [] [resultState] []
        (.nil resultState) (.nil []))
  have bodyRun : Runs NoCalls aliasState
      (.conjunction
        [.unify (.variable (.source "x")) (.integer value)])
      [resultState] :=
    .conjunction aliasState _ _ bodyAll
  have conditionalRun : Runs NoCalls aliasState
      (.ifThenElse (.identical (.atom "true") (.atom "true"))
        (.conjunction
          [.unify (.variable (.source "x")) (.integer value)])
        .fail)
      [resultState] :=
    .ifThenElseSuccess aliasState aliasState [] _ _ _ _ conditionRun bodyRun
  have complete : RunsAll NoCalls []
      [.unify (.variable (.source "x")) (.variable (.generated 0)),
       .ifThenElse (.identical (.atom "true") (.atom "true"))
         (.conjunction
           [.unify (.variable (.source "x")) (.integer value)])
         .fail]
      [resultState] := by
    exact .cons [] _ _ [aliasState] [resultState]
      (.unifySuccess [] aliasState _ _ aliasUnifies)
      (.cons aliasState [] _ [resultState] []
        (.cons aliasState _ [] [resultState] [resultState] conditionalRun
          (.cons resultState [] [] [resultState] []
            (.nil resultState) (.nil [])))
        (.nil _))
  simpa [aliasIfReferenceGoals, aliasIfReferenceQuery,
    aliasIfReferenceAnswer, resultState] using complete

/-- The independent answer instantiates the translated result to the branch
integer. -/
theorem aliasIf_reference_query_value (value : Int) :
    (aliasIfReferenceAnswer value).applyTerm aliasIfReferenceQuery =
      .integer value := by
  simp [aliasIfReferenceAnswer, aliasIfReferenceQuery,
    Substitution.applyTerm, Term.instantiateOne]

/-- Executable configuration initialized directly from the public compiler's
result term, goals, and next counter. -/
def aliasIfExecutableInitial (world : PWorld) (value : Int) : Conf :=
  { cur := some (aliasIfExecutableGoals value, [])
    alts := []
    world := world
    counter := 1
    qterm := aliasIfExecutableQuery }

private def aliasBinding : Subst := [("x", aliasIfExecutableQuery)]

private def resolvedBinding (value : Int) : Subst :=
  [("x", .gnd (.int value)),
   ("_q0", .gnd (.int value))]

private def finalBinding (value : Int) : Subst :=
  trimFor [] aliasIfExecutableQuery (resolvedBinding value)

private def afterAlias (world : PWorld) (value : Int) : Conf :=
  { aliasIfExecutableInitial world value with
    cur := some (aliasIfTail value, aliasBinding) }

private def afterChoice (world : PWorld) (value : Int) : Conf :=
  { afterAlias world value with
    cur := some (aliasIfThenGoals value, aliasBinding) }

private def beforeAnswer (world : PWorld) (value : Int) : Conf :=
  { afterChoice world value with
    cur := some ([], finalBinding value) }

private def answered (world : PWorld) (value : Int) : Conf :=
  { beforeAnswer world value with
      cur := none
      answers := subst (finalBinding value) aliasIfExecutableQuery ::
        (beforeAnswer world value).answers
      answerKeys := PersistentSubst.atomExactKey
          (subst (finalBinding value) aliasIfExecutableQuery) ::
        (beforeAnswer world value).answerKeys
      answerKeys_sound := by
        simp only [List.map_cons]
        rw [(beforeAnswer world value).answerKeys_sound] }

private def terminal (world : PWorld) (value : Int) : Conf :=
  pull (answered world value)

private theorem unify_alias :
    unifyB [] (.var "x") aliasIfExecutableQuery = some aliasBinding := by
  simpa [aliasBinding, aliasIfExecutableQuery, Metta.Subst.compose] using
    (unifyB_fresh_capture [] "x" (.var "_q0")
      (by simp [Metta.Subst.lookup])
      (by simp [Atom.vars]))

private theorem trim_alias (value : Int) :
    trimFor (aliasIfTail value) aliasIfExecutableQuery aliasBinding =
      aliasBinding := by
  apply trimFor_eq_self_of_root_keys
  · intro name atom hmem
    simp only [aliasBinding, List.mem_singleton, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact isTrimRoot_ite_then_eq_left
      (.sym "True") aliasIfExecutableQuery aliasIfExecutableQuery
      aliasIfExecutableQuery (.gnd (.int value)) "x" []
      (aliasIfExecutableQuery, aliasIfElseGoals)
  · simp [aliasBinding]

private theorem chosen_branch (value : Int) :
    iteBranchGoals aliasIfExecutableQuery
        (aliasIfExecutableQuery, aliasIfThenGoals value) =
      aliasIfThenGoals value := by
  unfold iteBranchGoals
  change (if (Atom.var "_q0" == Atom.var "_q0") = true then
      aliasIfThenGoals value
    else PLeaTTa.Goal.eq (.var "_q0") (.var "_q0") ::
      aliasIfThenGoals value) = aliasIfThenGoals value
  rw [if_pos (by decide)]

private theorem unify_alias_value (value : Int) :
    unifyB aliasBinding (.var "x") (.gnd (.int value)) =
      some (resolvedBinding value) := by
  let aliasState : Subst := [("x", .var "_q0")]
  change unifyB aliasState (.var "x") (.gnd (.int value)) =
    some [("x", .gnd (.int value)),
      ("_q0", .gnd (.int value))]
  have resultLookup : Metta.Subst.lookup aliasState "_q0" = none := by
    simp [aliasState, Metta.Subst.lookup]
  have resultFresh :
      "_q0" ∉ (subst aliasState (.gnd (.int value))).vars := by
    simp [Atom.vars]
  have capture := unifyB_fresh_capture aliasState "_q0"
    (.gnd (.int value)) resultLookup resultFresh
  have sourceValue : subst aliasState (.var "x") = .var "_q0" := by
    simp [aliasState, subst, substN, Metta.Subst.lookup]
  unfold unifyB at capture ⊢
  rw [sourceValue]
  simpa [aliasState, Metta.Subst.compose, Metta.Subst.apply,
    Metta.Subst.lookup] using capture

private def aliasTopological : SubstTopological aliasBinding :=
  SubstTopological.cons_of_fresh [] emptySubstTopological
    "x" (.var "_q0")
    (by simp [Metta.Subst.lookup])
    (by simp [Atom.vars])
    (by simp [AtomAvoids, Metta.Subst.lookup])

private def resolvedTopological (value : Int) :
    SubstTopological (resolvedBinding value) :=
  unifyB_topological aliasBinding (.var "x") (.gnd (.int value))
    (resolvedBinding value) aliasTopological (unify_alias_value value)

private theorem final_query_value (value : Int) :
    subst (finalBinding value) aliasIfExecutableQuery =
      .gnd (.int value) := by
  have preserved := subst_trimFor_eq_of_topological []
    aliasIfExecutableQuery (resolvedBinding value)
    (resolvedTopological value) aliasIfExecutableQuery
    (by
      intro name hmem
      simp only [aliasIfExecutableQuery, Atom.vars,
        List.mem_singleton] at hmem
      subst name
      exact isTrimRoot_qterm_var [] "_q0")
  have resolved : subst (resolvedBinding value) aliasIfExecutableQuery =
      .gnd (.int value) := by
    apply subst_var_of_lookup_closed
    · simp [resolvedBinding, Metta.Subst.lookup]
    · simp [Atom.vars]
  exact preserved.trans resolved

private theorem alias_step (program : Prog) (grounding : GroundingTable)
    (world : PWorld) (value : Int) :
    Step program grounding (aliasIfExecutableInitial world value)
      (afterAlias world value) := by
  have step := Step.eq_ok (prog := program) (gt := grounding)
    (aliasIfExecutableInitial world value)
    (.var "x") aliasIfExecutableQuery (aliasIfTail value)
    [] aliasBinding (by rfl) unify_alias
  simpa [afterAlias, aliasIfExecutableInitial, trim_alias] using step

private theorem choice_step (program : Prog) (grounding : GroundingTable)
    (world : PWorld) (value : Int) :
    Step program grounding (afterAlias world value)
      (afterChoice world value) := by
  have step := Step.ite_true (prog := program) (gt := grounding)
    (afterAlias world value) (.sym "True")
    (aliasIfExecutableQuery, aliasIfThenGoals value)
    (aliasIfExecutableQuery, aliasIfElseGoals)
    aliasIfExecutableQuery [] aliasBinding (by rfl) (by simp)
  rw [chosen_branch] at step
  simpa [afterChoice, afterAlias, aliasIfExecutableInitial, aliasIfTail,
    aliasIfConditional] using step

private theorem value_step (program : Prog) (grounding : GroundingTable)
    (world : PWorld) (value : Int) :
    Step program grounding (afterChoice world value)
      (beforeAnswer world value) := by
  have step := Step.eq_ok (prog := program) (gt := grounding)
    (afterChoice world value) (.var "x") (.gnd (.int value)) []
    aliasBinding (resolvedBinding value) (by rfl) (unify_alias_value value)
  simpa [beforeAnswer, afterChoice, afterAlias, aliasIfExecutableInitial,
    finalBinding] using step

private theorem answer_step (program : Prog) (grounding : GroundingTable)
    (world : PWorld) (value : Int) :
    Step program grounding (beforeAnswer world value)
      (terminal world value) := by
  have step := Step.answer (prog := program) (gt := grounding)
    (beforeAnswer world value) (finalBinding value) (by rfl)
  simpa [terminal, answered, beforeAnswer, afterChoice, afterAlias,
    aliasIfExecutableInitial] using step

private theorem terminal_is_terminal (world : PWorld) (value : Int) :
    Terminal (terminal world value) := by
  simp [Terminal, terminal, answered, beforeAnswer, afterChoice, afterAlias,
    aliasIfExecutableInitial, pull, pullAuxTracked, pullAux]

private theorem terminal_answer_values (world : PWorld) (value : Int) :
    (terminal world value).answerValues = [.gnd (.int value)] := by
  rw [terminal, pull_answerValues]
  simp [answered, beforeAnswer, afterChoice, afterAlias,
    aliasIfExecutableInitial, Conf.answerValues, final_query_value]

/-- The sealed executable machine follows the normalized alias prefix, takes
the true branch, and publishes exactly the selected integer.  Program and
grounding parameters are arbitrary because this call-free trace cannot
consult either oracle. -/
theorem aliasIf_executable_steps (program : Prog)
    (grounding : GroundingTable) (world : PWorld) (value : Int) :
    ∃ final,
      StepStar program grounding (aliasIfExecutableInitial world value)
          final ∧
      Terminal final ∧
      final.answerValues = [.gnd (.int value)] := by
  refine ⟨terminal world value, ?_, terminal_is_terminal world value,
    terminal_answer_values world value⟩
  exact .tail _ _ _ (alias_step program grounding world value)
    (.tail _ _ _ (choice_step program grounding world value)
      (.tail _ _ _ (value_step program grounding world value)
        (.tail _ _ _ (answer_step program grounding world value)
          (.refl _))))

/-- First concrete composition witness across the independent translator,
the public executable compiler, ordered open-substitution execution, and the
sealed small-step machine.  This theorem is deliberately one parametric
source family, not a universal `if` adequacy claim. -/
theorem aliasIf_source_to_observation (program : Prog)
    (grounding : GroundingTable) (world : PWorld) (value : Int) :
    TranslatesExpr emptyTranslatorState 0 (aliasIfSource value)
        aliasIfReferenceQuery (aliasIfReferenceGoals value) 1 ∧
    compileExpr emptyCompilerEnv 0 (aliasIfSource value) =
        .ok (aliasIfExecutableQuery, aliasIfExecutableGoals value, 1) ∧
    TermAgrees aliasIfReferenceQuery aliasIfExecutableQuery ∧
    GoalsAgree (aliasIfReferenceGoals value)
        (aliasIfExecutableGoals value) ∧
    RunsAll NoCalls [] (aliasIfReferenceGoals value)
        [aliasIfReferenceAnswer value] ∧
    TermAgrees
        ((aliasIfReferenceAnswer value).applyTerm aliasIfReferenceQuery)
        (.gnd (.int value)) ∧
    ∃ final,
      StepStar program grounding (aliasIfExecutableInitial world value)
          final ∧
      Terminal final ∧
      final.answerValues = [.gnd (.int value)] := by
  refine ⟨aliasIf_translates value, aliasIf_compiles value,
    (aliasIf_compiler_agrees value).1,
    (aliasIf_compiler_agrees value).2,
    aliasIf_reference_runs value, ?_,
    aliasIf_executable_steps program grounding world value⟩
  rw [aliasIf_reference_query_value]
  exact .integer value

end PLeaTTa.OpenOrderedStep
