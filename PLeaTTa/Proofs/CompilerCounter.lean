import PLeaTTa.Compile
import PLeaTTa.Proofs.CompilerTypeFreshening

namespace PLeaTTa

structure CompilerCounterAt (fuel : Nat) : Prop where
  expr : ∀ env start source term goals next,
    compileExprFuel fuel env start source = .ok (term, goals, next) →
      start ≤ next
  pattern : ∀ env start source term goals next,
    compilePatternFuel fuel env start source = .ok (term, goals, next) →
      start ≤ next
  app : ∀ env start head args term goals next,
    compileAppFuel fuel env start head args = .ok (term, goals, next) →
      start ≤ next
  appCore : ∀ env start head args term goals next,
    compileAppCoreFuel fuel env start head args = .ok (term, goals, next) →
      start ≤ next
  typedArgs : ∀ env start sources types terms goals next,
    compileTypedArgsFuel fuel env start sources types = .ok (terms, goals, next) →
      start ≤ next
  argsAt : ∀ env start head index sources terms goals next,
    compileArgsAtFuel fuel env start head index sources = .ok (terms, goals, next) →
      start ≤ next
  caseArms : ∀ env scrutinee result start arms goals next,
    compileCaseArmsFuel fuel env scrutinee result start arms =
        .ok (goals, next) →
      start ≤ next
  patternList : ∀ env start sources terms goals next,
    compilePatternListFuel fuel env start sources = .ok (terms, goals, next) →
      start ≤ next
  list : ∀ env start sources terms goals next,
    compileListFuel fuel env start sources = .ok (terms, goals, next) →
      start ≤ next

attribute [local grind =>] CompilerCounterAt.expr CompilerCounterAt.pattern
  CompilerCounterAt.app CompilerCounterAt.appCore CompilerCounterAt.typedArgs
  CompilerCounterAt.argsAt CompilerCounterAt.caseArms
  CompilerCounterAt.patternList CompilerCounterAt.list

theorem compilerCounterAt_zero : CompilerCounterAt 0 := by
  constructor <;> intros <;>
    simp only [compileExprFuel.eq_1, compilePatternFuel_zero_eq,
      compileAppFuel.eq_1, compileAppCoreFuel.eq_1,
      compileTypedArgsFuel.eq_1, compileArgsAtFuel_zero_eq,
      compileCaseArmsFuel_zero_eq, compilePatternListFuel.eq_1,
      compileListFuel.eq_1] at * <;> contradiction

theorem compileExprFuel_counter_step (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    ∀ env start source term goals next,
      compileExprFuel (fuel + 1) env start source = .ok (term, goals, next) →
        start ≤ next := by
  intro env start source term goals next compiled
  rw [compileExprFuel.eq_def] at compiled
  split at compiled <;> simp_all [fresh]
  · exact ih.app _ _ _ _ _ _ _ compiled
  · simp only [Bind.bind, Except.bind] at compiled
    split at compiled
    · simp at compiled
    · have first := ih.list _ _ _ _ _ _ (by assumption)
      rcases compiled with ⟨_, _, rfl⟩
      omega
  · simp only [Bind.bind, Except.bind] at compiled
    split at compiled
    · simp at compiled
    · have headMono := ih.expr _ _ _ _ _ _ (by assumption)
      split at compiled
      · simp at compiled
      · have tailMono := ih.list _ _ _ _ _ _ (by assumption)
        split at compiled
        · simp only [Except.ok.injEq] at compiled
          rcases compiled with ⟨_, _, rfl⟩
          omega
        · simp only [Except.ok.injEq] at compiled
          rcases compiled with ⟨_, _, rfl⟩
          omega

theorem compileListFuel_counter_step (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    ∀ env start sources terms goals next,
      compileListFuel (fuel + 1) env start sources =
          .ok (terms, goals, next) →
        start ≤ next := by
  intro env start sources terms goals next compiled
  cases sources with
  | nil =>
      rw [compileListFuel_nil_eq] at compiled
      rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
      exact Nat.le_refl _
  | cons source sources =>
      rw [compileListFuel_cons_eq] at compiled
      simp only [Bind.bind, Except.bind] at compiled
      split at compiled
      · contradiction
      · have first := ih.expr _ _ _ _ _ _ (by assumption)
        split at compiled
        · contradiction
        · have rest := ih.list _ _ _ _ _ _ (by assumption)
          rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
          exact Nat.le_trans first rest

theorem compilePatternListFuel_counter_step (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    ∀ env start sources terms goals next,
      compilePatternListFuel (fuel + 1) env start sources =
          .ok (terms, goals, next) →
        start ≤ next := by
  intro env start sources terms goals next compiled
  cases sources with
  | nil =>
      rw [compilePatternListFuel_nil_eq] at compiled
      rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
      exact Nat.le_refl _
  | cons source sources =>
      rw [compilePatternListFuel_cons_eq] at compiled
      simp only [Bind.bind, Except.bind] at compiled
      split at compiled
      · contradiction
      · have first := ih.pattern _ _ _ _ _ _ (by assumption)
        split at compiled
        · contradiction
        · have rest := ih.patternList _ _ _ _ _ _ (by assumption)
          rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
          exact Nat.le_trans first rest

theorem compileArgsAtFuel_counter_step (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    ∀ env start head index sources terms goals next,
      compileArgsAtFuel (fuel + 1) env start head index sources =
          .ok (terms, goals, next) →
        start ≤ next := by
  intro env start head index sources terms goals next compiled
  cases sources with
  | nil =>
      rw [compileArgsAtFuel_nil_eq] at compiled
      rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
      exact Nat.le_refl _
  | cons source sources =>
      cases staged : env.atomTyped head index with
      | true =>
          rw [compileArgsAtFuel_staged_eq fuel env start head index source
            sources staged] at compiled
          simp only [Bind.bind, Except.bind] at compiled
          split at compiled
          · contradiction
          · have rest := ih.argsAt _ _ _ _ _ _ _ _ (by assumption)
            rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
            exact rest
      | false =>
          rw [compileArgsAtFuel_evaluated_eq fuel env start head index source
            sources staged] at compiled
          simp only [Bind.bind, Except.bind] at compiled
          split at compiled
          · contradiction
          · have first := ih.expr _ _ _ _ _ _ (by assumption)
            split at compiled
            · contradiction
            · have rest := ih.argsAt _ _ _ _ _ _ _ _ (by assumption)
              rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
              exact Nat.le_trans first rest

theorem compileTypeCheckWhen_counter_le (requiresCheck : Bool)
    (value expected : Metta.Atom) (start : Nat) :
    start ≤ (compileTypeCheckWhen requiresCheck value expected start).2 := by
  cases requiresCheck with
  | false => simp [compileTypeCheckWhen]
  | true =>
      simp [compileTypeCheckWhen, fresh]
      omega

theorem compileTypeCheck_counter_le (value expected : Metta.Atom)
    (start : Nat) :
    start ≤ (compileTypeCheck value expected start).2 := by
  exact compileTypeCheckWhen_counter_le (typeRequiresCheck expected) value
    expected start

theorem compileResultTypeCheck_counter_le (value expected : Metta.Atom)
    (start : Nat) :
    start ≤ (compileResultTypeCheck value expected start).2 := by
  exact compileTypeCheckWhen_counter_le (resultTypeRequiresCheck expected)
    value expected start

theorem compileTypedArgsFuel_counter_step (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    ∀ env start sources types terms goals next,
      compileTypedArgsFuel (fuel + 1) env start sources types =
          .ok (terms, goals, next) →
        start ≤ next := by
  intro env start sources types terms goals next compiled
  cases sources with
  | nil =>
      cases types with
      | nil =>
          rw [compileTypedArgsFuel_nil_eq] at compiled
          rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
          exact Nat.le_refl _
      | cons ty types =>
          rw [compileTypedArgsFuel_surplus_type_eq] at compiled
          rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
          exact Nat.le_refl _
  | cons source sources =>
      cases types with
      | nil =>
          rw [compileTypedArgsFuel_missing_type_eq] at compiled
          contradiction
      | cons ty types =>
          cases expression : (ty == (.sym "Expression" : Metta.Atom)) with
          | true =>
              rw [compileTypedArgsFuel.eq_def] at compiled
              simp only [expression, if_true] at compiled
              simp only [Bind.bind, Except.bind] at compiled
              split at compiled
              · contradiction
              · have rest := ih.typedArgs _ _ _ _ _ _ _ (by assumption)
                rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
                exact rest
          | false =>
              rw [compileTypedArgsFuel_evaluated_eq fuel env start source ty
                sources types expression] at compiled
              simp only [Bind.bind, Except.bind] at compiled
              split at compiled
              · contradiction
              · have first := ih.expr _ _ _ _ _ _ (by assumption)
                split at compiled
                · contradiction
                · rename_i exprOutcome exprValue exprEq typedOutcome
                    typedValue typedEq
                  have checked := compileTypeCheck_counter_le exprValue.1 ty
                    exprValue.2.2
                  have rest := ih.typedArgs _ _ _ _ _ _ _ (by assumption)
                  rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
                  exact Nat.le_trans first (Nat.le_trans checked rest)

theorem compileCaseArmsFuel_counter_step (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    ∀ env scrutinee result start arms goals next,
      compileCaseArmsFuel (fuel + 1) env scrutinee result start arms =
          .ok (goals, next) →
        start ≤ next := by
  intro env scrutinee result start arms goals next compiled
  cases arms with
  | nil =>
      rw [compileCaseArmsFuel_nil_eq] at compiled
      rcases Except.ok.inj compiled with ⟨_, rfl⟩
      exact Nat.le_refl _
  | cons arm more =>
      cases arm with
      | var name =>
          rw [compileCaseArmsFuel_var_malformed_eq] at compiled
          contradiction
      | sym name =>
          rw [compileCaseArmsFuel_sym_malformed_eq] at compiled
          contradiction
      | gnd ground =>
          rw [compileCaseArmsFuel_gnd_malformed_eq] at compiled
          contradiction
      | expr items =>
          cases items with
          | nil =>
              rw [compileCaseArmsFuel_expr_nil_malformed_eq] at compiled
              contradiction
          | cons pattern tail =>
              cases tail with
              | nil =>
                  rw [compileCaseArmsFuel_expr_singleton_malformed_eq] at compiled
                  contradiction
              | cons body rest =>
                  cases rest with
                  | cons third rest =>
                      rw [compileCaseArmsFuel_expr_many_malformed_eq] at compiled
                      contradiction
                  | nil =>
                      cases pattern with
                      | var name =>
                          rw [compileCaseArmsFuel_var_pair_eq] at compiled
                          simp only [Bind.bind, Except.bind] at compiled
                          split at compiled
                          · contradiction
                          · have patternMono := ih.pattern _ _ _ _ _ _
                                (by assumption)
                            split at compiled
                            · contradiction
                            · have bodyMono := ih.expr _ _ _ _ _ _
                                  (by assumption)
                              split at compiled
                              · contradiction
                              · have armsMono := ih.caseArms _ _ _ _ _ _ _
                                    (by assumption)
                                rcases Except.ok.inj compiled with ⟨_, rfl⟩
                                exact Nat.le_trans patternMono
                                  (Nat.le_trans bodyMono armsMono)
                      | gnd ground =>
                          rw [compileCaseArmsFuel_gnd_pair_eq] at compiled
                          simp only [Bind.bind, Except.bind] at compiled
                          split at compiled
                          · contradiction
                          · have patternMono := ih.pattern _ _ _ _ _ _
                                (by assumption)
                            split at compiled
                            · contradiction
                            · have bodyMono := ih.expr _ _ _ _ _ _
                                  (by assumption)
                              split at compiled
                              · contradiction
                              · have armsMono := ih.caseArms _ _ _ _ _ _ _
                                    (by assumption)
                                rcases Except.ok.inj compiled with ⟨_, rfl⟩
                                exact Nat.le_trans patternMono
                                  (Nat.le_trans bodyMono armsMono)
                      | expr nested =>
                          rw [compileCaseArmsFuel_expr_pair_eq] at compiled
                          simp only [Bind.bind, Except.bind] at compiled
                          split at compiled
                          · contradiction
                          · have patternMono := ih.pattern _ _ _ _ _ _
                                (by assumption)
                            split at compiled
                            · contradiction
                            · have bodyMono := ih.expr _ _ _ _ _ _
                                  (by assumption)
                              split at compiled
                              · contradiction
                              · have armsMono := ih.caseArms _ _ _ _ _ _ _
                                    (by assumption)
                                rcases Except.ok.inj compiled with ⟨_, rfl⟩
                                exact Nat.le_trans patternMono
                                  (Nat.le_trans bodyMono armsMono)
                      | sym name =>
                          by_cases empty : name = "Empty"
                          · subst name
                            rw [compileCaseArmsFuel_empty_eq] at compiled
                            exact ih.caseArms _ _ _ _ _ _ _ compiled
                          · rw [compileCaseArmsFuel_sym_pair_eq fuel env
                              scrutinee result start name empty] at compiled
                            simp only [Bind.bind, Except.bind] at compiled
                            split at compiled
                            · contradiction
                            · have patternMono := ih.pattern _ _ _ _ _ _
                                  (by assumption)
                              split at compiled
                              · contradiction
                              · have bodyMono := ih.expr _ _ _ _ _ _
                                    (by assumption)
                                split at compiled
                                · contradiction
                                · have armsMono := ih.caseArms _ _ _ _ _ _ _
                                      (by assumption)
                                  rcases Except.ok.inj compiled with ⟨_, rfl⟩
                                  exact Nat.le_trans patternMono
                                    (Nat.le_trans bodyMono armsMono)

theorem compilePatternFuel_counter_step (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    ∀ env start source term goals next,
      compilePatternFuel (fuel + 1) env start source =
          .ok (term, goals, next) →
        start ≤ next := by
  intro env start source term goals next compiled
  cases source with
  | var name =>
      rw [compilePatternFuel_var_eq] at compiled
      rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
      exact Nat.le_refl _
  | sym name =>
      rw [compilePatternFuel_sym_eq] at compiled
      rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
      exact Nat.le_refl _
  | gnd ground =>
      rw [compilePatternFuel_gnd_eq] at compiled
      rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
      exact Nat.le_refl _
  | expr items =>
      cases items with
      | nil =>
          rw [compilePatternFuel_nil_eq] at compiled
          rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
          exact Nat.le_refl _
      | cons head arguments =>
          cases head with
          | var name =>
              rw [compilePatternFuel_var_head_eq] at compiled
              simp only [Bind.bind, Except.bind] at compiled
              split at compiled
              · contradiction
              · have mono := ih.patternList _ _ _ _ _ _ (by assumption)
                rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
                exact mono
          | gnd ground =>
              rw [compilePatternFuel_gnd_head_eq] at compiled
              simp only [Bind.bind, Except.bind] at compiled
              split at compiled
              · contradiction
              · have mono := ih.patternList _ _ _ _ _ _ (by assumption)
                rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
                exact mono
          | expr nested =>
              rw [compilePatternFuel_expr_head_eq] at compiled
              simp only [Bind.bind, Except.bind] at compiled
              split at compiled
              · contradiction
              · have mono := ih.patternList _ _ _ _ _ _ (by assumption)
                rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
                exact mono
          | sym name =>
              cases arguments with
              | nil =>
                  rw [compilePatternFuel_sym_nil_eq] at compiled
                  split at compiled
                  · exact ih.expr _ _ _ _ _ _ compiled
                  · simp only [Bind.bind, Except.bind] at compiled
                    split at compiled
                    · contradiction
                    · have mono := ih.patternList _ _ _ _ _ _
                          (by assumption)
                      rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
                      exact mono
              | cons first tail =>
                  cases tail with
                  | nil =>
                      rw [compilePatternFuel_sym_singleton_eq] at compiled
                      split at compiled
                      · exact ih.expr _ _ _ _ _ _ compiled
                      · simp only [Bind.bind, Except.bind] at compiled
                        split at compiled
                        · contradiction
                        · have mono := ih.patternList _ _ _ _ _ _
                              (by assumption)
                          rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
                          exact mono
                  | cons second rest =>
                      cases rest with
                      | nil =>
                          by_cases chain : name = "#c"
                          · subst name
                            rw [compilePatternFuel_chain_eq] at compiled
                            rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
                            exact Nat.le_refl _
                          · by_cases consName : name = "cons"
                            · subst name
                              rw [compilePatternFuel_cons_eq] at compiled
                              simp only [Bind.bind, Except.bind] at compiled
                              split at compiled
                              · contradiction
                              · have firstMono := ih.pattern _ _ _ _ _ _
                                    (by assumption)
                                split at compiled
                                · contradiction
                                · have secondMono := ih.pattern _ _ _ _ _ _
                                      (by assumption)
                                  rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
                                  exact Nat.le_trans firstMono secondMono
                            · rw [compilePatternFuel_sym_pair_other_eq fuel env
                                  start name first second chain consName] at compiled
                              split at compiled
                              · exact ih.expr _ _ _ _ _ _ compiled
                              · simp only [Bind.bind, Except.bind] at compiled
                                split at compiled
                                · contradiction
                                · have mono := ih.patternList _ _ _ _ _ _
                                      (by assumption)
                                  rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
                                  exact mono
                      | cons third rest =>
                          rw [compilePatternFuel_sym_many_eq] at compiled
                          split at compiled
                          · exact ih.expr _ _ _ _ _ _ compiled
                          · simp only [Bind.bind, Except.bind] at compiled
                            split at compiled
                            · contradiction
                            · have mono := ih.patternList _ _ _ _ _ _
                                  (by assumption)
                              rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
                              exact mono

theorem foldlM_counter_mono {state item error : Type}
    (step : (state × Nat) → item → Except error (state × Nat))
    (stepMono : ∀ accumulator element outcome,
      step accumulator element = .ok outcome →
        accumulator.2 ≤ outcome.2) :
    ∀ elements accumulator outcome,
      List.foldlM step accumulator elements = .ok outcome →
        accumulator.2 ≤ outcome.2 := by
  intro elements
  induction elements with
  | nil =>
      intro accumulator outcome folded
      rw [List.foldlM_nil] at folded
      rcases Except.ok.inj folded with rfl
      exact Nat.le_refl _
  | cons element elements ih =>
      intro accumulator outcome folded
      rw [List.foldlM_cons] at folded
      simp only [Bind.bind, Except.bind] at folded
      split at folded
      · contradiction
      · have first := stepMono _ _ _ (by assumption)
        have rest := ih _ _ folded
        exact Nat.le_trans first rest

theorem compileAmbBranchesWith_counter
    (compileExpr : Nat → Metta.Atom →
      CompileM (Metta.Atom × List Goal × Nat))
    (start : Nat) (expressions : List Metta.Atom)
    (outcome : List (Metta.Atom × List Goal) × Nat)
    (compiled :
      compileAmbBranchesWith compileExpr start expressions = .ok outcome)
    (compileMono : ∀ counter expression term goals next,
      compileExpr counter expression = .ok (term, goals, next) →
        counter ≤ next) :
    start ≤ outcome.2 := by
  unfold compileAmbBranchesWith at compiled
  exact foldlM_counter_mono _ (by
    intro accumulator expression branchOutcome branchCompiled
    simp only [Bind.bind, Except.bind] at branchCompiled
    split at branchCompiled
    · contradiction
    · have mono := compileMono _ _ _ _ _ (by assumption)
      rcases Except.ok.inj branchCompiled with rfl
      exact mono) expressions ([], start) outcome compiled

@[local grind =>]
theorem freshFold_counter_mono :
    ∀ (indices : List Nat) (accumulator : List Metta.Atom × Nat),
      accumulator.2 ≤
        (indices.foldl
          (fun acc _ =>
            (acc.1 ++ [Metta.Atom.var s!"_q{acc.2}"], acc.2 + 1))
          accumulator).2 := by
  intro indices
  induction indices with
  | nil =>
      intro accumulator
      exact Nat.le_refl _
  | cons _ indices ih =>
      intro accumulator
      rw [List.foldl_cons]
      exact Nat.le_trans (by simp) (ih _)

theorem freshFold_result_counter (indices : List Nat) (start next : Nat)
    (compiled :
      (indices.foldl
        (fun (acc : List Metta.Atom × Nat) _ =>
          (acc.1 ++ [Metta.Atom.var s!"_q{acc.2}"], acc.2 + 1))
        ([], start)).2 = next) :
    start ≤ next := by
  rw [← compiled]
  exact freshFold_counter_mono indices ([], start)

theorem typedDispatchStep_counter
    (compileTypedArgs : Nat → List Metta.Atom →
      CompileM (List Metta.Atom × List Goal × Nat))
    (typedMono : ∀ start types terms goals next,
      compileTypedArgs start types = .ok (terms, goals, next) →
        start ≤ next)
    (result : Metta.Atom) (head : String)
    (arities : List Nat) :
    ∀ (accumulator : List (Metta.Atom × List Goal) × Nat)
      (chain : List Metta.Atom)
      (outcome : List (Metta.Atom × List Goal) × Nat),
      compileTypedDispatchStepWith compileTypedArgs result head arities
          accumulator chain = Except.ok outcome →
        accumulator.2 ≤ outcome.2 := by
  intro accumulator chain outcome compiled
  unfold compileTypedDispatchStepWith at compiled
  rcases freshEq : freshenTypeChain accumulator.2 chain with
    ⟨freshChain, freshCounter⟩
  simp only [freshEq] at compiled
  cases lastEq : freshChain.getLast? with
  | none => simp [lastEq] at compiled
  | some resultType =>
      simp only [lastEq, Bind.bind, Except.bind] at compiled
      cases typedEq : compileTypedArgs freshCounter freshChain.dropLast with
      | error message => simp [typedEq] at compiled
      | ok value =>
          simp only [typedEq] at compiled
          have freshMono : accumulator.2 ≤ freshCounter := by
            simpa only [freshEq] using
              CompilerTypeFreshening.freshenTypeChain_counter_le
                accumulator.2 chain
          have argumentsMono := typedMono _ _ _ _ _ typedEq
          rcases Except.ok.inj compiled with rfl
          exact Nat.le_trans freshMono <|
            Nat.le_trans argumentsMono <|
              compileResultTypeCheck_counter_le _ _ _

theorem compileAppDefaultWith_counter
    (compileArgs : Nat →
      CompileM (List Metta.Atom × List Goal × Nat))
    (compileTypedArgs : Nat → List Metta.Atom →
      CompileM (List Metta.Atom × List Goal × Nat))
    (compileList : Nat →
      CompileM (List Metta.Atom × List Goal × Nat))
    (argsMono : ∀ start terms goals next,
      compileArgs start = .ok (terms, goals, next) → start ≤ next)
    (typedMono : ∀ start types terms goals next,
      compileTypedArgs start types = .ok (terms, goals, next) →
        start ≤ next)
    (listMono : ∀ start terms goals next,
      compileList start = .ok (terms, goals, next) → start ≤ next) :
    ∀ env start head arguments term goals next,
      compileAppDefaultWith compileArgs compileTypedArgs compileList
          env start head arguments = .ok (term, goals, next) →
        start ≤ next := by
  intro env start head arguments term goals next compiled
  unfold compileAppDefaultWith at compiled
  by_cases prolog : env.prologFunctions.contains head = true
  · simp only [prolog, if_true, Bind.bind, Except.bind] at compiled
    split at compiled
    · contradiction
    · have argumentsMono := argsMono _ _ _ _ (by assumption)
      simp only [fresh, Except.ok.injEq] at compiled
      rcases compiled with ⟨_, _, rfl⟩
      omega
  · have prologFalse : env.prologFunctions.contains head = false :=
      Bool.eq_false_iff.mpr prolog
    simp only [prologFalse, Bool.false_eq_true, if_false] at compiled
    by_cases defined : env.defined.contains head = true
    · simp only [defined, if_true] at compiled
      have shortageFalse :
          typedDispatchInputShortage (env.typeChains head)
            arguments.length = false := by
        cases shortage : typedDispatchInputShortage (env.typeChains head)
            arguments.length with
        | false => rfl
        | true =>
            simp only [shortage, if_true] at compiled
            cases compiled
      simp only [shortageFalse, Bool.false_eq_true, if_false] at compiled
      by_cases typed :
          shouldUseTypedDispatch (env.typeChains head) = true
      · simp only [typed, if_true] at compiled
        rcases freshEq : fresh start with ⟨result, firstCounter⟩
        simp only [freshEq] at compiled
        let step := compileTypedDispatchStepWith compileTypedArgs result
          head (env.arities head)
        have stepMono : ∀ accumulator chain outcome,
            step accumulator chain = .ok outcome →
              accumulator.2 ≤ outcome.2 := by
          intro accumulator chain outcome stepCompiled
          exact typedDispatchStep_counter compileTypedArgs typedMono
            result head (env.arities head) accumulator chain outcome
            stepCompiled
        have foldMono := foldlM_counter_mono step stepMono
          (env.typeChains head) ([], firstCounter)
        have freshMono : start ≤ firstCounter := by
          have freshCounterEq := congrArg Prod.snd freshEq
          simp only [fresh] at freshCounterEq
          omega
        simp only [Bind.bind, Except.bind] at compiled
        split at compiled
        · contradiction
        · rename_i foldDiscriminant foldOutcome foldCompiled
          have branchesMono := foldMono foldOutcome foldCompiled
          split at compiled
          · split at compiled
            · contradiction
            · have argumentsMono := argsMono _ _ _ _ (by assumption)
              split at compiled
              · simp only [fresh, Except.ok.injEq] at compiled
                rcases compiled with ⟨_, _, rfl⟩
                omega
              · rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
                exact argumentsMono
          · cases resolutionEq : resolveTypedSharedResult result
              foldOutcome.1 with
            | error message => simp [resolutionEq] at compiled
            | ok resolved =>
                simp only [resolutionEq] at compiled
                rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
                exact Nat.le_trans freshMono branchesMono
      · have typedFalse :
            shouldUseTypedDispatch (env.typeChains head) = false :=
          Bool.eq_false_iff.mpr typed
        simp only [typedFalse, Bool.false_eq_true, if_false,
          Bind.bind, Except.bind] at compiled
        split at compiled
        · contradiction
        · have argumentsMono := argsMono _ _ _ _ (by assumption)
          split at compiled
          · simp only [fresh, Except.ok.injEq] at compiled
            rcases compiled with ⟨_, _, rfl⟩
            omega
          · rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
            exact argumentsMono
    · have definedFalse : env.defined.contains head = false :=
        Bool.eq_false_iff.mpr defined
      simp only [definedFalse, Bool.false_eq_true, if_false] at compiled
      by_cases binary : env.isBin head = true
      · simp only [binary, if_true, Bind.bind, Except.bind] at compiled
        split at compiled
        · contradiction
        · have argumentsMono := argsMono _ _ _ _ (by assumption)
          split at compiled
          · split at compiled
            · simp only [fresh, Except.ok.injEq] at compiled
              rcases compiled with ⟨_, _, rfl⟩
              omega
            · rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
              exact argumentsMono
          · simp only [fresh, Except.ok.injEq] at compiled
            rcases compiled with ⟨_, _, rfl⟩
            omega
      · have binaryFalse : env.isBin head = false :=
          Bool.eq_false_iff.mpr binary
        simp only [binaryFalse, Bool.false_eq_true, if_false,
          Bind.bind, Except.bind] at compiled
        split at compiled
        · contradiction
        · have termsMono := listMono _ _ _ _ (by assumption)
          split at compiled
          · simp only [fresh, Except.ok.injEq] at compiled
            rcases compiled with ⟨_, _, rfl⟩
            omega
          · rcases Except.ok.inj compiled with ⟨_, _, rfl⟩
            exact termsMono

theorem compileAppFuel_counter_step (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    ∀ env start head arguments term goals next,
      compileAppFuel (fuel + 1) env start head arguments =
          .ok (term, goals, next) →
        start ≤ next := by
  intro env start head arguments term goals next compiled
  rw [compileAppFuel.eq_def] at compiled
  split at compiled
  · contradiction
  · simp_all only [Nat.succ.injEq]
    split at compiled
    · exact ih.expr _ _ _ _ _ _ compiled
    · split at compiled
      · simp only [Bind.bind, Except.bind] at compiled
        split at compiled
        · contradiction
        · have argsMono := ih.argsAt _ _ _ _ _ _ _ _ (by assumption)
          simp only [fresh, Except.ok.injEq] at compiled
          rcases compiled with ⟨_, _, rfl⟩
          omega
      · exact ih.appCore _ _ _ _ _ _ _ compiled

/-- The `translatePredicate` staging helper preserves the compiler counter
lower bound supplied by its ordered argument traversal. -/
private theorem compileTranslatePredicateWith_counter
    (fuel : Nat) (ih : CompilerCounterAt fuel)
    (env : CEnv) (start : Nat) (goal term : Metta.Atom)
    (goals : List Goal) (next : Nat)
    (compiled : compileTranslatePredicateWith
      (fun counter arguments =>
        compileListFuel fuel env counter arguments)
      start goal = .ok (term, goals, next)) :
    start ≤ next := by
  unfold compileTranslatePredicateWith at compiled
  split at compiled <;> try contradiction
  simp only [Bind.bind, Except.bind] at compiled
  split at compiled
  · contradiction
  · rename_i listOutcome listValue listEq
    have listCounter := ih.list _ _ _ _ _ _ listEq
    simp only [fresh, Except.ok.injEq] at compiled
    rcases compiled with ⟨_, _, rfl⟩
    omega

local macro "solve_app_core_counter" fuel:ident ih:ident : tactic => `(tactic|
  (intro env start head arguments term goals next classified compiled
   change compileAppCoreFuel (Nat.succ $fuel) env start head arguments =
     Except.ok (term, goals, next) at compiled
   rw [compileAppCoreFuel.eq_def] at compiled
   simp only [classified] at compiled
   try (split at compiled <;> try contradiction)
   all_goals try simp only [Bind.bind, Except.bind] at compiled
   all_goals try (repeat' split at compiled)
   all_goals try contradiction
   all_goals try simp_all [fresh]
   all_goals try
     exact compileAppDefaultWith_counter _ _ _
       (by
         intro counter terms argumentGoals nextCounter argumentCompilation
         exact CompilerCounterAt.argsAt $ih _ counter _ 0 _ terms argumentGoals nextCounter
           argumentCompilation)
       (by
         intro counter types terms argumentGoals nextCounter argumentCompilation
         exact CompilerCounterAt.typedArgs $ih _ counter _ types terms argumentGoals nextCounter
           argumentCompilation)
       (by
         intro counter terms argumentGoals nextCounter argumentCompilation
         exact CompilerCounterAt.list $ih _ counter _ terms argumentGoals nextCounter
           argumentCompilation)
       _ _ _ _ _ _ _ compiled
   all_goals try
     exact Nat.le_trans
       (compileAmbBranchesWith_counter _ _ _ _ (by assumption) (by
         intro counter expression branchTerm branchGoals branchNext
           branchCompiled
         exact CompilerCounterAt.expr $ih _ counter expression branchTerm branchGoals branchNext
           branchCompiled))
       (by omega)
   all_goals try
     exact Nat.le_trans
       (CompilerCounterAt.expr $ih _ _ _ _ _ _ (by assumption))
       (freshFold_result_counter _ _ _ (by
         simpa [fresh] using compiled.2.2))
   all_goals try
     exact compileTranslatePredicateWith_counter $fuel $ih
       _ _ _ _ _ _ compiled
   all_goals grind [freshFold_counter_mono, foldlM_counter_mono]))

private abbrev AppCoreCounterFor (fuel : Nat) (kind : AppCoreHead) : Prop :=
  ∀ (env : CEnv) (start : Nat) (head : String)
    (arguments : List Metta.Atom) (term : Metta.Atom)
    (goals : List Goal) (next : Nat),
    classifyAppCoreHead head = kind →
    compileAppCoreFuel (fuel + 1) env start head arguments =
        Except.ok (term, goals, next) →
      start ≤ next

private theorem compileAppCoreFuel_hQuote_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hQuote := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hCase_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hCase := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hCallPredicate_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hCallPredicate := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih
private theorem compileAppCoreFuel_hPredicate_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hPredicate := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hTranslatePredicate_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hTranslatePredicate := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hAssertaPredicate_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hAssertaPredicate := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hAssertzPredicate_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hAssertzPredicate := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hRetractPredicate_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hRetractPredicate := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hProcessMettaString_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hProcessMettaString := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hUnquote_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hUnquote := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hEmpty_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hEmpty := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hCut_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hCut := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hTest_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hTest := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hTrace_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hTrace := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hAndThen_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hAndThen := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hOrElse_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hOrElse := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hHashPlus_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hHashPlus := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hHashMinus_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hHashMinus := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hCons_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hCons := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hIf_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hIf := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hLet_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hLet := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hLetStar_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hLetStar := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hCollapse_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hCollapse := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hOnce_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hOnce := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hSuperpose_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hSuperpose := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hUnify_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hUnify := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hSucceedsPredicate_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hSucceedsPredicate := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hFor_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hFor := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hChain_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hChain := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hFoldall_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hFoldall := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hForall_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hForall := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hProgn_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hProgn := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hProg1_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hProg1 := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hWithMutex_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hWithMutex := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hTransaction_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hTransaction := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hHyperpose_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hHyperpose := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hUnique_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hUnique := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hUnion_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hUnion := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hIntersection_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hIntersection := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hSubtraction_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hSubtraction := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hEval_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hEval := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hCatch_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hCatch := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hCall_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hCall := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hReduce_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hReduce := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hGetTypeSpace_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hGetTypeSpace := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hGetAtoms_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hGetAtoms := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hGetType_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hGetType := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hGetMetatype_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hGetMetatype := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hMatch_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hMatch := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hFind_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hFind := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hDoubleEqual_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hDoubleEqual := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hEqual_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hEqual := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hAddAtom_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hAddAtom := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hRemoveAtom_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hRemoveAtom := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hBind_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hBind := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hGetState_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hGetState := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_hChangeState_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .hChangeState := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih

private theorem compileAppCoreFuel_other_counter (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    AppCoreCounterFor fuel .other := by
  unfold AppCoreCounterFor
  solve_app_core_counter fuel ih


theorem compileAppCoreFuel_counter_step (fuel : Nat)
    (ih : CompilerCounterAt fuel) :
    ∀ (env : CEnv) (start : Nat) (head : String)
      (arguments : List Metta.Atom) (term : Metta.Atom)
      (goals : List Goal) (next : Nat),
      compileAppCoreFuel (fuel + 1) env start head arguments =
          Except.ok (term, goals, next) →
        start ≤ next := by
  intro env start head arguments term goals next compiled
  cases classified : classifyAppCoreHead head with
  | hQuote =>
      exact compileAppCoreFuel_hQuote_counter fuel ih env start head arguments
        term goals next classified compiled
  | hPredicate =>
      exact compileAppCoreFuel_hPredicate_counter fuel ih env start head arguments
        term goals next classified compiled
  | hTranslatePredicate =>
      exact compileAppCoreFuel_hTranslatePredicate_counter fuel ih env start head arguments
        term goals next classified compiled
  | hCallPredicate =>
      exact compileAppCoreFuel_hCallPredicate_counter fuel ih env start head arguments
        term goals next classified compiled
  | hAssertaPredicate =>
      exact compileAppCoreFuel_hAssertaPredicate_counter fuel ih env start head arguments
        term goals next classified compiled
  | hAssertzPredicate =>
      exact compileAppCoreFuel_hAssertzPredicate_counter fuel ih env start head arguments
        term goals next classified compiled
  | hRetractPredicate =>
      exact compileAppCoreFuel_hRetractPredicate_counter fuel ih env start head arguments
        term goals next classified compiled
  | hProcessMettaString =>
      exact compileAppCoreFuel_hProcessMettaString_counter fuel ih env start head arguments
        term goals next classified compiled
  | hUnquote =>
      exact compileAppCoreFuel_hUnquote_counter fuel ih env start head arguments
        term goals next classified compiled
  | hEmpty =>
      exact compileAppCoreFuel_hEmpty_counter fuel ih env start head arguments
        term goals next classified compiled
  | hCut =>
      exact compileAppCoreFuel_hCut_counter fuel ih env start head arguments
        term goals next classified compiled
  | hTest =>
      exact compileAppCoreFuel_hTest_counter fuel ih env start head arguments
        term goals next classified compiled
  | hTrace =>
      exact compileAppCoreFuel_hTrace_counter fuel ih env start head arguments
        term goals next classified compiled
  | hAndThen =>
      exact compileAppCoreFuel_hAndThen_counter fuel ih env start head arguments
        term goals next classified compiled
  | hOrElse =>
      exact compileAppCoreFuel_hOrElse_counter fuel ih env start head arguments
        term goals next classified compiled
  | hHashPlus =>
      exact compileAppCoreFuel_hHashPlus_counter fuel ih env start head arguments
        term goals next classified compiled
  | hHashMinus =>
      exact compileAppCoreFuel_hHashMinus_counter fuel ih env start head arguments
        term goals next classified compiled
  | hCons =>
      exact compileAppCoreFuel_hCons_counter fuel ih env start head arguments
        term goals next classified compiled
  | hIf =>
      exact compileAppCoreFuel_hIf_counter fuel ih env start head arguments
        term goals next classified compiled
  | hLet =>
      exact compileAppCoreFuel_hLet_counter fuel ih env start head arguments
        term goals next classified compiled
  | hLetStar =>
      exact compileAppCoreFuel_hLetStar_counter fuel ih env start head arguments
        term goals next classified compiled
  | hCase =>
      exact compileAppCoreFuel_hCase_counter fuel ih env start head arguments
        term goals next classified compiled
  | hCollapse =>
      exact compileAppCoreFuel_hCollapse_counter fuel ih env start head arguments
        term goals next classified compiled
  | hOnce =>
      exact compileAppCoreFuel_hOnce_counter fuel ih env start head arguments
        term goals next classified compiled
  | hSuperpose =>
      exact compileAppCoreFuel_hSuperpose_counter fuel ih env start head arguments
        term goals next classified compiled
  | hUnify =>
      exact compileAppCoreFuel_hUnify_counter fuel ih env start head arguments
        term goals next classified compiled
  | hSucceedsPredicate =>
      exact compileAppCoreFuel_hSucceedsPredicate_counter fuel ih env start head arguments
        term goals next classified compiled
  | hFor =>
      exact compileAppCoreFuel_hFor_counter fuel ih env start head arguments
        term goals next classified compiled
  | hChain =>
      exact compileAppCoreFuel_hChain_counter fuel ih env start head arguments
        term goals next classified compiled
  | hFoldall =>
      exact compileAppCoreFuel_hFoldall_counter fuel ih env start head arguments
        term goals next classified compiled
  | hForall =>
      exact compileAppCoreFuel_hForall_counter fuel ih env start head arguments
        term goals next classified compiled
  | hProgn =>
      exact compileAppCoreFuel_hProgn_counter fuel ih env start head arguments
        term goals next classified compiled
  | hProg1 =>
      exact compileAppCoreFuel_hProg1_counter fuel ih env start head arguments
        term goals next classified compiled
  | hWithMutex =>
      exact compileAppCoreFuel_hWithMutex_counter fuel ih env start head arguments
        term goals next classified compiled
  | hTransaction =>
      exact compileAppCoreFuel_hTransaction_counter fuel ih env start head arguments
        term goals next classified compiled
  | hHyperpose =>
      exact compileAppCoreFuel_hHyperpose_counter fuel ih env start head arguments
        term goals next classified compiled
  | hUnique =>
      exact compileAppCoreFuel_hUnique_counter fuel ih env start head arguments
        term goals next classified compiled
  | hUnion =>
      exact compileAppCoreFuel_hUnion_counter fuel ih env start head arguments
        term goals next classified compiled
  | hIntersection =>
      exact compileAppCoreFuel_hIntersection_counter fuel ih env start head arguments
        term goals next classified compiled
  | hSubtraction =>
      exact compileAppCoreFuel_hSubtraction_counter fuel ih env start head arguments
        term goals next classified compiled
  | hEval =>
      exact compileAppCoreFuel_hEval_counter fuel ih env start head arguments
        term goals next classified compiled
  | hCatch =>
      exact compileAppCoreFuel_hCatch_counter fuel ih env start head arguments
        term goals next classified compiled
  | hCall =>
      exact compileAppCoreFuel_hCall_counter fuel ih env start head arguments
        term goals next classified compiled
  | hReduce =>
      exact compileAppCoreFuel_hReduce_counter fuel ih env start head arguments
        term goals next classified compiled
  | hGetTypeSpace =>
      exact compileAppCoreFuel_hGetTypeSpace_counter fuel ih env start head arguments
        term goals next classified compiled
  | hGetAtoms =>
      exact compileAppCoreFuel_hGetAtoms_counter fuel ih env start head arguments
        term goals next classified compiled
  | hGetType =>
      exact compileAppCoreFuel_hGetType_counter fuel ih env start head arguments
        term goals next classified compiled
  | hGetMetatype =>
      exact compileAppCoreFuel_hGetMetatype_counter fuel ih env start head arguments
        term goals next classified compiled
  | hMatch =>
      exact compileAppCoreFuel_hMatch_counter fuel ih env start head arguments
        term goals next classified compiled
  | hFind =>
      exact compileAppCoreFuel_hFind_counter fuel ih env start head arguments
        term goals next classified compiled
  | hDoubleEqual =>
      exact compileAppCoreFuel_hDoubleEqual_counter fuel ih env start head arguments
        term goals next classified compiled
  | hEqual =>
      exact compileAppCoreFuel_hEqual_counter fuel ih env start head arguments
        term goals next classified compiled
  | hAddAtom =>
      exact compileAppCoreFuel_hAddAtom_counter fuel ih env start head arguments
        term goals next classified compiled
  | hRemoveAtom =>
      exact compileAppCoreFuel_hRemoveAtom_counter fuel ih env start head arguments
        term goals next classified compiled
  | hBind =>
      exact compileAppCoreFuel_hBind_counter fuel ih env start head arguments
        term goals next classified compiled
  | hGetState =>
      exact compileAppCoreFuel_hGetState_counter fuel ih env start head arguments
        term goals next classified compiled
  | hChangeState =>
      exact compileAppCoreFuel_hChangeState_counter fuel ih env start head arguments
        term goals next classified compiled
  | other =>
      exact compileAppCoreFuel_other_counter fuel ih env start head arguments
        term goals next classified compiled

theorem compilerCounterAt_succ (fuel : Nat) (ih : CompilerCounterAt fuel) :
    CompilerCounterAt (fuel + 1) where
  expr := compileExprFuel_counter_step fuel ih
  pattern := compilePatternFuel_counter_step fuel ih
  app := compileAppFuel_counter_step fuel ih
  appCore := compileAppCoreFuel_counter_step fuel ih
  typedArgs := compileTypedArgsFuel_counter_step fuel ih
  argsAt := compileArgsAtFuel_counter_step fuel ih
  caseArms := compileCaseArmsFuel_counter_step fuel ih
  patternList := compilePatternListFuel_counter_step fuel ih
  list := compileListFuel_counter_step fuel ih

theorem compilerCounterAt (fuel : Nat) : CompilerCounterAt fuel := by
  induction fuel with
  | zero => exact compilerCounterAt_zero
  | succ fuel ih =>
      simpa [Nat.succ_eq_add_one] using compilerCounterAt_succ fuel ih

theorem compileExprFuel_counter_mono
    (fuel : Nat) (env : CEnv) (start : Nat) (source term : Metta.Atom)
    (goals : List Goal) (next : Nat)
    (compiled : compileExprFuel fuel env start source = .ok (term, goals, next)) :
    start ≤ next :=
  (compilerCounterAt fuel).expr env start source term goals next compiled

theorem compilePatternFuel_counter_mono
    (fuel : Nat) (env : CEnv) (start : Nat) (source term : Metta.Atom)
    (goals : List Goal) (next : Nat)
    (compiled :
      compilePatternFuel fuel env start source = .ok (term, goals, next)) :
    start ≤ next :=
  (compilerCounterAt fuel).pattern env start source term goals next compiled

theorem compileAppFuel_counter_mono
    (fuel : Nat) (env : CEnv) (start : Nat) (head : String)
    (arguments : List Metta.Atom) (term : Metta.Atom) (goals : List Goal)
    (next : Nat)
    (compiled :
      compileAppFuel fuel env start head arguments = .ok (term, goals, next)) :
    start ≤ next :=
  (compilerCounterAt fuel).app env start head arguments term goals next compiled

theorem compileAppCoreFuel_counter_mono
    (fuel : Nat) (env : CEnv) (start : Nat) (head : String)
    (arguments : List Metta.Atom) (term : Metta.Atom) (goals : List Goal)
    (next : Nat)
    (compiled :
      compileAppCoreFuel fuel env start head arguments =
        .ok (term, goals, next)) :
    start ≤ next :=
  (compilerCounterAt fuel).appCore env start head arguments term goals next
    compiled

theorem compileTypedArgsFuel_counter_mono
    (fuel : Nat) (env : CEnv) (start : Nat)
    (sources types terms : List Metta.Atom) (goals : List Goal) (next : Nat)
    (compiled :
      compileTypedArgsFuel fuel env start sources types =
        .ok (terms, goals, next)) :
    start ≤ next :=
  (compilerCounterAt fuel).typedArgs env start sources types terms goals next
    compiled

theorem compileArgsAtFuel_counter_mono
    (fuel : Nat) (env : CEnv) (start : Nat) (head : String) (index : Nat)
    (sources terms : List Metta.Atom) (goals : List Goal) (next : Nat)
    (compiled :
      compileArgsAtFuel fuel env start head index sources =
        .ok (terms, goals, next)) :
    start ≤ next :=
  (compilerCounterAt fuel).argsAt env start head index sources terms goals next
    compiled

theorem compileCaseArmsFuel_counter_mono
    (fuel : Nat) (env : CEnv) (scrutinee result : Metta.Atom) (start : Nat)
    (arms : List Metta.Atom) (goals : List Goal) (next : Nat)
    (compiled :
      compileCaseArmsFuel fuel env scrutinee result start arms =
        .ok (goals, next)) :
    start ≤ next :=
  (compilerCounterAt fuel).caseArms env scrutinee result start arms goals next
    compiled

theorem compilePatternListFuel_counter_mono
    (fuel : Nat) (env : CEnv) (start : Nat)
    (sources terms : List Metta.Atom) (goals : List Goal) (next : Nat)
    (compiled :
      compilePatternListFuel fuel env start sources =
        .ok (terms, goals, next)) :
    start ≤ next :=
  (compilerCounterAt fuel).patternList env start sources terms goals next
    compiled

theorem compileListFuel_counter_mono
    (fuel : Nat) (env : CEnv) (start : Nat)
    (sources terms : List Metta.Atom) (goals : List Goal) (next : Nat)
    (compiled :
      compileListFuel fuel env start sources = .ok (terms, goals, next)) :
    start ≤ next :=
  (compilerCounterAt fuel).list env start sources terms goals next compiled

end PLeaTTa
