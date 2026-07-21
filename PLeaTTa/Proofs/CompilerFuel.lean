import PLeaTTa.Compile

namespace PLeaTTa

/-!
# Compiler fuel stability

The executable compiler is indexed by transparent recursion fuel.  A larger
fuel budget must not change a successful compilation result: fuel exhaustion
is an implementation guard, not part of PeTTa translation semantics.  This
module proves that law mutually for the executable compiler traversals.
-/

/-- Every successful compiler traversal at `fuel` has exactly the same
ordered result, goals, and fresh-name counter at `fuel + 1`. -/
structure CompilerFuelStepAt (fuel : Nat) : Prop where
  expr : ∀ env start source term goals next,
    compileExprFuel fuel env start source = .ok (term, goals, next) →
      compileExprFuel (fuel + 1) env start source = .ok (term, goals, next)
  pattern : ∀ env start source term goals next,
    compilePatternFuel fuel env start source = .ok (term, goals, next) →
      compilePatternFuel (fuel + 1) env start source = .ok (term, goals, next)
  app : ∀ env start head args term goals next,
    compileAppFuel fuel env start head args = .ok (term, goals, next) →
      compileAppFuel (fuel + 1) env start head args = .ok (term, goals, next)
  appCore : ∀ env start head args term goals next,
    compileAppCoreFuel fuel env start head args = .ok (term, goals, next) →
      compileAppCoreFuel (fuel + 1) env start head args =
        .ok (term, goals, next)
  typedArgs : ∀ env start sources types terms goals next,
    compileTypedArgsFuel fuel env start sources types =
        .ok (terms, goals, next) →
      compileTypedArgsFuel (fuel + 1) env start sources types =
        .ok (terms, goals, next)
  argsAt : ∀ env start head index sources terms goals next,
    compileArgsAtFuel fuel env start head index sources =
        .ok (terms, goals, next) →
      compileArgsAtFuel (fuel + 1) env start head index sources =
        .ok (terms, goals, next)
  caseArms : ∀ env scrutinee result start arms goals next,
    compileCaseArmsFuel fuel env scrutinee result start arms =
        .ok (goals, next) →
      compileCaseArmsFuel (fuel + 1) env scrutinee result start arms =
        .ok (goals, next)
  patternList : ∀ env start sources terms goals next,
    compilePatternListFuel fuel env start sources =
        .ok (terms, goals, next) →
      compilePatternListFuel (fuel + 1) env start sources =
        .ok (terms, goals, next)
  list : ∀ env start sources terms goals next,
    compileListFuel fuel env start sources = .ok (terms, goals, next) →
      compileListFuel (fuel + 1) env start sources =
        .ok (terms, goals, next)

theorem compilerFuelStepAt_zero : CompilerFuelStepAt 0 := by
  constructor <;> intros <;>
    simp only [compileExprFuel.eq_1, compilePatternFuel_zero_eq,
      compileAppFuel.eq_1, compileAppCoreFuel.eq_1,
      compileTypedArgsFuel.eq_1, compileArgsAtFuel_zero_eq,
      compileCaseArmsFuel_zero_eq, compilePatternListFuel.eq_1,
      compileListFuel.eq_1] at * <;> contradiction

/-- Pointwise preservation of successful steps lifts through an ordered
monadic left fold without changing its result or order. -/
theorem foldlM_success_stable {state item error : Type}
    (low high : state → item → Except error state)
    (stepStable : ∀ accumulator element outcome,
      low accumulator element = .ok outcome →
        high accumulator element = .ok outcome) :
    ∀ elements accumulator outcome,
      List.foldlM low accumulator elements = .ok outcome →
        List.foldlM high accumulator elements = .ok outcome := by
  intro elements
  induction elements with
  | nil =>
      intro accumulator outcome folded
      simpa using folded
  | cons element elements ih =>
      intro accumulator outcome folded
      rw [List.foldlM_cons] at folded ⊢
      simp only [Bind.bind, Except.bind] at folded ⊢
      split at folded
      · contradiction
      · rename_i firstOutcome firstValue firstEq
        rw [stepStable _ _ _ firstEq]
        exact ih _ _ folded

/-- Typed-dispatch branch construction is stable when its argument compiler
is stable. -/
theorem compileTypedDispatchStepWith_success_stable
    (low high : Nat → List Metta.Atom →
      CompileM (List Metta.Atom × List Goal × Nat))
    (typedStable : ∀ start types value,
      low start types = .ok value → high start types = .ok value)
    (result : Metta.Atom) (head : String) (arguments : List Metta.Atom) :
    ∀ accumulator chain outcome,
      compileTypedDispatchStepWith low result head arguments accumulator chain =
          .ok outcome →
        compileTypedDispatchStepWith high result head arguments accumulator chain =
          .ok outcome := by
  intro accumulator chain outcome compiled
  unfold compileTypedDispatchStepWith at compiled ⊢
  split at compiled
  · split at compiled
    · simp_all only [if_true]
    · simp_all only [if_false]
      simp only [Bind.bind, Except.bind] at compiled ⊢
      split at compiled
      · contradiction
      · rename_i typedOutcome typedValue typedEq
        rw [typedStable _ _ _ typedEq]
        exact compiled
  · exact compiled

/-- Ordered ambiguous-branch compilation is stable when expression
compilation is stable. -/
theorem compileAmbBranchesWith_success_stable
    (low high : Nat → Metta.Atom →
      CompileM (Metta.Atom × List Goal × Nat))
    (exprStable : ∀ start source value,
      low start source = .ok value → high start source = .ok value) :
    ∀ start expressions outcome,
      compileAmbBranchesWith low start expressions = .ok outcome →
        compileAmbBranchesWith high start expressions = .ok outcome := by
  intro start expressions outcome compiled
  unfold compileAmbBranchesWith at compiled ⊢
  apply foldlM_success_stable _ _ _ expressions ([], start) outcome compiled
  intro accumulator source branchOutcome branchCompiled
  simp only [Bind.bind, Except.bind] at branchCompiled ⊢
  split at branchCompiled
  · contradiction
  · rename_i expressionOutcome expressionValue expressionEq
    rw [exprStable _ _ _ expressionEq]
    exact branchCompiled

/-- The generic application fallback preserves a successful result when each
of its three compiler callbacks does.  This packages the ordered typed-chain
fold, ordinary argument compilation, and data-head fallback once, instead of
re-proving their fuel bookkeeping for every application head. -/
theorem compileAppDefaultWith_success_stable
    (lowArgs highArgs : Nat →
      CompileM (List Metta.Atom × List Goal × Nat))
    (lowTyped highTyped : Nat → List Metta.Atom →
      CompileM (List Metta.Atom × List Goal × Nat))
    (lowList highList : Nat →
      CompileM (List Metta.Atom × List Goal × Nat))
    (argsStable : ∀ start value,
      lowArgs start = .ok value → highArgs start = .ok value)
    (typedStable : ∀ start types value,
      lowTyped start types = .ok value → highTyped start types = .ok value)
    (listStable : ∀ start value,
      lowList start = .ok value → highList start = .ok value) :
    ∀ env start head arguments outcome,
      compileAppDefaultWith lowArgs lowTyped lowList
          env start head arguments = .ok outcome →
        compileAppDefaultWith highArgs highTyped highList
          env start head arguments = .ok outcome := by
  intro env start head arguments outcome compiled
  unfold compileAppDefaultWith at compiled ⊢
  by_cases prolog : env.prologFunctions.contains head = true
  · simp only [prolog, if_true, Bind.bind, Except.bind] at compiled ⊢
    split at compiled
    · contradiction
    · rename_i argsOutcome argsValue argsEq
      rw [argsStable _ _ argsEq]
      exact compiled
  · have prologFalse : env.prologFunctions.contains head = false :=
      Bool.eq_false_iff.mpr prolog
    simp only [prologFalse, Bool.false_eq_true, if_false] at compiled ⊢
    by_cases defined : env.defined.contains head = true
    · simp only [defined, if_true] at compiled ⊢
      by_cases typed : shouldUseTypedDispatch (env.typeChains head) = true
      · simp only [typed, if_true] at compiled ⊢
        let result := (fresh start).1
        let firstCounter := (fresh start).2
        let lowStep := compileTypedDispatchStepWith lowTyped result head arguments
        let highStep := compileTypedDispatchStepWith highTyped result head arguments
        have stepStable : ∀ accumulator chain branchOutcome,
            lowStep accumulator chain = .ok branchOutcome →
              highStep accumulator chain = .ok branchOutcome := by
          intro accumulator chain branchOutcome branchCompiled
          exact compileTypedDispatchStepWith_success_stable
            lowTyped highTyped typedStable result head arguments
            accumulator chain branchOutcome branchCompiled
        have foldStable : ∀ branchOutcome,
            (env.typeChains head).foldlM lowStep ([], firstCounter) =
                .ok branchOutcome →
              (env.typeChains head).foldlM highStep ([], firstCounter) =
                .ok branchOutcome := by
          intro branchOutcome branchCompiled
          exact foldlM_success_stable lowStep highStep stepStable
            (env.typeChains head) ([], firstCounter) branchOutcome branchCompiled
        simp only [result, firstCounter, lowStep, highStep] at foldStable
        simp only [Bind.bind, Except.bind] at compiled ⊢
        split at compiled
        · contradiction
        · rename_i branchesOutcome branchesValue branchesEq
          rw [foldStable _ branchesEq]
          cases empty : branchesValue.1.isEmpty with
          | false =>
              simp only [empty, Bool.false_eq_true, if_false] at compiled ⊢
              exact compiled
          | true =>
              simp only [empty, if_true, Bind.bind, Except.bind] at compiled ⊢
              split at compiled
              · contradiction
              · rename_i argsOutcome argsValue argsEq
                rw [argsStable _ _ argsEq]
                exact compiled
      · have typedFalse :
            shouldUseTypedDispatch (env.typeChains head) = false :=
          Bool.eq_false_iff.mpr typed
        simp only [typedFalse, Bool.false_eq_true, if_false,
          Bind.bind, Except.bind] at compiled ⊢
        split at compiled
        · contradiction
        · rename_i argsOutcome argsValue argsEq
          rw [argsStable _ _ argsEq]
          exact compiled
    · have definedFalse : env.defined.contains head = false :=
        Bool.eq_false_iff.mpr defined
      simp only [definedFalse, Bool.false_eq_true, if_false] at compiled ⊢
      by_cases binary : env.isBin head = true
      · simp only [binary, if_true, Bind.bind, Except.bind] at compiled ⊢
        split at compiled
        · contradiction
        · rename_i argsOutcome argsValue argsEq
          rw [argsStable _ _ argsEq]
          exact compiled
      · have binaryFalse : env.isBin head = false :=
          Bool.eq_false_iff.mpr binary
        simp only [binaryFalse, Bool.false_eq_true, if_false,
          Bind.bind, Except.bind] at compiled ⊢
        split at compiled
        · contradiction
        · rename_i listOutcome listValue listEq
          rw [listStable _ _ listEq]
          exact compiled

/-- Fuel stability for the executable compiler's generic application path.
The captured environment, head, and arguments are identical on both sides;
only the recursive fuel supplied to its callbacks grows. -/
theorem compileAppDefaultFuel_success_stable (fuel : Nat)
    (ih : CompilerFuelStepAt fuel) (env : CEnv) (start : Nat)
    (head : String) (arguments : List Metta.Atom) (outcome) :
    compileAppDefaultWith
        (fun counter =>
          compileArgsAtFuel fuel env counter head 0 arguments)
        (fun counter types =>
          compileTypedArgsFuel fuel env counter arguments types)
        (fun counter => compileListFuel fuel env counter arguments)
        env start head arguments = .ok outcome →
      compileAppDefaultWith
        (fun counter =>
          compileArgsAtFuel (fuel + 1) env counter head 0 arguments)
        (fun counter types =>
          compileTypedArgsFuel (fuel + 1) env counter arguments types)
        (fun counter => compileListFuel (fuel + 1) env counter arguments)
        env start head arguments = .ok outcome := by
  intro compiled
  exact compileAppDefaultWith_success_stable
    (fun counter => compileArgsAtFuel fuel env counter head 0 arguments)
    (fun counter => compileArgsAtFuel (fuel + 1) env counter head 0 arguments)
    (fun counter types =>
      compileTypedArgsFuel fuel env counter arguments types)
    (fun counter types =>
      compileTypedArgsFuel (fuel + 1) env counter arguments types)
    (fun counter => compileListFuel fuel env counter arguments)
    (fun counter => compileListFuel (fuel + 1) env counter arguments)
    (by
      intro counter value argumentCompilation
      exact ih.argsAt env counter head 0 arguments value.1 value.2.1 value.2.2
        argumentCompilation)
    (by
      intro counter types value argumentCompilation
      exact ih.typedArgs env counter arguments types value.1 value.2.1 value.2.2
        argumentCompilation)
    (by
      intro counter value argumentCompilation
      exact ih.list env counter arguments value.1 value.2.1 value.2.2
        argumentCompilation)
    env start head arguments outcome compiled

theorem compileListFuel_stable_step (fuel : Nat)
    (ih : CompilerFuelStepAt fuel) :
    ∀ env start sources terms goals next,
      compileListFuel (fuel + 1) env start sources =
          .ok (terms, goals, next) →
        compileListFuel (fuel + 2) env start sources =
          .ok (terms, goals, next) := by
  intro env start sources terms goals next compiled
  cases sources with
  | nil =>
      rw [compileListFuel_nil_eq] at compiled
      rw [show fuel + 2 = (fuel + 1) + 1 by omega,
        compileListFuel_nil_eq]
      exact compiled
  | cons source sources =>
      rw [compileListFuel_cons_eq] at compiled
      rw [show fuel + 2 = (fuel + 1) + 1 by omega,
        compileListFuel_cons_eq]
      simp only [Bind.bind, Except.bind] at compiled ⊢
      split at compiled
      · contradiction
      · rename_i firstOutcome firstValue firstEq
        have firstHigh := ih.expr _ _ _ _ _ _ firstEq
        rw [firstHigh]
        split at compiled
        · contradiction
        · rename_i restOutcome restValue restEq
          have restHigh := ih.list _ _ _ _ _ _ restEq
          rw [restHigh]
          exact compiled

theorem compilePatternListFuel_stable_step (fuel : Nat)
    (ih : CompilerFuelStepAt fuel) :
    ∀ env start sources terms goals next,
      compilePatternListFuel (fuel + 1) env start sources =
          .ok (terms, goals, next) →
        compilePatternListFuel (fuel + 2) env start sources =
          .ok (terms, goals, next) := by
  intro env start sources terms goals next compiled
  cases sources with
  | nil =>
      rw [compilePatternListFuel_nil_eq] at compiled
      rw [show fuel + 2 = (fuel + 1) + 1 by omega,
        compilePatternListFuel_nil_eq]
      exact compiled
  | cons source sources =>
      rw [compilePatternListFuel_cons_eq] at compiled
      rw [show fuel + 2 = (fuel + 1) + 1 by omega,
        compilePatternListFuel_cons_eq]
      simp only [Bind.bind, Except.bind] at compiled ⊢
      split at compiled
      · contradiction
      · rename_i firstOutcome firstValue firstEq
        have firstHigh := ih.pattern _ _ _ _ _ _ firstEq
        rw [firstHigh]
        split at compiled
        · contradiction
        · rename_i restOutcome restValue restEq
          have restHigh := ih.patternList _ _ _ _ _ _ restEq
          rw [restHigh]
          exact compiled

theorem compileArgsAtFuel_stable_step (fuel : Nat)
    (ih : CompilerFuelStepAt fuel) :
    ∀ env start head index sources terms goals next,
      compileArgsAtFuel (fuel + 1) env start head index sources =
          .ok (terms, goals, next) →
        compileArgsAtFuel (fuel + 2) env start head index sources =
          .ok (terms, goals, next) := by
  intro env start head index sources terms goals next compiled
  cases sources with
  | nil =>
      rw [compileArgsAtFuel_nil_eq] at compiled
      rw [show fuel + 2 = (fuel + 1) + 1 by omega,
        compileArgsAtFuel_nil_eq]
      exact compiled
  | cons source sources =>
      cases staged : env.atomTyped head index with
      | true =>
          rw [compileArgsAtFuel_staged_eq fuel env start head index source
            sources staged] at compiled
          rw [show fuel + 2 = (fuel + 1) + 1 by omega,
            compileArgsAtFuel_staged_eq (fuel + 1) env start head index source
              sources staged]
          simp only [Bind.bind, Except.bind] at compiled ⊢
          split at compiled
          · contradiction
          · rename_i restOutcome restValue restEq
            have restHigh := ih.argsAt _ _ _ _ _ _ _ _ restEq
            rw [restHigh]
            exact compiled
      | false =>
          rw [compileArgsAtFuel_evaluated_eq fuel env start head index source
            sources staged] at compiled
          rw [show fuel + 2 = (fuel + 1) + 1 by omega,
            compileArgsAtFuel_evaluated_eq (fuel + 1) env start head index
              source sources staged]
          simp only [Bind.bind, Except.bind] at compiled ⊢
          split at compiled
          · contradiction
          · rename_i firstOutcome firstValue firstEq
            have firstHigh := ih.expr _ _ _ _ _ _ firstEq
            rw [firstHigh]
            split at compiled
            · contradiction
            · rename_i restOutcome restValue restEq
              have restHigh := ih.argsAt _ _ _ _ _ _ _ _ restEq
              rw [restHigh]
              exact compiled

theorem compileTypedArgsFuel_stable_step (fuel : Nat)
    (ih : CompilerFuelStepAt fuel) :
    ∀ env start sources types terms goals next,
      compileTypedArgsFuel (fuel + 1) env start sources types =
          .ok (terms, goals, next) →
        compileTypedArgsFuel (fuel + 2) env start sources types =
          .ok (terms, goals, next) := by
  intro env start sources types terms goals next compiled
  cases sources with
  | nil =>
      cases types with
      | nil =>
          rw [compileTypedArgsFuel_nil_eq] at compiled
          rw [show fuel + 2 = (fuel + 1) + 1 by omega,
            compileTypedArgsFuel_nil_eq]
          exact compiled
      | cons ty types =>
          rw [compileTypedArgsFuel_surplus_type_eq] at compiled
          contradiction
  | cons source sources =>
      cases types with
      | nil =>
          rw [compileTypedArgsFuel_missing_type_eq] at compiled
          contradiction
      | cons ty types =>
          cases expression : (ty == (.sym "Expression" : Metta.Atom)) with
          | true =>
              rw [compileTypedArgsFuel.eq_def] at compiled ⊢
              simp only [show fuel + 2 = Nat.succ (fuel + 1) by omega,
                expression, if_true] at compiled ⊢
              simp only [Bind.bind, Except.bind] at compiled ⊢
              split at compiled
              · contradiction
              · rename_i restOutcome restValue restEq
                have restHigh := ih.typedArgs _ _ _ _ _ _ _ restEq
                rw [restHigh]
                exact compiled
          | false =>
              rw [compileTypedArgsFuel_evaluated_eq fuel env start source ty
                sources types expression] at compiled
              rw [show fuel + 2 = (fuel + 1) + 1 by omega,
                compileTypedArgsFuel_evaluated_eq (fuel + 1) env start source
                  ty sources types expression]
              simp only [Bind.bind, Except.bind] at compiled ⊢
              split at compiled
              · contradiction
              · rename_i firstOutcome firstValue firstEq
                have firstHigh := ih.expr _ _ _ _ _ _ firstEq
                rw [firstHigh]
                split at compiled
                · contradiction
                · rename_i restOutcome restValue restEq
                  have restHigh := ih.typedArgs _ _ _ _ _ _ _ restEq
                  rw [restHigh]
                  exact compiled

theorem compileCaseArmsFuel_stable_step (fuel : Nat)
    (ih : CompilerFuelStepAt fuel) :
    ∀ env scrutinee result start arms goals next,
      compileCaseArmsFuel (fuel + 1) env scrutinee result start arms =
          .ok (goals, next) →
        compileCaseArmsFuel (fuel + 2) env scrutinee result start arms =
          .ok (goals, next) := by
  intro env scrutinee result start arms goals next compiled
  cases arms with
  | nil =>
      rw [compileCaseArmsFuel_nil_eq] at compiled
      rw [show fuel + 2 = (fuel + 1) + 1 by omega,
        compileCaseArmsFuel_nil_eq]
      exact compiled
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
                          rw [show fuel + 2 = (fuel + 1) + 1 by omega,
                            compileCaseArmsFuel_var_pair_eq]
                          simp only [Bind.bind, Except.bind] at compiled ⊢
                          split at compiled
                          · contradiction
                          · rename_i patternOutcome patternValue patternEq
                            rw [ih.pattern _ _ _ _ _ _ patternEq]
                            split at compiled
                            · contradiction
                            · rename_i bodyOutcome bodyValue bodyEq
                              rw [ih.expr _ _ _ _ _ _ bodyEq]
                              split at compiled
                              · contradiction
                              · rename_i armsOutcome armsValue armsEq
                                rw [ih.caseArms _ _ _ _ _ _ _ armsEq]
                                exact compiled
                      | gnd ground =>
                          rw [compileCaseArmsFuel_gnd_pair_eq] at compiled
                          rw [show fuel + 2 = (fuel + 1) + 1 by omega,
                            compileCaseArmsFuel_gnd_pair_eq]
                          simp only [Bind.bind, Except.bind] at compiled ⊢
                          split at compiled
                          · contradiction
                          · rename_i patternOutcome patternValue patternEq
                            rw [ih.pattern _ _ _ _ _ _ patternEq]
                            split at compiled
                            · contradiction
                            · rename_i bodyOutcome bodyValue bodyEq
                              rw [ih.expr _ _ _ _ _ _ bodyEq]
                              split at compiled
                              · contradiction
                              · rename_i armsOutcome armsValue armsEq
                                rw [ih.caseArms _ _ _ _ _ _ _ armsEq]
                                exact compiled
                      | expr nested =>
                          rw [compileCaseArmsFuel_expr_pair_eq] at compiled
                          rw [show fuel + 2 = (fuel + 1) + 1 by omega,
                            compileCaseArmsFuel_expr_pair_eq]
                          simp only [Bind.bind, Except.bind] at compiled ⊢
                          split at compiled
                          · contradiction
                          · rename_i patternOutcome patternValue patternEq
                            rw [ih.pattern _ _ _ _ _ _ patternEq]
                            split at compiled
                            · contradiction
                            · rename_i bodyOutcome bodyValue bodyEq
                              rw [ih.expr _ _ _ _ _ _ bodyEq]
                              split at compiled
                              · contradiction
                              · rename_i armsOutcome armsValue armsEq
                                rw [ih.caseArms _ _ _ _ _ _ _ armsEq]
                                exact compiled
                      | sym name =>
                          by_cases empty : name = "Empty"
                          · subst name
                            rw [compileCaseArmsFuel_empty_eq] at compiled
                            rw [show fuel + 2 = (fuel + 1) + 1 by omega,
                              compileCaseArmsFuel_empty_eq]
                            exact ih.caseArms _ _ _ _ _ _ _ compiled
                          · rw [compileCaseArmsFuel_sym_pair_eq fuel env
                              scrutinee result start name empty] at compiled
                            rw [show fuel + 2 = (fuel + 1) + 1 by omega,
                              compileCaseArmsFuel_sym_pair_eq (fuel + 1) env
                                scrutinee result start name empty]
                            simp only [Bind.bind, Except.bind] at compiled ⊢
                            split at compiled
                            · contradiction
                            · rename_i patternOutcome patternValue patternEq
                              rw [ih.pattern _ _ _ _ _ _ patternEq]
                              split at compiled
                              · contradiction
                              · rename_i bodyOutcome bodyValue bodyEq
                                rw [ih.expr _ _ _ _ _ _ bodyEq]
                                split at compiled
                                · contradiction
                                · rename_i armsOutcome armsValue armsEq
                                  rw [ih.caseArms _ _ _ _ _ _ _ armsEq]
                                  exact compiled

theorem compileExprFuel_stable_step (fuel : Nat)
    (ih : CompilerFuelStepAt fuel) :
    ∀ env start source term goals next,
      compileExprFuel (fuel + 1) env start source =
          .ok (term, goals, next) →
        compileExprFuel (fuel + 2) env start source =
          .ok (term, goals, next) := by
  intro env start source term goals next compiled
  rw [compileExprFuel.eq_def] at compiled ⊢
  split at compiled <;> simp_all [fresh]
  · exact ih.app _ _ _ _ _ _ _ compiled
  · simp only [Bind.bind, Except.bind] at compiled ⊢
    split at compiled
    · contradiction
    · rename_i listOutcome listValue listEq
      rw [ih.list _ _ _ _ _ _ listEq]
      exact compiled
  · simp only [Bind.bind, Except.bind] at compiled ⊢
    split at compiled
    · contradiction
    · rename_i headOutcome headValue headEq
      rw [ih.expr _ _ _ _ _ _ headEq]
      split at compiled
      · contradiction
      · rename_i tailOutcome tailValue tailEq
        rw [ih.list _ _ _ _ _ _ tailEq]
        exact compiled

theorem compileAppFuel_stable_step (fuel : Nat)
    (ih : CompilerFuelStepAt fuel) :
    ∀ env start head args term goals next,
      compileAppFuel (fuel + 1) env start head args =
          .ok (term, goals, next) →
        compileAppFuel (fuel + 2) env start head args =
          .ok (term, goals, next) := by
  intro env start head args term goals next compiled
  rw [compileAppFuel.eq_def] at compiled ⊢
  split at compiled
  · contradiction
  · simp_all only [Nat.succ.injEq]
    split at compiled
    · exact ih.expr _ _ _ _ _ _ compiled
    · split at compiled
      · simp_all only [if_true]
        simp only [Bind.bind, Except.bind] at compiled ⊢
        split at compiled
        · contradiction
        · rename_i argsOutcome argsValue argsEq
          rw [ih.argsAt _ _ _ _ _ _ _ _ argsEq]
          exact compiled
      · simp_all only [if_false]
        exact ih.appCore _ _ _ _ _ _ _ compiled

theorem compilePatternFuel_stable_step (fuel : Nat)
    (ih : CompilerFuelStepAt fuel) :
    ∀ env start source term goals next,
      compilePatternFuel (fuel + 1) env start source =
          .ok (term, goals, next) →
        compilePatternFuel (fuel + 2) env start source =
          .ok (term, goals, next) := by
  intro env start source term goals next compiled
  cases source with
  | var name =>
      rw [compilePatternFuel_var_eq] at compiled
      rw [show fuel + 2 = (fuel + 1) + 1 by omega,
        compilePatternFuel_var_eq]
      exact compiled
  | sym name =>
      rw [compilePatternFuel_sym_eq] at compiled
      rw [show fuel + 2 = (fuel + 1) + 1 by omega,
        compilePatternFuel_sym_eq]
      exact compiled
  | gnd ground =>
      rw [compilePatternFuel_gnd_eq] at compiled
      rw [show fuel + 2 = (fuel + 1) + 1 by omega,
        compilePatternFuel_gnd_eq]
      exact compiled
  | expr items =>
      cases items with
      | nil =>
          rw [compilePatternFuel_nil_eq] at compiled
          rw [show fuel + 2 = (fuel + 1) + 1 by omega,
            compilePatternFuel_nil_eq]
          exact compiled
      | cons head arguments =>
          cases head with
          | var name =>
              rw [compilePatternFuel_var_head_eq] at compiled
              rw [show fuel + 2 = (fuel + 1) + 1 by omega,
                compilePatternFuel_var_head_eq]
              simp only [Bind.bind, Except.bind] at compiled ⊢
              split at compiled
              · contradiction
              · rename_i listOutcome listValue listEq
                rw [ih.patternList _ _ _ _ _ _ listEq]
                exact compiled
          | gnd ground =>
              rw [compilePatternFuel_gnd_head_eq] at compiled
              rw [show fuel + 2 = (fuel + 1) + 1 by omega,
                compilePatternFuel_gnd_head_eq]
              simp only [Bind.bind, Except.bind] at compiled ⊢
              split at compiled
              · contradiction
              · rename_i listOutcome listValue listEq
                rw [ih.patternList _ _ _ _ _ _ listEq]
                exact compiled
          | expr nested =>
              rw [compilePatternFuel_expr_head_eq] at compiled
              rw [show fuel + 2 = (fuel + 1) + 1 by omega,
                compilePatternFuel_expr_head_eq]
              simp only [Bind.bind, Except.bind] at compiled ⊢
              split at compiled
              · contradiction
              · rename_i listOutcome listValue listEq
                rw [ih.patternList _ _ _ _ _ _ listEq]
                exact compiled
          | sym name =>
              cases arguments with
              | nil =>
                  rw [compilePatternFuel_sym_nil_eq] at compiled
                  rw [show fuel + 2 = (fuel + 1) + 1 by omega,
                    compilePatternFuel_sym_nil_eq]
                  split at compiled
                  · simp_all only [if_true]
                    exact ih.expr _ _ _ _ _ _ compiled
                  · simp_all only [if_false]
                    simp only [Bind.bind, Except.bind] at compiled ⊢
                    split at compiled
                    · contradiction
                    · rename_i listOutcome listValue listEq
                      rw [ih.patternList _ _ _ _ _ _ listEq]
                      exact compiled
              | cons first tail =>
                  cases tail with
                  | nil =>
                      rw [compilePatternFuel_sym_singleton_eq] at compiled
                      rw [show fuel + 2 = (fuel + 1) + 1 by omega,
                        compilePatternFuel_sym_singleton_eq]
                      split at compiled
                      · simp_all only [if_true]
                        exact ih.expr _ _ _ _ _ _ compiled
                      · simp_all only [if_false]
                        simp only [Bind.bind, Except.bind] at compiled ⊢
                        split at compiled
                        · contradiction
                        · rename_i listOutcome listValue listEq
                          rw [ih.patternList _ _ _ _ _ _ listEq]
                          exact compiled
                  | cons second rest =>
                      cases rest with
                      | nil =>
                          by_cases chain : name = "#c"
                          · subst name
                            rw [compilePatternFuel_chain_eq] at compiled
                            rw [show fuel + 2 = (fuel + 1) + 1 by omega,
                              compilePatternFuel_chain_eq]
                            exact compiled
                          · by_cases consName : name = "cons"
                            · subst name
                              rw [compilePatternFuel_cons_eq] at compiled
                              rw [show fuel + 2 = (fuel + 1) + 1 by omega,
                                compilePatternFuel_cons_eq]
                              simp only [Bind.bind, Except.bind] at compiled ⊢
                              split at compiled
                              · contradiction
                              · rename_i firstOutcome firstValue firstEq
                                rw [ih.pattern _ _ _ _ _ _ firstEq]
                                split at compiled
                                · contradiction
                                · rename_i secondOutcome secondValue secondEq
                                  rw [ih.pattern _ _ _ _ _ _ secondEq]
                                  exact compiled
                            · rw [compilePatternFuel_sym_pair_other_eq fuel env
                                  start name first second chain consName] at compiled
                              rw [show fuel + 2 = (fuel + 1) + 1 by omega,
                                compilePatternFuel_sym_pair_other_eq (fuel + 1)
                                  env start name first second chain consName]
                              split at compiled
                              · simp_all only [if_true]
                                exact ih.expr _ _ _ _ _ _ compiled
                              · simp_all only [if_false]
                                simp only [Bind.bind, Except.bind] at compiled ⊢
                                split at compiled
                                · contradiction
                                · rename_i listOutcome listValue listEq
                                  rw [ih.patternList _ _ _ _ _ _ listEq]
                                  exact compiled
                      | cons third rest =>
                          rw [compilePatternFuel_sym_many_eq] at compiled
                          rw [show fuel + 2 = (fuel + 1) + 1 by omega,
                            compilePatternFuel_sym_many_eq]
                          split at compiled
                          · simp_all only [if_true]
                            exact ih.expr _ _ _ _ _ _ compiled
                          · simp_all only [if_false]
                            simp only [Bind.bind, Except.bind] at compiled ⊢
                            split at compiled
                            · contradiction
                            · rename_i listOutcome listValue listEq
                              rw [ih.patternList _ _ _ _ _ _ listEq]
                              exact compiled

private abbrev AppCoreFuelStableFor (fuel : Nat) (kind : AppCoreHead) : Prop :=
  ∀ env start head arguments term goals next,
    classifyAppCoreHead head = kind →
    compileAppCoreFuel (fuel + 1) env start head arguments =
        .ok (term, goals, next) →
      compileAppCoreFuel (fuel + 2) env start head arguments =
        .ok (term, goals, next)

local macro "solve_app_core_fuel" fuel:ident ih:ident : tactic => `(tactic|
  (intro env start head arguments term goals next classified compiled
   change (compileAppCoreFuel (Nat.succ $fuel) env start head arguments =
      .ok (term, goals, next)) at compiled
   change (compileAppCoreFuel (Nat.succ ($fuel + 1)) env start head arguments =
      .ok (term, goals, next))
   rw [compileAppCoreFuel.eq_def] at compiled ⊢
   simp only [classified] at compiled ⊢
   clear classified
   try (split at compiled <;> try contradiction)
   all_goals try simp only [Bind.bind, Except.bind] at compiled ⊢
   all_goals try (repeat' split at compiled)
   all_goals try contradiction
   all_goals try
     exact compileAppDefaultFuel_success_stable $fuel $ih _ _ _ _ _ compiled
   all_goals try simp_all [fresh]
   all_goals try
     have ambStable := compileAmbBranchesWith_success_stable
       (fun counter expression =>
         compileExprFuel $fuel env counter expression)
       (fun counter expression =>
         compileExprFuel ($fuel + 1) env counter expression)
       (by
         intro counter expression value branchCompiled
         exact CompilerFuelStepAt.expr $ih env counter expression
           value.1 value.2.1 value.2.2 branchCompiled)
       _ _ _ (by assumption)
     simp_all
   all_goals grind [CompilerFuelStepAt.expr, CompilerFuelStepAt.pattern,
     CompilerFuelStepAt.app, CompilerFuelStepAt.typedArgs,
     CompilerFuelStepAt.argsAt, CompilerFuelStepAt.caseArms,
     CompilerFuelStepAt.patternList, CompilerFuelStepAt.list]))

local macro "prove_app_core_fuel" theoremName:ident kind:term : command =>
  `(private theorem $theoremName (fuel : Nat)
      (ih : CompilerFuelStepAt fuel) :
      AppCoreFuelStableFor fuel $kind := by
        unfold AppCoreFuelStableFor
        solve_app_core_fuel fuel ih)

prove_app_core_fuel compileAppCoreFuel_hQuote_stable .hQuote
prove_app_core_fuel compileAppCoreFuel_hPredicate_stable .hPredicate
prove_app_core_fuel compileAppCoreFuel_hTranslatePredicate_stable .hTranslatePredicate
prove_app_core_fuel compileAppCoreFuel_hCallPredicate_stable .hCallPredicate
prove_app_core_fuel compileAppCoreFuel_hAssertaPredicate_stable .hAssertaPredicate
prove_app_core_fuel compileAppCoreFuel_hAssertzPredicate_stable .hAssertzPredicate
prove_app_core_fuel compileAppCoreFuel_hRetractPredicate_stable .hRetractPredicate
prove_app_core_fuel compileAppCoreFuel_hProcessMettaString_stable .hProcessMettaString
prove_app_core_fuel compileAppCoreFuel_hUnquote_stable .hUnquote
prove_app_core_fuel compileAppCoreFuel_hEmpty_stable .hEmpty
prove_app_core_fuel compileAppCoreFuel_hCut_stable .hCut
prove_app_core_fuel compileAppCoreFuel_hTest_stable .hTest
prove_app_core_fuel compileAppCoreFuel_hTrace_stable .hTrace
prove_app_core_fuel compileAppCoreFuel_hAndThen_stable .hAndThen
prove_app_core_fuel compileAppCoreFuel_hOrElse_stable .hOrElse
prove_app_core_fuel compileAppCoreFuel_hHashPlus_stable .hHashPlus
prove_app_core_fuel compileAppCoreFuel_hHashMinus_stable .hHashMinus
prove_app_core_fuel compileAppCoreFuel_hCons_stable .hCons
prove_app_core_fuel compileAppCoreFuel_hIf_stable .hIf
prove_app_core_fuel compileAppCoreFuel_hLet_stable .hLet
prove_app_core_fuel compileAppCoreFuel_hLetStar_stable .hLetStar
prove_app_core_fuel compileAppCoreFuel_hCase_stable .hCase
prove_app_core_fuel compileAppCoreFuel_hCollapse_stable .hCollapse
prove_app_core_fuel compileAppCoreFuel_hOnce_stable .hOnce
prove_app_core_fuel compileAppCoreFuel_hSuperpose_stable .hSuperpose
prove_app_core_fuel compileAppCoreFuel_hUnify_stable .hUnify
prove_app_core_fuel compileAppCoreFuel_hSucceedsPredicate_stable .hSucceedsPredicate
prove_app_core_fuel compileAppCoreFuel_hFor_stable .hFor
prove_app_core_fuel compileAppCoreFuel_hChain_stable .hChain
prove_app_core_fuel compileAppCoreFuel_hFoldall_stable .hFoldall
prove_app_core_fuel compileAppCoreFuel_hForall_stable .hForall
prove_app_core_fuel compileAppCoreFuel_hProgn_stable .hProgn
prove_app_core_fuel compileAppCoreFuel_hProg1_stable .hProg1
prove_app_core_fuel compileAppCoreFuel_hWithMutex_stable .hWithMutex
prove_app_core_fuel compileAppCoreFuel_hTransaction_stable .hTransaction
prove_app_core_fuel compileAppCoreFuel_hHyperpose_stable .hHyperpose
prove_app_core_fuel compileAppCoreFuel_hUnique_stable .hUnique
prove_app_core_fuel compileAppCoreFuel_hUnion_stable .hUnion
prove_app_core_fuel compileAppCoreFuel_hIntersection_stable .hIntersection
prove_app_core_fuel compileAppCoreFuel_hSubtraction_stable .hSubtraction
prove_app_core_fuel compileAppCoreFuel_hEval_stable .hEval
prove_app_core_fuel compileAppCoreFuel_hCatch_stable .hCatch
prove_app_core_fuel compileAppCoreFuel_hCall_stable .hCall
prove_app_core_fuel compileAppCoreFuel_hReduce_stable .hReduce
prove_app_core_fuel compileAppCoreFuel_hGetTypeSpace_stable .hGetTypeSpace
prove_app_core_fuel compileAppCoreFuel_hGetAtoms_stable .hGetAtoms
prove_app_core_fuel compileAppCoreFuel_hGetType_stable .hGetType
prove_app_core_fuel compileAppCoreFuel_hGetMetatype_stable .hGetMetatype
prove_app_core_fuel compileAppCoreFuel_hMatch_stable .hMatch
prove_app_core_fuel compileAppCoreFuel_hFind_stable .hFind
prove_app_core_fuel compileAppCoreFuel_hDoubleEqual_stable .hDoubleEqual
prove_app_core_fuel compileAppCoreFuel_hEqual_stable .hEqual
prove_app_core_fuel compileAppCoreFuel_hAddAtom_stable .hAddAtom
prove_app_core_fuel compileAppCoreFuel_hRemoveAtom_stable .hRemoveAtom
prove_app_core_fuel compileAppCoreFuel_hBind_stable .hBind
prove_app_core_fuel compileAppCoreFuel_hGetState_stable .hGetState
prove_app_core_fuel compileAppCoreFuel_hChangeState_stable .hChangeState
prove_app_core_fuel compileAppCoreFuel_other_stable .other

private theorem compileAppCoreFuel_all_kinds_stable (fuel : Nat)
    (ih : CompilerFuelStepAt fuel) :
    ∀ kind, AppCoreFuelStableFor fuel kind := by
  intro kind
  cases kind <;>
    first
    | exact compileAppCoreFuel_hQuote_stable fuel ih
    | exact compileAppCoreFuel_hPredicate_stable fuel ih
    | exact compileAppCoreFuel_hTranslatePredicate_stable fuel ih
    | exact compileAppCoreFuel_hCallPredicate_stable fuel ih
    | exact compileAppCoreFuel_hAssertaPredicate_stable fuel ih
    | exact compileAppCoreFuel_hAssertzPredicate_stable fuel ih
    | exact compileAppCoreFuel_hRetractPredicate_stable fuel ih
    | exact compileAppCoreFuel_hProcessMettaString_stable fuel ih
    | exact compileAppCoreFuel_hUnquote_stable fuel ih
    | exact compileAppCoreFuel_hEmpty_stable fuel ih
    | exact compileAppCoreFuel_hCut_stable fuel ih
    | exact compileAppCoreFuel_hTest_stable fuel ih
    | exact compileAppCoreFuel_hTrace_stable fuel ih
    | exact compileAppCoreFuel_hAndThen_stable fuel ih
    | exact compileAppCoreFuel_hOrElse_stable fuel ih
    | exact compileAppCoreFuel_hHashPlus_stable fuel ih
    | exact compileAppCoreFuel_hHashMinus_stable fuel ih
    | exact compileAppCoreFuel_hCons_stable fuel ih
    | exact compileAppCoreFuel_hIf_stable fuel ih
    | exact compileAppCoreFuel_hLet_stable fuel ih
    | exact compileAppCoreFuel_hLetStar_stable fuel ih
    | exact compileAppCoreFuel_hCase_stable fuel ih
    | exact compileAppCoreFuel_hCollapse_stable fuel ih
    | exact compileAppCoreFuel_hOnce_stable fuel ih
    | exact compileAppCoreFuel_hSuperpose_stable fuel ih
    | exact compileAppCoreFuel_hUnify_stable fuel ih
    | exact compileAppCoreFuel_hSucceedsPredicate_stable fuel ih
    | exact compileAppCoreFuel_hFor_stable fuel ih
    | exact compileAppCoreFuel_hChain_stable fuel ih
    | exact compileAppCoreFuel_hFoldall_stable fuel ih
    | exact compileAppCoreFuel_hForall_stable fuel ih
    | exact compileAppCoreFuel_hProgn_stable fuel ih
    | exact compileAppCoreFuel_hProg1_stable fuel ih
    | exact compileAppCoreFuel_hWithMutex_stable fuel ih
    | exact compileAppCoreFuel_hTransaction_stable fuel ih
    | exact compileAppCoreFuel_hHyperpose_stable fuel ih
    | exact compileAppCoreFuel_hUnique_stable fuel ih
    | exact compileAppCoreFuel_hUnion_stable fuel ih
    | exact compileAppCoreFuel_hIntersection_stable fuel ih
    | exact compileAppCoreFuel_hSubtraction_stable fuel ih
    | exact compileAppCoreFuel_hEval_stable fuel ih
    | exact compileAppCoreFuel_hCatch_stable fuel ih
    | exact compileAppCoreFuel_hCall_stable fuel ih
    | exact compileAppCoreFuel_hReduce_stable fuel ih
    | exact compileAppCoreFuel_hGetTypeSpace_stable fuel ih
    | exact compileAppCoreFuel_hGetAtoms_stable fuel ih
    | exact compileAppCoreFuel_hGetType_stable fuel ih
    | exact compileAppCoreFuel_hGetMetatype_stable fuel ih
    | exact compileAppCoreFuel_hMatch_stable fuel ih
    | exact compileAppCoreFuel_hFind_stable fuel ih
    | exact compileAppCoreFuel_hDoubleEqual_stable fuel ih
    | exact compileAppCoreFuel_hEqual_stable fuel ih
    | exact compileAppCoreFuel_hAddAtom_stable fuel ih
    | exact compileAppCoreFuel_hRemoveAtom_stable fuel ih
    | exact compileAppCoreFuel_hBind_stable fuel ih
    | exact compileAppCoreFuel_hGetState_stable fuel ih
    | exact compileAppCoreFuel_hChangeState_stable fuel ih
    | exact compileAppCoreFuel_other_stable fuel ih

theorem compileAppCoreFuel_stable_step (fuel : Nat)
    (ih : CompilerFuelStepAt fuel) :
    ∀ env start head arguments term goals next,
      compileAppCoreFuel (fuel + 1) env start head arguments =
          .ok (term, goals, next) →
        compileAppCoreFuel (fuel + 2) env start head arguments =
          .ok (term, goals, next) := by
  intro env start head arguments term goals next compiled
  exact compileAppCoreFuel_all_kinds_stable fuel ih
    (classifyAppCoreHead head) env start head arguments term goals next rfl compiled

/-- The mutual compiler stability invariant advances by one fuel layer. -/
theorem compilerFuelStepAt_succ (fuel : Nat)
    (ih : CompilerFuelStepAt fuel) : CompilerFuelStepAt (fuel + 1) where
  expr := compileExprFuel_stable_step fuel ih
  pattern := compilePatternFuel_stable_step fuel ih
  app := compileAppFuel_stable_step fuel ih
  appCore := compileAppCoreFuel_stable_step fuel ih
  typedArgs := compileTypedArgsFuel_stable_step fuel ih
  argsAt := compileArgsAtFuel_stable_step fuel ih
  caseArms := compileCaseArmsFuel_stable_step fuel ih
  patternList := compilePatternListFuel_stable_step fuel ih
  list := compileListFuel_stable_step fuel ih

/-- Every executable compiler traversal preserves successful results when
one unit of fuel is added. -/
theorem compilerFuelStepAt (fuel : Nat) : CompilerFuelStepAt fuel := by
  induction fuel with
  | zero => exact compilerFuelStepAt_zero
  | succ fuel ih =>
      simpa [Nat.succ_eq_add_one] using compilerFuelStepAt_succ fuel ih

/-- Once expression compilation succeeds, any additional fuel preserves its
exact term, ordered goal stream, and fresh-name counter. -/
theorem compileExprFuel_mono (fuel extra : Nat) (env : CEnv) (start : Nat)
    (source term : Metta.Atom) (goals : List Goal) (next : Nat)
    (compiled : compileExprFuel fuel env start source =
      .ok (term, goals, next)) :
    compileExprFuel (fuel + extra) env start source =
      .ok (term, goals, next) := by
  induction extra with
  | zero => simpa using compiled
  | succ extra ih =>
      rw [Nat.add_succ]
      exact (compilerFuelStepAt (fuel + extra)).expr
        env start source term goals next ih

/-- Order-theoretic form of `compileExprFuel_mono`: any larger budget
preserves a successful expression compilation exactly. -/
theorem compileExprFuel_mono_of_le {fuel more : Nat} (env : CEnv)
    (start : Nat) (source term : Metta.Atom) (goals : List Goal) (next : Nat)
    (fuelLe : fuel ≤ more)
    (compiled : compileExprFuel fuel env start source =
      .ok (term, goals, next)) :
    compileExprFuel more env start source = .ok (term, goals, next) := by
  rw [show more = fuel + (more - fuel) by omega]
  exact compileExprFuel_mono fuel (more - fuel) env start source term goals
    next compiled

end PLeaTTa
