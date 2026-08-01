import PLeaTTa.PersistentSubst
import PLeaTTa.Semantics
import PLeaTTa.Proofs.Unification

namespace PLeaTTa

open Metta (Atom Subst GroundingTable)

/-- Every terminal resolution token on the live clause-copy surface is below
the configuration's monotone allocation counter. Stored world clauses and
atoms cross this boundary only through total suffix-renaming or an explicit
counter advance. -/
def ConfBelowResolutionCounter (conf : Conf) : Prop :=
  resolutionLiveHighWater conf ≤ conf.counter

private def resolutionCurVars (conf : Conf) : List String :=
  match conf.cur with
  | none => []
  | some (goals, binding) =>
      specializationGoalsVars goals ++ resolutionSubstVars binding

theorem ConfBelowResolutionCounter.name {conf : Conf}
    (below : ConfBelowResolutionCounter conf) (name : String)
    (member : name ∈ resolutionLiveVars conf) :
    resolutionSeedHighWaterName name ≤ conf.counter := by
  exact (PersistentSubst.resolutionSeedHighWaterNames_le_iff
    (resolutionLiveVars conf) conf.counter).mp below name member

theorem ConfBelowResolutionCounter.of_names (conf : Conf)
    (bounded : ∀ name ∈ resolutionLiveVars conf,
      resolutionSeedHighWaterName name ≤ conf.counter) :
    ConfBelowResolutionCounter conf := by
  exact (PersistentSubst.resolutionSeedHighWaterNames_le_iff
    (resolutionLiveVars conf) conf.counter).mpr bounded

theorem ConfBelowResolutionCounter.of_subset {source target : Conf}
    (below : ConfBelowResolutionCounter source)
    (counterMono : source.counter ≤ target.counter)
    (subset : ∀ name, name ∈ resolutionLiveVars target →
      name ∈ resolutionLiveVars source) :
    ConfBelowResolutionCounter target := by
  apply ConfBelowResolutionCounter.of_names
  intro name member
  exact Nat.le_trans (below.name name (subset name member)) counterMono

theorem ConfBelowResolutionCounter.of_origin {source target : Conf}
    (below : ConfBelowResolutionCounter source)
    (counterMono : source.counter ≤ target.counter)
    (origin : ∀ name, name ∈ resolutionLiveVars target →
      name ∈ resolutionLiveVars source ∨
        resolutionSeedHighWaterName name ≤ target.counter) :
    ConfBelowResolutionCounter target := by
  apply ConfBelowResolutionCounter.of_names
  intro name member
  rcases origin name member with hsource | hbounded
  · exact Nat.le_trans (below.name name hsource) counterMono
  · exact hbounded

theorem resolutionLiveVars_pull_subset
    (conf : Conf) (name : String)
    (member : name ∈ resolutionLiveVars (pull conf)) :
    name ∈ resolutionLiveVars conf := by
  rcases conf with
    ⟨cur, alts, world, counter, qterm, answers, answerKeys,
      answerKeys_sound, barriers⟩
  cases cur with
  | none =>
      induction alts generalizing barriers with
      | nil =>
          cases barriers <;>
            simpa [PLeaTTa.pull, pullAux, pullAuxTracked,
              pullAuxCached, resolutionLiveVars] using member
      | cons alt rest ih =>
          cases alt with
          | barrier =>
              cases barriers with
              | none =>
                  simpa [PLeaTTa.pull, pullAux, pullAuxTracked,
                    resolutionLiveVars, resolutionAltVars] using
                    ih (barriers := none) member
              | some depth =>
                  simpa [PLeaTTa.pull, pullAux, pullAuxTracked,
                    pullAuxCached, resolutionLiveVars, resolutionAltVars] using
                    ih (barriers := some (depth - 1)) member
          | br goals binding =>
              cases barriers <;>
                simpa [PLeaTTa.pull, pullAux, pullAuxTracked,
                  pullAuxCached, resolutionLiveVars, resolutionAltVars,
                  List.append_assoc] using member
  | some branch =>
      rcases branch with ⟨activeGoals, activeBinding⟩
      induction alts generalizing barriers with
      | nil =>
          have extended := List.mem_append_right
            (specializationGoalsVars activeGoals ++
              resolutionSubstVars activeBinding) member
          cases barriers <;>
            simpa [PLeaTTa.pull, pullAux, pullAuxTracked,
              pullAuxCached, resolutionLiveVars, List.append_assoc] using
              extended
      | cons alt rest ih =>
          cases alt with
          | barrier =>
              cases barriers with
              | none =>
                  simpa [PLeaTTa.pull, pullAux, pullAuxTracked,
                    resolutionLiveVars, resolutionAltVars] using
                    ih (barriers := none) member
              | some depth =>
                  simpa [PLeaTTa.pull, pullAux, pullAuxTracked,
                    pullAuxCached, resolutionLiveVars, resolutionAltVars] using
                    ih (barriers := some (depth - 1)) member
          | br goals binding =>
              have extended := List.mem_append_right
                (specializationGoalsVars activeGoals ++
                  resolutionSubstVars activeBinding) member
              cases barriers <;>
                simpa [PLeaTTa.pull, pullAux, pullAuxTracked,
                  pullAuxCached, resolutionLiveVars, resolutionAltVars,
                  List.append_assoc] using extended

theorem ConfBelowResolutionCounter.pull {conf : Conf}
    (below : ConfBelowResolutionCounter conf) :
    ConfBelowResolutionCounter (pull conf) :=
  below.of_subset (by
    unfold PLeaTTa.pull
    generalize pullAuxTracked conf.barriers conf.alts = result
    rcases result with ⟨result, cache⟩
    cases result <;> exact Nat.le_refl _)
    (resolutionLiveVars_pull_subset conf)

private theorem resolutionSeedHighWaterName_le_of_mem
    (names : List String) (name : String) (member : name ∈ names) :
    resolutionSeedHighWaterName name ≤ resolutionSeedHighWaterNames names := by
  induction names with
  | nil => simp at member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

theorem resolutionSeedHighWaterNames_le_of_subset
    {left right : List String}
    (subset : ∀ name, name ∈ left → name ∈ right) :
    resolutionSeedHighWaterNames left ≤ resolutionSeedHighWaterNames right := by
  induction left with
  | nil => simp [resolutionSeedHighWaterNames]
  | cons head rest ih =>
      simp only [resolutionSeedHighWaterNames]
      apply Nat.max_le.mpr
      constructor
      · exact resolutionSeedHighWaterName_le_of_mem right head
          (subset head (by simp))
      · exact ih (fun name member => subset name (by simp [member]))

@[simp] theorem resolutionSeedHighWaterNames_append
    (left right : List String) :
    resolutionSeedHighWaterNames (left ++ right) =
      max (resolutionSeedHighWaterNames left)
        (resolutionSeedHighWaterNames right) := by
  induction left with
  | nil => simp [resolutionSeedHighWaterNames]
  | cons head rest ih =>
      simp only [List.cons_append, resolutionSeedHighWaterNames, ih]
      omega

theorem confBelowResolutionCounter_iff (conf : Conf) :
    ConfBelowResolutionCounter conf ↔
      resolutionSeedHighWaterNames (resolutionCurVars conf) ≤ conf.counter ∧
      resolutionSeedHighWaterNames
          (conf.alts.flatMap resolutionAltVars) ≤ conf.counter ∧
      resolutionSeedHighWaterNames conf.qterm.vars ≤ conf.counter ∧
      resolutionSeedHighWaterNames
          (conf.answers.flatMap Atom.vars) ≤ conf.counter := by
  cases hcur : conf.cur with
  | none =>
      simp [ConfBelowResolutionCounter, resolutionLiveHighWater,
        resolutionLiveVars, resolutionCurVars, resolutionSeedHighWaterNames,
        hcur]
  | some branch =>
      rcases branch with ⟨goals, binding⟩
      simp [ConfBelowResolutionCounter, resolutionLiveHighWater,
        resolutionLiveVars, resolutionCurVars, hcur]
      omega

theorem ConfBelowResolutionCounter.components {conf : Conf}
    (below : ConfBelowResolutionCounter conf) :
    resolutionSeedHighWaterNames (resolutionCurVars conf) ≤ conf.counter ∧
    resolutionSeedHighWaterNames
        (conf.alts.flatMap resolutionAltVars) ≤ conf.counter ∧
    resolutionSeedHighWaterNames conf.qterm.vars ≤ conf.counter ∧
    resolutionSeedHighWaterNames
        (conf.answers.flatMap Atom.vars) ≤ conf.counter :=
  (confBelowResolutionCounter_iff conf).mp below

theorem ConfBelowResolutionCounter.of_components (conf : Conf)
    (hcur : resolutionSeedHighWaterNames (resolutionCurVars conf) ≤
      conf.counter)
    (halts : resolutionSeedHighWaterNames
      (conf.alts.flatMap resolutionAltVars) ≤ conf.counter)
    (hqterm : resolutionSeedHighWaterNames conf.qterm.vars ≤ conf.counter)
    (hanswers : resolutionSeedHighWaterNames
      (conf.answers.flatMap Atom.vars) ≤ conf.counter) :
    ConfBelowResolutionCounter conf :=
  (confBelowResolutionCounter_iff conf).mpr
    ⟨hcur, halts, hqterm, hanswers⟩

theorem ConfBelowResolutionCounter.active {conf : Conf}
    (below : ConfBelowResolutionCounter conf) (goals : List Goal)
    (binding : Subst) (hcur : conf.cur = some (goals, binding)) :
    resolutionSeedHighWaterNames
        (specializationGoalsVars goals ++ resolutionSubstVars binding) ≤
      conf.counter := by
  have hactive := below.components.1
  simpa [resolutionCurVars, hcur] using hactive

theorem ConfBelowResolutionCounter.alts {conf : Conf}
    (below : ConfBelowResolutionCounter conf) :
    resolutionSeedHighWaterNames
        (conf.alts.flatMap resolutionAltVars) ≤ conf.counter :=
  below.components.2.1

theorem ConfBelowResolutionCounter.qterm {conf : Conf}
    (below : ConfBelowResolutionCounter conf) :
    resolutionSeedHighWaterNames conf.qterm.vars ≤ conf.counter :=
  below.components.2.2.1

theorem ConfBelowResolutionCounter.answers {conf : Conf}
    (below : ConfBelowResolutionCounter conf) :
    resolutionSeedHighWaterNames
      (conf.answers.flatMap Atom.vars) ≤ conf.counter :=
  below.components.2.2.2

theorem ConfBelowResolutionCounter.answerValues {conf : Conf}
    (below : ConfBelowResolutionCounter conf) :
    resolutionSeedHighWaterNames
      (conf.answerValues.flatMap Atom.vars) ≤ conf.counter := by
  apply Nat.le_trans (resolutionSeedHighWaterNames_le_of_subset ?_)
    below.answers
  intro name member
  simp only [Conf.answerValues, List.mem_flatMap] at member ⊢
  obtain ⟨answer, hanswer, hname⟩ := member
  exact ⟨answer, List.mem_reverse.mp hanswer, hname⟩

theorem ConfBelowResolutionCounter.clearActive {conf : Conf}
    (below : ConfBelowResolutionCounter conf) :
    ConfBelowResolutionCounter { conf with cur := none } := by
  apply ConfBelowResolutionCounter.of_components
  · simp [resolutionCurVars, resolutionSeedHighWaterNames]
  · exact below.alts
  · exact below.qterm
  · exact below.answers

theorem ConfBelowResolutionCounter.replaceActive {conf : Conf}
    (below : ConfBelowResolutionCounter conf) (oldGoals : List Goal)
    (oldBinding : Subst)
    (hcur : conf.cur = some (oldGoals, oldBinding))
    (newGoals : List Goal) (newBinding : Subst)
    (origin : ∀ name,
      name ∈ specializationGoalsVars newGoals ++
          resolutionSubstVars newBinding →
        name ∈ specializationGoalsVars oldGoals ++
          resolutionSubstVars oldBinding) :
    ConfBelowResolutionCounter
      { conf with cur := some (newGoals, newBinding) } := by
  apply ConfBelowResolutionCounter.of_components
  · simp only [resolutionCurVars]
    exact Nat.le_trans
      (resolutionSeedHighWaterNames_le_of_subset origin)
      (below.active oldGoals oldBinding hcur)
  · exact below.alts
  · exact below.qterm
  · exact below.answers

/-- Prepending one primitive equality preserves the live-name bound when
both new operands are already below the current allocation counter.  Unlike
`replaceActiveEq`, this form does not require the operands to originate in
the old active goals; a query term already bounded elsewhere in the
configuration is a legitimate equality operand. -/
theorem ConfBelowResolutionCounter.prependEq {conf : Conf}
    (below : ConfBelowResolutionCounter conf) (goals : List Goal)
    (binding : Subst) (hcur : conf.cur = some (goals, binding))
    (left right : Atom)
    (leftBelow : resolutionSeedHighWaterNames left.vars ≤ conf.counter)
    (rightBelow : resolutionSeedHighWaterNames right.vars ≤ conf.counter) :
    ConfBelowResolutionCounter
      { conf with cur := some (Goal.eq left right :: goals, binding) } := by
  apply ConfBelowResolutionCounter.of_components
  · have oldBelow := below.active goals binding hcur
    simp only [resolutionCurVars, specializationGoalsVars,
      specializationGoalVars, resolutionSeedHighWaterNames_append] at oldBelow ⊢
    omega
  · exact below.alts
  · exact below.qterm
  · exact below.answers

@[simp] theorem resolutionSeedHighWaterName_append_compact
    (name : String) (seed : Nat) :
    resolutionSeedHighWaterName (name ++ resolutionCompactSuffix seed) =
      seed + 1 := by
  simp [resolutionSeedHighWaterName, terminalResolutionSeed?_append]

theorem resolutionSeedHighWaterAtom_renameCompact_le
    (atom : Atom) (seed : Nat) :
    resolutionSeedHighWaterNames
        (renameAtomSuffix (resolutionCompactSuffix seed) atom).vars ≤
      seed + 1 := by
  rw [PersistentSubst.resolutionSeedHighWaterNames_le_iff]
  intro name member
  rw [mem_renameAtomSuffix_vars] at member
  obtain ⟨source, _, rfl⟩ := member
  rw [resolutionSeedHighWaterName_append_compact]

theorem resolutionSeedHighWaterAtomList_renameCompact_le
    (atoms : List Atom) (seed : Nat) :
    resolutionSeedHighWaterNames
        ((atoms.map (renameAtomSuffix (resolutionCompactSuffix seed))).flatMap
          Atom.vars) ≤
      seed + 1 := by
  rw [PersistentSubst.resolutionSeedHighWaterNames_le_iff]
  intro name member
  simp only [List.mem_flatMap, List.mem_map] at member
  obtain ⟨renamed, ⟨source, hsource, rfl⟩, hname⟩ := member
  have hatom := resolutionSeedHighWaterAtom_renameCompact_le source seed
  exact (PersistentSubst.resolutionSeedHighWaterNames_le_iff
    (renameAtomSuffix (resolutionCompactSuffix seed) source).vars
    (seed + 1)).mp hatom name hname

/-- One certified collection copy is below the high-water it returns. -/
theorem copyFindallAtom_value_below (counter : Nat) (value : Atom) :
    resolutionSeedHighWaterNames
        (copyFindallAtom counter value).value.vars ≤
      (copyFindallAtom counter value).counter := by
  simp only [copyFindallAtom]
  split
  next closed =>
    have noVars : value.vars = [] :=
      (PersistentSubst.atomClosed_eq_true_iff_vars_nil value).mp closed
    simp [noVars, resolutionSeedHighWaterNames]
  next isOpen =>
    exact resolutionSeedHighWaterAtom_renameCompact_le value
      (advanceCounterPastAtoms counter [value])

/-- Every copied bag value is below the final threaded collection high-water. -/
theorem copyFindallBag_values_below :
    ∀ (counter : Nat) (values : List Atom),
      resolutionSeedHighWaterNames
          ((copyFindallBag counter values).values.flatMap Atom.vars) ≤
        (copyFindallBag counter values).counter
  | counter, [] => by simp [copyFindallBag, resolutionSeedHighWaterNames]
  | counter, value :: rest => by
      simp only [copyFindallBag, List.flatMap_cons,
        resolutionSeedHighWaterNames_append]
      apply Nat.max_le.mpr
      constructor
      · exact Nat.le_trans (copyFindallAtom_value_below counter value)
          (copyFindallBag_counter_mono
            (copyFindallAtom counter value).counter rest)
      · exact copyFindallBag_values_below
          (copyFindallAtom counter value).counter rest

mutual

theorem resolutionSeedHighWaterGoal_renameCompact_le
    (goal : Goal) (barrier seed : Nat) :
    resolutionSeedHighWaterNames
        (specializationGoalVars
          (renameGoalSuffix (resolutionCompactSuffix seed) barrier goal)) ≤
      seed + 1 := by
  cases goal with
  | call function args result =>
      have hargs := resolutionSeedHighWaterAtomList_renameCompact_le args seed
      have hresult := resolutionSeedHighWaterAtom_renameCompact_le result seed
      simp only [renameGoalSuffix, specializationGoalVars,
        resolutionSeedHighWaterNames_append]
      omega
  | bin operation args result =>
      have hargs := resolutionSeedHighWaterAtomList_renameCompact_le args seed
      have hresult := resolutionSeedHighWaterAtom_renameCompact_le result seed
      simp only [renameGoalSuffix, specializationGoalVars,
        resolutionSeedHighWaterNames_append]
      omega
  | callDyn head args result =>
      have hhead := resolutionSeedHighWaterAtom_renameCompact_le head seed
      have hargs := resolutionSeedHighWaterAtomList_renameCompact_le args seed
      have hresult := resolutionSeedHighWaterAtom_renameCompact_le result seed
      simp only [renameGoalSuffix, specializationGoalVars,
        resolutionSeedHighWaterNames_append]
      omega
  | evalg value result =>
      have hvalue := resolutionSeedHighWaterAtom_renameCompact_le value seed
      have hresult := resolutionSeedHighWaterAtom_renameCompact_le result seed
      simp only [renameGoalSuffix, specializationGoalVars,
        resolutionSeedHighWaterNames_append]
      omega
  | catchg template sub result =>
      have htemplate := resolutionSeedHighWaterAtom_renameCompact_le template seed
      have hsub := resolutionSeedHighWaterGoals_renameCompact_le sub barrier seed
      have hresult := resolutionSeedHighWaterAtom_renameCompact_le result seed
      simp only [renameGoalSuffix, specializationGoalVars,
        resolutionSeedHighWaterNames_append]
      omega
  | softcut template sub thenGoals elseGoals =>
      have htemplate := resolutionSeedHighWaterAtom_renameCompact_le template seed
      have hsub := resolutionSeedHighWaterGoals_renameCompact_le sub barrier seed
      have hthen := resolutionSeedHighWaterGoals_renameCompact_le
        thenGoals barrier seed
      have helse := resolutionSeedHighWaterGoals_renameCompact_le
        elseGoals barrier seed
      simp only [renameGoalSuffix, specializationGoalVars,
        resolutionSeedHighWaterNames_append]
      omega
  | eq left right =>
      have hleft := resolutionSeedHighWaterAtom_renameCompact_le left seed
      have hright := resolutionSeedHighWaterAtom_renameCompact_le right seed
      simp only [renameGoalSuffix, specializationGoalVars,
        resolutionSeedHighWaterNames_append]
      omega
  | compileAlias left right =>
      have hleft := resolutionSeedHighWaterAtom_renameCompact_le left seed
      have hright := resolutionSeedHighWaterAtom_renameCompact_le right seed
      simp only [renameGoalSuffix, specializationGoalVars,
        resolutionSeedHighWaterNames_append]
      omega
  | cut => simp [renameGoalSuffix, specializationGoalVars,
      resolutionSeedHighWaterNames]
  | cutAt index => simp [renameGoalSuffix, specializationGoalVars,
      resolutionSeedHighWaterNames]
  | findall template sub result =>
      have htemplate := resolutionSeedHighWaterAtom_renameCompact_le template seed
      have hsub := resolutionSeedHighWaterGoals_renameCompact_le sub barrier seed
      have hresult := resolutionSeedHighWaterAtom_renameCompact_le result seed
      simp only [renameGoalSuffix, specializationGoalVars,
        resolutionSeedHighWaterNames_append]
      omega
  | onceg template sub result =>
      have htemplate := resolutionSeedHighWaterAtom_renameCompact_le template seed
      have hsub := resolutionSeedHighWaterGoals_renameCompact_le sub barrier seed
      have hresult := resolutionSeedHighWaterAtom_renameCompact_le result seed
      simp only [renameGoalSuffix, specializationGoalVars,
        resolutionSeedHighWaterNames_append]
      omega
  | transactiong template sub =>
      have htemplate := resolutionSeedHighWaterAtom_renameCompact_le template seed
      have hsub := resolutionSeedHighWaterGoals_renameCompact_le sub barrier seed
      simp only [renameGoalSuffix, specializationGoalVars,
        resolutionSeedHighWaterNames_append]
      omega
  | amb branches result =>
      have hbranches := resolutionSeedHighWaterBranches_renameCompact_le
        branches barrier seed
      have hresult := resolutionSeedHighWaterAtom_renameCompact_le result seed
      simp only [renameGoalSuffix, specializationGoalVars,
        resolutionSeedHighWaterNames_append]
      omega
  | spread value result =>
      have hvalue := resolutionSeedHighWaterAtom_renameCompact_le value seed
      have hresult := resolutionSeedHighWaterAtom_renameCompact_le result seed
      simp only [renameGoalSuffix, specializationGoalVars,
        resolutionSeedHighWaterNames_append]
      omega
  | ite condition thenBranch elseBranch result =>
      have hcondition := resolutionSeedHighWaterAtom_renameCompact_le
        condition seed
      have hthenValue := resolutionSeedHighWaterAtom_renameCompact_le
        thenBranch.1 seed
      have hthenGoals := resolutionSeedHighWaterGoals_renameCompact_le
        thenBranch.2 barrier seed
      have helseValue := resolutionSeedHighWaterAtom_renameCompact_le
        elseBranch.1 seed
      have helseGoals := resolutionSeedHighWaterGoals_renameCompact_le
        elseBranch.2 barrier seed
      have hresult := resolutionSeedHighWaterAtom_renameCompact_le result seed
      simp only [renameGoalSuffix, specializationGoalVars,
        resolutionSeedHighWaterNames_append]
      omega
  | smatch pattern =>
      exact resolutionSeedHighWaterAtom_renameCompact_le pattern seed
  | wact operation args result =>
      have hargs := resolutionSeedHighWaterAtomList_renameCompact_le args seed
      have hresult := resolutionSeedHighWaterAtom_renameCompact_le result seed
      simp only [renameGoalSuffix, specializationGoalVars,
        resolutionSeedHighWaterNames_append]
      omega

theorem resolutionSeedHighWaterGoals_renameCompact_le
    (goals : List Goal) (barrier seed : Nat) :
    resolutionSeedHighWaterNames
        (specializationGoalsVars
          (renameGoalsSuffix (resolutionCompactSuffix seed) barrier goals)) ≤
      seed + 1 := by
  cases goals with
  | nil => simp [renameGoalsSuffix, specializationGoalsVars,
      resolutionSeedHighWaterNames]
  | cons goal rest =>
      have hgoal := resolutionSeedHighWaterGoal_renameCompact_le
        goal barrier seed
      have hrest := resolutionSeedHighWaterGoals_renameCompact_le
        rest barrier seed
      simp only [renameGoalsSuffix, specializationGoalsVars,
        resolutionSeedHighWaterNames_append]
      omega

theorem resolutionSeedHighWaterBranches_renameCompact_le
    (branches : List (Atom × List Goal)) (barrier seed : Nat) :
    resolutionSeedHighWaterNames
        (specializationBranchVars
          (renameBranchesSuffix (resolutionCompactSuffix seed) barrier
            branches)) ≤
      seed + 1 := by
  cases branches with
  | nil => simp [renameBranchesSuffix, specializationBranchVars,
      resolutionSeedHighWaterNames]
  | cons branch rest =>
      have htemplate := resolutionSeedHighWaterAtom_renameCompact_le
        branch.1 seed
      have hgoals := resolutionSeedHighWaterGoals_renameCompact_le
        branch.2 barrier seed
      have hrest := resolutionSeedHighWaterBranches_renameCompact_le
        rest barrier seed
      simp only [renameBranchesSuffix, specializationBranchVars,
        resolutionSeedHighWaterNames_append]
      omega

end

mutual

@[simp] theorem specializationGoalVars_tagCutsGoal
    (barrier : Nat) (goal : Goal) :
    specializationGoalVars (tagCutsGoal barrier goal) =
      specializationGoalVars goal := by
  cases goal <;>
    simp [tagCutsGoal, specializationGoalVars,
      specializationGoalsVars_tagCutsGoals,
      specializationBranchVars_tagCutsBranches]

@[simp] theorem specializationGoalsVars_tagCutsGoals
    (barrier : Nat) (goals : List Goal) :
    specializationGoalsVars (tagCutsGoals barrier goals) =
      specializationGoalsVars goals := by
  cases goals with
  | nil => rfl
  | cons goal rest =>
      simp [tagCutsGoals, specializationGoalsVars,
        specializationGoalVars_tagCutsGoal,
        specializationGoalsVars_tagCutsGoals]

@[simp] theorem specializationBranchVars_tagCutsBranches
    (barrier : Nat) (branches : List (Atom × List Goal)) :
    specializationBranchVars (tagCutsBranches barrier branches) =
      specializationBranchVars branches := by
  cases branches with
  | nil => rfl
  | cons branch rest =>
      rcases branch with ⟨template, goals⟩
      simp [tagCutsBranches, specializationBranchVars,
        specializationGoalsVars_tagCutsGoals,
        specializationBranchVars_tagCutsBranches]

end

theorem specializationGoalsVars_iteBranchGoals_subset
    (res : Atom) (branch : Atom × List Goal) (name : String)
    (member : name ∈ specializationGoalsVars (iteBranchGoals res branch)) :
    name ∈ branch.1.vars ++ specializationGoalsVars branch.2 ++ res.vars := by
  unfold iteBranchGoals at member
  split at member
  · simp only [List.mem_append]
    exact Or.inl (Or.inr member)
  · simp only [specializationGoalsVars, specializationGoalVars,
      List.mem_append] at member ⊢
    rcases member with (hhead | hres) | hgoals
    · exact Or.inl (Or.inl hhead)
    · exact Or.inr hres
    · exact Or.inl (Or.inr hgoals)

theorem resolutionSeedHighWaterClause_freshen_le
    (argsv args : List Atom) (res : Atom) (rest : List Goal)
    (binding : Subst) (qterm : Atom) (seed barrier : Nat)
    (clause : Clause) :
    resolutionSeedHighWaterNames
        (resolutionClauseVars
          (freshenResolutionClause argsv args res rest binding qterm seed
            barrier clause)) ≤
      seed + 1 := by
  have hparams := resolutionSeedHighWaterAtomList_renameCompact_le
    clause.params seed
  have hresult := resolutionSeedHighWaterAtom_renameCompact_le
    clause.result seed
  have hbody := resolutionSeedHighWaterGoals_renameCompact_le
    clause.body barrier seed
  have hrenameGoals :
      clause.body.map
          (renameGoalSuffix (resolutionCompactSuffix seed) barrier) =
        renameGoalsSuffix (resolutionCompactSuffix seed) barrier clause.body := by
    induction clause.body with
    | nil => rfl
    | cons goal goals ih =>
        simp only [List.map_cons, renameGoalsSuffix]
        rw [ih]
  unfold freshenResolutionClause resolutionFreshSuffix resolutionClauseVars
  dsimp only
  rw [hrenameGoals]
  change resolutionSeedHighWaterNames
      ((clause.params.map
          (renameAtomSuffix (resolutionCompactSuffix seed))).flatMap
        Atom.vars ++
        (renameAtomSuffix (resolutionCompactSuffix seed) clause.result).vars ++
        specializationGoalsVars
          (renameGoalsSuffix (resolutionCompactSuffix seed) barrier
            clause.body)) ≤ seed + 1
  simp only [resolutionSeedHighWaterNames_append]
  omega

@[simp] theorem specializationGoalsVars_append
    (left right : List Goal) :
    specializationGoalsVars (left ++ right) =
      specializationGoalsVars left ++ specializationGoalsVars right := by
  induction left with
  | nil => rfl
  | cons goal goals ih =>
      simp only [List.cons_append, specializationGoalsVars, ih,
        List.append_assoc]

private theorem flatten_map_eq_flatMap {α β : Type}
    (items : List α) (f : α → List β) :
    (items.map f).flatten = items.flatMap f := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.map_cons, List.flatten_cons, List.flatMap_cons, ih]

theorem resolutionAlt_freshClause_below
    (argsv args : List Atom) (res : Atom) (rest : List Goal)
    (binding : Subst) (qterm : Atom) (seed barrier : Nat)
    (clause : Clause)
    (hsource : resolutionSeedHighWaterNames
      (args.flatMap Atom.vars ++ res.vars ++ specializationGoalsVars rest ++
        resolutionSubstVars binding) ≤ seed) :
    let copied := freshenResolutionClause argsv args res rest binding qterm
      seed barrier clause
    resolutionSeedHighWaterNames
      (resolutionAltVars
        (Alt.br
          (Goal.eq (Atom.expr (args ++ [res]))
              (Atom.expr (copied.params ++ [copied.result])) ::
            copied.body ++ rest)
          binding)) ≤ seed + 1 := by
  dsimp only
  have hcopied := resolutionSeedHighWaterClause_freshen_le
    argsv args res rest binding qterm seed barrier clause
  unfold resolutionClauseVars at hcopied
  unfold resolutionAltVars
  simp only [specializationGoalsVars, specializationGoalVars,
    specializationGoalsVars_append, Atom.vars, List.map_append,
    List.map_singleton, List.flatten_append, List.flatten_singleton,
    flatten_map_eq_flatMap,
    resolutionSeedHighWaterNames_append] at hsource hcopied ⊢
  omega

@[simp] theorem resolutionSeedHighWaterAtoms_eq
    (atoms : List Atom) :
    resolutionSeedHighWaterAtoms atoms =
      resolutionSeedHighWaterNames (atoms.flatMap Atom.vars) := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
      simp only [resolutionSeedHighWaterAtoms, resolutionSeedHighWaterAtom,
        List.flatMap_cons, resolutionSeedHighWaterNames_append, ih]

theorem advanceCounterPastAtoms_mono (counter : Nat) (atoms : List Atom) :
    counter ≤ advanceCounterPastAtoms counter atoms := by
  unfold advanceCounterPastAtoms
  exact Nat.le_max_left _ _

theorem advanceCounterPastGoals_mono (counter : Nat) (goals : List Goal) :
    counter ≤ advanceCounterPastGoals counter goals := by
  unfold advanceCounterPastGoals
  exact Nat.le_max_left _ _

theorem resolveAlts_counter_mono (clauses : List Clause)
    (argsv args : List Atom) (res : Atom) (rest : List Goal)
    (binding : Subst) (qterm : Atom) (barrier counter : Nat) :
    counter ≤
      (resolveAlts clauses argsv args res rest binding qterm barrier counter).2 := by
  let addClause := fun (acc : List Alt × Nat) (clause : Clause) =>
    if clause.params.length != argsv.length then acc
    else if !prologMatchCompatList argsv clause.params then acc
    else if !prologMatchCompat (subst binding res) clause.result then acc
    else
      let copied := freshenResolutionClause argsv args res rest binding qterm
        acc.2 barrier clause
      (Alt.br
        (Goal.eq (Atom.expr (args ++ [res]))
              (Atom.expr (copied.params ++ [copied.result])) ::
            copied.body ++ rest)
          binding :: acc.1,
        acc.2 + 1)
  have addClause_mono (acc : List Alt × Nat) (clause : Clause) :
      acc.2 ≤ (addClause acc clause).2 := by
    dsimp [addClause]
    split <;> try exact Nat.le_refl _
    split <;> try exact Nat.le_refl _
    split <;> try exact Nat.le_refl _
    exact Nat.le_add_right _ _
  have fold_mono : ∀ (remaining : List Clause) (acc : List Alt × Nat),
      acc.2 ≤ (remaining.foldl addClause acc).2 := by
    intro remaining
    induction remaining with
    | nil => exact fun acc => Nat.le_refl _
    | cons clause tail ih =>
        intro acc
        simp only [List.foldl_cons]
        exact Nat.le_trans (addClause_mono acc clause)
          (ih (addClause acc clause))
  change counter ≤ (clauses.foldl addClause ([], counter)).2
  exact fold_mono clauses ([], counter)

/-- Every alternative minted by clause resolution is below the counter
    returned with that alternative bank. -/
theorem resolveAlts_alts_below (clauses : List Clause)
    (argsv args : List Atom) (res : Atom) (rest : List Goal)
    (binding : Subst) (qterm : Atom) (barrier counter : Nat)
    (hsource : resolutionSeedHighWaterNames
      (args.flatMap Atom.vars ++ res.vars ++ specializationGoalsVars rest ++
        resolutionSubstVars binding) ≤ counter) :
    resolutionSeedHighWaterNames
        ((resolveAlts clauses argsv args res rest binding qterm barrier
          counter).1.flatMap resolutionAltVars) ≤
      (resolveAlts clauses argsv args res rest binding qterm barrier
        counter).2 := by
  let resv := subst binding res
  let addClause := fun (acc : List Alt × Nat) (clause : Clause) =>
    if clause.params.length != argsv.length then acc
    else if !prologMatchCompatList argsv clause.params then acc
    else if !prologMatchCompat resv clause.result then acc
    else
      let copied := freshenResolutionClause argsv args res rest binding qterm
        acc.2 barrier clause
      (Alt.br
          (Goal.eq (Atom.expr (args ++ [res]))
                (Atom.expr (copied.params ++ [copied.result])) ::
              copied.body ++ rest)
            binding :: acc.1,
        acc.2 + 1)
  have preserve : ∀ (remaining : List Clause) (acc : List Alt × Nat),
      counter ≤ acc.2 →
      resolutionSeedHighWaterNames
          (acc.1.flatMap resolutionAltVars) ≤ acc.2 →
      resolutionSeedHighWaterNames
          ((remaining.foldl addClause acc).1.flatMap resolutionAltVars) ≤
        (remaining.foldl addClause acc).2 := by
    intro remaining
    induction remaining with
    | nil =>
        intro acc _ hacc
        exact hacc
    | cons clause tail ih =>
        intro acc hcounter hacc
        simp only [List.foldl_cons]
        apply ih
        · dsimp [addClause]
          split <;> try exact hcounter
          split <;> try exact hcounter
          split <;> try exact hcounter
          omega
        · dsimp [addClause]
          split <;> try exact hacc
          split <;> try exact hacc
          split <;> try exact hacc
          have hsourceAcc : resolutionSeedHighWaterNames
              (args.flatMap Atom.vars ++ res.vars ++
                specializationGoalsVars rest ++ resolutionSubstVars binding) ≤
              acc.2 :=
            Nat.le_trans hsource hcounter
          have hnew := resolutionAlt_freshClause_below argsv args res rest
            binding qterm acc.2 barrier clause hsourceAcc
          have hnew' : resolutionSeedHighWaterNames
              (resolutionAltVars
                (Alt.br
                  (Goal.eq (Atom.expr (args ++ [res]))
                        (Atom.expr
                          ((freshenResolutionClause argsv args res rest binding
                            qterm acc.2 barrier clause).params ++
                            [(freshenResolutionClause argsv args res rest binding
                              qterm acc.2 barrier clause).result])) ::
                    ((freshenResolutionClause argsv args res rest binding qterm
                      acc.2 barrier clause).body ++ rest))
                  binding)) ≤ acc.2 + 1 := by
            simpa only [List.cons_append] using hnew
          simp only [List.flatMap_cons,
            resolutionSeedHighWaterNames_append]
          omega
  unfold resolveAlts
  change resolutionSeedHighWaterNames
      ((clauses.foldl addClause ([], counter)).1.reverse.flatMap
        resolutionAltVars) ≤
    (clauses.foldl addClause ([], counter)).2
  have hfold := preserve clauses ([], counter) (Nat.le_refl _) (by
    simp [resolutionSeedHighWaterNames])
  exact Nat.le_trans
    (resolutionSeedHighWaterNames_le_of_subset (by
      intro name member
      simp only [List.mem_flatMap] at member ⊢
      obtain ⟨alt, halt, hname⟩ := member
      exact ⟨alt, List.mem_reverse.mp halt, hname⟩))
    hfold

theorem spacePatView_query_vars_subset (pat : Atom) (name : String)
    (member : name ∈ (spacePatView pat).2.vars) :
    name ∈ pat.vars := by
  cases pat with
  | sym symbol => simpa [spacePatView] using member
  | var source => simpa [spacePatView] using member
  | gnd ground => simpa [spacePatView] using member
  | expr atoms =>
      rcases atoms with _ | ⟨head, tail⟩
      · simpa [spacePatView] using member
      · cases head with
        | sym symbol =>
            by_cases hsymbol : symbol = "#space"
            · subst symbol
              rcases tail with _ | ⟨space, tail⟩
              · simpa [spacePatView] using member
              · rcases tail with _ | ⟨query, tail⟩
                · simpa [spacePatView] using member
                · rcases tail with _ | ⟨extra, tail⟩
                  · have hquery : name ∈ query.vars := by
                      simpa [spacePatView] using member
                    simpa [Atom.vars] using
                      (show name ∈ space.vars ∨ name ∈ query.vars from
                        Or.inr hquery)
                  · simpa [spacePatView] using member
            · simpa [spacePatView, hsymbol] using member
        | var source => simpa [spacePatView] using member
        | gnd ground => simpa [spacePatView] using member
        | expr children => simpa [spacePatView] using member

theorem resolutionAlt_match_below (query renamed : Atom)
    (rest : List Goal) (binding : Subst) (counter : Nat)
    (hsource : resolutionSeedHighWaterNames
      (query.vars ++ specializationGoalsVars rest ++
        resolutionSubstVars binding) ≤ counter)
    (hrenamed : resolutionSeedHighWaterNames renamed.vars ≤ counter + 1) :
    resolutionSeedHighWaterNames
      (resolutionAltVars (Alt.br (Goal.eq query renamed :: rest) binding)) ≤
        counter + 1 := by
  unfold resolutionAltVars
  simp only [specializationGoalsVars, specializationGoalVars,
    resolutionSeedHighWaterNames_append] at hsource ⊢
  omega

theorem resolutionSeedHighWaterAtom_subst_le (binding : Subst)
    (atom : Atom) (counter : Nat)
    (hatom : resolutionSeedHighWaterNames atom.vars ≤ counter)
    (hbinding : resolutionSeedHighWaterNames
      (resolutionSubstVars binding) ≤ counter) :
    resolutionSeedHighWaterNames (subst binding atom).vars ≤ counter := by
  rw [PersistentSubst.resolutionSeedHighWaterNames_le_iff]
  intro name member
  rcases subst_vars_origin binding atom name member with hatomOrigin | hrange
  · exact (PersistentSubst.resolutionSeedHighWaterNames_le_iff
      atom.vars counter).mp hatom name hatomOrigin
  · apply (PersistentSubst.resolutionSeedHighWaterNames_le_iff
      (resolutionSubstVars binding) counter).mp hbinding name
    simp only [resolutionSubstVars, List.mem_flatMap] at ⊢
    simp only [List.mem_flatMap] at hrange
    obtain ⟨entry, hentry, hname⟩ := hrange
    exact ⟨entry, hentry, by simp [hname]⟩

theorem substAtomList_vars_origin (binding : Subst) (atoms : List Atom)
    (name : String)
    (member : name ∈ (atoms.map (subst binding)).flatMap Atom.vars) :
    name ∈ atoms.flatMap Atom.vars ∨
      name ∈ resolutionSubstVars binding := by
  simp only [List.mem_flatMap, List.mem_map] at member
  obtain ⟨substituted, ⟨source, hsource, rfl⟩, hname⟩ := member
  rcases subst_vars_origin binding source name hname with horigin | hrange
  · exact Or.inl (by
      simp only [List.mem_flatMap]
      exact ⟨source, hsource, horigin⟩)
  · exact Or.inr (by
      simp only [resolutionSubstVars, List.mem_flatMap]
      simp only [List.mem_flatMap] at hrange
      obtain ⟨entry, hentry, htarget⟩ := hrange
      exact ⟨entry, hentry, by simp [htarget]⟩)

theorem resolutionSeedHighWaterAtomList_subst_le (binding : Subst)
    (atoms : List Atom) (counter : Nat)
    (hatoms : resolutionSeedHighWaterNames
      (atoms.flatMap Atom.vars) ≤ counter)
    (hbinding : resolutionSeedHighWaterNames
      (resolutionSubstVars binding) ≤ counter) :
    resolutionSeedHighWaterNames
      ((atoms.map (subst binding)).flatMap Atom.vars) ≤ counter := by
  rw [PersistentSubst.resolutionSeedHighWaterNames_le_iff]
  intro name member
  rcases substAtomList_vars_origin binding atoms name member with
    hatom | hbindingOrigin
  · exact (PersistentSubst.resolutionSeedHighWaterNames_le_iff _ counter).mp
      hatoms name hatom
  · exact (PersistentSubst.resolutionSeedHighWaterNames_le_iff _ counter).mp
      hbinding name hbindingOrigin

/-- An active local-call head already places the complete clause-copy
freshness surface below the configuration counter.

This is stronger than merely bounding the raw goal variables: substituted
arguments may acquire variables from the current binding range, while
`resolutionOccupiedVars` also retains the binding domain/range and the
observable query term.  All four sources are discharged from the sealed
configuration invariant rather than supplied as an independent freshness
assumption. -/
theorem ConfBelowResolutionCounter.resolutionOccupied_of_call
    {conf : Conf} (below : ConfBelowResolutionCounter conf)
    (function : String) (args : List Atom) (res : Atom)
    (rest : List Goal) (binding : Subst)
    (hcur :
      conf.cur = some (Goal.call function args res :: rest, binding)) :
    resolutionSeedHighWaterNames
        (resolutionOccupiedVars
          (args.map (subst binding)) res rest binding conf.qterm) ≤
      conf.counter := by
  have hactive := below.active
    (Goal.call function args res :: rest) binding hcur
  simp only [specializationGoalsVars, specializationGoalVars,
    resolutionSeedHighWaterNames_append] at hactive
  have hrawArgs :
      resolutionSeedHighWaterNames (args.flatMap Atom.vars) ≤
        conf.counter := by
    omega
  have hres :
      resolutionSeedHighWaterNames res.vars ≤ conf.counter := by
    omega
  have hrest :
      resolutionSeedHighWaterNames (specializationGoalsVars rest) ≤
        conf.counter := by
    omega
  have hbinding :
      resolutionSeedHighWaterNames (resolutionSubstVars binding) ≤
        conf.counter := by
    omega
  have hsubArgs :=
    resolutionSeedHighWaterAtomList_subst_le binding args conf.counter
      hrawArgs hbinding
  have hqterm := below.qterm
  unfold resolutionOccupiedVars
  change
    resolutionSeedHighWaterNames
        ((args.map (subst binding)).flatMap Atom.vars ++ res.vars ++
          specializationGoalsVars rest ++ resolutionSubstVars binding ++
          conf.qterm.vars) ≤
      conf.counter
  simp only [resolutionSeedHighWaterNames_append]
  omega

theorem canonBool_vars_subset (atom : Atom) (name : String)
    (member : name ∈ (canonBool atom).vars) : name ∈ atom.vars := by
  cases atom with
  | sym symbol =>
      by_cases htrue : symbol = "true" <;>
        by_cases hfalse : symbol = "false" <;>
        simp_all [canonBool, Atom.vars]
  | var source => simpa [canonBool]
  | gnd ground =>
      cases ground with
      | bool value => cases value <;> simp [canonBool, Atom.vars] at member
      | int value | float value | str value | error value | external value _ =>
          simpa [canonBool] using member
      | unit => simpa [canonBool] using member
  | expr atoms => simpa [canonBool]

theorem canonBoolList_vars_subset (atoms : List Atom) (name : String)
    (member : name ∈ (atoms.map canonBool).flatMap Atom.vars) :
    name ∈ atoms.flatMap Atom.vars := by
  simp only [List.mem_flatMap, List.mem_map] at member
  obtain ⟨canonical, ⟨source, hsource, rfl⟩, hname⟩ := member
  simp only [List.mem_flatMap]
  exact ⟨source, hsource, canonBool_vars_subset source name hname⟩

theorem chainOf_vars_subset (atoms : List Atom) (name : String)
    (member : name ∈ (chainOf atoms).vars) :
    name ∈ atoms.flatMap Atom.vars := by
  induction atoms with
  | nil => simp [chainOf, nilA, Atom.vars] at member
  | cons atom rest ih =>
      simp only [chainOf, List.foldr_cons, consC, Atom.vars,
        List.mem_flatten, List.mem_map] at member
      rcases member with ⟨vars, hvariables, hname⟩
      rcases hvariables with ⟨child, hchild, rfl⟩
      simp only [List.mem_cons] at hchild
      rcases hchild with hclosed | hatom | htail
      · subst child
        simp [Atom.vars] at hname
      · subst child
        simp only [List.flatMap_cons, List.mem_append]
        exact Or.inl hname
      · rcases htail with htail | hfalse
        · subst child
          simp only [List.flatMap_cons, List.mem_append]
          exact Or.inr (ih hname)
        · simp at hfalse

private theorem resolutionAtomSize_le_sum_of_mem {atom : Atom} :
    (atoms : List Atom) → atom ∈ atoms →
      atom.size ≤ (atoms.map Atom.size).sum
  | [], member => by simp at member
  | head :: rest, member => by
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simp
      · simp only [List.map_cons, List.sum_cons]
        exact Nat.le_trans (resolutionAtomSize_le_sum_of_mem rest member)
          (Nat.le_add_left _ _)

@[elab_as_elim, induction_eliminator]
private def resolutionAtomRecAux {motive : Atom → Prop}
    (sym : ∀ symbol, motive (Atom.sym symbol))
    (var : ∀ source, motive (Atom.var source))
    (gnd : ∀ ground, motive (Atom.gnd ground))
    (expr : ∀ atoms, (∀ atom ∈ atoms, motive atom) →
      motive (Atom.expr atoms)) :
    (atom : Atom) → motive atom
  | .sym symbol => sym symbol
  | .var source => var source
  | .gnd ground => gnd ground
  | .expr atoms => expr atoms (fun atom _member =>
      resolutionAtomRecAux sym var gnd expr atom)
termination_by atom => atom.size
decreasing_by
  simp only [Atom.size]
  simpa [Nat.add_comm] using Nat.lt_add_one_of_le
    (resolutionAtomSize_le_sum_of_mem atoms _member)

theorem chainListM_vars_subset (atom : Atom) :
    ∀ (items : List Atom), chainListM atom = some items →
      ∀ name, name ∈ items.flatMap Atom.vars → name ∈ atom.vars := by
  induction atom using resolutionAtomRecAux with
  | sym symbol =>
      intro items hitems name member
      simp [chainListM] at hitems
  | var source =>
      intro items hitems
      simp [chainListM] at hitems
  | gnd ground =>
      intro items hitems name member
      cases ground with
      | int | float | str | bool | unit | error =>
          simp [chainListM] at hitems
      | external kind payload =>
          by_cases kindEq : kind = "PLeaTTa.internal"
          · subst kind
            by_cases payloadEq : payload = "nil"
            · subst payload
              simp [chainListM] at hitems
              subst items
              simp at member
            · simp [chainListM, payloadEq] at hitems
          · simp [chainListM, kindEq] at hitems
  | expr atoms ih =>
      intro items hitems name member
      rcases atoms with _ | ⟨first, tail⟩
      · simp [chainListM] at hitems
      · cases first with
        | sym symbol =>
            by_cases hcons : symbol = "#c"
            · subst symbol
              rcases tail with _ | ⟨head, tail⟩
              · simp [chainListM] at hitems
              · rcases tail with _ | ⟨next, tail⟩
                · simp [chainListM] at hitems
                · rcases tail with _ | ⟨extra, tail⟩
                  · cases htail : chainListM next with
                    | none => simp [chainListM, htail] at hitems
                    | some restItems =>
                        simp [chainListM, htail] at hitems
                        subst items
                        simp only [List.flatMap_cons, List.mem_append]
                          at member
                        rcases member with hhead | hrest
                        · simp [Atom.vars, hhead]
                        · have hnext := ih next (by simp) restItems htail
                            name hrest
                          simp [Atom.vars, hnext]
                  · simp [chainListM] at hitems
            · simp [chainListM, hcons] at hitems
        | var source => simp [chainListM] at hitems
        | gnd ground => simp [chainListM] at hitems
        | expr children => simp [chainListM] at hitems

theorem chainListM_getD_vars_subset (atom : Atom) (fallback : List Atom)
    (name : String)
    (member : name ∈ ((chainListM atom).getD fallback).flatMap Atom.vars) :
    name ∈ atom.vars ∨ name ∈ fallback.flatMap Atom.vars := by
  cases hchain : chainListM atom with
  | none =>
      rw [hchain] at member
      change name ∈ fallback.flatMap Atom.vars at member
      exact Or.inr member
  | some items =>
      rw [hchain] at member
      change name ∈ items.flatMap Atom.vars at member
      exact Or.inl (chainListM_vars_subset atom items hchain name member)

theorem chainSplits_append_eq (items left right : List Atom)
    (member : (left, right) ∈ chainSplits items) :
    left ++ right = items := by
  induction items generalizing left right with
  | nil =>
      simp [chainSplits] at member
      rcases member with ⟨rfl, rfl⟩
      rfl
  | cons head tail ih =>
      simp only [chainSplits, List.mem_cons, List.mem_map] at member
      rcases member with hfirst | hmapped
      · cases hfirst
        rfl
      · obtain ⟨split, hsplit, hpair⟩ := hmapped
        rcases split with ⟨leftPart, rightPart⟩
        simp only [Prod.mk.injEq] at hpair
        rcases hpair with ⟨rfl, rfl⟩
        simp only [List.cons_append]
        rw [ih leftPart rightPart hsplit]

theorem unionReverseAlts_below (args : List Atom) (res : Atom)
    (rest : List Goal) (binding : Subst) (alts : List Alt)
    (counter : Nat)
    (hsource : resolutionSeedHighWaterNames
      (args.flatMap Atom.vars ++ res.vars ++ specializationGoalsVars rest ++
        resolutionSubstVars binding) ≤ counter)
    (hbranches : unionReverseAlts args res rest binding = some alts) :
    resolutionSeedHighWaterNames
      (alts.flatMap resolutionAltVars) ≤ counter := by
  cases args with
  | nil => simp [unionReverseAlts] at hbranches
  | cons left tail =>
      cases tail with
      | nil => simp [unionReverseAlts] at hbranches
      | cons right extra =>
          cases extra with
          | cons third remaining => simp [unionReverseAlts] at hbranches
          | nil =>
              cases hchain : chainListM (subst binding res) with
              | none => simp [unionReverseAlts, hchain] at hbranches
              | some items =>
                  simp only [unionReverseAlts, hchain, Option.some.injEq]
                    at hbranches
                  subst alts
                  simp only [List.flatMap_cons, List.flatMap_nil,
                    List.append_nil, resolutionSeedHighWaterNames_append]
                    at hsource
                  have hres : resolutionSeedHighWaterNames res.vars ≤
                      counter := by omega
                  have hbinding : resolutionSeedHighWaterNames
                      (resolutionSubstVars binding) ≤ counter := by omega
                  have hsubst := resolutionSeedHighWaterAtom_subst_le binding
                    res counter hres hbinding
                  have hitems : resolutionSeedHighWaterNames
                      (items.flatMap Atom.vars) ≤ counter :=
                    Nat.le_trans
                      (resolutionSeedHighWaterNames_le_of_subset (by
                        intro name member
                        exact chainListM_vars_subset (subst binding res) items
                          hchain name member))
                      hsubst
                  have hleft : resolutionSeedHighWaterNames left.vars ≤
                      counter := by omega
                  have hright : resolutionSeedHighWaterNames right.vars ≤
                      counter := by omega
                  have hrest : resolutionSeedHighWaterNames
                      (specializationGoalsVars rest) ≤ counter := by omega
                  rw [PersistentSubst.resolutionSeedHighWaterNames_le_iff]
                  intro name member
                  simp only [List.mem_flatMap, List.mem_map] at member
                  obtain ⟨alternative, ⟨split, hsplit, rfl⟩, halt⟩ := member
                  rcases split with ⟨leftPart, rightPart⟩
                  have hpartition := chainSplits_append_eq items leftPart rightPart
                    hsplit
                  simp only [resolutionAltVars, specializationGoalsVars,
                    specializationGoalVars, List.mem_append] at halt
                  rcases halt with hgoals | hbindingName
                  · rcases hgoals with hfirst | htail
                    · rcases hfirst with hleftName | hleftChain
                      · exact
                          (PersistentSubst.resolutionSeedHighWaterNames_le_iff _
                            counter).mp hleft name hleftName
                      · apply
                          (PersistentSubst.resolutionSeedHighWaterNames_le_iff _
                            counter).mp hitems name
                        have horigin := chainOf_vars_subset leftPart name
                          hleftChain
                        rw [← hpartition]
                        simp only [List.flatMap_append, List.mem_append]
                        exact Or.inl horigin
                    · rcases htail with hsecond | hrestName
                      · rcases hsecond with hrightName | hrightChain
                        · exact
                            (PersistentSubst.resolutionSeedHighWaterNames_le_iff _
                              counter).mp hright name hrightName
                        · apply
                            (PersistentSubst.resolutionSeedHighWaterNames_le_iff _
                              counter).mp hitems name
                          have horigin := chainOf_vars_subset rightPart name
                            hrightChain
                          rw [← hpartition]
                          simp only [List.flatMap_append, List.mem_append]
                          exact Or.inr horigin
                      · exact
                          (PersistentSubst.resolutionSeedHighWaterNames_le_iff _
                            counter).mp hrest name hrestName
                  · exact
                      (PersistentSubst.resolutionSeedHighWaterNames_le_iff _
                        counter).mp hbinding name hbindingName

theorem cutTo_resolutionAltVars_subset (alts : List Alt) (cut : Nat)
    (name : String)
    (member : name ∈ (cutTo cut alts).flatMap resolutionAltVars) :
    name ∈ alts.flatMap resolutionAltVars := by
  induction alts with
  | nil => simp [cutTo] at member
  | cons alt rest ih =>
      unfold cutTo at member
      split at member
      · simp only [List.flatMap_cons, List.mem_append]
        exact Or.inr (ih member)
      · exact member

theorem cutToCached_resolutionAltVars_subset (alts : List Alt) (cut depth : Nat)
    (name : String)
    (member : name ∈ (cutToCached cut depth alts).1.flatMap resolutionAltVars) :
    name ∈ alts.flatMap resolutionAltVars := by
  induction alts generalizing depth with
  | nil => simp [cutToCached] at member
  | cons alt rest ih =>
      cases alt with
      | barrier =>
          unfold cutToCached at member
          split at member
          · simp only [List.flatMap_cons, List.mem_append]
            exact Or.inr (ih (depth := depth - 1) member)
          · exact member
      | br goals binding =>
          unfold cutToCached at member
          split at member
          · simp only [List.flatMap_cons, List.mem_append]
            exact Or.inr (ih (depth := depth) member)
          · exact member

theorem cutToTracked_resolutionAltVars_subset (alts : List Alt) (cut : Nat)
    (cache : Option Nat) (name : String)
    (member : name ∈ (cutToTracked cut cache alts).1.flatMap resolutionAltVars) :
    name ∈ alts.flatMap resolutionAltVars := by
  cases cache with
  | none => exact cutTo_resolutionAltVars_subset alts cut name member
  | some depth => exact cutToCached_resolutionAltVars_subset alts cut depth name member

theorem mappedEqAlts_below (items : List Atom) (res : Atom)
    (rest : List Goal) (binding : Subst) (counter : Nat)
    (hsource : resolutionSeedHighWaterNames
      (res.vars ++ specializationGoalsVars rest ++
        resolutionSubstVars binding) ≤ counter)
    (hitems : resolutionSeedHighWaterNames
      (items.flatMap Atom.vars) ≤ counter) :
    resolutionSeedHighWaterNames
      ((items.map (fun item =>
        Alt.br (Goal.eq res item :: rest) binding)).flatMap
          resolutionAltVars) ≤ counter := by
  rw [PersistentSubst.resolutionSeedHighWaterNames_le_iff]
  intro name member
  simp only [List.mem_flatMap, List.mem_map] at member
  obtain ⟨branch, ⟨item, hitem, rfl⟩, hbranch⟩ := member
  simp only [resolutionAltVars, specializationGoalsVars,
    specializationGoalVars, List.mem_append] at hbranch
  rcases hbranch with ((hres | hvalue) | hrest) | hbinding
  · exact (PersistentSubst.resolutionSeedHighWaterNames_le_iff _ counter).mp
      hsource name (by simp [hres])
  · exact (PersistentSubst.resolutionSeedHighWaterNames_le_iff _ counter).mp
      hitems name (by
      simp only [List.mem_flatMap]
      exact ⟨item, hitem, hvalue⟩)
  · exact (PersistentSubst.resolutionSeedHighWaterNames_le_iff _ counter).mp
      hsource name (by simp [hrest])
  · exact (PersistentSubst.resolutionSeedHighWaterNames_le_iff _ counter).mp
      hsource name (by simp [hbinding])

theorem localGetTypeExtensionAlts_below (world : PWorld) (value res : Atom)
    (rest : List Goal) (binding : Subst) (counter : Nat)
    (hsource : resolutionSeedHighWaterNames
      (value.vars ++ res.vars ++ specializationGoalsVars rest ++
        resolutionSubstVars binding) ≤ counter) :
    resolutionSeedHighWaterNames
      ((localGetTypeExtensionAlts world value res rest binding).flatMap
        resolutionAltVars) ≤ counter := by
  unfold localGetTypeExtensionAlts
  split
  · simp [resolutionSeedHighWaterNames]
  · simpa [resolutionAltVars, specializationGoalsVars,
      specializationGoalVars] using hsource

theorem ConfBelowResolutionCounter.enqueueEqAlts {conf : Conf}
    (below : ConfBelowResolutionCounter conf) (oldGoals : List Goal)
    (binding : Subst) (hcur : conf.cur = some (oldGoals, binding))
    (res : Atom) (rest : List Goal) (items : List Atom)
    (world : PWorld) (counter : Nat)
    (counterMono : conf.counter ≤ counter)
    (sourceOrigin : ∀ name,
      name ∈ res.vars ++ specializationGoalsVars rest ++
          resolutionSubstVars binding →
        name ∈ specializationGoalsVars oldGoals ++
          resolutionSubstVars binding)
    (itemsBelow : resolutionSeedHighWaterNames
      (items.flatMap Atom.vars) ≤ counter) :
    ConfBelowResolutionCounter
      (Conf.mk none
        (items.map (fun item =>
          Alt.br (Goal.eq res item :: rest) binding) ++ conf.alts)
        world counter conf.qterm conf.answers conf.answerKeys
          conf.answerKeys_sound conf.barriers) := by
  have hsource : resolutionSeedHighWaterNames
      (res.vars ++ specializationGoalsVars rest ++
        resolutionSubstVars binding) ≤ counter :=
    Nat.le_trans
      (resolutionSeedHighWaterNames_le_of_subset sourceOrigin)
      (Nat.le_trans (below.active oldGoals binding hcur) counterMono)
  have hnew := mappedEqAlts_below items res rest binding counter hsource
    itemsBelow
  apply ConfBelowResolutionCounter.of_components
  · simp [resolutionCurVars, resolutionSeedHighWaterNames]
  · simp only [List.flatMap_append, resolutionSeedHighWaterNames_append]
    exact Nat.max_le.mpr
      ⟨hnew, Nat.le_trans below.alts counterMono⟩
  · exact Nat.le_trans below.qterm counterMono
  · exact Nat.le_trans below.answers counterMono

theorem ConfBelowResolutionCounter.replaceActiveEq {conf : Conf}
    (below : ConfBelowResolutionCounter conf) (oldGoals : List Goal)
    (binding : Subst) (hcur : conf.cur = some (oldGoals, binding))
    (res value : Atom) (rest : List Goal) (world : PWorld) (counter : Nat)
    (counterMono : conf.counter ≤ counter)
    (sourceOrigin : ∀ name,
      name ∈ res.vars ++ specializationGoalsVars rest ++
          resolutionSubstVars binding →
        name ∈ specializationGoalsVars oldGoals ++
          resolutionSubstVars binding)
    (valueBelow : resolutionSeedHighWaterNames value.vars ≤ counter) :
    ConfBelowResolutionCounter
      (Conf.mk (some (Goal.eq res value :: rest, binding)) conf.alts world
        counter conf.qterm conf.answers conf.answerKeys
          conf.answerKeys_sound conf.barriers) := by
  have hsource : resolutionSeedHighWaterNames
      (res.vars ++ specializationGoalsVars rest ++
        resolutionSubstVars binding) ≤ counter :=
    Nat.le_trans
      (resolutionSeedHighWaterNames_le_of_subset sourceOrigin)
      (Nat.le_trans (below.active oldGoals binding hcur) counterMono)
  apply ConfBelowResolutionCounter.of_components
  · simp only [resolutionCurVars, specializationGoalsVars,
      specializationGoalVars, resolutionSeedHighWaterNames_append]
    simp only [resolutionSeedHighWaterNames_append] at hsource
    omega
  · exact Nat.le_trans below.alts counterMono
  · exact Nat.le_trans below.qterm counterMono
  · exact Nat.le_trans below.answers counterMono

theorem specializationBranchVars_of_mem
    (branches : List (Atom × List Goal)) (template : Atom)
    (goals : List Goal) (hmem : (template, goals) ∈ branches)
    (name : String)
    (member : name ∈ template.vars ++ specializationGoalsVars goals) :
    name ∈ specializationBranchVars branches := by
  induction branches with
  | nil => simp at hmem
  | cons branch rest ih =>
      rcases branch with ⟨headTemplate, headGoals⟩
      simp only [List.mem_cons] at hmem
      simp only [specializationBranchVars, List.mem_append]
      rcases hmem with hhead | htail
      · cases hhead
        simp only [List.mem_append] at member
        exact Or.inl member
      · exact Or.inr (ih htail)

theorem ambAlts_below (branches : List (Atom × List Goal))
    (res : Atom) (rest : List Goal) (binding : Subst) (counter : Nat)
    (hsource : resolutionSeedHighWaterNames
      (specializationBranchVars branches ++ res.vars ++
        specializationGoalsVars rest ++ resolutionSubstVars binding) ≤
      counter) :
    resolutionSeedHighWaterNames
      ((branches.map (fun branch =>
        Alt.br (ambBranchGoals res branch ++ rest)
          binding)).flatMap resolutionAltVars) ≤ counter := by
  rw [PersistentSubst.resolutionSeedHighWaterNames_le_iff]
  intro name member
  simp only [List.mem_flatMap, List.mem_map] at member
  obtain ⟨alt, ⟨branch, hbranch, rfl⟩, halt⟩ := member
  rcases branch with ⟨template, goals⟩
  simp only [resolutionAltVars] at halt
  have sourceBound :=
    (PersistentSubst.resolutionSeedHighWaterNames_le_iff _ counter).mp
      hsource
  rcases List.mem_append.mp halt with hsequence | hbinding
  · rw [specializationGoalsVars_append] at hsequence
    rcases List.mem_append.mp hsequence with hprefix | hrest
    · unfold ambBranchGoals at hprefix
      split at hprefix
      · have hbranchVar := specializationBranchVars_of_mem branches template
          goals hbranch name (by simp [hprefix])
        exact sourceBound name (by simp [hbranchVar])
      · rw [specializationGoalsVars_append] at hprefix
        rcases List.mem_append.mp hprefix with hgoals | heq
        · have hbranchVar := specializationBranchVars_of_mem branches template
            goals hbranch name (by simp [hgoals])
          exact sourceBound name (by simp [hbranchVar])
        · have heq' : name ∈ res.vars ∨ name ∈ template.vars := by
            simpa [specializationGoalsVars, specializationGoalVars] using heq
          rcases heq' with hres | htemplate
          · exact sourceBound name (by simp [hres])
          · have hbranchVar := specializationBranchVars_of_mem branches
              template goals hbranch name (by simp [htemplate])
            exact sourceBound name (by simp [hbranchVar])
    · exact sourceBound name (by simp [hrest])
  · exact sourceBound name (by simp [hbinding])

/-- Every alternative minted by mutable-space matching is below the counter
    returned with that alternative bank, including for an incoherent index
    state.  Coherent worlds retain the old counter exactly by
    `smatchAlts_eq_naive`. -/
theorem smatchAlts_alts_below (world : PWorld) (counter : Nat)
    (binding : Subst) (pat : Atom) (rest : List Goal) (qterm : Atom)
    (hsource : resolutionSeedHighWaterNames
      ((spacePatView pat).2.vars ++ specializationGoalsVars rest ++
        resolutionSubstVars binding) ≤ counter) :
    resolutionSeedHighWaterNames
        ((smatchAlts world counter binding pat rest qterm).1.flatMap
          resolutionAltVars) ≤
      (smatchAlts world counter binding pat rest qterm).2 := by
  unfold smatchAlts
  rcases hview : spacePatView pat with ⟨spacePattern, queryPattern⟩
  simp only
  let query := subst binding queryPattern
  let space := subst binding spacePattern
  let candidates := world.atomCandidates space query
  let suffix := resolutionFreshSuffix [query] queryPattern rest binding qterm
    counter
  let addAtom := fun (acc : List Alt) (atom : Atom) =>
    let renamed := renameAtomSuffixShared suffix atom
    if matchCompat query renamed then
      Alt.br (Goal.eq queryPattern renamed :: rest) binding :: acc
    else acc
  have hsource' : resolutionSeedHighWaterNames
      (queryPattern.vars ++ specializationGoalsVars rest ++
        resolutionSubstVars binding) ≤ counter := by
    simpa [hview] using hsource
  have preserve : ∀ (atoms : List Atom) (acc : List Alt),
      resolutionSeedHighWaterNames
          (acc.flatMap resolutionAltVars) ≤ counter + 1 →
      resolutionSeedHighWaterNames
          ((atoms.foldl addAtom acc).flatMap resolutionAltVars) ≤
        counter + 1 := by
    intro atoms
    induction atoms with
    | nil =>
        intro acc hacc
        exact hacc
    | cons atom tail ih =>
        intro acc hacc
        simp only [List.foldl_cons]
        apply ih
        dsimp [addAtom]
        split
        · have hrenamed : resolutionSeedHighWaterNames
              (renameAtomSuffixShared suffix atom).vars ≤ counter + 1 := by
            rw [renameAtomSuffixShared_eq]
            simpa [suffix, resolutionFreshSuffix] using
              resolutionSeedHighWaterAtom_renameCompact_le atom counter
          have hnew := resolutionAlt_match_below queryPattern
            (renameAtomSuffixShared suffix atom) rest binding counter
            hsource' hrenamed
          simp only [List.flatMap_cons,
            resolutionSeedHighWaterNames_append]
          omega
        · exact hacc
  have hfold := preserve candidates [] (by
    simp [resolutionSeedHighWaterNames])
  have hreverse : resolutionSeedHighWaterNames
      ((candidates.foldl addAtom []).reverse.flatMap resolutionAltVars) ≤
      counter + 1 :=
    Nat.le_trans
      (resolutionSeedHighWaterNames_le_of_subset (by
        intro name member
        simp only [List.mem_flatMap] at member ⊢
        obtain ⟨alt, halt, hname⟩ := member
        exact ⟨alt, List.mem_reverse.mp halt, hname⟩))
      hfold
  change resolutionSeedHighWaterNames
      ((candidates.foldl addAtom []).reverse.flatMap resolutionAltVars) ≤
    counter + max (world.atomsOf space).length candidates.length
  cases hcandidates : candidates with
  | nil =>
      simp [addAtom, resolutionSeedHighWaterNames]
  | cons atom atoms =>
      have hlength : 1 ≤ candidates.length := by simp [hcandidates]
      have hconsLength : 1 ≤ (atom :: atoms).length := by simp
      have hreverse' : resolutionSeedHighWaterNames
          (((atom :: atoms).foldl addAtom []).reverse.flatMap
            resolutionAltVars) ≤ counter + 1 := by
        simpa [hcandidates] using hreverse
      omega

theorem smatchAlts_counter_mono (world : PWorld) (counter : Nat)
    (binding : Subst) (pat : Atom) (rest : List Goal) (qterm : Atom) :
    counter ≤ (smatchAlts world counter binding pat rest qterm).2 := by
  unfold smatchAlts
  rcases spacePatView pat with ⟨space, query⟩
  simp only
  exact Nat.le_add_right _ _

@[simp] theorem pull_counter {Binding : Type} (conf : Conf Binding) :
    (pull conf).counter = conf.counter := by
  unfold pull
  generalize pullAuxTracked conf.barriers conf.alts = result
  rcases result with ⟨result, cache⟩
  cases result <;> rfl

theorem Step.counter_mono {prog : Prog} {gt : GroundingTable}
    {source target : Conf} (hstep : Step prog gt source target) :
    source.counter ≤ target.counter := by
  apply Step.rec
    (motive_1 := fun source target _ => source.counter ≤ target.counter)
    (motive_2 := fun source target _ => source.counter ≤ target.counter)
    (motive_3 := fun source target _ _ => source.counter ≤ target.counter)
    (t := hstep)
  all_goals intros
  all_goals try simp_all [pull_counter, advanceCounterPastAtoms,
    advanceCounterPastGoals]
  case call_resolve c f args res rest binding branches counter' h hne ha hres =>
    have hcounter := resolveAlts_counter_mono
      (c.world.resolutionCandidates f args.length)
      (args.map (subst binding)) args res rest binding c.qterm
      (barrierDepth c + 1) c.counter
    rw [hres] at hcounter
    exact hcounter
  case smatch c pat rest binding alts counter' h hsmatch =>
    have hcounter := smatchAlts_counter_mono c.world c.counter binding pat
      rest c.qterm
    rw [hsmatch] at hcounter
    exact hcounter
  case findall =>
    exact Nat.le_trans (by omega) (copyFindallBag_counter_mono _ _)
  case retract_matched =>
    exact retractPredicateMatchedCounter_old_le _ _ _
  all_goals omega

theorem StepStar.counter_mono {prog : Prog} {gt : GroundingTable}
    {source target : Conf} (run : StepStar prog gt source target) :
    source.counter ≤ target.counter := by
  apply StepStar.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun source target _ => source.counter ≤ target.counter)
    (motive_3 := fun _ _ _ _ => True)
    (t := run)
  all_goals try { intros; trivial }
  case tail =>
    intro first middle last step tail _ tailMono
    exact Nat.le_trans step.counter_mono tailMono

theorem Raises.counter_mono {prog : Prog} {gt : GroundingTable}
    {source target : Conf} {err : Atom}
    (run : Raises prog gt source target err) :
    source.counter ≤ target.counter := by
  apply Raises.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun source target _ _ =>
      source.counter ≤ target.counter)
    (t := run)
  all_goals try { intros; trivial }
  case step =>
    intro first middle last err step raise _ raiseMono
    exact Nat.le_trans step.counter_mono raiseMono
  case table =>
    intro c d function args res rest binding tableResult err h hcan hcache
      hfresh run runMono
    change advanceCounterPastAtoms (c.counter + 1) [tableResult] ≤
      d.counter at runMono
    exact Nat.le_trans
      (Nat.le_trans (Nat.le_add_right c.counter 1)
        (advanceCounterPastAtoms_mono (c.counter + 1) [tableResult]))
      runMono

theorem ConfBelowResolutionCounter.nested {conf : Conf}
    (below : ConfBelowResolutionCounter conf) (oldGoals nestedGoals : List Goal)
    (binding : Subst) (hcur : conf.cur = some (oldGoals, binding))
    (world : PWorld) (qterm : Atom)
    (origin : ∀ name,
      name ∈ specializationGoalsVars nestedGoals ++
          resolutionSubstVars binding ++ qterm.vars →
        name ∈ specializationGoalsVars oldGoals ++
          resolutionSubstVars binding) :
    ConfBelowResolutionCounter
      (Conf.mk (some (nestedGoals, binding)) [] world conf.counter qterm []
        [] (by rfl) (resetBarrierCache conf.barriers)) := by
  have hsurface : resolutionSeedHighWaterNames
      (specializationGoalsVars nestedGoals ++ resolutionSubstVars binding ++
        qterm.vars) ≤ conf.counter :=
    Nat.le_trans (resolutionSeedHighWaterNames_le_of_subset origin)
      (below.active oldGoals binding hcur)
  apply ConfBelowResolutionCounter.of_components
  · simp only [resolutionCurVars, resolutionSeedHighWaterNames_append]
    simp only [resolutionSeedHighWaterNames_append] at hsurface
    omega
  · simp [resolutionSeedHighWaterNames]
  · have hqterm : resolutionSeedHighWaterNames qterm.vars ≤
        conf.counter := by
      simp only [resolutionSeedHighWaterNames_append] at hsurface
      omega
    simpa using hqterm
  · simp [resolutionSeedHighWaterNames]

/-- The monotone resolution-name counter bounds every variable on the live
    execution surface after every formal semantic step. -/
theorem Step.preserves_belowResolutionCounter {prog : Prog}
    {gt : GroundingTable} {source target : Conf}
    (hstep : Step prog gt source target)
    (below : ConfBelowResolutionCounter source) :
    ConfBelowResolutionCounter target := by
  revert below
  apply Step.rec
    (motive_1 := fun source target _ =>
      ConfBelowResolutionCounter source →
        ConfBelowResolutionCounter target)
    (motive_2 := fun source target _ =>
      ConfBelowResolutionCounter source →
        ConfBelowResolutionCounter target)
    (motive_3 := fun source target _ _ =>
      ConfBelowResolutionCounter source →
        ConfBelowResolutionCounter target)
    (t := hstep)
  case pull_next =>
    intro c h hne below
    exact below.pull
  case refl =>
    intro c below
    exact below
  case tail =>
    intro a b c hstep htail ihStep ihTail below
    exact ihTail (ihStep below)
  case bin =>
    intro c op args res rest binding err h herr below
    exact below
  case step =>
    intro a b d err hstep hraise ihStep ihRaise below
    exact ihRaise (ihStep below)
  case answer =>
    intro c binding hcur below
    have hactive := below.active [] binding hcur
    have hbinding : resolutionSeedHighWaterNames
        (resolutionSubstVars binding) ≤ c.counter := by
      simpa [specializationGoalsVars, resolutionSeedHighWaterNames] using
        hactive
    have hanswer := resolutionSeedHighWaterAtom_subst_le binding c.qterm
      c.counter below.qterm hbinding
    apply ConfBelowResolutionCounter.pull
    apply ConfBelowResolutionCounter.of_components
    · simp [resolutionCurVars, resolutionSeedHighWaterNames]
    · exact below.alts
    · exact below.qterm
    · simp only [List.flatMap_cons, resolutionSeedHighWaterNames_append]
      exact Nat.max_le.mpr ⟨hanswer, below.answers⟩
  case eq_fail =>
    intro c x y rest binding hcur hunify below
    exact below.clearActive.pull
  case compileAlias_fail =>
    intro c x y rest binding hcur hunify below
    exact below.clearActive.pull
  case cut_untagged =>
    intro c rest binding hcur below
    exact below.clearActive.pull
  case bin_nonstrict_fail =>
    intro c op args res rest binding hcur hnp hlocal hns hnso hresult below
    exact below.clearActive.pull
  case bin_mode_fail =>
    intro c op args res rest binding hcur hnp hlocal hns hop hng hrv hnav
      below
    exact below.clearActive.pull
  case bin_fail =>
    intro c op args res rest binding hcur hnp hlocal hns hnmode hgnd hresult
      below
    exact below.clearActive.pull
  case bin_flounder =>
    intro c op args res rest binding hcur hnp hlocal hns hnmode hgnd hrest
      below
    exact below.clearActive.pull
  case wact_fail =>
    intro c op args res rest binding hcur _notRetract hdispatch below
    exact below.clearActive.pull
  case retract_missing =>
    intro c payload res rest binding counter' hcur _scan below
    let counter := max c.counter counter'
    have hcounter : c.counter ≤ counter := Nat.le_max_left _ _
    have hnext := below.replaceActiveEq
      (Goal.wact "retractPredicate" [payload] res :: rest) binding hcur
      res (Atom.sym "False") rest c.world counter hcounter (by
        intro name member
        simp only [specializationGoalsVars, specializationGoalVars,
          List.mem_append] at member ⊢
        rcases member with (hres | hrest) | hbinding
        · simp [hres]
        · simp [hrest]
        · simp [hbinding]) (by
          simp [Atom.vars, resolutionSeedHighWaterNames])
    simpa [counter] using hnext
  case retract_malformed =>
    intro c payload res rest binding hcur _scan below
    exact below.clearActive.pull
  case retract_matched =>
    intro c payload res rest binding result functor before selected after
      counter' hcur _scan below
    let counter := retractPredicateMatchedCounter c.counter counter' result
    have hcounter : c.counter ≤ counter := by
      exact retractPredicateMatchedCounter_old_le c.counter counter' result
    have hresult : resolutionSeedHighWaterNames
        (resolutionSubstVars result) ≤ counter := by
      exact retractPredicateMatchedCounter_binding_le c.counter counter'
        result
    have hactive := below.active
      (Goal.wact "retractPredicate" [payload] res :: rest) binding hcur
    have hempty : resolutionSeedHighWaterNames ([] : List String) = 0 := rfl
    apply ConfBelowResolutionCounter.of_components
    · simp only [resolutionCurVars, specializationGoalsVars,
        specializationGoalVars, resolutionSeedHighWaterNames_append,
        trueA, Atom.vars, hempty] at hactive ⊢
      omega
    · exact Nat.le_trans below.alts hcounter
    · exact Nat.le_trans below.qterm hcounter
    · exact Nat.le_trans below.answers hcounter
  case eq_ok =>
    intro c left right rest binding result hcur hunify below
    apply below.replaceActive (Goal.eq left right :: rest) binding hcur rest
      (trimFor rest c.qterm result)
    intro name member
    simp only [specializationGoalsVars, specializationGoalVars,
      List.mem_append] at member ⊢
    rcases member with hrest | htrim
    · exact Or.inl (Or.inr hrest)
    · have hresult := trimFor_substVars_origin rest c.qterm result name htrim
      rcases unifyB_substVars_origin binding left right result hunify name
          hresult with hbinding | hleft | hright
      · exact Or.inr hbinding
      · exact Or.inl (Or.inl (Or.inl hleft))
      · exact Or.inl (Or.inl (Or.inr hright))
  case compileAlias_ok =>
    intro c left right rest binding result hcur hunify below
    apply below.replaceActive
      (Goal.compileAlias left right :: rest) binding hcur rest
      (trimFor rest c.qterm result)
    intro name member
    simp only [specializationGoalsVars, specializationGoalVars,
      List.mem_append] at member ⊢
    rcases member with hrest | htrim
    · exact Or.inl (Or.inr hrest)
    · have hresult := trimFor_substVars_origin rest c.qterm result name htrim
      rcases unifyB_substVars_origin binding left right result hunify name
          hresult with hbinding | hleft | hright
      · exact Or.inr hbinding
      · exact Or.inl (Or.inl (Or.inl hleft))
      · exact Or.inl (Or.inl (Or.inr hright))
  case cut_at =>
    intro c cut rest binding hcur below
    have hactive := below.active (Goal.cutAt cut :: rest) binding hcur
    apply ConfBelowResolutionCounter.of_components
    · simpa [resolutionCurVars, specializationGoalsVars,
        specializationGoalVars, resolutionSeedHighWaterNames] using hactive
    · exact Nat.le_trans
        (resolutionSeedHighWaterNames_le_of_subset (by
          intro name member
          exact cutToTracked_resolutionAltVars_subset c.alts cut c.barriers
            name member))
        below.alts
    · exact below.qterm
    · exact below.answers
  case call_data =>
    intro c function args res rest binding hcur hnone goal hgoal below
    subst goal
    apply below.replaceActive (Goal.call function args res :: rest) binding
      hcur (Goal.eq res (chainOf (Atom.sym function :: args)) :: rest)
      binding
    intro name member
    simp only [specializationGoalsVars, specializationGoalVars,
      List.mem_append] at member ⊢
    rcases member with ((hres | hchain) | hrest) | hbinding
    · exact Or.inl (Or.inl (Or.inr hres))
    · have horigin := chainOf_vars_subset (Atom.sym function :: args) name
          hchain
      simp only [List.flatMap_cons, Atom.vars, List.nil_append] at horigin
      exact Or.inl (Or.inl (Or.inl horigin))
    · exact Or.inl (Or.inr hrest)
    · exact Or.inr hbinding
  case call_partial =>
    intro c function args res rest binding hcur hdefined harity goal hgoal
      below
    subst goal
    apply below.replaceActive (Goal.call function args res :: rest) binding
      hcur
      (Goal.eq res
        (partialC function (chainOf args)) :: rest)
      binding
    intro name member
    simp only [specializationGoalsVars, specializationGoalVars,
      List.mem_append] at member ⊢
    rcases member with ((hres | hchain) | hrest) | hbinding
    · exact Or.inl (Or.inl (Or.inr hres))
    · have hinner : name ∈ (chainOf args).vars := by
        simpa [partialC, partialTagA, Atom.vars] using hchain
      have hargs := chainOf_vars_subset args name hinner
      exact Or.inl (Or.inl (Or.inl hargs))
    · exact Or.inl (Or.inr hrest)
    · exact Or.inr hbinding
  case call_table_cached =>
    intro c function args res rest binding answers hcur hcan hcache below
    let counter := advanceCounterPastAtoms c.counter answers
    have hcounter : c.counter ≤ counter :=
      advanceCounterPastAtoms_mono c.counter answers
    have hitems : resolutionSeedHighWaterNames
        (answers.flatMap Atom.vars) ≤ counter := by
      unfold counter advanceCounterPastAtoms
      rw [resolutionSeedHighWaterAtoms_eq]
      exact Nat.le_max_right _ _
    have hqueued := below.enqueueEqAlts
      (Goal.call function args res :: rest) binding hcur res rest answers
      c.world counter hcounter (by
        intro name member
        simp only [specializationGoalsVars, specializationGoalVars,
          List.mem_append] at member ⊢
        rcases member with (hres | hrest) | hbinding
        · exact Or.inl (Or.inl (Or.inr hres))
        · exact Or.inl (Or.inr hrest)
        · exact Or.inr hbinding) hitems
    simpa [counter, List.map_map, Function.comp_def] using hqueued.pull
  case call_resolve =>
    intro c function args res rest binding branches counter hcur hdefined
      harity hresolve below
    have hactive := below.active (Goal.call function args res :: rest)
      binding hcur
    have hsource : resolutionSeedHighWaterNames
        (args.flatMap Atom.vars ++ res.vars ++
          specializationGoalsVars rest ++ resolutionSubstVars binding) ≤
        c.counter := by
      simpa [specializationGoalsVars, specializationGoalVars] using hactive
    have hbranches := resolveAlts_alts_below
      (c.world.resolutionCandidates function args.length)
      (args.map (subst binding)) args res rest binding c.qterm
      (barrierDepth c + 1) c.counter hsource
    rw [hresolve] at hbranches
    have hcounter := resolveAlts_counter_mono
      (c.world.resolutionCandidates function args.length)
      (args.map (subst binding)) args res rest binding c.qterm
      (barrierDepth c + 1) c.counter
    rw [hresolve] at hcounter
    apply ConfBelowResolutionCounter.pull
    apply ConfBelowResolutionCounter.of_components
    · simp [resolutionCurVars, resolutionSeedHighWaterNames]
    · simp only [List.flatMap_append, List.flatMap_cons, resolutionAltVars,
        List.nil_append, resolutionSeedHighWaterNames_append]
      exact Nat.max_le.mpr
        ⟨hbranches, Nat.le_trans below.alts hcounter⟩
    · exact Nat.le_trans below.qterm hcounter
    · exact Nat.le_trans below.answers hcounter
  case bin_partial =>
    intro c operation args res rest binding hpartial hcur goal hgoal below
    subst goal
    apply below.replaceActive (Goal.bin operation args res :: rest) binding
      hcur
      (Goal.eq res
        (partialC operation
          (chainOf (args.map (subst binding)))) :: rest)
      binding
    intro name member
    simp only [specializationGoalsVars, specializationGoalVars,
      List.mem_append] at member ⊢
    rcases member with ((hres | hchain) | hrest) | hbinding
    · exact Or.inl (Or.inl (Or.inr hres))
    · have hinner : name ∈ (chainOf (args.map (subst binding))).vars := by
        simpa [partialC, partialTagA, Atom.vars] using hchain
      have hsubstituted := chainOf_vars_subset
        (args.map (subst binding)) name hinner
      rcases substAtomList_vars_origin binding args name hsubstituted with
        hargs | hbindingOrigin
      · exact Or.inl (Or.inl (Or.inl hargs))
      · exact Or.inr hbindingOrigin
    · exact Or.inl (Or.inr hrest)
    · exact Or.inr hbinding
  case bin_local_translate =>
    intro c operation args res rest binding goals hcur hpartial hlocal below
    let counter := advanceCounterPastGoals c.counter goals
    have hcounter : c.counter ≤ counter := by
      exact advanceCounterPastGoals_mono c.counter goals
    have hactive := below.active
      (Goal.bin operation args res :: rest) binding hcur
    have hbinding : resolutionSeedHighWaterNames
        (resolutionSubstVars binding) ≤ counter := by
      simp only [specializationGoalsVars, specializationGoalVars,
        resolutionSeedHighWaterNames_append] at hactive
      omega
    apply ConfBelowResolutionCounter.of_components
    · simp only [resolutionCurVars, resolutionSeedHighWaterNames_append]
      exact Nat.max_le.mpr ⟨by
        unfold advanceCounterPastGoals
        exact Nat.le_max_right _ _, hbinding⟩
    · exact Nat.le_trans below.alts hcounter
    · exact Nat.le_trans below.qterm hcounter
    · exact Nat.le_trans below.answers hcounter
  case bin_gettype =>
    intro c args res rest binding types oracleCounter hcur hpartial hlocal
      horacle below
    let counter := advanceCounterPastAtoms (max c.counter oracleCounter) types
    have hcounter : c.counter ≤ counter := by
      unfold counter advanceCounterPastAtoms
      exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    have hitems : resolutionSeedHighWaterNames
        (types.flatMap Atom.vars) ≤ counter := by
      unfold counter advanceCounterPastAtoms
      rw [resolutionSeedHighWaterAtoms_eq]
      exact Nat.le_max_right _ _
    have hactive := below.active
      (Goal.bin "get-type" args res :: rest) binding hcur
    have hsource : resolutionSeedHighWaterNames
        (res.vars ++ specializationGoalsVars rest ++
          resolutionSubstVars binding) ≤ counter :=
      Nat.le_trans
        (resolutionSeedHighWaterNames_le_of_subset (by
          intro name member
          simp only [specializationGoalsVars, specializationGoalVars,
            List.mem_append] at member ⊢
          rcases member with (hres | hrest) | hbinding
          · exact Or.inl (Or.inl (Or.inr hres))
          · exact Or.inl (Or.inr hrest)
          · exact Or.inr hbinding))
        (Nat.le_trans hactive hcounter)
    have hrawArgs : resolutionSeedHighWaterNames
        (args.flatMap Atom.vars) ≤ c.counter := by
      simp only [specializationGoalsVars, specializationGoalVars,
        resolutionSeedHighWaterNames_append] at hactive
      omega
    have hrawBinding : resolutionSeedHighWaterNames
        (resolutionSubstVars binding) ≤ c.counter := by
      simp only [specializationGoalsVars, specializationGoalVars,
        resolutionSeedHighWaterNames_append] at hactive
      omega
    have hsubArgs := resolutionSeedHighWaterAtomList_subst_le binding args
      c.counter hrawArgs hrawBinding
    have hvalue : resolutionSeedHighWaterNames
        ((args.map (subst binding)).headD (Atom.sym "?")).vars ≤ counter := by
      apply Nat.le_trans ?_ (Nat.le_trans hsubArgs hcounter)
      apply resolutionSeedHighWaterNames_le_of_subset
      intro name member
      cases args <;> simp_all [Atom.vars]
    have hext := localGetTypeExtensionAlts_below c.world
      ((args.map (subst binding)).headD (Atom.sym "?")) res rest binding
      counter (by
        simp only [resolutionSeedHighWaterNames_append] at hsource ⊢
        omega)
    have hmapped := mappedEqAlts_below types res rest binding counter hsource
      hitems
    apply ConfBelowResolutionCounter.pull
    apply ConfBelowResolutionCounter.of_components
    · simp [resolutionCurVars, resolutionSeedHighWaterNames]
    · simp only [List.flatMap_append,
        resolutionSeedHighWaterNames_append]
      have hold := Nat.le_trans below.alts hcounter
      omega
    · exact Nat.le_trans below.qterm hcounter
    · exact Nat.le_trans below.answers hcounter
  case bin_getmetatype =>
    intro c args res rest binding metatype hcur hpartial hlocal hmetatype goal
      hgoal below
    subst goal
    apply below.replaceActive (Goal.bin "get-metatype" args res :: rest)
      binding hcur (Goal.eq res (Atom.sym metatype) :: rest) binding
    intro name member
    simp only [specializationGoalsVars, specializationGoalVars, Atom.vars,
      List.not_mem_nil, or_false, List.mem_append] at member ⊢
    rcases member with (hres | hrest) | hbinding
    · exact Or.inl (Or.inl (Or.inr hres))
    · exact Or.inl (Or.inr hrest)
    · exact Or.inr hbinding
  case bin_nonstrict_ok =>
    intro c operation args res rest binding results hcur hpartial hlocal
      hspecial hnonstrict hresult below
    let counter := advanceCounterPastAtoms c.counter results
    have hcounter : c.counter ≤ counter :=
      advanceCounterPastAtoms_mono c.counter results
    have hraw : resolutionSeedHighWaterNames
        (results.flatMap Atom.vars) ≤ counter := by
      unfold counter advanceCounterPastAtoms
      rw [resolutionSeedHighWaterAtoms_eq]
      exact Nat.le_max_right _ _
    have hitems : resolutionSeedHighWaterNames
        ((results.map canonBool).flatMap Atom.vars) ≤ counter :=
      Nat.le_trans
        (resolutionSeedHighWaterNames_le_of_subset (by
          intro name member
          exact canonBoolList_vars_subset results name member))
        hraw
    have hqueued := below.enqueueEqAlts
      (Goal.bin operation args res :: rest) binding hcur res rest
      (results.map canonBool) c.world counter hcounter (by
        intro name member
        simp only [specializationGoalsVars, specializationGoalVars,
          List.mem_append] at member ⊢
        rcases member with (hres | hrest) | hbinding
        · exact Or.inl (Or.inl (Or.inr hres))
        · exact Or.inl (Or.inr hrest)
        · exact Or.inr hbinding) hitems
    simpa [counter, List.map_map, Function.comp_def] using hqueued.pull
  case bin_ok =>
    intro c operation args res rest binding results hcur hground hpartial
      hlocal hspecial hmode hresult below
    let counter := advanceCounterPastAtoms c.counter results
    have hcounter : c.counter ≤ counter :=
      advanceCounterPastAtoms_mono c.counter results
    have hraw : resolutionSeedHighWaterNames
        (results.flatMap Atom.vars) ≤ counter := by
      unfold counter advanceCounterPastAtoms
      rw [resolutionSeedHighWaterAtoms_eq]
      exact Nat.le_max_right _ _
    have hitems : resolutionSeedHighWaterNames
        ((results.map canonBool).flatMap Atom.vars) ≤ counter :=
      Nat.le_trans
        (resolutionSeedHighWaterNames_le_of_subset (by
          intro name member
          exact canonBoolList_vars_subset results name member))
        hraw
    have hqueued := below.enqueueEqAlts
      (Goal.bin operation args res :: rest) binding hcur res rest
      (results.map canonBool) c.world counter hcounter (by
        intro name member
        simp only [specializationGoalsVars, specializationGoalVars,
          List.mem_append] at member ⊢
        rcases member with (hres | hrest) | hbinding
        · exact Or.inl (Or.inl (Or.inr hres))
        · exact Or.inl (Or.inr hrest)
        · exact Or.inr hbinding) hitems
    simpa [counter, List.map_map, Function.comp_def] using hqueued.pull
  case bin_mode =>
    intro c operation args res rest binding left right hcur hpartial hlocal
      hspecial hop hargs hnotGround hresGround goal hgoal below
    have hactive := below.active (Goal.bin operation args res :: rest)
      binding hcur
    simp only [specializationGoalsVars, specializationGoalVars,
      resolutionSeedHighWaterNames_append] at hactive
    have hrawArgs : resolutionSeedHighWaterNames
        (args.flatMap Atom.vars) ≤ c.counter := by omega
    have hrawRes : resolutionSeedHighWaterNames res.vars ≤ c.counter := by
      omega
    have hrest : resolutionSeedHighWaterNames
        (specializationGoalsVars rest) ≤ c.counter := by omega
    have hbinding : resolutionSeedHighWaterNames
        (resolutionSubstVars binding) ≤ c.counter := by omega
    have hsubArgs := resolutionSeedHighWaterAtomList_subst_le binding args
      c.counter hrawArgs hbinding
    rw [hargs] at hsubArgs
    simp only [List.flatMap_cons, List.flatMap_nil,
      List.append_nil, resolutionSeedHighWaterNames_append] at hsubArgs
    have hsubRes := resolutionSeedHighWaterAtom_subst_le binding res
      c.counter hrawRes hbinding
    have hleft : resolutionSeedHighWaterNames left.vars ≤ c.counter := by
      omega
    have hright : resolutionSeedHighWaterNames right.vars ≤ c.counter := by
      omega
    have binBound (op : String) (first second result : Atom)
        (hfirst : resolutionSeedHighWaterNames first.vars ≤ c.counter)
        (hsecond : resolutionSeedHighWaterNames second.vars ≤ c.counter)
        (hresult : resolutionSeedHighWaterNames result.vars ≤ c.counter) :
        resolutionSeedHighWaterNames
          (specializationGoalVars (Goal.bin op [first, second] result)) ≤
            c.counter := by
      simp only [specializationGoalVars, List.flatMap_cons,
        List.flatMap_nil, List.append_nil,
        resolutionSeedHighWaterNames_append]
      omega
    have finish (next : Goal)
        (hnext : resolutionSeedHighWaterNames
          (specializationGoalVars next) ≤ c.counter) :
        ConfBelowResolutionCounter
          { c with cur := some (next :: rest, binding) } := by
      apply ConfBelowResolutionCounter.of_components
      · simp only [resolutionCurVars, specializationGoalsVars,
          resolutionSeedHighWaterNames_append]
        omega
      · exact below.alts
      · exact below.qterm
      · exact below.answers
    split at hgoal <;> split at hgoal
    all_goals subst goal
    all_goals apply finish
    all_goals apply binBound <;> assumption
  case bin_delay =>
    intro c operation args res rest binding hcur hpartial hlocal hspecial
      hmode hground hnonempty below
    have hactive := below.active (Goal.bin operation args res :: rest)
      binding hcur
    apply ConfBelowResolutionCounter.of_components
    · simp only [resolutionCurVars, specializationGoalsVars_append,
        specializationGoalsVars, specializationGoalVars,
        resolutionSeedHighWaterNames_append,
        resolutionSeedHighWaterNames] at hactive ⊢
      omega
    · exact below.alts
    · exact below.qterm
    · exact below.answers
  case ite_true =>
    intro c condition thenBranch elseBranch res rest binding hcur hcondition
      below
    apply below.replaceActive
      (Goal.ite condition thenBranch elseBranch res :: rest) binding hcur
      (iteBranchGoals res thenBranch ++ rest) binding
    intro name member
    simp only [specializationGoalsVars_append, List.mem_append] at member
    rcases member with (hbranch | hrest) | hbinding
    · have hchosen := specializationGoalsVars_iteBranchGoals_subset
        res thenBranch name hbranch
      simp only [specializationGoalsVars, specializationGoalVars,
        List.mem_append] at hchosen ⊢
      rcases hchosen with (hhead | hgoals) | hres
      · simp [hhead]
      · simp [hgoals]
      · simp [hres]
    · simp only [specializationGoalsVars, specializationGoalVars,
        List.mem_append]
      simp [hrest]
    · simp only [specializationGoalsVars, specializationGoalVars,
        List.mem_append]
      simp [hbinding]
  case ite_else =>
    intro c condition thenBranch elseBranch res rest binding hcur hcondition
      below
    apply below.replaceActive
      (Goal.ite condition thenBranch elseBranch res :: rest) binding hcur
      (iteBranchGoals res elseBranch ++ rest) binding
    intro name member
    simp only [specializationGoalsVars_append, List.mem_append] at member
    rcases member with (hbranch | hrest) | hbinding
    · have hchosen := specializationGoalsVars_iteBranchGoals_subset
        res elseBranch name hbranch
      simp only [specializationGoalsVars, specializationGoalVars,
        List.mem_append] at hchosen ⊢
      rcases hchosen with (hhead | hgoals) | hres
      · simp [hhead]
      · simp [hgoals]
      · simp [hres]
    · simp only [specializationGoalsVars, specializationGoalVars,
        List.mem_append]
      simp [hrest]
    · simp only [specializationGoalsVars, specializationGoalVars,
        List.mem_append]
      simp [hbinding]
  case smatch =>
    intro c pattern rest binding branches counter hcur hmatch below
    have hactive := below.active (Goal.smatch pattern :: rest) binding hcur
    have hsource : resolutionSeedHighWaterNames
        ((spacePatView pattern).2.vars ++ specializationGoalsVars rest ++
          resolutionSubstVars binding) ≤ c.counter := by
      exact Nat.le_trans
        (resolutionSeedHighWaterNames_le_of_subset
          (left := (spacePatView pattern).2.vars ++
            specializationGoalsVars rest ++ resolutionSubstVars binding)
          (right := pattern.vars ++ specializationGoalsVars rest ++
            resolutionSubstVars binding) (by
          intro name member
          simp only [List.mem_append] at member ⊢
          rcases member with (hquery | hrest) | hbinding
          · exact Or.inl (Or.inl
              (spacePatView_query_vars_subset pattern name hquery))
          · exact Or.inl (Or.inr hrest)
          · exact Or.inr hbinding))
        (by
          simpa [specializationGoalsVars, specializationGoalVars] using
            hactive)
    have hbranches := smatchAlts_alts_below c.world c.counter binding
      pattern rest c.qterm hsource
    rw [hmatch] at hbranches
    have hcounter := smatchAlts_counter_mono c.world c.counter binding
      pattern rest c.qterm
    rw [hmatch] at hcounter
    apply ConfBelowResolutionCounter.pull
    apply ConfBelowResolutionCounter.of_components
    · simp [resolutionCurVars, resolutionSeedHighWaterNames]
    · simp only [List.flatMap_append, resolutionSeedHighWaterNames_append]
      exact Nat.max_le.mpr
        ⟨hbranches, Nat.le_trans below.alts hcounter⟩
    · exact Nat.le_trans below.qterm hcounter
    · exact Nat.le_trans below.answers hcounter
  case amb =>
    intro c branches res rest binding hcur below
    have hactive := below.active (Goal.amb branches res :: rest) binding hcur
    have hsource : resolutionSeedHighWaterNames
        (specializationBranchVars branches ++ res.vars ++
          specializationGoalsVars rest ++ resolutionSubstVars binding) ≤
        c.counter := by
      simpa [specializationGoalsVars, specializationGoalVars] using hactive
    have hbranches := ambAlts_below branches res rest binding c.counter
      hsource
    apply ConfBelowResolutionCounter.pull
    apply ConfBelowResolutionCounter.of_components
    · simp [resolutionCurVars, resolutionSeedHighWaterNames]
    · simp only [List.flatMap_append, resolutionSeedHighWaterNames_append]
      exact Nat.max_le.mpr ⟨hbranches, below.alts⟩
    · exact below.qterm
    · exact below.answers
  case spread =>
    intro c value res rest binding elements hcur helements below
    have hactive := below.active (Goal.spread value res :: rest) binding hcur
    simp only [specializationGoalsVars, specializationGoalVars,
      resolutionSeedHighWaterNames_append] at hactive
    have hvalue : resolutionSeedHighWaterNames value.vars ≤ c.counter := by
      omega
    have hbinding : resolutionSeedHighWaterNames
        (resolutionSubstVars binding) ≤ c.counter := by omega
    have hsubValue := resolutionSeedHighWaterAtom_subst_le binding value
      c.counter hvalue hbinding
    have helementsBelow : resolutionSeedHighWaterNames
        (elements.flatMap Atom.vars) ≤ c.counter := by
      rw [PersistentSubst.resolutionSeedHighWaterNames_le_iff]
      intro name member
      rw [helements] at member
      rcases chainListM_getD_vars_subset (subst binding value)
          [subst binding value] name member with horigin | hfallback
      · exact (PersistentSubst.resolutionSeedHighWaterNames_le_iff _
          c.counter).mp hsubValue name horigin
      · simp only [List.flatMap_singleton] at hfallback
        exact (PersistentSubst.resolutionSeedHighWaterNames_le_iff _
          c.counter).mp hsubValue name hfallback
    have hqueued := below.enqueueEqAlts
      (Goal.spread value res :: rest) binding hcur res rest elements c.world
      c.counter (Nat.le_refl _) (by
        intro name member
        simp only [specializationGoalsVars, specializationGoalVars,
          List.mem_append] at member ⊢
        rcases member with (hres | hrest) | hbindingOrigin
        · exact Or.inl (Or.inl (Or.inr hres))
        · exact Or.inl (Or.inr hrest)
        · exact Or.inr hbindingOrigin) helementsBelow
    exact hqueued.pull
  case callDyn_call =>
    intro c head function args res rest binding hcur hhead hdefined below
    have hactive := below.active
      (Goal.callDyn head args res :: rest) binding hcur
    apply ConfBelowResolutionCounter.of_components
    · simp only [resolutionCurVars, specializationGoalsVars,
        specializationGoalVars, resolutionSeedHighWaterNames_append]
        at hactive ⊢
      omega
    · exact below.alts
    · exact below.qterm
    · exact below.answers
  case callDyn_bin =>
    intro c head function args res rest binding hcur hhead hnone hgrounded
      below
    have hactive := below.active
      (Goal.callDyn head args res :: rest) binding hcur
    apply ConfBelowResolutionCounter.of_components
    · simp only [resolutionCurVars, specializationGoalsVars,
        specializationGoalVars, resolutionSeedHighWaterNames_append]
        at hactive ⊢
      omega
    · exact below.alts
    · exact below.qterm
    · exact below.answers
  case callDyn_symdata =>
    intro c head function args res rest binding hcur hhead hnone hnotBuiltin
      goal hgoal below
    subst goal
    apply below.replaceActive (Goal.callDyn head args res :: rest) binding
      hcur (Goal.eq res (chainOf (Atom.sym function :: args)) :: rest)
      binding
    intro name member
    simp only [specializationGoalsVars, specializationGoalVars,
      List.mem_append] at ⊢
    have member' :
        name ∈ res.vars ∨
          name ∈ (chainOf (Atom.sym function :: args)).vars ∨
          name ∈ specializationGoalsVars rest ∨
          name ∈ resolutionSubstVars binding := by
      simpa [specializationGoalsVars, specializationGoalVars] using member
    rcases member' with hres | hchain | hrest | hbinding
    · simp [hres]
    · have horigin := chainOf_vars_subset (Atom.sym function :: args) name
          hchain
      simp only [List.flatMap_cons, Atom.vars, List.nil_append] at horigin
      simp [horigin]
    · simp [hrest]
    · simp [hbinding]
  case callDyn_data =>
    intro c head args res rest binding hcur hnotSymbol hnotPartial goal hgoal
      below
    subst goal
    apply below.replaceActive (Goal.callDyn head args res :: rest) binding
      hcur (Goal.eq res (chainOf (subst binding head :: args)) :: rest)
      binding
    intro name member
    simp only [specializationGoalsVars, specializationGoalVars,
      List.mem_append] at ⊢
    have member' :
        name ∈ res.vars ∨
          name ∈ (chainOf (subst binding head :: args)).vars ∨
          name ∈ specializationGoalsVars rest ∨
          name ∈ resolutionSubstVars binding := by
      simpa [specializationGoalsVars, specializationGoalVars] using member
    rcases member' with hres | hchain | hrest | hbinding
    · simp [hres]
    · have horigin := chainOf_vars_subset (subst binding head :: args) name
          hchain
      simp only [List.flatMap_cons, List.mem_append] at horigin
      rcases horigin with hsubHead | hargs
      · rcases subst_vars_origin binding head name hsubHead with
          hheadOrigin | hrange
        · simp [hheadOrigin]
        · exact Or.inr (by
            simp only [resolutionSubstVars, List.mem_flatMap]
            simp only [List.mem_flatMap] at hrange
            obtain ⟨entry, hentry, htarget⟩ := hrange
            exact ⟨entry, hentry, by simp [htarget]⟩)
      · simp [hargs]
    · simp [hrest]
    · simp [hbinding]
  case callDyn_partial =>
    intro c head args res rest binding base boundList bound hcur hnotSymbol
      hpartial hbound goal hgoal below
    have hactive := below.active (Goal.callDyn head args res :: rest)
      binding hcur
    simp only [specializationGoalsVars, specializationGoalVars,
      resolutionSeedHighWaterNames_append] at hactive
    have hhead : resolutionSeedHighWaterNames head.vars ≤ c.counter := by
      omega
    have hargs : resolutionSeedHighWaterNames
        (args.flatMap Atom.vars) ≤ c.counter := by omega
    have hres : resolutionSeedHighWaterNames res.vars ≤ c.counter := by omega
    have hrest : resolutionSeedHighWaterNames
        (specializationGoalsVars rest) ≤ c.counter := by omega
    have hbinding : resolutionSeedHighWaterNames
        (resolutionSubstVars binding) ≤ c.counter := by omega
    have hboundBelow : resolutionSeedHighWaterNames
        (bound.flatMap Atom.vars) ≤ c.counter := by
      rw [PersistentSubst.resolutionSeedHighWaterNames_le_iff]
      intro name member
      rw [hbound] at member
      rcases chainListM_getD_vars_subset boundList [] name member with
        hboundList | himpossible
      · have hpartialShape := partialView?_sound hpartial
        have hsubHead : name ∈ (subst binding head).vars := by
          rw [hpartialShape]
          simpa [partialC, partialTagA, Atom.vars] using hboundList
        rcases subst_vars_origin binding head name hsubHead with
          hheadOrigin | hrange
        · exact (PersistentSubst.resolutionSeedHighWaterNames_le_iff _
            c.counter).mp hhead name hheadOrigin
        · apply (PersistentSubst.resolutionSeedHighWaterNames_le_iff _
            c.counter).mp hbinding name
          simp only [resolutionSubstVars, List.mem_flatMap]
          simp only [List.mem_flatMap] at hrange
          obtain ⟨entry, hentry, htarget⟩ := hrange
          exact ⟨entry, hentry, by simp [htarget]⟩
      · simp at himpossible
    subst goal
    apply ConfBelowResolutionCounter.of_components
    · simp only [resolutionCurVars, specializationGoalsVars,
        specializationGoalVars, Atom.vars, List.flatMap_append,
        resolutionSeedHighWaterNames_append,
        resolutionSeedHighWaterNames] at ⊢
      omega
    · exact below.alts
    · exact below.qterm
    · exact below.answers
  case evalg_ok =>
    intro c value res rest binding translated compiled compilerCounter
      profileWorld profileGoals newGoals hcur hcompile hspecialize hnewGoals
      below
    subst newGoals
    let scannedGoals := profileGoals ++ [Goal.eq res translated] ++ rest
    let counter := advanceCounterPastGoals (max c.counter compilerCounter)
      scannedGoals
    have hcounter : c.counter ≤ counter := by
      unfold counter
      exact Nat.le_trans (Nat.le_max_left _ _)
        (advanceCounterPastGoals_mono _ _)
    have hscan : resolutionSeedHighWaterNames
        (specializationGoalsVars scannedGoals) ≤ counter := by
      unfold counter advanceCounterPastGoals
      exact Nat.le_max_right _ _
    have hactive := below.active (Goal.evalg value res :: rest) binding hcur
    have hbinding : resolutionSeedHighWaterNames
        (resolutionSubstVars binding) ≤ counter := by
      apply Nat.le_trans _ hcounter
      simp only [specializationGoalsVars, specializationGoalVars,
        resolutionSeedHighWaterNames_append] at hactive
      omega
    apply ConfBelowResolutionCounter.of_components
    · unfold resolutionCurVars
      simp only [resolutionSeedHighWaterNames_append]
      apply Nat.max_le.mpr
      constructor
      · have hvars : specializationGoalsVars
            (tagCutsGoals (barrierDepth c + 1) profileGoals ++
              [Goal.eq res translated] ++ rest) =
            specializationGoalsVars scannedGoals := by
          simp [scannedGoals, specializationGoalsVars_append]
        rw [hvars]
        exact hscan
      · exact hbinding
    · exact Nat.le_trans below.alts hcounter
    · exact Nat.le_trans below.qterm hcounter
    · exact Nat.le_trans below.answers hcounter
  case evalg_err =>
    intro c value res rest binding message hcur hcompile goal hgoal below
    subst goal
    let data := chainify (unchainify 10000 (subst binding value))
    let counter := advanceCounterPastAtoms c.counter [data]
    have hcounter : c.counter ≤ counter :=
      advanceCounterPastAtoms_mono c.counter [data]
    have hdata : resolutionSeedHighWaterNames data.vars ≤ counter := by
      unfold counter advanceCounterPastAtoms
      rw [resolutionSeedHighWaterAtoms_eq]
      simp only [List.flatMap_singleton]
      exact Nat.le_max_right _ _
    have hnext := below.replaceActiveEq
      (Goal.evalg value res :: rest) binding hcur res data rest c.world
      counter hcounter (by
        intro name member
        simp only [specializationGoalsVars, specializationGoalVars,
          List.mem_append] at member ⊢
        rcases member with (hres | hrest) | hbinding
        · exact Or.inl (Or.inl (Or.inr hres))
        · exact Or.inl (Or.inr hrest)
        · exact Or.inr hbinding) hdata
    simpa [data, counter] using hnext
  case catch_direct_error =>
    intro c template sub res rest binding err hcur hcatch below
    let counter := advanceCounterPastAtoms c.counter [err]
    have hcounter : c.counter ≤ counter :=
      advanceCounterPastAtoms_mono c.counter [err]
    have herr : resolutionSeedHighWaterNames err.vars ≤ counter := by
      unfold counter advanceCounterPastAtoms
      rw [resolutionSeedHighWaterAtoms_eq]
      simp only [List.flatMap_singleton]
      exact Nat.le_max_right _ _
    have hnext := below.replaceActiveEq
      (Goal.catchg template sub res :: rest) binding hcur res err rest
      c.world counter hcounter (by
        intro name member
        simp only [specializationGoalsVars, specializationGoalVars,
          List.mem_append] at member ⊢
        rcases member with (hres | hrest) | hbinding
        · simp [hres]
        · simp [hrest]
        · simp [hbinding]) herr
    simpa [counter] using hnext
  case catch_direct_answers =>
    intro c template sub res rest binding answers hcur hcatch below
    let counter := advanceCounterPastAtoms c.counter answers
    have hcounter : c.counter ≤ counter :=
      advanceCounterPastAtoms_mono c.counter answers
    have hitems : resolutionSeedHighWaterNames
        (answers.flatMap Atom.vars) ≤ counter := by
      unfold counter advanceCounterPastAtoms
      rw [resolutionSeedHighWaterAtoms_eq]
      exact Nat.le_max_right _ _
    have hqueued := below.enqueueEqAlts
      (Goal.catchg template sub res :: rest) binding hcur res rest answers
      c.world counter hcounter (by
        intro name member
        simp only [specializationGoalsVars, specializationGoalVars,
          List.mem_append] at member ⊢
        rcases member with (hres | hrest) | hbinding
        · simp [hres]
        · simp [hrest]
        · simp [hbinding]) hitems
    simpa [counter] using hqueued.pull
  case bin_union_reverse =>
    intro c args res rest binding branches hcur hpartial hlocal hnonstrict
      hmode hground hreverse below
    have hactive := below.active
      (Goal.bin "union-atom" args res :: rest) binding hcur
    have hsource : resolutionSeedHighWaterNames
        (args.flatMap Atom.vars ++ res.vars ++ specializationGoalsVars rest ++
          resolutionSubstVars binding) ≤ c.counter := by
      simpa [specializationGoalsVars, specializationGoalVars] using hactive
    have hbranches := unionReverseAlts_below args res rest binding branches
      c.counter hsource hreverse
    apply ConfBelowResolutionCounter.pull
    apply ConfBelowResolutionCounter.of_components
    · simp [resolutionCurVars, resolutionSeedHighWaterNames]
    · simp only [List.flatMap_append, resolutionSeedHighWaterNames_append]
      exact Nat.max_le.mpr ⟨hbranches, below.alts⟩
    · exact below.qterm
    · exact below.answers
  case catch_run =>
    intro c d template sub res rest binding hcur hdirect hrun hterminal ih
      below
    have nestedBelow : ConfBelowResolutionCounter
        (Conf.mk (some (sub, binding)) [] c.world c.counter template []
          [] (by rfl) (resetBarrierCache c.barriers)) :=
      below.nested (Goal.catchg template sub res :: rest) sub binding hcur
        c.world template (by
          intro name member
          simp only [specializationGoalsVars, specializationGoalVars,
            List.mem_append] at member ⊢
          rcases member with (hsub | hbinding) | htemplate
          · simp [hsub]
          · simp [hbinding]
          · simp [htemplate])
    have dBelow := ih nestedBelow
    have hcounter : c.counter ≤ d.counter := by
      simpa using hrun.counter_mono
    have hqueued := below.enqueueEqAlts
      (Goal.catchg template sub res :: rest) binding hcur res rest
      d.answerValues
      d.world d.counter hcounter (by
        intro name member
        simp only [specializationGoalsVars, specializationGoalVars,
          List.mem_append] at member ⊢
        rcases member with (hres | hrest) | hbinding
        · simp [hres]
        · simp [hrest]
        · simp [hbinding]) dBelow.answerValues
    exact hqueued.pull
  case catch_run_error =>
    intro c d template sub res rest binding err hcur hdirect hrun ih below
    let counter := advanceCounterPastAtoms d.counter [err]
    have hcounter : c.counter ≤ counter :=
      Nat.le_trans (by simpa using hrun.counter_mono)
        (advanceCounterPastAtoms_mono d.counter [err])
    have herr : resolutionSeedHighWaterNames err.vars ≤ counter := by
      unfold counter advanceCounterPastAtoms
      rw [resolutionSeedHighWaterAtoms_eq]
      simp only [List.flatMap_singleton]
      exact Nat.le_max_right _ _
    have hnext := below.replaceActiveEq
      (Goal.catchg template sub res :: rest) binding hcur res err rest
      d.world counter hcounter (by
        intro name member
        simp only [specializationGoalsVars, specializationGoalVars,
          List.mem_append] at member ⊢
        rcases member with (hres | hrest) | hbinding
        · simp [hres]
        · simp [hrest]
        · simp [hbinding]) herr
    simpa [counter] using hnext
  case softcut_some =>
    intro c d template sub thenGoals elseGoals rest binding hcur hrun
      hterminal hnonempty ih below
    have nestedBelow : ConfBelowResolutionCounter
        (Conf.mk (some (sub, binding)) [] c.world c.counter template []
          [] (by rfl) (resetBarrierCache c.barriers)) :=
      below.nested
        (Goal.softcut template sub thenGoals elseGoals :: rest) sub binding
        hcur c.world template (by
          intro name member
          simp only [specializationGoalsVars, specializationGoalVars,
            List.mem_append] at member ⊢
          rcases member with (hsub | hbinding) | htemplate
          · simp [hsub]
          · simp [hbinding]
          · simp [htemplate])
    have dBelow := ih nestedBelow
    have hcounter : c.counter ≤ d.counter := by
      simpa using hrun.counter_mono
    have hqueued := below.enqueueEqAlts
      (Goal.softcut template sub thenGoals elseGoals :: rest) binding hcur
      template (thenGoals ++ rest) d.answerValues d.world d.counter hcounter (by
        intro name member
        simp only [specializationGoalsVars_append, specializationGoalsVars,
          specializationGoalVars, List.mem_append] at member ⊢
        rcases member with (htemplate | hthen | hrest) | hbinding
        · simp [htemplate]
        · simp [hthen]
        · simp [hrest]
        · simp [hbinding]) dBelow.answerValues
    exact hqueued.pull
  case softcut_none =>
    intro c d template sub thenGoals elseGoals rest binding hcur hrun
      hterminal hempty ih below
    have hcounter : c.counter ≤ d.counter := by
      simpa using hrun.counter_mono
    have hactive := below.active
      (Goal.softcut template sub thenGoals elseGoals :: rest) binding hcur
    apply ConfBelowResolutionCounter.of_components
    · simp only [resolutionCurVars, specializationGoalsVars_append,
        specializationGoalsVars, specializationGoalVars,
        resolutionSeedHighWaterNames_append] at hactive ⊢
      omega
    · exact Nat.le_trans below.alts hcounter
    · exact Nat.le_trans below.qterm hcounter
    · exact Nat.le_trans below.answers hcounter
  case transaction_some =>
    intro c d template sub rest binding hcur hrun hterminal hnonempty ih
      below
    have nestedBelow : ConfBelowResolutionCounter
        (Conf.mk (some (transactionSub template sub, binding)) [] c.world
          c.counter template [] [] (by rfl)
            (resetBarrierCache c.barriers)) :=
      below.nested (Goal.transactiong template sub :: rest)
        (transactionSub template sub) binding hcur c.world template (by
          intro name member
          simp [transactionSub, specializationGoalsVars,
            specializationGoalVars] at member ⊢
          rcases member with htemplate | member
          · exact Or.inl htemplate
          · rcases member with hsub | member
            · exact Or.inr (Or.inl hsub)
            · rcases member with htemplate | member
              · exact Or.inl htemplate
              · rcases member with hbinding | htemplate
                · exact Or.inr (Or.inr (Or.inr hbinding))
                · exact Or.inl htemplate)
    have dBelow := ih nestedBelow
    have hcounter : c.counter ≤ d.counter := by
      simpa using hrun.counter_mono
    have hqueued := below.enqueueEqAlts
      (Goal.transactiong template sub :: rest) binding hcur template rest
      d.answerValues d.world d.counter hcounter (by
        intro name member
        simp only [specializationGoalsVars, specializationGoalVars,
          List.mem_append] at member ⊢
        rcases member with (htemplate | hrest) | hbinding
        · simp [htemplate]
        · simp [hrest]
        · simp [hbinding]) dBelow.answerValues
    exact hqueued.pull
  case transaction_none =>
    intro c d template sub rest binding hcur hrun hterminal hempty ih below
    have hcounter : c.counter ≤ d.counter := by
      simpa using hrun.counter_mono
    apply ConfBelowResolutionCounter.pull
    apply ConfBelowResolutionCounter.of_components
    · simp [resolutionCurVars, resolutionSeedHighWaterNames]
    · exact Nat.le_trans below.alts hcounter
    · exact Nat.le_trans below.qterm hcounter
    · exact Nat.le_trans below.answers hcounter
  case onceg =>
    intro c template sub res rest binding hcur below
    have hactive := below.active
      (Goal.onceg template sub res :: rest) binding hcur
    have hnew : resolutionSeedHighWaterNames
        (resolutionAltVars
          (Alt.br
            (sub ++ [Goal.cutAt (barrierDepth c + 1),
              Goal.eq res template] ++ rest) binding)) ≤ c.counter := by
      simp only [resolutionAltVars, specializationGoalsVars_append,
        specializationGoalsVars, specializationGoalVars,
        resolutionSeedHighWaterNames_append,
        resolutionSeedHighWaterNames] at hactive ⊢
      omega
    apply ConfBelowResolutionCounter.pull
    apply ConfBelowResolutionCounter.of_components
    · simp [resolutionCurVars, resolutionSeedHighWaterNames]
    · simpa only [List.flatMap_cons, resolutionAltVars, List.nil_append,
        resolutionSeedHighWaterNames_append] using
          (Nat.max_le.mpr ⟨hnew, below.alts⟩)
    · exact below.qterm
    · exact below.answers
  case wact_ok =>
    intro c operation args res result rest binding world counter' hcur
      _notRetract hdispatch below
    let counter := max c.counter counter'
    have hcounter : c.counter ≤ counter := by
      exact Nat.le_max_left _ _
    have hresult : resolutionSeedHighWaterNames result.vars ≤ counter :=
      Nat.le_trans
        (wactDispatch_result_below c.world gt c.counter operation
          (args.map (subst binding)) result world counter' hdispatch)
        (Nat.le_max_right _ _)
    have hnext := below.replaceActiveEq
      (Goal.wact operation args res :: rest) binding hcur res result rest
      world counter hcounter (by
        intro name member
        simp only [specializationGoalsVars, specializationGoalVars,
          List.mem_append] at member ⊢
        rcases member with (hres | hrest) | hbinding
        · simp [hres]
        · simp [hrest]
        · simp [hbinding]) hresult
    simpa [counter] using hnext
  case findall =>
    intro c d template sub res rest binding hcur hrun hterminal ih below
    have nestedBelow : ConfBelowResolutionCounter
        (Conf.mk (some (sub, binding)) [] c.world c.counter template []
          [] (by rfl) (resetBarrierCache c.barriers)) :=
      below.nested (Goal.findall template sub res :: rest) sub binding hcur
        c.world template (by
          intro name member
          simp only [specializationGoalsVars, specializationGoalVars,
            List.mem_append] at member ⊢
          rcases member with (hsub | hbinding) | htemplate
          · simp [hsub]
          · simp [hbinding]
          · simp [htemplate])
    have dBelow := ih nestedBelow
    have hrunCounter : c.counter ≤ d.counter := by
      simpa using hrun.counter_mono
    let copied := copyFindallBag d.counter d.answerValues
    have hcounter : c.counter ≤ copied.counter :=
      Nat.le_trans hrunCounter (copyFindallBag_counter_mono _ _)
    have hchain : resolutionSeedHighWaterNames
        (chainOf copied.values).vars ≤ copied.counter :=
      Nat.le_trans
        (resolutionSeedHighWaterNames_le_of_subset (by
          intro name member
          exact chainOf_vars_subset copied.values name member))
        (copyFindallBag_values_below _ _)
    have next := below.replaceActiveEq
      (Goal.findall template sub res :: rest) binding hcur res
      (chainOf copied.values) rest d.world copied.counter hcounter (by
        intro name member
        simp only [specializationGoalsVars, specializationGoalVars,
          List.mem_append] at member ⊢
        rcases member with (hres | hrest) | hbinding
        · simp [hres]
        · simp [hrest]
        · simp [hbinding]) hchain
    simpa [copied, rejoinFindall] using next
  case call_table_compute =>
    intro c d function args res rest binding tres hcur hcan hcache htres hrun
      hdone ih below
    have hactive := below.active (Goal.call function args res :: rest) binding hcur
    have hsource : resolutionSeedHighWaterNames
        (args.flatMap Atom.vars ++ res.vars ++
          specializationGoalsVars rest ++ resolutionSubstVars binding) ≤ c.counter := by
      simpa [specializationGoalsVars, specializationGoalVars] using hactive
    have hargs : resolutionSeedHighWaterNames (args.flatMap Atom.vars) ≤ c.counter :=
      Nat.le_trans (resolutionSeedHighWaterNames_le_of_subset (by
        intro name member
        simp only [List.mem_append]
        exact Or.inl (Or.inl (Or.inl member)))) hsource
    have hbind : resolutionSeedHighWaterNames (resolutionSubstVars binding) ≤ c.counter :=
      Nat.le_trans (resolutionSeedHighWaterNames_le_of_subset (by
        intro name member
        simp only [List.mem_append]
        exact Or.inr member)) hsource
    have hstart : c.counter ≤ advanceCounterPastAtoms (c.counter + 1) [tres] :=
      Nat.le_trans (Nat.le_succ c.counter)
        (advanceCounterPastAtoms_mono (c.counter + 1) [tres])
    have htres : resolutionSeedHighWaterNames ([tres].flatMap Atom.vars) ≤
        advanceCounterPastAtoms (c.counter + 1) [tres] := by
      unfold advanceCounterPastAtoms
      rw [resolutionSeedHighWaterAtoms_eq]
      exact Nat.le_max_right _ _
    have hsubArgs : resolutionSeedHighWaterNames
        ((args.map (subst binding)).flatMap Atom.vars) ≤
        advanceCounterPastAtoms (c.counter + 1) [tres] :=
      Nat.le_trans
        (resolutionSeedHighWaterAtomList_subst_le binding args c.counter hargs hbind)
        hstart
    have dBelow : ConfBelowResolutionCounter d := by
      apply ih
      apply ConfBelowResolutionCounter.of_components
      · simp only [resolutionCurVars, specializationGoalsVars, specializationGoalVars,
          resolutionSubstVars, List.append_nil, List.flatMap_nil,
          resolutionSeedHighWaterNames_append]
        refine Nat.max_le.mpr ⟨hsubArgs, ?_⟩
        simpa [List.flatMap_cons, List.flatMap_nil] using htres
      · simp [resolutionSeedHighWaterNames]
      · simpa [List.flatMap_cons, List.flatMap_nil] using htres
      · simp [resolutionSeedHighWaterNames]
    have hcounter : c.counter ≤ d.counter :=
      Nat.le_trans hstart hrun.counter_mono
    simpa [List.map_map, Function.comp_def] using
      (below.enqueueEqAlts (Goal.call function args res :: rest) binding hcur
        res rest d.answerValues _ d.counter hcounter (by
          intro name member
          simp only [specializationGoalsVars, specializationGoalVars,
            List.mem_append] at member ⊢
          rcases member with (hres | hrest) | hbinding
          · exact Or.inl (Or.inl (Or.inr hres))
          · exact Or.inl (Or.inr hrest)
          · exact Or.inr hbinding) dBelow.answerValues).pull
  case transaction =>
    intro c d tmpl sub rest b err hcur hraise ih below
    exact ih (below.nested (Goal.transactiong tmpl sub :: rest)
      (transactionSub tmpl sub) b hcur c.world tmpl (by
        intro name member
        simp [transactionSub, specializationGoalsVars, specializationGoalVars]
          at member ⊢
        rcases member with htemplate | member
        · exact Or.inl htemplate
        · rcases member with hsub | member
          · exact Or.inr (Or.inl hsub)
          · rcases member with htemplate | member
            · exact Or.inl htemplate
            · rcases member with hbinding | htemplate
              · exact Or.inr (Or.inr (Or.inr hbinding))
              · exact Or.inl htemplate))
  case softcut =>
    intro c d tmpl sub thn els rest b err hcur hraise ih below
    apply ih
    have hactive := below.active (Goal.softcut tmpl sub thn els :: rest) b hcur
    apply ConfBelowResolutionCounter.of_components
    · simp only [resolutionCurVars, specializationGoalsVars,
        specializationGoalVars, resolutionSeedHighWaterNames_append] at hactive ⊢
      omega
    · simp [resolutionSeedHighWaterNames]
    · simp only [specializationGoalsVars, specializationGoalVars,
        resolutionSeedHighWaterNames_append] at hactive ⊢
      omega
    · simp [resolutionSeedHighWaterNames]
  case table =>
    intro c d function args res rest binding tres err hcur hcan hcache htres
      hraise ih below
    apply ih
    have hactive := below.active (Goal.call function args res :: rest) binding hcur
    have hsource : resolutionSeedHighWaterNames
        (args.flatMap Atom.vars ++ res.vars ++
          specializationGoalsVars rest ++ resolutionSubstVars binding) ≤ c.counter := by
      simpa [specializationGoalsVars, specializationGoalVars] using hactive
    have hargs : resolutionSeedHighWaterNames (args.flatMap Atom.vars) ≤ c.counter :=
      Nat.le_trans (resolutionSeedHighWaterNames_le_of_subset (by
        intro name member
        simp only [List.mem_append]
        exact Or.inl (Or.inl (Or.inl member)))) hsource
    have hbind : resolutionSeedHighWaterNames (resolutionSubstVars binding) ≤ c.counter :=
      Nat.le_trans (resolutionSeedHighWaterNames_le_of_subset (by
        intro name member
        simp only [List.mem_append]
        exact Or.inr member)) hsource
    have hstart : c.counter ≤ advanceCounterPastAtoms (c.counter + 1) [tres] :=
      Nat.le_trans (Nat.le_succ c.counter)
        (advanceCounterPastAtoms_mono (c.counter + 1) [tres])
    have htres : resolutionSeedHighWaterNames ([tres].flatMap Atom.vars) ≤
        advanceCounterPastAtoms (c.counter + 1) [tres] := by
      unfold advanceCounterPastAtoms
      rw [resolutionSeedHighWaterAtoms_eq]
      exact Nat.le_max_right _ _
    have hsubArgs : resolutionSeedHighWaterNames
        ((args.map (subst binding)).flatMap Atom.vars) ≤
        advanceCounterPastAtoms (c.counter + 1) [tres] :=
      Nat.le_trans
        (resolutionSeedHighWaterAtomList_subst_le binding args c.counter hargs hbind)
        hstart
    apply ConfBelowResolutionCounter.of_components
    · simp only [resolutionCurVars, specializationGoalsVars, specializationGoalVars,
        resolutionSubstVars, List.append_nil, List.flatMap_nil,
        resolutionSeedHighWaterNames_append]
      refine Nat.max_le.mpr ⟨hsubArgs, ?_⟩
      simpa [List.flatMap_cons, List.flatMap_nil] using htres
    · simp [resolutionSeedHighWaterNames]
    · simpa [List.flatMap_cons, List.flatMap_nil] using htres
    · simp [resolutionSeedHighWaterNames]
  case findall =>
    intro c d tmpl sub res rest b err hcur hraise ih below
    apply ih
    have hactive := below.active (Goal.findall tmpl sub res :: rest) b hcur
    apply ConfBelowResolutionCounter.of_components
    · simp only [resolutionCurVars, specializationGoalsVars,
        specializationGoalVars, resolutionSeedHighWaterNames_append] at hactive ⊢
      omega
    · simp [resolutionSeedHighWaterNames]
    · simp only [specializationGoalsVars, specializationGoalVars,
        resolutionSeedHighWaterNames_append] at hactive ⊢
      omega
    · simp [resolutionSeedHighWaterNames]

theorem seededConf_belowResolutionCounter (prog : Prog) (conf : Conf) :
    ConfBelowResolutionCounter
      ({ conf with counter :=
          (Nat.max conf.counter (resolutionConfHighWater prog conf)) } : Conf) := by
  unfold ConfBelowResolutionCounter resolutionLiveHighWater
  calc
    resolutionSeedHighWaterNames (resolutionLiveVars conf) ≤
        resolutionSeedHighWaterNames (resolutionConfVars conf) := by
      apply resolutionSeedHighWaterNames_le_of_subset
      intro name member
      simp only [resolutionLiveVars, resolutionConfVars,
        List.mem_append] at member ⊢
      rcases member with ((hcur | halts) | hqterm) | hanswers
      · exact Or.inl (Or.inl (Or.inl (Or.inl hcur)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr halts)))
      · exact Or.inl (Or.inr hqterm)
      · exact Or.inr hanswers
    _ ≤ resolutionSeedHighWaterNames
          (resolutionProgVars prog ++ resolutionConfVars conf) := by
      apply resolutionSeedHighWaterNames_le_of_subset
      exact fun name member => List.mem_append_right _ member
    _ ≤ Nat.max conf.counter (resolutionConfHighWater prog conf) := by
      unfold resolutionConfHighWater
      exact Nat.le_max_right _ _

/-- The globally seeded counter discharges the old per-resolution occupied
scan whenever the occupied surface is part of the configuration surface. -/
theorem resolutionFreshSuffix_target_ne_of_confBelow
    (conf : Conf)
    (below : ConfBelowResolutionCounter conf)
    (argsv : List Atom) (res : Atom) (rest : List Goal) (binding : Subst)
    (qterm : Atom)
    (occupiedSubset : ∀ name,
      name ∈ resolutionOccupiedVars argsv res rest binding qterm →
      name ∈ resolutionLiveVars conf)
    (source caller : String)
    (callerOccupied : caller ∈
      resolutionOccupiedVars argsv res rest binding qterm) :
    source ++ resolutionFreshSuffix argsv res rest binding qterm conf.counter ≠
      caller := by
  apply resolutionFreshSuffix_target_ne argsv res rest binding qterm
    conf.counter
  · exact Nat.le_trans
      (resolutionSeedHighWaterNames_le_of_subset occupiedSubset)
      below
  · exact callerOccupied

end PLeaTTa
