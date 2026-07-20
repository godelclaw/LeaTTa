import PLeaTTa.SubstEngine

namespace PLeaTTa

open Metta (Atom Subst GroundingTable ReduceResult callGrounded)

namespace SubstEngine

@[simp] theorem reference_empty : reference.empty = ([] : Subst) := rfl

@[simp] theorem reference_denote (state : Subst) :
    reference.denote state = state := rfl

@[simp] theorem reference_subst (state : Subst) (atom : Atom) :
    reference.subst state atom = (PLeaTTa.subst state atom, state) := rfl

@[simp] theorem reference_substMany (state : Subst) (atoms : List Atom) :
    reference.substMany state atoms =
      (atoms.map (PLeaTTa.subst state), state) := rfl

@[simp] theorem reference_substPrepared (state : Subst) (atom : Atom) :
    reference.substPrepared state atom =
      (PersistentSubst.PreparedAtom.ofAtom (PLeaTTa.subst state atom),
        state) := rfl

@[simp] theorem reference_preparedExactKey (state : Subst)
    (prepared : PersistentSubst.PreparedAtom) :
    reference.preparedExactKey state prepared =
      PersistentSubst.atomExactKey prepared.atom := by
  exact reference.preparedExactKey_value state prepared

@[simp] theorem reference_trimFor (state : Subst) (goals : List Goal)
    (qterm : Atom) :
    reference.trimFor state goals qterm =
      PLeaTTa.trimFor goals qterm state := rfl

@[simp] theorem reference_unify (state : Subst) (left right : Atom) :
    reference.unify state left right =
      PLeaTTa.unifyB state left right := rfl

@[simp] theorem unifyB_reference (state : Subst) (left right : Atom) :
    reference.unifyB state left right = PLeaTTa.unifyB state left right := by
  have erased := unifyB_map_denote reference state left right True.intro
  simpa [reference] using erased

/-- Replace the reference binding carried by an alternative with an
engine state. The goals and barrier structure are unchanged. -/
def rebindAlt {State : Type} (state : State) : Alt → Alt State
  | .br goals _ => .br goals state
  | .barrier => .barrier

def rebindAlts {State : Type} (state : State) (alts : List Alt) :
    List (Alt State) :=
  alts.map (rebindAlt state)

def Carries (binding : Subst) : Alt → Prop
  | .br _ carried => carried = binding
  | .barrier => True

theorem rebindAlt_eq_self_of_carries (binding : Subst) (alt : Alt)
    (carries : Carries binding alt) :
    rebindAlt binding alt = alt := by
  cases alt with
  | barrier => rfl
  | br goals carried =>
      simp only [Carries] at carries
      subst carried
      rfl

theorem rebindAlts_eq_self_of_forall (binding : Subst) (alts : List Alt)
    (carries : ∀ alt ∈ alts, Carries binding alt) :
    rebindAlts binding alts = alts := by
  induction alts with
  | nil => rfl
  | cons alt rest ih =>
      simp only [rebindAlts, List.map_cons]
      rw [rebindAlt_eq_self_of_carries binding alt
        (carries alt (by simp))]
      change alt :: rebindAlts binding rest = alt :: rest
      rw [ih (fun candidate member => carries candidate (by simp [member]))]

@[simp] theorem mapAlt_rebindAlt (engine : SubstEngine)
    (state : engine.State) (alt : Alt) :
    mapAlt engine.denote (rebindAlt state alt) =
      rebindAlt (engine.denote state) alt := by
  cases alt <;> rfl

@[simp] theorem mapAlt_rebindAlts (engine : SubstEngine)
    (state : engine.State) (alts : List Alt) :
    (rebindAlts state alts).map (mapAlt engine.denote) =
      rebindAlts (engine.denote state) alts := by
  induction alts with
  | nil => rfl
  | cons alt rest ih =>
      change mapAlt engine.denote (rebindAlt state alt) ::
          (rebindAlts state rest).map (mapAlt engine.denote) =
        rebindAlt (engine.denote state) alt ::
          rebindAlts (engine.denote state) rest
      rw [mapAlt_rebindAlt, ih]

private theorem barrierFold_mapAlt {Source Target : Type}
    (map : Source → Target) (initial : Nat) :
    ∀ alts : List (Alt Source),
      (alts.map (mapAlt map)).foldl
          (fun count alt => match alt with
            | .barrier => count + 1
            | _ => count)
          initial =
        alts.foldl
          (fun count alt => match alt with
            | .barrier => count + 1
            | _ => count)
          initial
  | [] => rfl
  | alt :: rest => by
      cases alt <;> exact barrierFold_mapAlt map _ rest

@[simp] theorem barrierCount_mapAlt {Source Target : Type}
    (map : Source → Target) (alts : List (Alt Source)) :
    barrierCount (alts.map (mapAlt map)) = barrierCount alts :=
  barrierFold_mapAlt map 0 alts

@[simp] theorem cutTo_mapAlt {Source Target : Type} (map : Source → Target)
    (count : Nat) (alts : List (Alt Source)) :
    cutTo count (alts.map (mapAlt map)) =
      (cutTo count alts).map (mapAlt map) := by
  induction alts with
  | nil => rfl
  | cons alt rest ih =>
      simp only [List.map_cons, cutTo]
      have countEq :
          barrierCount (mapAlt map alt :: rest.map (mapAlt map)) =
            barrierCount (alt :: rest) :=
        barrierCount_mapAlt map (alt :: rest)
      rw [countEq]
      split <;> simp [ih]

theorem cutToCached_mapAlt {Source Target : Type} (map : Source → Target)
    (count : Nat) : ∀ (depth : Nat) (alts : List (Alt Source)),
    cutToCached count depth (alts.map (mapAlt map)) =
      ((cutToCached count depth alts).1.map (mapAlt map),
        (cutToCached count depth alts).2)
  | _, [] => rfl
  | depth, .br goals state :: rest => by
      simp only [List.map_cons, mapAlt, cutToCached]
      split
      · exact cutToCached_mapAlt map count depth rest
      · rfl
  | depth, .barrier :: rest => by
      simp only [List.map_cons, mapAlt, cutToCached]
      split
      · exact cutToCached_mapAlt map count (depth - 1) rest
      · rfl

@[simp] theorem cutToTracked_mapAlt {Source Target : Type}
    (map : Source → Target) (count : Nat) (cache : Option Nat)
    (alts : List (Alt Source)) :
    cutToTracked count cache (alts.map (mapAlt map)) =
      ((cutToTracked count cache alts).1.map (mapAlt map),
        (cutToTracked count cache alts).2) := by
  cases cache with
  | none =>
      change (cutTo count (alts.map (mapAlt map)), none) =
        ((cutTo count alts).map (mapAlt map), none)
      rw [cutTo_mapAlt]
  | some depth =>
      simp only [cutToTracked]
      rw [cutToCached_mapAlt]

theorem pullAux_mapAlt {Source Target : Type} (map : Source → Target) :
    ∀ alts : List (Alt Source),
      pullAux (alts.map (mapAlt map)) =
        (pullAux alts).map (fun result =>
          ((result.1.1, map result.1.2), result.2.map (mapAlt map)))
  | [] => rfl
  | .barrier :: rest => pullAux_mapAlt map rest
  | .br _ _ :: _ => rfl

theorem pullAuxCached_mapAlt {Source Target : Type} (map : Source → Target) :
    ∀ (depth : Nat) (alts : List (Alt Source)),
      pullAuxCached depth (alts.map (mapAlt map)) =
        ((pullAuxCached depth alts).1.map (fun result =>
          ((result.1.1, map result.1.2), result.2.map (mapAlt map))),
          (pullAuxCached depth alts).2)
  | _, [] => rfl
  | depth, .barrier :: rest =>
      pullAuxCached_mapAlt map (depth - 1) rest
  | _, .br _ _ :: _ => rfl

@[simp] theorem mapConf_fields {Source Target : Type}
    (map : Source → Target) (cur : Option (List Goal × Source))
    (alts : List (Alt Source)) (world : PWorld) (counter : Nat)
    (qterm : Atom) (answers : List Atom)
    (answerKeys : List (Option PersistentSubst.AtomExactKey))
    (answerKeys_sound : answerKeys =
      answers.map PersistentSubst.atomExactKey)
    (barriers : Option Nat) :
    mapConf map
        ({ cur := cur
           alts := alts
           world := world
           counter := counter
           qterm := qterm
           answers := answers
           answerKeys := answerKeys
           answerKeys_sound := answerKeys_sound
           barriers := barriers } : Conf Source) =
      ({ cur := cur.map (fun branch => (branch.1, map branch.2))
         alts := alts.map (mapAlt map)
         world := world
         counter := counter
         qterm := qterm
         answers := answers
         answerKeys := answerKeys
         answerKeys_sound := answerKeys_sound
         barriers := barriers } : Conf Target) := by
  rfl

@[simp] theorem mapConf_setCurSome {Source Target : Type}
    (map : Source → Target) (conf : Conf Source) (goals : List Goal)
    (state : Source) :
    mapConf map { conf with cur := some (goals, state) } =
      { mapConf map conf with cur := some (goals, map state) } := by
  rcases conf with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
  rfl

@[simp] theorem mapConf_setCurNone {Source Target : Type}
    (map : Source → Target) (conf : Conf Source) :
    mapConf map { conf with cur := none } =
      { mapConf map conf with cur := none } := by
  rcases conf with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
  rfl

@[simp] theorem tableFresh_mapConf {Source Target : Type}
    (map : Source → Target) (conf : Conf Source) :
    tableFresh (mapConf map conf) = tableFresh conf := by
  rcases conf with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
  rfl

@[simp] theorem mapConf_cur_isNone {Source Target : Type}
    (map : Source → Target) (conf : Conf Source) :
    (mapConf map conf).cur.isNone = conf.cur.isNone := by
  rcases conf with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
  cases cur <;> rfl

@[simp] theorem mapConf_alts_isEmpty {Source Target : Type}
    (map : Source → Target) (conf : Conf Source) :
    (mapConf map conf).alts.isEmpty = conf.alts.isEmpty := by
  rcases conf with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
  cases alts <;> rfl

@[simp] theorem mapConf_answers {Source Target : Type}
    (map : Source → Target) (conf : Conf Source) :
    (mapConf map conf).answers = conf.answers := rfl

@[simp] theorem mapConf_answerValues {Source Target : Type}
    (map : Source → Target) (conf : Conf Source) :
    (mapConf map conf).answerValues = conf.answerValues := by
  simp [Conf.answerValues]

@[simp] theorem barrierDepth_mapConf {Source Target : Type}
    (map : Source → Target) (conf : Conf Source) :
    barrierDepth (mapConf map conf) = barrierDepth conf := by
  rcases conf with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
  cases barriers <;>
    simp [mapConf, barrierDepth, barrierCount_mapAlt]

theorem world_eq_of_erase_eq (engine : SubstEngine)
    {source : Conf engine.State} {target : Conf}
    (equality : erase engine source = target) :
    source.world = target.world := by
  have projected := congrArg Conf.world equality
  simpa [erase, mapConf] using projected

theorem counter_eq_of_erase_eq (engine : SubstEngine)
    {source : Conf engine.State} {target : Conf}
    (equality : erase engine source = target) :
    source.counter = target.counter := by
  have projected := congrArg Conf.counter equality
  simpa [erase, mapConf] using projected

theorem answers_eq_of_erase_eq (engine : SubstEngine)
    {source : Conf engine.State} {target : Conf}
    (equality : erase engine source = target) :
    source.answers = target.answers := by
  have projected := congrArg Conf.answers equality
  simpa [erase, mapConf] using projected

@[simp] theorem mapConf_pull {Source Target : Type} (map : Source → Target)
    (conf : Conf Source) :
    mapConf map (pull conf) = pull (mapConf map conf) := by
  rcases conf with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
  apply Conf.ext
  all_goals
    cases barriers <;>
      simp [pull, mapConf, pullAuxTracked, pullAux_mapAlt,
        pullAuxCached_mapAlt] <;>
      split <;> simp_all

theorem mapConf_oncePull {Source Target : Type} (map : Source → Target)
    (conf : Conf Source) (sub rest : List Goal) (res tmpl : Atom)
    (state : Source) :
    mapConf map
        (pull { conf with
          cur := none
          alts := Alt.br
              (sub ++ [Goal.cutAt (barrierDepth conf + 1),
                Goal.eq res tmpl] ++ rest) state ::
            (Alt.barrier :: conf.alts)
          barriers := pushBarrierCache conf.barriers }) =
      pull { mapConf map conf with
        cur := none
        alts := Alt.br
            (sub ++ [Goal.cutAt
              (barrierDepth (mapConf map conf) + 1),
              Goal.eq res tmpl] ++ rest) (map state) ::
          (Alt.barrier :: (mapConf map conf).alts)
        barriers := pushBarrierCache (mapConf map conf).barriers } := by
  rw [mapConf_pull]
  rcases conf with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
  cases barriers <;>
    simp [mapConf, mapAlt, barrierDepth, barrierCount_mapAlt,
      pushBarrierCache]

theorem mapConf_barrierCurrent {Source Target : Type}
    (map : Source → Target) (conf : Conf Source)
    (goals : Nat → List Goal) (state : Source) (nextWorld : PWorld)
    (nextCounter : Nat) :
    mapConf map
        { conf with
          cur := some (goals (barrierDepth conf), state)
          world := nextWorld
          counter := nextCounter } =
      { mapConf map conf with
        cur := some
          (goals (barrierDepth (mapConf map conf)), map state)
        world := nextWorld
        counter := nextCounter } := by
  rcases conf with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
  cases barriers <;>
    simp [mapConf, barrierDepth, barrierCount_mapAlt]

theorem pullAux_valid (engine : SubstEngine) :
    ∀ alts : List (Alt engine.State),
      (∀ alt ∈ alts, AltValid engine alt) →
      match pullAux alts with
      | none => True
      | some ((_, state), rest) =>
          engine.Valid state ∧ ∀ alt ∈ rest, AltValid engine alt
  | [], _ => trivial
  | .barrier :: rest, valid => by
      apply pullAux_valid engine rest
      intro alt member
      exact valid alt (by simp [member])
  | .br goals state :: rest, valid => by
      constructor
      · exact valid (.br goals state) (by simp)
      · intro alt member
        exact valid alt (by simp [member])

theorem pull_valid (engine : SubstEngine) (conf : Conf engine.State)
    (valid : ConfValid engine conf) :
    ConfValid engine (pull conf) := by
  have auxiliary := pullAux_valid engine conf.alts valid.2
  unfold pull
  generalize trackedEq : pullAuxTracked conf.barriers conf.alts = tracked
  rcases tracked with ⟨pulled, cache⟩
  have pulledEq : pulled = pullAux conf.alts := by
    have firstEq := pullAuxTracked_fst conf.barriers conf.alts
    simpa [trackedEq] using firstEq
  rw [pulledEq]
  cases result : pullAux conf.alts with
  | none =>
      constructor
      · simp
      · simp
  | some pulled =>
      rcases pulled with ⟨⟨goals, state⟩, rest⟩
      simp only [result] at auxiliary
      constructor
      · intro currentGoals currentState equality
        simp only [Option.some.injEq, Prod.mk.injEq] at equality
        rcases equality with ⟨rfl, rfl⟩
        exact auxiliary.1
      · exact auxiliary.2

def AltsValid (engine : SubstEngine)
    (alts : List (Alt engine.State)) : Prop :=
  ∀ alt ∈ alts, AltValid engine alt

theorem altsValid_append (engine : SubstEngine)
    {left right : List (Alt engine.State)}
    (leftValid : AltsValid engine left)
    (rightValid : AltsValid engine right) :
    AltsValid engine (left ++ right) := by
  intro alt member
  rcases List.mem_append.mp member with member | member
  · exact leftValid alt member
  · exact rightValid alt member

theorem altsValid_map_br (engine : SubstEngine) {α : Type}
    (items : List α) (goals : α → List Goal) (state : engine.State)
    (stateValid : engine.Valid state) :
    AltsValid engine (items.map (fun item => Alt.br (goals item) state)) := by
  intro alt member
  rcases List.mem_map.mp member with ⟨item, _, rfl⟩
  exact stateValid

theorem confValid_none (engine : SubstEngine)
    (alts : List (Alt engine.State)) (world : PWorld) (counter : Nat)
    (qterm : Atom) (answers : List Atom)
    (answerKeys : List (Option PersistentSubst.AtomExactKey))
    (answerKeys_sound : answerKeys =
      answers.map PersistentSubst.atomExactKey)
    (barriers : Option Nat)
    (valid : AltsValid engine alts) :
    ConfValid engine
      { cur := none
        alts := alts
        world := world
        counter := counter
        qterm := qterm
        answers := answers
        answerKeys := answerKeys
        answerKeys_sound := answerKeys_sound
        barriers := barriers } := by
  exact ⟨by simp, valid⟩

theorem confValid_some (engine : SubstEngine) (goals : List Goal)
    (state : engine.State) (alts : List (Alt engine.State))
    (world : PWorld) (counter : Nat) (qterm : Atom) (answers : List Atom)
    (answerKeys : List (Option PersistentSubst.AtomExactKey))
    (answerKeys_sound : answerKeys =
      answers.map PersistentSubst.atomExactKey)
    (barriers : Option Nat)
    (stateValid : engine.Valid state) (altsValid : AltsValid engine alts) :
    ConfValid engine
      { cur := some (goals, state)
        alts := alts
        world := world
        counter := counter
        qterm := qterm
        answers := answers
        answerKeys := answerKeys
        answerKeys_sound := answerKeys_sound
        barriers := barriers } := by
  constructor
  · intro currentGoals currentState equality
    simp only [Option.some.injEq, Prod.mk.injEq] at equality
    rcases equality with ⟨rfl, rfl⟩
    exact stateValid
  · exact altsValid

theorem altsValid_cons (engine : SubstEngine)
    {alt : Alt engine.State} {alts : List (Alt engine.State)}
    (altValid : AltValid engine alt) (restValid : AltsValid engine alts) :
    AltsValid engine (alt :: alts) := by
  intro candidate member
  rcases List.mem_cons.mp member with rfl | member
  · exact altValid
  · exact restValid candidate member

theorem cutTo_valid (engine : SubstEngine) (count : Nat) :
    ∀ alts : List (Alt engine.State), AltsValid engine alts →
      AltsValid engine (cutTo count alts)
  | [], _ => by
      simp [AltsValid, cutTo]
  | alt :: rest, valid => by
      unfold cutTo
      split
      · apply cutTo_valid engine count rest
        intro candidate member
        exact valid candidate (List.mem_cons_of_mem alt member)
      · exact valid

theorem cutToCached_valid (engine : SubstEngine) (count : Nat) :
    ∀ (depth : Nat) (alts : List (Alt engine.State)),
      AltsValid engine alts →
      AltsValid engine (cutToCached count depth alts).1
  | _, [], _ => by simp [AltsValid, cutToCached]
  | depth, alt :: rest, valid => by
      unfold cutToCached
      split
      · apply cutToCached_valid engine count _ rest
        intro candidate member
        exact valid candidate (List.mem_cons_of_mem alt member)
      · exact valid

theorem cutToTracked_valid (engine : SubstEngine) (count : Nat)
    (cache : Option Nat) (alts : List (Alt engine.State))
    (valid : AltsValid engine alts) :
    AltsValid engine (cutToTracked count cache alts).1 := by
  cases cache with
  | none => exact cutTo_valid engine count alts valid
  | some depth => exact cutToCached_valid engine count depth alts valid

/-- Standardize one clause apart using a precomputed summary of caller names. -/
def freshenResolutionClauseSummary
    (summary : PersistentSubst.FreshSummary) (dynamic : List String)
    (seed bc : Nat)
    (clause : Clause) : Clause :=
  let suffix := resolutionFreshSuffixCached summary dynamic seed
  { params := clause.params.map (renameAtomSuffix suffix)
    result := renameAtomSuffix suffix clause.result
    body := clause.body.map (renameGoalSuffix suffix bc) }

/-- Clause-goal construction after the engine has substituted the output and
combined its cached substitution summary with the current goal surface. -/
def resolveGoalsPrepared (cs : List Clause)
    (argsv args : List Atom) (res : Atom) (rest : List Goal)
    (resv : Atom) (summary : PersistentSubst.FreshSummary)
    (dynamic : List String)
    (bc counter : Nat) : List (List Goal) × Nat :=
  let (revAlts, counter') := cs.foldl
    (fun (acc : List (List Goal) × Nat) clause =>
      if clause.params.length != argsv.length then acc
      else if !matchCompatList argsv clause.params then acc
      else if !matchCompat resv clause.result then acc
      else
        let copied := freshenResolutionClauseSummary summary dynamic acc.2 bc
          clause
        let goals := Goal.eq (Atom.expr (args ++ [res]))
            (Atom.expr (copied.params ++ [copied.result])) ::
          copied.body ++ rest
        (goals :: acc.1, acc.2 + 1))
    ([], counter)
  (revAlts.reverse, counter')

def resolveAltsPrepared {Binding : Type} (cs : List Clause)
    (argsv args : List Atom) (res : Atom) (rest : List Goal)
    (resv : Atom) (summary : PersistentSubst.FreshSummary)
    (dynamic : List String)
    (binding : Binding) (bc counter : Nat) :
    List (Alt Binding) × Nat :=
  let result := resolveGoalsPrepared cs argsv args res rest resv summary
    dynamic bc counter
  (result.1.map (fun goals => Alt.br goals binding), result.2)

@[simp] theorem mapAlt_resolveAltsPrepared {Source Target : Type}
    (map : Source → Target) (cs : List Clause) (argsv args : List Atom)
    (res : Atom) (rest : List Goal) (resv : Atom)
    (summary : PersistentSubst.FreshSummary) (binding : Source)
    (dynamic : List String)
    (bc counter : Nat) :
    ((resolveAltsPrepared cs argsv args res rest resv summary dynamic binding bc
        counter).1.map (mapAlt map),
      (resolveAltsPrepared cs argsv args res rest resv summary dynamic binding bc
        counter).2) =
      resolveAltsPrepared cs argsv args res rest resv summary dynamic
        (map binding) bc counter := by
  unfold resolveAltsPrepared
  cases resolveGoalsPrepared cs argsv args res rest resv summary dynamic bc
    counter
  simp [List.map_map, Function.comp_def, mapAlt]

theorem freshenResolutionClauseSummary_eq_reference
    (argsv args : List Atom) (res : Atom) (rest : List Goal)
    (binding : Subst) (qterm : Atom) (seed bc : Nat) (clause : Clause)
    (summary : PersistentSubst.FreshSummary) (dynamic : List String) :
    freshenResolutionClauseSummary summary
        dynamic seed bc clause =
      freshenResolutionClause argsv args res rest binding qterm seed bc
        clause := by
  unfold freshenResolutionClauseSummary freshenResolutionClause
  rfl

theorem resolveAltsPrepared_eq_reference (cs : List Clause)
    (argsv args : List Atom) (res : Atom) (rest : List Goal)
    (binding : Subst) (qterm : Atom) (bc counter : Nat)
    (summary : PersistentSubst.FreshSummary) (dynamic : List String) :
    resolveAltsPrepared cs argsv args res rest (PLeaTTa.subst binding res)
        summary dynamic binding bc counter =
      resolveAlts cs argsv args res rest binding qterm bc counter := by
  let summaryFolder := fun (acc : List (List Goal) × Nat)
      (clause : Clause) =>
    if clause.params.length != argsv.length then acc
    else if !matchCompatList argsv clause.params then acc
    else if !matchCompat (PLeaTTa.subst binding res) clause.result then acc
    else
      let copied := freshenResolutionClauseSummary summary
        dynamic acc.2 bc clause
      let goals := Goal.eq (Atom.expr (args ++ [res]))
          (Atom.expr (copied.params ++ [copied.result])) ::
        copied.body ++ rest
      (goals :: acc.1, acc.2 + 1)
  let referenceFolder := fun (acc : List Alt × Nat) (clause : Clause) =>
    if clause.params.length != argsv.length then acc
    else if !matchCompatList argsv clause.params then acc
    else if !matchCompat (PLeaTTa.subst binding res) clause.result then acc
    else
      let copied := freshenResolutionClause argsv args res rest binding qterm
        acc.2 bc clause
      let goals := Goal.eq (Atom.expr (args ++ [res]))
          (Atom.expr (copied.params ++ [copied.result])) ::
        copied.body ++ rest
      (Alt.br goals binding :: acc.1, acc.2 + 1)
  let liftAcc := fun (acc : List (List Goal) × Nat) =>
    (acc.1.map (fun goals => Alt.br goals binding), acc.2)
  have stepEq : ∀ acc clause,
      liftAcc (summaryFolder acc clause) =
        referenceFolder (liftAcc acc) clause := by
    intro acc clause
    unfold summaryFolder referenceFolder liftAcc
    rw [freshenResolutionClauseSummary_eq_reference argsv args res rest
      binding qterm acc.2 bc clause summary dynamic]
    split <;> try rfl
    split <;> try rfl
    split <;> rfl
  have foldEq : ∀ (clauses : List Clause)
      (acc : List (List Goal) × Nat),
      liftAcc (clauses.foldl summaryFolder acc) =
        clauses.foldl referenceFolder (liftAcc acc) := by
    intro clauses
    induction clauses with
    | nil => intro acc; rfl
    | cons clause tail ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [ih, stepEq]
  let summaryResult := cs.foldl summaryFolder ([], counter)
  let referenceResult := cs.foldl referenceFolder ([], counter)
  have folded : liftAcc summaryResult = referenceResult := by
    simpa [summaryResult, referenceResult, liftAcc] using
      foldEq cs ([], counter)
  have listEq : summaryResult.1.map (fun goals => Alt.br goals binding) =
      referenceResult.1 := by
    exact congrArg Prod.fst folded
  have counterEq : summaryResult.2 = referenceResult.2 := by
    exact congrArg Prod.snd folded
  unfold resolveAltsPrepared resolveGoalsPrepared resolveAlts
  change
    (summaryResult.1.reverse.map (fun goals => Alt.br goals binding),
      summaryResult.2) =
    (referenceResult.1.reverse, referenceResult.2)
  apply Prod.ext
  · simp only [List.map_reverse]
    rw [listEq]
  · exact counterEq

/-- Engine-polymorphic clause construction. The globally seeded resolution
counter makes clause-copy freshness independent of substitution contents. -/
def resolveAltsWith (engine : SubstEngine) (cs : List Clause)
    (argsv args : List Atom) (res : Atom) (rest : List Goal)
    (state : engine.State) (_qterm : Atom) (bc counter : Nat) :
    List (Alt engine.State) × Nat :=
  let resResult := engine.subst state res
  resolveAltsPrepared cs argsv args res rest resResult.1
    PersistentSubst.FreshSummary.empty [] resResult.2 bc counter

theorem resolveAlts_carries (cs : List Clause) (argsv args : List Atom)
    (res : Atom) (rest : List Goal) (binding : Subst) (qterm : Atom)
    (bc counter : Nat) :
    ∀ alt ∈ (resolveAlts cs argsv args res rest binding qterm bc counter).1,
      Carries binding alt := by
  unfold resolveAlts
  dsimp only
  let folder := fun (acc : List Alt × Nat) (clause : Clause) =>
    if clause.params.length != argsv.length then acc
    else if !matchCompatList argsv clause.params then acc
    else if !matchCompat (PLeaTTa.subst binding res) clause.result then acc
    else
      let copied := freshenResolutionClause argsv args res rest binding qterm
        acc.2 bc clause
      let goals := Goal.eq (Atom.expr (args ++ [res]))
        (Atom.expr (copied.params ++ [copied.result])) ::
        copied.body ++ rest
      (Alt.br goals binding :: acc.1, acc.2 + 1)
  have folder_preserves (acc : List Alt × Nat) (clause : Clause)
      (valid : ∀ alt ∈ acc.1, Carries binding alt) :
      ∀ alt ∈ (folder acc clause).1, Carries binding alt := by
    unfold folder
    split <;> try assumption
    split <;> try assumption
    split <;> try assumption
    simp only [List.mem_cons]
    intro alt member
    rcases member with rfl | member
    · rfl
    · exact valid alt member
  have fold_preserves : ∀ (remaining : List Clause) (acc : List Alt × Nat),
      (∀ alt ∈ acc.1, Carries binding alt) →
      ∀ alt ∈ (remaining.foldl folder acc).1, Carries binding alt := by
    intro remaining
    induction remaining with
    | nil => exact fun acc valid => valid
    | cons clause tail ih =>
        intro acc valid
        exact ih (folder acc clause) (folder_preserves acc clause valid)
  intro alt member
  have folded := fold_preserves cs ([], counter) (by simp)
  apply folded alt
  simpa [folder] using member

@[simp] theorem resolveAltsWith_reference (cs : List Clause)
    (argsv args : List Atom) (res : Atom) (rest : List Goal)
    (binding : Subst) (qterm : Atom) (bc counter : Nat) :
    resolveAltsWith reference cs argsv args res rest binding qterm bc counter =
      resolveAlts cs argsv args res rest binding qterm bc counter := by
  unfold resolveAltsWith
  simp only [reference, referenceSubst]
  exact resolveAltsPrepared_eq_reference cs argsv args res rest binding qterm
    bc counter PersistentSubst.FreshSummary.empty []

/-- Convert one prepared child into the uniquely determined shallow metadata
    stored by the mutable-space index. -/
def indexedChildOfPrepared
    (prepared : PersistentSubst.PreparedAtom) : SpaceIndex.IndexedChild :=
  match cacheFound : prepared.exact with
  | none => SpaceIndex.prepareChild prepared.atom
  | some (some key) =>
      { atom := prepared.atom
        closed := true
        exact := some key
        closed_eq := by
          have keyFound : PersistentSubst.atomExactKey prepared.atom =
              some key :=
            (prepared.exact_sound (some key) cacheFound).symm
          exact (PersistentSubst.atomExactKey_some_atomClosed
            prepared.atom key keyFound).symm
        exact_eq := by
          have sound := prepared.exact_sound (some key) cacheFound
          exact sound.trans
            (SpaceIndex.exactKey_eq_atomExactKey prepared.atom).symm }
  | some none =>
      { atom := prepared.atom
        closed := PersistentSubst.atomClosed prepared.atom
        exact := none
        closed_eq := rfl
        exact_eq := by
          have sound := prepared.exact_sound none cacheFound
          exact sound.trans
            (SpaceIndex.exactKey_eq_atomExactKey prepared.atom).symm }

@[simp] theorem indexedChildOfPrepared_atom
    (prepared : PersistentSubst.PreparedAtom) :
    (indexedChildOfPrepared prepared).atom = prepared.atom := by
  unfold indexedChildOfPrepared
  split <;> rfl

/-- Recover immediate child metadata from an already prepared expression.
    Pointer-fast child agreement is checked before using it; malformed or
    summary-only inputs take the canonical structural preparation path. -/
def indexedChildrenOfPrepared : PersistentSubst.PreparedAtom →
    List SpaceIndex.IndexedChild
  | prepared@(.expr (.expr atoms) children _ _ _) =>
      if PersistentSubst.PreparedAtom.sameAtoms children atoms then
        children.map indexedChildOfPrepared
      else
        SpaceIndex.prepareChildren prepared.atom
  | prepared => SpaceIndex.prepareChildren prepared.atom

theorem indexedChildrenOfPrepared_eq
    (prepared : PersistentSubst.PreparedAtom) :
    indexedChildrenOfPrepared prepared =
      SpaceIndex.prepareChildren prepared.atom := by
  cases prepared with
  | summary atom cachedVariables exact exactSound => rfl
  | expr atom children cachedVariables exact exactSound =>
      cases atom with
      | sym symbol | var symbol | gnd symbol => rfl
      | expr atoms =>
          by_cases equal :
              PersistentSubst.PreparedAtom.sameAtoms children atoms = true
          · simp only [indexedChildrenOfPrepared, equal, if_true]
            have atomsEqual :=
              PersistentSubst.PreparedAtom.sameAtoms_eq_true equal
            change children.map indexedChildOfPrepared =
              atoms.map SpaceIndex.prepareChild
            rw [← atomsEqual, List.map_map]
            apply List.map_congr_left
            intro child member
            simpa [Function.comp_def] using
              (SpaceIndex.prepareChild_atom_eq
                (indexedChildOfPrepared child)).symm
          · simp [indexedChildrenOfPrepared, equal]

/-- A successfully decoded prepared chain carries the proof that its logical
    items erase to the ordinary `chainListM` view.  Runtime code can therefore
    reuse item metadata without changing the canonical space index. -/
structure PreparedChainItems
    (root : PersistentSubst.PreparedAtom) where
  items : List PersistentSubst.PreparedAtom
  sound : chainListM root.atom =
    some (items.map PersistentSubst.PreparedAtom.atom)

private structure PreparedChainView (atom : Atom) where
  items : List PersistentSubst.PreparedAtom
  sound : chainListM atom =
    some (items.map PersistentSubst.PreparedAtom.atom)

/-- Follow only the raw `#c` spine while checking that prepared child
    metadata remains aligned.  Well-founded recursion uses the raw tail as
    its decreasing argument; unlike explicit `atom.size` fuel, the measure is
    proof-only and does not traverse every growing logical item at runtime. -/
private def preparedChainView? (atom : Atom)
    (prepared : PersistentSubst.PreparedAtom) :
    Option (PreparedChainView atom) :=
  match atom, prepared.children with
  | .sym "#nil", _ =>
      some
        { items := []
          sound := rfl }
  | .expr [.sym "#c", headAtom, tailAtom],
      [markerPrepared, headPrepared, tailPrepared] =>
      if aligned : PersistentSubst.PreparedAtom.sameAtoms
          [markerPrepared, headPrepared, tailPrepared]
          [.sym "#c", headAtom, tailAtom] then
        match preparedChainView? tailAtom tailPrepared with
        | none => none
        | some tailItems =>
            some
              { items := headPrepared :: tailItems.items
                sound := by
                  have atomsEqual :=
                    PersistentSubst.PreparedAtom.sameAtoms_eq_true aligned
                  simp only [List.map_cons, List.map_nil,
                    List.cons.injEq] at atomsEqual
                  simp only [chainListM]
                  rw [tailItems.sound]
                  simp [atomsEqual.2.1] }
      else none
  | _, _ => none
termination_by atom.size
decreasing_by
  simp [Atom.size]
  omega

/-- Prepared logical chain items, when their metadata is available and
    structurally aligned with the raw atom. -/
def preparedChainItems?
    (prepared : PersistentSubst.PreparedAtom) :
    Option (PreparedChainItems prepared) :=
  match preparedChainView? prepared.atom prepared with
  | none => none
  | some view => some { items := view.items, sound := view.sound }

/-- Build canonical logical-item metadata from prepared substitution output.
    The fast branch traverses just the chain spine and reuses each logical
    item's certified exact-key cache. -/
def indexedItemsOfPrepared
    (prepared : PersistentSubst.PreparedAtom) :
    List SpaceIndex.IndexedChild :=
  match preparedChainItems? prepared with
  | some chain => chain.items.map indexedChildOfPrepared
  | none => SpaceIndex.prepareItems prepared.atom

theorem indexedItemsOfPrepared_eq
    (prepared : PersistentSubst.PreparedAtom) :
    indexedItemsOfPrepared prepared =
      SpaceIndex.prepareItems prepared.atom := by
  unfold indexedItemsOfPrepared
  split
  · rename_i chain found
    unfold SpaceIndex.prepareItems
    rw [chain.sound]
    simp only [Option.getD_some]
    rw [List.map_map]
    apply List.map_congr_left
    intro child member
    simpa [Function.comp_def] using
      (SpaceIndex.prepareChild_atom_eq
        (indexedChildOfPrepared child)).symm
  · rfl

/-- Convert an intrinsically certified exact-key cache into insertion metadata.
Unknown summaries use the ordinary one-time index preparation path. -/
def indexedAtomOfPrepared
    (prepared : PersistentSubst.PreparedAtom) : SpaceIndex.IndexedAtom :=
  match cacheFound : prepared.exact with
  | none => SpaceIndex.prepareAtom prepared.atom
  | some (some key) =>
      { atom := prepared.atom
        closed := true
        exact := some key
        children := indexedChildrenOfPrepared prepared
        items := indexedItemsOfPrepared prepared
        closed_eq := by
          have keyFound : PersistentSubst.atomExactKey prepared.atom =
              some key :=
            (prepared.exact_sound (some key) cacheFound).symm
          exact (PersistentSubst.atomExactKey_some_atomClosed
            prepared.atom key keyFound).symm
        exact_eq := by
          have sound := prepared.exact_sound (some key) cacheFound
          exact sound.trans
            (SpaceIndex.exactKey_eq_atomExactKey prepared.atom).symm
        children_eq := indexedChildrenOfPrepared_eq prepared
        items_eq := indexedItemsOfPrepared_eq prepared }
  | some none =>
      { atom := prepared.atom
        closed := PersistentSubst.atomClosed prepared.atom
        exact := none
        children := indexedChildrenOfPrepared prepared
        items := indexedItemsOfPrepared prepared
        closed_eq := rfl
        exact_eq := by
          have sound := prepared.exact_sound none cacheFound
          exact sound.trans
            (SpaceIndex.exactKey_eq_atomExactKey prepared.atom).symm
        children_eq := indexedChildrenOfPrepared_eq prepared
        items_eq := indexedItemsOfPrepared_eq prepared }

@[simp] theorem indexedAtomOfPrepared_atom
    (prepared : PersistentSubst.PreparedAtom) :
    (indexedAtomOfPrepared prepared).atom = prepared.atom := by
  unfold indexedAtomOfPrepared
  split <;> rfl

def renameIndexedAtomSuffix (suffix : String)
    (prepared : SpaceIndex.IndexedAtom) : Atom :=
  if prepared.closed then prepared.atom
  else renameAtomSuffix suffix prepared.atom

@[simp] theorem renameIndexedAtomSuffix_prepareAtom (suffix : String)
    (atom : Atom) :
    renameIndexedAtomSuffix suffix (SpaceIndex.prepareAtom atom) =
    renameAtomSuffixShared suffix atom := by
  rfl

/-- Turn deterministic indexed child metadata back into a valid prepared
    summary without rescanning the child atom. -/
def preparedAtomOfIndexedChild (child : SpaceIndex.IndexedChild) :
    PersistentSubst.PreparedAtom :=
  .summary child.atom (if child.closed then [] else child.atom.vars)
    (some child.exact) (by
      intro result found
      have resultEq : result = child.exact :=
        (Option.some.inj found).symm
      calc
        result = child.exact := resultEq
        _ = SpaceIndex.exactKey child.atom := child.exact_eq
        _ = PersistentSubst.atomExactKey child.atom :=
          SpaceIndex.exactKey_eq_atomExactKey child.atom)

@[simp] theorem preparedAtomOfIndexedChild_atom
    (child : SpaceIndex.IndexedChild) :
    (preparedAtomOfIndexedChild child).atom = child.atom := rfl

theorem preparedAtomOfIndexedChild_valid
    (child : SpaceIndex.IndexedChild) :
    (preparedAtomOfIndexedChild child).Valid := by
  unfold preparedAtomOfIndexedChild
  apply PersistentSubst.PreparedAtom.Valid.cached
  split
  next closed =>
    exact ((PersistentSubst.atomClosed_eq_true_iff_vars_nil child.atom).mp
      (by rw [← child.closed_eq]; exact closed)).symm
  next _ => rfl

/-- Rebuild a prepared internal chain from its indexed logical items.  Each
    element retains the exact-key metadata certified when the atom entered the
    mutable space. -/
def preparedChainOfIndexedItems : List SpaceIndex.IndexedChild →
    PersistentSubst.PreparedAtom
  | [] => PersistentSubst.PreparedAtom.ofAtom nilA
  | item :: rest =>
      PersistentSubst.PreparedAtom.mkExpr
        [PersistentSubst.PreparedAtom.ofAtom (.sym "#c"),
          preparedAtomOfIndexedChild item,
          preparedChainOfIndexedItems rest]

@[simp] theorem preparedChainOfIndexedItems_atom
    (items : List SpaceIndex.IndexedChild) :
    (preparedChainOfIndexedItems items).atom =
      chainOf (items.map SpaceIndex.IndexedChild.atom) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      change Atom.expr [Atom.sym "#c",
          (preparedAtomOfIndexedChild item).atom,
          (preparedChainOfIndexedItems rest).atom] =
        Atom.expr [Atom.sym "#c", item.atom,
          chainOf (rest.map SpaceIndex.IndexedChild.atom)]
      rw [preparedAtomOfIndexedChild_atom, ih]

theorem preparedChainOfIndexedItems_valid :
    ∀ items : List SpaceIndex.IndexedChild,
      (preparedChainOfIndexedItems items).Valid
  | [] => PersistentSubst.PreparedAtom.ofAtom_valid nilA
  | item :: rest => by
      apply PersistentSubst.PreparedAtom.mkExpr_valid
      intro child member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact PersistentSubst.PreparedAtom.ofAtom_valid (.sym "#c")
      · exact preparedAtomOfIndexedChild_valid item
      · exact preparedChainOfIndexedItems_valid rest

/-- Reconstruct a prepared candidate with cached immediate children when the
    atom is not a complete PeTTa chain. -/
def preparedAtomOfIndexedShallow (prepared : SpaceIndex.IndexedAtom) :
    PersistentSubst.PreparedAtom :=
  match prepared.atom with
  | .expr _ => PersistentSubst.PreparedAtom.mkExpr
      (prepared.children.map preparedAtomOfIndexedChild)
  | _ => preparedAtomOfIndexedChild
      { atom := prepared.atom
        closed := prepared.closed
        exact := prepared.exact
        closed_eq := prepared.closed_eq
        exact_eq := prepared.exact_eq }

@[simp] theorem preparedAtomOfIndexedShallow_atom
    (prepared : SpaceIndex.IndexedAtom) :
    (preparedAtomOfIndexedShallow prepared).atom = prepared.atom := by
  rcases prepared with
    ⟨atom, closed, exact, children, items, closedEq, exactEq, childrenEq,
      itemsEq⟩
  subst closed
  subst exact
  subst children
  subst items
  cases atom <;>
    simp [preparedAtomOfIndexedShallow, SpaceIndex.prepareChildren,
      preparedAtomOfIndexedChild, SpaceIndex.prepareChild,
      PersistentSubst.PreparedAtom.mkExpr,
      PersistentSubst.PreparedAtom.atom,
      Function.comp_def]

theorem preparedAtomOfIndexedShallow_valid
    (prepared : SpaceIndex.IndexedAtom) :
    (preparedAtomOfIndexedShallow prepared).Valid := by
  unfold preparedAtomOfIndexedShallow
  split
  next atoms equality =>
    apply PersistentSubst.PreparedAtom.mkExpr_valid
    intro child member
    rcases List.mem_map.mp member with ⟨indexed, _, rfl⟩
    exact preparedAtomOfIndexedChild_valid indexed
  next => exact preparedAtomOfIndexedChild_valid _

/-- Reconstruct a prepared candidate from the canonical space metadata.  A
    complete internal chain uses logical-item metadata; all other atoms retain
    the verified shallow reconstruction path. -/
def preparedAtomOfIndexed (prepared : SpaceIndex.IndexedAtom) :
    PersistentSubst.PreparedAtom :=
  match chainListM prepared.atom with
  | some _ => preparedChainOfIndexedItems prepared.items
  | none => preparedAtomOfIndexedShallow prepared

@[simp] theorem preparedAtomOfIndexed_atom
    (prepared : SpaceIndex.IndexedAtom) :
    (preparedAtomOfIndexed prepared).atom = prepared.atom := by
  cases parsed : chainListM prepared.atom with
  | none =>
      simp [preparedAtomOfIndexed, parsed]
  | some atoms =>
      simp only [preparedAtomOfIndexed, parsed,
        preparedChainOfIndexedItems_atom]
      have itemsAtoms :
          prepared.items.map SpaceIndex.IndexedChild.atom = atoms := by
        rw [prepared.items_eq]
        simp [SpaceIndex.prepareItems, parsed, Function.comp_def]
      rw [itemsAtoms]
      exact (chainListM_sound prepared.atom atoms parsed).symm

theorem preparedAtomOfIndexed_valid
    (prepared : SpaceIndex.IndexedAtom) :
    (preparedAtomOfIndexed prepared).Valid := by
  unfold preparedAtomOfIndexed
  split
  · exact preparedChainOfIndexedItems_valid _
  · exact preparedAtomOfIndexedShallow_valid prepared

/-- Reuse exact/closed metadata already certified by the mutable-space
index.  Atoms outside the exact-key fragment simply take the ordinary path. -/
def closedRootOfIndexed (prepared : SpaceIndex.IndexedAtom) :
    Option PersistentSubst.ClosedRoot :=
  match exactFound : prepared.exact with
  | none => none
  | some key =>
      let exact : PersistentSubst.atomExactKey prepared.atom = some key := by
        rw [← SpaceIndex.exactKey_eq_atomExactKey prepared.atom]
        rw [← prepared.exact_eq]
        exact exactFound
      some
        { atom := prepared.atom
          key := key
          closed :=
            (PersistentSubst.atomClosed_eq_true_iff_vars_nil
              prepared.atom).mp
              (PersistentSubst.atomExactKey_some_atomClosed
                prepared.atom key exact)
          exact := exact
          prepared := preparedAtomOfIndexed prepared
          prepared_valid := preparedAtomOfIndexed_valid prepared
          prepared_atom := preparedAtomOfIndexed_atom prepared }

def smatchBranchState (engine : SubstEngine) (state : engine.State)
    (prepared : SpaceIndex.IndexedAtom) : engine.State :=
  match closedRootOfIndexed prepared with
  | none => state
  | some root => engine.rememberClosed state root

theorem smatchBranchState_denote (engine : SubstEngine)
    (state : engine.State) (prepared : SpaceIndex.IndexedAtom) :
    engine.denote (smatchBranchState engine state prepared) =
      engine.denote state := by
  unfold smatchBranchState
  split
  · rfl
  · exact engine.rememberClosed_denote state _

theorem smatchBranchState_valid (engine : SubstEngine)
    (state : engine.State) (prepared : SpaceIndex.IndexedAtom)
    (valid : engine.Valid state) :
    engine.Valid (smatchBranchState engine state prepared) := by
  unfold smatchBranchState
  split
  · exact valid
  · exact engine.rememberClosed_valid state _ valid

@[simp] theorem smatchBranchState_reference (state : Subst)
    (prepared : SpaceIndex.IndexedAtom) :
    smatchBranchState reference state prepared = state := by
  unfold smatchBranchState
  split <;> rfl

def smatchGoalsPrepared (w : PWorld) (counter : Nat) (space query : Atom)
    (queryPattern : Atom) (rest : List Goal) : List (List Goal) × Nat :=
  let suffix := resolutionCompactSuffix counter
  let revGoals := (w.preparedAtomCandidates space query).foldl
    (fun (acc : List (List Goal)) prepared =>
      let renamed := renameIndexedAtomSuffix suffix prepared
      if matchCompat query renamed then
        (Goal.eq queryPattern renamed :: rest) :: acc
      else
        acc)
    []
  (revGoals.reverse,
    counter + max (w.atomsOf space).length
      (w.atomCandidates space query).length)

def smatchAltsPrepared {Binding : Type} (w : PWorld) (counter : Nat)
    (binding : Binding) (space query queryPattern : Atom)
    (rest : List Goal) : List (Alt Binding) × Nat :=
  let suffix := resolutionCompactSuffix counter
  let revAlts := (w.preparedAtomCandidates space query).foldl
    (fun (acc : List (Alt Binding)) prepared =>
      let renamed := renameIndexedAtomSuffix suffix prepared
      if matchCompat query renamed then
        Alt.br (Goal.eq queryPattern renamed :: rest) binding :: acc
      else
        acc)
    []
  (revAlts.reverse,
    counter + max (w.atomsOf space).length
      (w.atomCandidates space query).length)

/-- Engine-aware mutable-space alternatives.  Each branch retains the
indexed candidate's closed root for the immediately following equality
goal; the cache changes no substitution denotation. -/
def smatchAltsPreparedWith (engine : SubstEngine) (w : PWorld)
    (counter : Nat) (state : engine.State) (space query queryPattern : Atom)
    (rest : List Goal) : List (Alt engine.State) × Nat :=
  let suffix := resolutionCompactSuffix counter
  let revAlts := (w.preparedAtomCandidates space query).foldl
    (fun (acc : List (Alt engine.State)) prepared =>
      let renamed := renameIndexedAtomSuffix suffix prepared
      if matchCompat query renamed then
        Alt.br (Goal.eq queryPattern renamed :: rest)
          (smatchBranchState engine state prepared) :: acc
      else
        acc)
    []
  (revAlts.reverse,
    counter + max (w.atomsOf space).length
      (w.atomCandidates space query).length)

theorem smatchAltsPreparedWith_erase (engine : SubstEngine) (w : PWorld)
    (counter : Nat) (state : engine.State) (space query queryPattern : Atom)
    (rest : List Goal) :
    ((smatchAltsPreparedWith engine w counter state space query queryPattern
          rest).1.map (mapAlt engine.denote),
      (smatchAltsPreparedWith engine w counter state space query queryPattern
          rest).2) =
      smatchAltsPrepared w counter (engine.denote state) space query
        queryPattern rest := by
  unfold smatchAltsPreparedWith smatchAltsPrepared
  let sourceFolder := fun (acc : List (Alt engine.State))
      (prepared : SpaceIndex.IndexedAtom) =>
    let renamed := renameIndexedAtomSuffix
      (resolutionCompactSuffix counter) prepared
    if matchCompat query renamed then
      Alt.br (Goal.eq queryPattern renamed :: rest)
        (smatchBranchState engine state prepared) :: acc
    else acc
  let targetFolder := fun (acc : List Alt)
      (prepared : SpaceIndex.IndexedAtom) =>
    let renamed := renameIndexedAtomSuffix
      (resolutionCompactSuffix counter) prepared
    if matchCompat query renamed then
      Alt.br (Goal.eq queryPattern renamed :: rest) (engine.denote state) :: acc
    else acc
  have foldMap : ∀ (prepared : List SpaceIndex.IndexedAtom)
      (acc : List (Alt engine.State)),
      (prepared.foldl sourceFolder acc).map (mapAlt engine.denote) =
        prepared.foldl targetFolder (acc.map (mapAlt engine.denote)) := by
    intro prepared
    induction prepared with
    | nil => intro acc; rfl
    | cons atom tail ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [ih]
        have step :
            (sourceFolder acc atom).map (mapAlt engine.denote) =
              targetFolder (acc.map (mapAlt engine.denote)) atom := by
          unfold sourceFolder targetFolder
          dsimp only
          split
          · simp [mapAlt, smatchBranchState_denote]
          · rfl
        rw [step]
  apply Prod.ext
  · rw [List.map_reverse, foldMap]
    rfl
  · rfl

theorem smatchAltsPreparedWith_valid (engine : SubstEngine) (w : PWorld)
    (counter : Nat) (state : engine.State) (space query queryPattern : Atom)
    (rest : List Goal) (valid : engine.Valid state) :
    ∀ alt ∈ (smatchAltsPreparedWith engine w counter state space query
      queryPattern rest).1, AltValid engine alt := by
  unfold smatchAltsPreparedWith
  let folder := fun (acc : List (Alt engine.State))
      (prepared : SpaceIndex.IndexedAtom) =>
    let renamed := renameIndexedAtomSuffix
      (resolutionCompactSuffix counter) prepared
    if matchCompat query renamed then
      Alt.br (Goal.eq queryPattern renamed :: rest)
        (smatchBranchState engine state prepared) :: acc
    else acc
  have foldValid : ∀ (prepared : List SpaceIndex.IndexedAtom)
      (acc : List (Alt engine.State)),
      (∀ alt ∈ acc, AltValid engine alt) →
      ∀ alt ∈ prepared.foldl folder acc, AltValid engine alt := by
    intro prepared
    induction prepared with
    | nil => intro acc hvalid; exact hvalid
    | cons atom tail ih =>
        intro acc hvalid
        apply ih
        unfold folder
        dsimp only
        split
        · intro alt member
          rcases List.mem_cons.mp member with rfl | member
          · exact smatchBranchState_valid engine state atom valid
          · exact hvalid alt member
        · exact hvalid
  intro alt member
  have forward : alt ∈
      (w.preparedAtomCandidates space query).foldl folder [] := by
    simpa using member
  exact foldValid (w.preparedAtomCandidates space query) [] (by simp)
    alt forward

@[simp] theorem smatchAltsPreparedWith_reference (w : PWorld)
    (counter : Nat) (binding : Subst) (space query queryPattern : Atom)
    (rest : List Goal) :
    smatchAltsPreparedWith reference w counter binding space query
        queryPattern rest =
      smatchAltsPrepared w counter binding space query queryPattern rest := by
  unfold smatchAltsPreparedWith smatchAltsPrepared
  simp only [smatchBranchState_reference]
  rfl

@[simp] theorem mapAlt_smatchAltsPrepared {Source Target : Type}
    (map : Source → Target) (w : PWorld) (counter : Nat)
    (binding : Source) (space query queryPattern : Atom)
    (rest : List Goal) :
    ((smatchAltsPrepared w counter binding space query queryPattern rest).1.map
        (mapAlt map),
      (smatchAltsPrepared w counter binding space query queryPattern rest).2) =
      smatchAltsPrepared w counter (map binding) space query queryPattern
        rest := by
  unfold smatchAltsPrepared
  let folderSource := fun (acc : List (Alt Source))
      (prepared : SpaceIndex.IndexedAtom) =>
    let renamed := renameIndexedAtomSuffix
      (resolutionCompactSuffix counter) prepared
    if matchCompat query renamed then
      Alt.br (Goal.eq queryPattern renamed :: rest) binding :: acc
    else acc
  let folderTarget := fun (acc : List (Alt Target))
      (prepared : SpaceIndex.IndexedAtom) =>
    let renamed := renameIndexedAtomSuffix
      (resolutionCompactSuffix counter) prepared
    if matchCompat query renamed then
      Alt.br (Goal.eq queryPattern renamed :: rest) (map binding) :: acc
    else acc
  have foldMap : ∀ (prepared : List SpaceIndex.IndexedAtom)
      (acc : List (Alt Source)),
      (prepared.foldl folderSource acc).map (mapAlt map) =
        prepared.foldl folderTarget (acc.map (mapAlt map)) := by
    intro prepared
    induction prepared with
    | nil => intro acc; rfl
    | cons atom tail ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [ih]
        have step : (folderSource acc atom).map (mapAlt map) =
            folderTarget (acc.map (mapAlt map)) atom := by
          unfold folderSource folderTarget
          dsimp only
          split <;> simp [mapAlt]
        rw [step]
  apply Prod.ext
  · rw [List.map_reverse, foldMap]
    rfl
  · rfl

/-- Engine-polymorphic mutable-space matching. Both query operands are read
through the selected substitution engine and every alternative shares the
resulting persistent state; no list-denotation round trip occurs. -/
def smatchAltsWith (engine : SubstEngine) (w : PWorld) (counter : Nat)
    (state : engine.State) (pat : Atom) (rest : List Goal) (_qterm : Atom) :
    List (Alt engine.State) × Nat :=
  match spacePatView pat with
  | (spacePattern, queryPattern) =>
      let queryResult := engine.subst state queryPattern
      let spaceResult := engine.subst queryResult.2 spacePattern
      smatchAltsPreparedWith engine w counter spaceResult.2 spaceResult.1
        queryResult.1 queryPattern rest

theorem smatchAltsPrepared_eq_reference (w : PWorld) (counter : Nat)
    (binding : Subst) (pat : Atom) (rest : List Goal) (qterm : Atom) :
    (match spacePatView pat with
      | (spacePattern, queryPattern) =>
          smatchAltsPrepared w counter binding
            (PLeaTTa.subst binding spacePattern)
            (PLeaTTa.subst binding queryPattern) queryPattern rest) =
      smatchAlts w counter binding pat rest qterm := by
  unfold smatchAlts
  rcases view : spacePatView pat with ⟨spacePattern, queryPattern⟩
  simp only
  let query := PLeaTTa.subst binding queryPattern
  let space := PLeaTTa.subst binding spacePattern
  let suffix := resolutionCompactSuffix counter
  let altFolder := fun (acc : List Alt) (atom : Atom) =>
    let renamed := renameAtomSuffixShared suffix atom
    if matchCompat query renamed then
      Alt.br (Goal.eq queryPattern renamed :: rest) binding :: acc
    else
      acc
  unfold smatchAltsPrepared
  rw [w.preparedAtomCandidates_eq space query]
  simp only [List.foldl_map, renameIndexedAtomSuffix_prepareAtom]
  change
    (((w.atomCandidates space query).foldl altFolder []).reverse,
      counter + max (w.atomsOf space).length
        (w.atomCandidates space query).length) =
    (((w.atomCandidates space query).foldl altFolder []).reverse,
      counter + max (w.atomsOf space).length
        (w.atomCandidates space query).length)
  rfl

theorem smatchAlts_carries (w : PWorld) (counter : Nat)
    (binding : Subst) (pat : Atom) (rest : List Goal) (qterm : Atom) :
    ∀ alt ∈ (smatchAlts w counter binding pat rest qterm).1,
      Carries binding alt := by
  unfold smatchAlts
  rcases view : spacePatView pat with ⟨spacePattern, queryPattern⟩
  simp only
  let query := PLeaTTa.subst binding queryPattern
  let space := PLeaTTa.subst binding spacePattern
  let suffix := resolutionFreshSuffix [query] queryPattern rest binding qterm
    counter
  let folder := fun (acc : List Alt) (atom : Atom) =>
    let renamed := renameAtomSuffixShared suffix atom
    if matchCompat query renamed then
      Alt.br (Goal.eq queryPattern renamed :: rest) binding :: acc
    else acc
  have folder_preserves (acc : List Alt) (atom : Atom)
      (valid : ∀ alt ∈ acc, Carries binding alt) :
      ∀ alt ∈ folder acc atom, Carries binding alt := by
    change ∀ alt ∈
      (if matchCompat query (renameAtomSuffixShared suffix atom) then
        Alt.br (Goal.eq queryPattern (renameAtomSuffixShared suffix atom) :: rest)
          binding :: acc
       else acc), Carries binding alt
    split
    · simp only [List.mem_cons]
      intro alt member
      rcases member with rfl | member
      · rfl
      · exact valid alt member
    · exact valid
  have fold_preserves : ∀ (atoms : List Atom) (acc : List Alt),
      (∀ alt ∈ acc, Carries binding alt) →
      ∀ alt ∈ atoms.foldl folder acc, Carries binding alt := by
    intro atoms
    induction atoms with
    | nil => exact fun acc valid => valid
    | cons atom tail ih =>
        intro acc valid
        exact ih (folder acc atom) (folder_preserves acc atom valid)
  intro alt member
  have folded := fold_preserves (w.atomCandidates space query) [] (by simp)
  apply folded alt
  simpa [folder, query, space, suffix, view] using member

@[simp] theorem smatchAltsWith_reference (w : PWorld) (counter : Nat)
    (binding : Subst) (pat : Atom) (rest : List Goal) (qterm : Atom) :
    smatchAltsWith reference w counter binding pat rest qterm =
      smatchAlts w counter binding pat rest qterm := by
  rcases view : spacePatView pat with ⟨spacePattern, queryPattern⟩
  unfold smatchAltsWith
  rw [view]
  dsimp only
  rw [show reference.subst binding queryPattern =
      (PLeaTTa.subst binding queryPattern, binding) from rfl]
  dsimp only
  rw [show reference.subst binding spacePattern =
      (PLeaTTa.subst binding spacePattern, binding) from rfl]
  dsimp only
  rw [smatchAltsPreparedWith_reference]
  have referenceEq := smatchAltsPrepared_eq_reference w counter binding pat
    rest qterm
  rw [view] at referenceEq
  exact referenceEq

def unionReverseAltsWith (engine : SubstEngine) (args : List Atom)
    (res : Atom) (rest : List Goal) (state : engine.State) :
    Option (List (Alt engine.State)) :=
  let result := engine.subst state res
  (unionReverseAlts args res rest (engine.denote result.2)).map
    (rebindAlts result.2)

/-- Guard the only denotation-dependent builtin alternative builder before
calling it. Ordinary builtins therefore stay entirely on the persistent
lookup path. -/
def unionReverseAltsWithForOp (engine : SubstEngine) (op : String)
    (args : List Atom) (res : Atom) (rest : List Goal)
    (state : engine.State) : Option (List (Alt engine.State)) :=
  if op == "union-atom" then
    unionReverseAltsWith engine args res rest state
  else none

theorem unionReverseAlts_carries (args : List Atom) (res : Atom)
    (rest : List Goal) (binding : Subst) :
    ∀ alts, unionReverseAlts args res rest binding = some alts →
      ∀ alt ∈ alts, Carries binding alt := by
  intro alts equality
  unfold unionReverseAlts at equality
  split at equality
  next xs ys zs chainEquality =>
    simp only [Option.some.injEq] at equality
    subst alts
    intro alt member
    rw [List.mem_map] at member
    rcases member with ⟨split, _, rfl⟩
    rfl
  next => contradiction

@[simp] theorem unionReverseAltsWith_reference (args : List Atom)
    (res : Atom) (rest : List Goal) (binding : Subst) :
    unionReverseAltsWith reference args res rest binding =
      unionReverseAlts args res rest binding := by
  unfold unionReverseAltsWith
  simp only [reference, referenceSubst, id_eq]
  cases result : unionReverseAlts args res rest binding with
  | none => rfl
  | some alts =>
      change some (rebindAlts binding alts) = some alts
      exact congrArg some (rebindAlts_eq_self_of_forall binding alts
        (unionReverseAlts_carries args res rest binding alts result))

@[simp] theorem unionReverseAltsWithForOp_reference (op : String)
    (args : List Atom) (res : Atom) (rest : List Goal) (binding : Subst) :
    unionReverseAltsWithForOp reference op args res rest binding =
      unionReverseAltsForOp op args res rest binding := by
  unfold unionReverseAltsWithForOp unionReverseAltsForOp
  split
  · exact unionReverseAltsWith_reference args res rest binding
  · rfl

theorem resolveAltsWith_erase (engine : SubstEngine) (cs : List Clause)
    (argsv args : List Atom) (res : Atom) (rest : List Goal)
    (state : engine.State) (qterm : Atom) (bc counter : Nat)
    (valid : engine.Valid state) :
    ((resolveAltsWith engine cs argsv args res rest state qterm bc counter).1.map
        (mapAlt engine.denote),
      (resolveAltsWith engine cs argsv args res rest state qterm bc counter).2) =
      resolveAlts cs argsv args res rest (engine.denote state) qterm bc
        counter := by
  have nextValid := engine.subst_valid state res valid
  have valueEq := engine.subst_value state res valid
  have nextDenote := engine.subst_denote state res valid
  cases result : engine.subst state res with
  | mk value next =>
      simp only [result] at nextValid valueEq nextDenote
      have valueEqNext : value = PLeaTTa.subst (engine.denote next) res := by
        rw [nextDenote]
        exact valueEq
      simp only [resolveAltsWith, result]
      rw [mapAlt_resolveAltsPrepared]
      rw [valueEqNext]
      rw [resolveAltsPrepared_eq_reference cs argsv args res rest
        (engine.denote next) qterm bc counter _ _]
      rw [nextDenote]

theorem resolveAltsWith_valid (engine : SubstEngine) (cs : List Clause)
    (argsv args : List Atom) (res : Atom) (rest : List Goal)
    (state : engine.State) (qterm : Atom) (bc counter : Nat)
    (valid : engine.Valid state) :
    ∀ alt ∈
      (resolveAltsWith engine cs argsv args res rest state qterm bc counter).1,
      AltValid engine alt := by
  have nextValid := engine.subst_valid state res valid
  cases result : engine.subst state res with
  | mk value next =>
      simp only [result] at nextValid
      simp only [resolveAltsWith, result, resolveAltsPrepared,
        List.mem_map]
      intro alt member
      rcases member with ⟨goals, _, rfl⟩
      exact nextValid

theorem smatchAltsWith_erase (engine : SubstEngine) (w : PWorld)
    (counter : Nat) (state : engine.State) (pat : Atom)
    (rest : List Goal) (qterm : Atom) (valid : engine.Valid state) :
    ((smatchAltsWith engine w counter state pat rest qterm).1.map
        (mapAlt engine.denote),
      (smatchAltsWith engine w counter state pat rest qterm).2) =
      smatchAlts w counter (engine.denote state) pat rest qterm := by
  rcases view : spacePatView pat with ⟨spacePattern, queryPattern⟩
  have queryValid := engine.subst_valid state queryPattern valid
  have queryValue := engine.subst_value state queryPattern valid
  have queryDenote := engine.subst_denote state queryPattern valid
  cases queryResult : engine.subst state queryPattern with
  | mk query queryState =>
      simp only [queryResult] at queryValid queryValue queryDenote
      have spaceValue := engine.subst_value queryState spacePattern queryValid
      have spaceDenote := engine.subst_denote queryState spacePattern queryValid
      cases spaceResult : engine.subst queryState spacePattern with
      | mk space spaceState =>
          simp only [spaceResult] at spaceValue spaceDenote
          simp only [smatchAltsWith, view, queryResult, spaceResult]
          rw [smatchAltsPreparedWith_erase]
          rw [spaceValue, queryValue, spaceDenote, queryDenote]
          have referenceEq := smatchAltsPrepared_eq_reference w counter
            (engine.denote state) pat rest qterm
          rw [view] at referenceEq
          exact referenceEq

theorem smatchAltsWith_valid (engine : SubstEngine) (w : PWorld)
    (counter : Nat) (state : engine.State) (pat : Atom)
    (rest : List Goal) (qterm : Atom) (valid : engine.Valid state) :
    ∀ alt ∈ (smatchAltsWith engine w counter state pat rest qterm).1,
      AltValid engine alt := by
  rcases view : spacePatView pat with ⟨spacePattern, queryPattern⟩
  have queryValid := engine.subst_valid state queryPattern valid
  cases queryResult : engine.subst state queryPattern with
  | mk query queryState =>
      simp only [queryResult] at queryValid
      have spaceValid := engine.subst_valid queryState spacePattern queryValid
      cases spaceResult : engine.subst queryState spacePattern with
      | mk space spaceState =>
          simp only [spaceResult] at spaceValid
          simp only [smatchAltsWith, view, queryResult, spaceResult]
          exact smatchAltsPreparedWith_valid engine w counter spaceState
            space query queryPattern rest spaceValid

theorem unionReverseAltsWith_erase (engine : SubstEngine)
    (args : List Atom) (res : Atom) (rest : List Goal)
    (state : engine.State) (valid : engine.Valid state) :
    (unionReverseAltsWith engine args res rest state).map
        (List.map (mapAlt engine.denote)) =
      unionReverseAlts args res rest (engine.denote state) := by
  have nextDenote := engine.subst_denote state res valid
  cases result : engine.subst state res with
  | mk value next =>
      simp only [result] at nextDenote
      simp only [unionReverseAltsWith, result]
      rw [nextDenote]
      cases referenceResult :
          unionReverseAlts args res rest (engine.denote state) with
      | none => rfl
      | some alts =>
          change some ((rebindAlts next alts).map
            (mapAlt engine.denote)) = some alts
          rw [mapAlt_rebindAlts, nextDenote]
          exact congrArg some (rebindAlts_eq_self_of_forall
            (engine.denote state) alts
            (unionReverseAlts_carries args res rest (engine.denote state)
              alts referenceResult))

theorem unionReverseAltsWith_valid (engine : SubstEngine)
    (args : List Atom) (res : Atom) (rest : List Goal)
    (state : engine.State) (valid : engine.Valid state) :
    ∀ alts, unionReverseAltsWith engine args res rest state = some alts →
      ∀ alt ∈ alts, AltValid engine alt := by
  have nextValid := engine.subst_valid state res valid
  cases result : engine.subst state res with
  | mk value next =>
      simp only [result] at nextValid
      intro alts equality
      simp only [unionReverseAltsWith, result] at equality
      cases referenceResult :
          unionReverseAlts args res rest (engine.denote next) with
      | none => simp [referenceResult] at equality
      | some referenceAlts =>
          simp only [referenceResult, Option.map_some,
            Option.some.injEq] at equality
          subst alts
          intro alt member
          simp only [rebindAlts, List.mem_map] at member
          rcases member with ⟨referenceAlt, _, rfl⟩
          cases referenceAlt <;> simp [rebindAlt, AltValid, nextValid]

theorem unionReverseAltsWithForOp_erase (engine : SubstEngine)
    (op : String) (args : List Atom) (res : Atom) (rest : List Goal)
    (state : engine.State) (valid : engine.Valid state) :
    (unionReverseAltsWithForOp engine op args res rest state).map
        (List.map (mapAlt engine.denote)) =
      unionReverseAltsForOp op args res rest (engine.denote state) := by
  unfold unionReverseAltsWithForOp unionReverseAltsForOp
  split
  · exact unionReverseAltsWith_erase engine args res rest state valid
  · rfl

theorem unionReverseAltsWithForOp_valid (engine : SubstEngine)
    (op : String) (args : List Atom) (res : Atom) (rest : List Goal)
    (state : engine.State) (valid : engine.Valid state) :
    ∀ alts,
      unionReverseAltsWithForOp engine op args res rest state = some alts →
      ∀ alt ∈ alts, AltValid engine alt := by
  unfold unionReverseAltsWithForOp
  split
  · exact unionReverseAltsWith_valid engine args res rest state valid
  · simp

@[simp] theorem mapAlt_localGetTypeExtensionAlts {Source Target : Type}
    (map : Source → Target) (world : PWorld) (value result : Atom)
    (rest : List Goal) (state : Source) :
    (localGetTypeExtensionAlts world value result rest state).map
        (mapAlt map) =
      localGetTypeExtensionAlts world value result rest (map state) := by
  unfold localGetTypeExtensionAlts
  split <;> simp [mapAlt]

theorem localGetTypeExtensionAlts_valid (engine : SubstEngine)
    (world : PWorld) (value result : Atom) (rest : List Goal)
    (state : engine.State) (stateValid : engine.Valid state) :
    AltsValid engine
      (localGetTypeExtensionAlts world value result rest state) := by
  unfold localGetTypeExtensionAlts
  split
  · simp [AltsValid]
  · exact altsValid_cons engine stateValid (by simp [AltsValid])

theorem mapConf_binResolvedStep {Source Target : Type}
    (map : Source → Target) (gt : GroundingTable) (conf : Conf Source)
    (op : String) (args : List Atom) (res : Atom) (rest : List Goal)
    (state : Source) (av : List Atom) (rv : Atom)
    (allGround : Bool)
    (advanceResults : List Atom → Nat)
    (grounded : Unit → ReduceResult)
    (unionAlts : Option (List (Alt Source))) :
    mapConf map
        (binResolvedStep gt conf op args res rest state av rv allGround
          advanceResults grounded unionAlts) =
      binResolvedStep gt (mapConf map conf) op args res rest (map state) av rv
        allGround advanceResults grounded
          (unionAlts.map (List.map (mapAlt map))) := by
  rcases conf with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
  unfold binResolvedStep
  split
  · simp_all [mapConf]
  · split
    · simp_all [mapConf_pull, List.map_append, List.map_map,
        Function.comp_def, mapAlt]
    · split
      · simp_all
      · split
        · split <;> simp_all [mapConf_pull, List.map_append, List.map_map,
            Function.comp_def, mapAlt]
        · split
          · split <;> simp_all [mapConf_pull]
          · split
            · split <;> simp_all [mapConf_pull, List.map_append,
                List.map_map, Function.comp_def, mapAlt]
            · split
              · cases unionAlts with
                | none => cases rest <;> simp_all [mapConf_pull]
                | some union =>
                    simp_all [mapConf_pull, List.map_append]
              · cases rest <;> simp_all [mapConf_pull]

theorem binResolvedStep_valid (engine : SubstEngine) (gt : GroundingTable)
    (conf : Conf engine.State) (op : String) (args : List Atom)
    (res : Atom) (rest : List Goal) (state : engine.State)
    (av : List Atom) (rv : Atom)
    (allGround : Bool)
    (advanceResults : List Atom → Nat)
    (grounded : Unit → ReduceResult)
    (unionAlts : Option (List (Alt engine.State)))
    (confValid : ConfValid engine conf) (stateValid : engine.Valid state)
    (unionValid : ∀ alts, unionAlts = some alts →
      ∀ alt ∈ alts, AltValid engine alt) :
    ConfValid engine
      (binResolvedStep gt conf op args res rest state av rv allGround
        advanceResults grounded unionAlts) := by
  rcases conf with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
  have oldAltsValid : AltsValid engine alts := confValid.2
  unfold binResolvedStep
  split
  · apply confValid_some engine
    · exact stateValid
    · exact oldAltsValid
  · split
    · apply pull_valid engine
      apply confValid_none engine
      apply altsValid_append engine
      · apply altsValid_append engine
        · apply altsValid_map_br engine
          exact stateValid
        · exact localGetTypeExtensionAlts_valid engine world
            (av.headD (Atom.sym "?")) res rest state stateValid
      · exact oldAltsValid
    · split
      · apply confValid_some engine
        · exact stateValid
        · exact oldAltsValid
      · split
        · split
          all_goals
            apply pull_valid engine
            apply confValid_none engine
            first
            | exact oldAltsValid
            | (apply altsValid_append engine
               · apply altsValid_map_br engine
                 exact stateValid
               · exact oldAltsValid)
        · split
          · split
            all_goals
              first
              | (apply confValid_some engine
                 · exact stateValid
                 · exact oldAltsValid)
              | (apply pull_valid engine
                 apply confValid_none engine
                 exact oldAltsValid)
          · split
            · split
              all_goals
                apply pull_valid engine
                apply confValid_none engine
                first
                | exact oldAltsValid
                | (apply altsValid_append engine
                   · apply altsValid_map_br engine
                     exact stateValid
                   · exact oldAltsValid)
            · split
              · cases unionChoice : unionAlts with
                | none =>
                    cases rest with
                    | nil =>
                        apply pull_valid engine
                        apply confValid_none engine
                        exact oldAltsValid
                    | cons goal goals =>
                        apply confValid_some engine
                        · exact stateValid
                        · exact oldAltsValid
                | some union =>
                    have unionMembers := unionValid union unionChoice
                    apply pull_valid engine
                    apply confValid_none engine
                    exact altsValid_append engine unionMembers oldAltsValid
              · cases rest with
                | nil =>
                    apply pull_valid engine
                    apply confValid_none engine
                    exact oldAltsValid
                | cons goal goals =>
                    apply confValid_some engine
                    · exact stateValid
                    · exact oldAltsValid

/-- Prepare the exact `cons-atom` result from certified arguments.  The
structural check keeps pointer identity an optimization rather than an
assumption about the grounded implementation. -/
def preparedConsResult? (args : List CertifiedPreparedAtom)
    (grounded : ReduceResult) : Option CertifiedPreparedAtom :=
  match args, grounded with
  | [head, tail], .ok [root@(.expr atoms)] =>
      let children : List PersistentSubst.PreparedAtom :=
        [PersistentSubst.PreparedAtom.ofAtom (.sym "#c"), head.1, tail.1]
      if PersistentSubst.PreparedAtom.sameAtoms children atoms then
        let prepared :=
          PersistentSubst.PreparedAtom.mkExprFrom root children
        some ⟨prepared, by
          apply PersistentSubst.PreparedAtom.mkExprFrom_valid
          intro child member
          simp only [children, List.mem_cons, List.not_mem_nil,
            or_false] at member
          rcases member with rfl | rfl | rfl
          · exact PersistentSubst.PreparedAtom.ofAtom_valid _
          · exact head.2
          · exact tail.2⟩
      else none
  | _, _ => none

/-- Retain a certified `cons-atom` result as representation-only metadata. -/
def rememberConsResult (engine : SubstEngine) (state : engine.State)
    (args : List CertifiedPreparedAtom) (grounded : ReduceResult) :
    engine.State :=
  match preparedConsResult? args grounded with
  | some prepared =>
      engine.rememberRecent state prepared.1 prepared.2
  | none => state

@[simp] theorem rememberConsResult_denote (engine : SubstEngine)
    (state : engine.State) (args : List CertifiedPreparedAtom)
    (grounded : ReduceResult) :
    engine.denote (rememberConsResult engine state args grounded) =
      engine.denote state := by
  unfold rememberConsResult
  split
  · exact engine.rememberRecent_denote _ _ _
  · rfl

theorem rememberConsResult_valid (engine : SubstEngine)
    (state : engine.State) (args : List CertifiedPreparedAtom)
    (grounded : ReduceResult) (valid : engine.Valid state) :
    engine.Valid (rememberConsResult engine state args grounded) := by
  unfold rememberConsResult
  split
  · exact engine.rememberRecent_valid _ _ _ valid
  · exact valid

@[simp] theorem rememberConsResult_reference (state : Subst)
    (args : List CertifiedPreparedAtom) (grounded : ReduceResult) :
    rememberConsResult reference state args grounded = state := by
  unfold rememberConsResult
  split <;> rfl

@[simp] theorem caughtBinErrorResolvedWithGround_substManyCertified
    (engine : SubstEngine) (gt : GroundingTable) (state : engine.State)
    (op : String) (args : List Atom) :
    caughtBinErrorResolvedWithGround? gt op
        ((engine.substManyCertified state args).1.map
          (fun prepared => prepared.1.atom))
        (preparedAtomsAllGround
          (engine.substManyCertified state args).1) =
      caughtBinErrorResolved? gt op
        (args.map (PLeaTTa.subst (engine.denote state))) := by
  rw [engine.substManyCertified_value,
    substManyCertified_allGround]
  exact caughtBinErrorResolvedWithGround_eq gt op _ _ rfl

@[simp] theorem caughtBinErrorResolvedWithGround_referenceCertified
    (gt : GroundingTable) (state : Subst) (op : String)
    (args : List Atom) :
    caughtBinErrorResolvedWithGround? gt op
        ((referenceSubstManyCertified state args).1.unattach.map
          PersistentSubst.PreparedAtom.atom)
        (preparedAtomsAllGround
          (referenceSubstManyCertified state args).1) =
      caughtBinErrorResolved? gt op
        (args.map (PLeaTTa.subst state)) := by
  rw [certifiedAtoms_eq]
  simpa only [reference, id_eq] using
    caughtBinErrorResolvedWithGround_substManyCertified
      reference gt state op args

def subConfOfWith (engine : SubstEngine) (c : Conf engine.State)
    (sub : List Goal) (state : engine.State) (tmpl : Atom) :
    Conf engine.State :=
  { cur := some (sub, state)
    alts := []
    world := c.world
    counter := c.counter
    qterm := tmpl
    barriers := resetBarrierCache c.barriers }

def tableSubConfOfWith (engine : SubstEngine) (c : Conf engine.State)
    (f : String) (argsv : List Atom) (tres key : Atom) :
    Conf engine.State :=
  let subWorld := { c.world with
    tableActive := key :: c.world.tableActive }
  { cur := some ([Goal.call f argsv tres], engine.empty)
    alts := []
    world := subWorld
    counter := advanceCounterPastAtoms (c.counter + 1) [tres]
    qterm := tres
    barriers := resetBarrierCache c.barriers }

theorem subConfOfWith_valid (engine : SubstEngine)
    (c : Conf engine.State) (sub : List Goal) (state : engine.State)
    (tmpl : Atom) (stateValid : engine.Valid state) :
    ConfValid engine (subConfOfWith engine c sub state tmpl) := by
  unfold subConfOfWith
  apply confValid_some engine
  · exact stateValid
  · intro alt member
    simp at member

theorem tableSubConfOfWith_valid (engine : SubstEngine)
    (c : Conf engine.State) (f : String) (argsv : List Atom)
    (tres key : Atom) :
    ConfValid engine (tableSubConfOfWith engine c f argsv tres key) := by
  unfold tableSubConfOfWith
  apply confValid_some engine
  · exact engine.empty_valid
  · intro alt member
    simp at member

@[simp] theorem erase_subConfOfWith (engine : SubstEngine)
    (c : Conf engine.State) (sub : List Goal) (state : engine.State)
    (tmpl : Atom) :
    erase engine (subConfOfWith engine c sub state tmpl) =
      subConfOfWith reference (erase engine c) sub (engine.denote state)
        tmpl := by
  rcases c with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
  rfl

@[simp] theorem erase_tableSubConfOfWith (engine : SubstEngine)
    (c : Conf engine.State) (f : String) (argsv : List Atom)
    (tres key : Atom) :
    erase engine (tableSubConfOfWith engine c f argsv tres key) =
      tableSubConfOfWith reference (erase engine c) f argsv tres key := by
  rcases c with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
  simp [erase, mapConf, tableSubConfOfWith, engine.denote_empty,
    reference]

@[simp] theorem subConfOfWith_reference (c : Conf) (sub : List Goal)
    (state : Subst) (tmpl : Atom) :
    subConfOfWith reference c sub state tmpl =
      subConfOf c sub state tmpl := by
  rfl

@[simp] theorem tableSubConfOfWith_reference (c : Conf) (f : String)
    (argsv : List Atom) (tres key : Atom) :
    tableSubConfOfWith reference c f argsv tres key =
      tableSubConfOf c f argsv tres key := by
  rfl

/-- Rejoin the outer search after a nested `catch` evaluation. Keeping this
post-processing separate makes its representation naturality explicit. -/
def finishCatch {State : Type} (c done : Conf State) (rest : List Goal)
    (res : Atom) (state : State) : Conf State :=
  if done.answers.isEmpty then
    pull { c with
      cur := none
      world := done.world
      counter := done.counter }
  else
    pull { c with
      cur := none
      world := done.world
      counter := done.counter
      alts := done.answerValues.map (fun inst =>
        Alt.br (Goal.eq res inst :: rest) state) ++ c.alts }

/-- Rejoin the outer search after a nested soft-cut condition. -/
def finishSoftcut {State : Type} (c done : Conf State) (rest thn els : List Goal)
    (tmpl : Atom) (state : State) : Conf State :=
  if done.answers.isEmpty then
    { c with
      cur := some (els ++ rest, state)
      world := done.world
      counter := done.counter }
  else
    pull { c with
      cur := none
      world := done.world
      counter := done.counter
      alts := done.answerValues.map (fun inst =>
        Alt.br (Goal.eq tmpl inst :: thn ++ rest) state) ++ c.alts }

/-- A nested answer accumulator already carries exact keys in discovery
order.  Fold those keys in the same order as `chainOf`; when every answer has
an exact key, the resulting list root is closed without another atom walk. -/
def answerChainClosedRoot {State : Type} (done : Conf State) :
    Option PersistentSubst.ClosedRoot :=
  match found : chainExactKeys done.answerKeyValues with
  | none => none
  | some key =>
      let exact : PersistentSubst.atomExactKey (chainOf done.answerValues) =
          some key := by
        rw [done.answerKeyValues_sound, chainExactKeys_sound] at found
        exact found
      let closed : (chainOf done.answerValues).vars = [] :=
        (PersistentSubst.atomClosed_eq_true_iff_vars_nil _).mp
          (PersistentSubst.atomExactKey_some_atomClosed _ key exact)
      some
        { atom := chainOf done.answerValues
          key := key
          closed := closed
          exact := exact
          prepared := PersistentSubst.PreparedAtom.ofClosed
            (chainOf done.answerValues)
          prepared_valid := PersistentSubst.PreparedAtom.ofClosed_valid _ closed
          prepared_atom := rfl }

/-- Install the exact closed answer-chain root as transient engine metadata.
The denotation is unchanged; only subsequent prepared substitution can reuse
the already-computed root. -/
def rememberAnswerChain (engine : SubstEngine) (done : Conf engine.State)
    (state : engine.State) : engine.State :=
  match answerChainClosedRoot done with
  | none => state
  | some root => engine.rememberClosed state root

@[simp] theorem rememberAnswerChain_denote (engine : SubstEngine)
    (done : Conf engine.State) (state : engine.State) :
    engine.denote (rememberAnswerChain engine done state) =
      engine.denote state := by
  unfold rememberAnswerChain
  split
  · rfl
  · exact engine.rememberClosed_denote _ _

@[simp] theorem rememberAnswerChain_reference (done : Conf)
    (state : Subst) :
    rememberAnswerChain reference done state = state := by
  unfold rememberAnswerChain
  split <;> rfl

theorem rememberAnswerChain_valid (engine : SubstEngine)
    (done : Conf engine.State) (state : engine.State)
    (valid : engine.Valid state) :
    engine.Valid (rememberAnswerChain engine done state) := by
  unfold rememberAnswerChain
  split
  · exact valid
  · exact engine.rememberClosed_valid _ _ valid

/-- Rejoin the outer search after collecting every nested answer. -/
def finishFindall {State : Type} (c done : Conf State) (rest : List Goal)
    (res : Atom) (state : State) : Conf State :=
  { c with
    cur := some (Goal.eq res (chainOf done.answerValues) :: rest, state)
    world := done.world
    counter := done.counter }

/-- Rejoin the outer search after a transactional nested evaluation. -/
def finishTransaction {State : Type} (c done : Conf State) (rest : List Goal)
    (tmpl : Atom) (state : State) : Conf State :=
  if done.answers.isEmpty then
    pull { c with
      cur := none
      world := c.world
      counter := done.counter }
  else
    pull { c with
      cur := none
      world := done.world
      counter := done.counter
      alts := done.answerValues.map (fun inst =>
        Alt.br (Goal.eq tmpl inst :: rest) state) ++ c.alts }

/-- Add already-computed table answers to the outer search. -/
def enqueueAnswers {State : Type} (c : Conf State) (found : List Atom)
    (rest : List Goal) (res : Atom) (state : State) : Conf State :=
  pull { c with
    cur := none
    counter := advanceCounterPastAtoms c.counter found
    alts := found.map (fun answer =>
      Alt.br (Goal.eq res answer :: rest) state) ++ c.alts }

/-- Rejoin after answers supplied directly by a grounded host operation. -/
def enqueueHostAnswers {State : Type} (c : Conf State) (found : List Atom)
    (rest : List Goal) (res : Atom) (state : State) : Conf State :=
  enqueueAnswers c found rest res state

/-- Publish the result of a newly evaluated table entry, then rejoin the
outer search. -/
def finishTable {State : Type} (c done : Conf State) (key : Atom)
    (rest : List Goal) (res : Atom) (state : State) : Conf State :=
  let answerValues := done.answerValues
  let nextWorld := (done.world.deactivateTable key).tableInsert key answerValues
  if done.answers.isEmpty then
    pull { c with
      cur := none
      world := nextWorld
      counter := done.counter }
  else
    pull { c with
      cur := none
      world := nextWorld
      counter := done.counter
      alts := answerValues.map (fun answer =>
        Alt.br (Goal.eq res answer :: rest) state) ++ c.alts }

/-- Add freshly constructed resolution alternatives behind a cut barrier. -/
def finishResolution {State : Type} (c : Conf State)
    (built : List (Alt State) × Nat) : Conf State :=
  pull { c with
    cur := none
    counter := built.2
    alts := built.1 ++ (Alt.barrier :: c.alts)
    barriers := pushBarrierCache c.barriers }

theorem mapConf_finishCatch {Source Target : Type} (map : Source → Target)
    (c done : Conf Source) (rest : List Goal) (res : Atom) (state : Source) :
    mapConf map (finishCatch c done rest res state) =
      finishCatch (mapConf map c) (mapConf map done) rest res (map state) := by
  rcases c with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
  rcases done with ⟨doneCur, doneAlts, doneWorld, doneCounter,
    doneQterm, doneAnswers, doneAnswerKeys, doneAnswerKeysSound, doneBarriers⟩
  unfold finishCatch
  split <;> rw [mapConf_pull] <;>
    simp [mapConf, mapAlt, Conf.answerValues, Function.comp_def, *]

theorem mapConf_finishSoftcut {Source Target : Type}
    (map : Source → Target) (c done : Conf Source) (rest thn els : List Goal)
    (tmpl : Atom) (state : Source) :
    mapConf map (finishSoftcut c done rest thn els tmpl state) =
      finishSoftcut (mapConf map c) (mapConf map done) rest thn els tmpl
        (map state) := by
  rcases c with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
  rcases done with ⟨doneCur, doneAlts, doneWorld, doneCounter,
    doneQterm, doneAnswers, doneAnswerKeys, doneAnswerKeysSound, doneBarriers⟩
  unfold finishSoftcut
  split
  · simp [mapConf, *]
  · rw [mapConf_pull]
    simp [mapConf, mapAlt, Conf.answerValues, Function.comp_def, *]

theorem mapConf_finishFindall {Source Target : Type}
    (map : Source → Target) (c done : Conf Source) (rest : List Goal)
    (res : Atom) (state : Source) :
    mapConf map (finishFindall c done rest res state) =
      finishFindall (mapConf map c) (mapConf map done) rest res (map state) := by
  rcases c with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
  rcases done with ⟨doneCur, doneAlts, doneWorld, doneCounter,
    doneQterm, doneAnswers, doneAnswerKeys, doneAnswerKeysSound, doneBarriers⟩
  rfl

theorem mapConf_finishTransaction {Source Target : Type}
    (map : Source → Target) (c done : Conf Source) (rest : List Goal)
    (tmpl : Atom) (state : Source) :
    mapConf map (finishTransaction c done rest tmpl state) =
      finishTransaction (mapConf map c) (mapConf map done) rest tmpl
        (map state) := by
  rcases c with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
  rcases done with ⟨doneCur, doneAlts, doneWorld, doneCounter,
    doneQterm, doneAnswers, doneAnswerKeys, doneAnswerKeysSound, doneBarriers⟩
  unfold finishTransaction
  split <;> rw [mapConf_pull] <;>
    simp [mapConf, mapAlt, Conf.answerValues, Function.comp_def, *]

theorem mapConf_enqueueAnswers {Source Target : Type}
    (map : Source → Target) (c : Conf Source) (found : List Atom)
    (rest : List Goal) (res : Atom) (state : Source) :
    mapConf map (enqueueAnswers c found rest res state) =
      enqueueAnswers (mapConf map c) found rest res (map state) := by
  unfold enqueueAnswers
  rw [mapConf_pull]
  rcases c with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
  simp [mapConf, mapAlt, Function.comp_def]

theorem mapConf_enqueueHostAnswers {Source Target : Type}
    (map : Source → Target) (c : Conf Source) (found : List Atom)
    (rest : List Goal) (res : Atom) (state : Source) :
    mapConf map (enqueueHostAnswers c found rest res state) =
      enqueueHostAnswers (mapConf map c) found rest res (map state) := by
  unfold enqueueHostAnswers
  rw [mapConf_enqueueAnswers]

theorem mapConf_finishTable {Source Target : Type} (map : Source → Target)
    (c done : Conf Source) (key : Atom) (rest : List Goal) (res : Atom)
    (state : Source) :
    mapConf map (finishTable c done key rest res state) =
      finishTable (mapConf map c) (mapConf map done) key rest res
        (map state) := by
  rcases c with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
  rcases done with ⟨doneCur, doneAlts, doneWorld, doneCounter,
    doneQterm, doneAnswers, doneAnswerKeys, doneAnswerKeysSound, doneBarriers⟩
  unfold finishTable
  split <;> rw [mapConf_pull] <;>
    simp [mapConf, mapAlt, Conf.answerValues, Function.comp_def, *]

theorem mapConf_finishResolution {Source Target : Type}
    (map : Source → Target) (c : Conf Source)
    (built : List (Alt Source) × Nat) :
    mapConf map (finishResolution c built) =
      finishResolution (mapConf map c)
        (built.1.map (mapAlt map), built.2) := by
  unfold finishResolution
  rw [mapConf_pull]
  rcases c with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
  rcases built with ⟨builtAlts, nextCounter⟩
  simp [mapConf, mapAlt]

/-- Substitute a world action and retain its post-read engine state. Ordinary
actions use the batch path; data `add-atom` additionally carries certified
exact-key metadata into the derived space index. -/
def wactDispatchWithState (engine : SubstEngine) (world : PWorld)
    (gt : GroundingTable) (counter : Nat) (state : engine.State)
    (op : String) (args : List Atom) :
    Option (Atom × PWorld × Nat × engine.State) :=
  match op, args with
  | "add-atom", [atom] =>
      let atomResult := engine.substPreparedRemembered state atom
      let indexed := indexedAtomOfPrepared atomResult.1
      (wactDispatchAddIndexed world gt counter none indexed).map
        fun (result, nextWorld, nextCounter) =>
          (result, nextWorld, nextCounter, atomResult.2)
  | "add-atom", [space, atom] =>
      let spaceResult := engine.subst state space
      let atomResult := engine.substPreparedRemembered spaceResult.2 atom
      let indexed := indexedAtomOfPrepared atomResult.1
      (wactDispatchAddIndexed world gt counter (some spaceResult.1)
        indexed).map fun (result, nextWorld, nextCounter) =>
          (result, nextWorld, nextCounter, atomResult.2)
  | _, _ =>
      let argsResult := engine.substMany state args
      (wactDispatch world gt counter op argsResult.1).map
        fun (result, nextWorld, nextCounter) =>
          (result, nextWorld, nextCounter, argsResult.2)

theorem wactDispatchWithState_erase (engine : SubstEngine) (world : PWorld)
    (gt : GroundingTable) (counter : Nat) (state : engine.State)
    (op : String) (args : List Atom) (valid : engine.Valid state) :
    (wactDispatchWithState engine world gt counter state op args).map
        (fun (result, nextWorld, nextCounter, next) =>
          (result, nextWorld, nextCounter, engine.denote next)) =
      (wactDispatch world gt counter op
          (args.map (PLeaTTa.subst (engine.denote state)))).map
        (fun (result, nextWorld, nextCounter) =>
          (result, nextWorld, nextCounter, engine.denote state)) := by
  unfold wactDispatchWithState
  split
  · rename_i atom
    have value := engine.substPreparedRemembered_value state atom valid
    have denote := engine.substPreparedRemembered_denote state atom valid
    cases substituted : engine.substPreparedRemembered state atom with
    | mk prepared next =>
        simp only [substituted] at value denote
        simp only
        rw [wactDispatchAddIndexed_eq]
        simp only [indexedAtomOfPrepared_atom, value]
        cases dispatched : wactDispatch world gt counter "add-atom"
            [PLeaTTa.subst (engine.denote state) atom] <;>
          simp [dispatched, denote]
  · rename_i space atom
    have spaceValue := engine.subst_value state space valid
    have spaceValid := engine.subst_valid state space valid
    have spaceDenote := engine.subst_denote state space valid
    cases spaceSubstituted : engine.subst state space with
    | mk spaceValueRuntime afterSpace =>
        simp only [spaceSubstituted] at spaceValue spaceValid spaceDenote
        have atomValue := engine.substPreparedRemembered_value afterSpace atom
          spaceValid
        have atomDenote := engine.substPreparedRemembered_denote afterSpace atom
          spaceValid
        cases atomSubstituted : engine.substPreparedRemembered afterSpace atom with
        | mk prepared next =>
            simp only [atomSubstituted] at atomValue atomDenote
            simp only [atomSubstituted]
            rw [wactDispatchAddIndexed_eq]
            simp only [indexedAtomOfPrepared_atom, spaceValue, atomValue,
              spaceDenote]
            cases dispatched : wactDispatch world gt counter "add-atom"
                [PLeaTTa.subst (engine.denote state) space,
                  PLeaTTa.subst (engine.denote state) atom] <;>
              simp [dispatched, atomDenote, spaceDenote]
  · have values := engine.substMany_value state args valid
    have denote := engine.substMany_denote state args valid
    cases substituted : engine.substMany state args with
    | mk runtimeValues next =>
        simp only [substituted] at values denote
        rw [values]
        cases dispatched : wactDispatch world gt counter op
            (args.map (PLeaTTa.subst (engine.denote state))) <;>
          simp [dispatched, denote]

@[simp] theorem wactDispatchWithState_reference (world : PWorld)
    (gt : GroundingTable) (counter : Nat) (binding : Subst)
    (op : String) (args : List Atom) :
    wactDispatchWithState reference world gt counter binding op args =
      (wactDispatch world gt counter op
        (args.map (PLeaTTa.subst binding))).map
          fun (result, nextWorld, nextCounter) =>
            (result, nextWorld, nextCounter, binding) := by
  have erased := wactDispatchWithState_erase reference world gt counter
    binding op args True.intro
  simpa [reference] using erased

theorem mapConf_wactDispatchWithState (engine : SubstEngine)
    (world : PWorld) (gt : GroundingTable) (counter : Nat)
    (state : engine.State) (op : String) (args : List Atom)
    (res : Atom) (rest : List Goal) (alts : List (Alt engine.State))
    (qterm : Atom) (answers : List Atom)
    (answerKeys : List (Option PersistentSubst.AtomExactKey))
    (answerKeys_sound : answerKeys =
      answers.map PersistentSubst.atomExactKey)
    (barriers : Option Nat)
    (valid : engine.Valid state) :
    mapConf engine.denote
        (match wactDispatchWithState engine world gt counter state op args with
        | some (result, nextWorld, nextCounter, next) =>
            ({ cur := some (Goal.eq res result :: rest, next)
               alts := alts
               world := nextWorld
               counter := max counter nextCounter
               qterm := qterm
               answers := answers
               answerKeys := answerKeys
               answerKeys_sound := answerKeys_sound
               barriers := barriers } : Conf engine.State)
        | none =>
            pull
              ({ cur := none
                 alts := alts
                 world := world
                 counter := counter
                 qterm := qterm
                 answers := answers
                 answerKeys := answerKeys
                 answerKeys_sound := answerKeys_sound
                 barriers := barriers } : Conf engine.State)) =
      (match wactDispatch world gt counter op
          (args.map (PLeaTTa.subst (engine.denote state))) with
      | some (result, nextWorld, nextCounter) =>
          ({ cur := some (Goal.eq res result :: rest, engine.denote state)
             alts := alts.map (mapAlt engine.denote)
             world := nextWorld
             counter := max counter nextCounter
             qterm := qterm
             answers := answers
             answerKeys := answerKeys
             answerKeys_sound := answerKeys_sound
             barriers := barriers } : Conf)
      | none =>
          pull
            ({ cur := none
               alts := alts.map (mapAlt engine.denote)
               world := world
               counter := counter
               qterm := qterm
               answers := answers
               answerKeys := answerKeys
               answerKeys_sound := answerKeys_sound
               barriers := barriers } : Conf)) := by
  have erased := wactDispatchWithState_erase engine world gt counter state op
    args valid
  cases runtime : wactDispatchWithState engine world gt counter state op args with
  | none =>
      simp only [runtime, Option.map_none] at erased
      cases raw : wactDispatch world gt counter op
          (args.map (PLeaTTa.subst (engine.denote state))) with
      | none =>
          rw [mapConf_pull]
          rfl
      | some output => simp [raw] at erased
  | some output =>
      rcases output with ⟨result, nextWorld, nextCounter, next⟩
      simp only [runtime, Option.map_some] at erased
      cases raw : wactDispatch world gt counter op
          (args.map (PLeaTTa.subst (engine.denote state))) with
      | none => simp [raw] at erased
      | some rawOutput =>
          rcases rawOutput with ⟨rawResult, rawWorld, rawCounter⟩
          simp only [raw, Option.map_some] at erased
          simp only [Option.some.injEq, Prod.mk.injEq] at erased
          rcases erased with ⟨rfl, rfl, rfl, nextDenote⟩
          simp [mapConf, nextDenote]

@[simp] theorem reference_wactStep (world : PWorld) (gt : GroundingTable)
    (counter : Nat) (binding : Subst) (op : String) (args : List Atom)
    (res : Atom) (rest : List Goal) (alts : List Alt) (qterm : Atom)
    (answers : List Atom)
    (answerKeys : List (Option PersistentSubst.AtomExactKey))
    (answerKeys_sound : answerKeys =
      answers.map PersistentSubst.atomExactKey)
    (barriers : Option Nat) :
    (match wactDispatchWithState reference world gt counter binding op args with
    | some (result, nextWorld, nextCounter, next) =>
        ({ cur := some (Goal.eq res result :: rest, next)
           alts := alts
           world := nextWorld
           counter := max counter nextCounter
           qterm := qterm
           answers := answers
           answerKeys := answerKeys
           answerKeys_sound := answerKeys_sound
           barriers := barriers } : Conf)
    | none =>
        pull
          ({ cur := none
             alts := alts
             world := world
             counter := counter
             qterm := qterm
             answers := answers
             answerKeys := answerKeys
             answerKeys_sound := answerKeys_sound
             barriers := barriers } : Conf)) =
      (match wactDispatch world gt counter op
          (args.map (PLeaTTa.subst binding)) with
      | some (result, nextWorld, nextCounter) =>
          ({ cur := some (Goal.eq res result :: rest, binding)
             alts := alts
             world := nextWorld
             counter := max counter nextCounter
             qterm := qterm
             answers := answers
             answerKeys := answerKeys
             answerKeys_sound := answerKeys_sound
             barriers := barriers } : Conf)
      | none =>
          pull
            ({ cur := none
               alts := alts
               world := world
               counter := counter
               qterm := qterm
               answers := answers
               answerKeys := answerKeys
               answerKeys_sound := answerKeys_sound
               barriers := barriers } : Conf)) := by
  rw [wactDispatchWithState_reference]
  cases dispatched : wactDispatch world gt counter op
      (args.map (PLeaTTa.subst binding)) <;> rfl

mutual

/-- The shared operational machine over a law-bearing substitution engine.
The list engine is the reference instance; the persistent engine is the
executable instance. -/
def stepWith (engine : SubstEngine) (prog : Prog) (gt : GroundingTable)
    (fuel : Nat) (c : Conf engine.State) : Conf engine.State :=
  match c.cur with
  | none => pull c
  | some ([], state) =>
      let answerResult := engine.substPrepared state c.qterm
      let answer := answerResult.1.atom
      pull { c with
        cur := none
        answers := answer :: c.answers
        answerKeys :=
          engine.preparedExactKey answerResult.2 answerResult.1 :: c.answerKeys
        answerKeys_sound := by
          simp only [List.map_cons]
          rw [engine.preparedExactKey_value]
          rw [c.answerKeys_sound] }
  | some (g :: rest, state) =>
    match g with
    | .eq x y =>
        match engine.unify state x y with
        | some next =>
            { c with cur := some (rest,
                engine.trimFor next rest c.qterm) }
        | none => pull { c with cur := none }
    | .cut => pull { c with cur := none }
    | .cutAt k =>
        let cut := cutToTracked k c.barriers c.alts
        { c with
          cur := some (rest, state)
          alts := cut.1
          barriers := cut.2 }
    | .callDyn hd args res =>
        let headResult := engine.subst state hd
        let next := headResult.2
        match headResult.1 with
        | Atom.sym f =>
            if !(c.world.clauseHeadCandidates f).isEmpty then
              { c with cur := some (Goal.call f args res :: rest, next) }
            else if (Metta.GroundingTable.lookup gt f).isSome then
              { c with cur := some (Goal.bin f args res :: rest, next) }
            else
              let goal := Goal.eq res (chainOf (Atom.sym f :: args))
              { c with cur := some (goal :: rest, next) }
        | other =>
            match chainListM other with
            | some [Atom.sym "partial", Atom.sym base, boundList] =>
                let bound := (chainListM boundList).getD []
                let goal := Goal.callDyn (Atom.sym base) (bound ++ args) res
                { c with cur := some (goal :: rest, next) }
            | _ =>
                let goal := Goal.eq res (chainOf (other :: args))
                { c with cur := some (goal :: rest, next) }
    | .evalg value res =>
        let valueResult := engine.subst state value
        let next := valueResult.2
        let evaluated := unchainify 10000 valueResult.1
        match compileExpr (runtimeEnv c.world gt) (c.counter + 1) evaluated with
        | .ok (term, goals, counter') =>
            let (profileWorld, profileGoals) :=
              specializeGoals (specializationIsBin gt)
                specializationBuildFuel c.world goals
            let barrier := barrierDepth c + 1
            let tagged := tagCutsGoals barrier profileGoals
            let newgoals := tagged ++ [Goal.eq res term] ++ rest
            { c with
              cur := some (newgoals, next)
              world := profileWorld
              counter := advanceCounterPastGoals (max c.counter counter')
                (profileGoals ++ [Goal.eq res term] ++ rest) }
        | .error _ =>
            let data := chainify evaluated
            { c with
              cur := some (Goal.eq res data :: rest, next)
              counter := advanceCounterPastAtoms c.counter [data] }
    | .catchg tmpl sub res =>
        match catchDirect? gt (engine.denote state) tmpl sub with
        | some (.error err) =>
            { c with
              cur := some (Goal.eq res err :: rest, state)
              world := c.world
              counter := advanceCounterPastAtoms c.counter [err] }
        | some (.answers answers) =>
            if answers.isEmpty then
              pull { c with cur := none }
            else
              enqueueHostAnswers c answers rest res state
        | none =>
            let subConf := subConfOfWith engine c sub state tmpl
            let done := runWith engine prog gt fuel subConf none
            finishCatch c done rest res state
    | .transactiong tmpl sub =>
        let txSub := transactionSub tmpl sub
        let subConf := subConfOfWith engine c txSub state tmpl
        let done := runWith engine prog gt fuel subConf none
        finishTransaction c done rest tmpl state
    | .softcut tmpl sub thn els =>
        let subConf := subConfOfWith engine c sub state tmpl
        let done := runWith engine prog gt fuel subConf none
        finishSoftcut c done rest thn els tmpl state
    | .call f args res =>
        let argsResult := engine.substMany state args
        let argsv := argsResult.1
        let next := argsResult.2
        let key := tableKey f argsv
        if c.world.canTableCall f argsv then
          match c.world.tableLookup key with
          | some answers =>
              enqueueAnswers c answers rest res next
          | none =>
              let tres := tableFresh c
              let subConf := tableSubConfOfWith engine c f argsv tres key
              let done := runWith engine prog gt fuel subConf none
              finishTable c done key rest res next
        else
          let headClauses := c.world.clauseHeadCandidates f
          if headClauses.isEmpty then
            let goal := Goal.eq res (chainOf (Atom.sym f :: args))
            { c with cur := some (goal :: rest, next) }
          else
            let clauses := c.world.resolutionCandidates f args.length
            if !(clauses.any (fun clause =>
                clause.params.length == args.length)) then
              let partialValue :=
                chainOf [Atom.sym "partial", Atom.sym f, chainOf args]
              { c with
                cur := some (Goal.eq res partialValue :: rest, next) }
            else
              let barrier := barrierDepth c + 1
              let built := resolveAltsWith engine clauses argsv args res rest
                next c.qterm barrier c.counter
              finishResolution c built
    | .bin op args res =>
        let argsResult := engine.substManyCertified state args
        let av := argsResult.1.map (fun prepared => prepared.1.atom)
        let allGround := preparedAtomsAllGround argsResult.1
        let afterArgs := argsResult.2
        if binArity op != 0 && av.length < binArity op then
          let partialValue :=
            chainOf [Atom.sym "partial", Atom.sym op, chainOf av]
          { c with
            cur := some (Goal.eq res partialValue :: rest, afterArgs) }
        else
          let resultResult := engine.subst afterArgs res
          let next := resultResult.2
          if op == "cons-atom" && allGround then
            let grounded := callGrounded gt op av
            let remembered :=
              rememberConsResult engine next argsResult.1 grounded
            binResolvedStep gt c op args res rest remembered av
              resultResult.1 allGround
              (advanceCounterPastPreparedResult c.counter
                (preparedConsResult? argsResult.1 grounded))
              (fun _ => grounded)
              (unionReverseAltsWithForOp engine op args res rest remembered)
          else
            binResolvedStep gt c op args res rest next av resultResult.1
              allGround (advanceCounterPastAtoms c.counter)
              (fun _ => callGrounded gt op av)
              (unionReverseAltsWithForOp engine op args res rest next)
    | .ite cond thn els res =>
        let condResult := engine.subst state cond
        let next := condResult.2
        if condResult.1 == trueA then
          { c with
            cur := some (iteBranchGoals res thn ++ rest, next) }
        else
          { c with
            cur := some (iteBranchGoals res els ++ rest, next) }
    | .amb branches res =>
        let alts := branches.map (fun branch =>
          Alt.br (branch.2 ++ [Goal.eq res branch.1] ++ rest) state)
        pull { c with cur := none, alts := alts ++ c.alts }
    | .spread value res =>
        let valueResult := engine.subst state value
        let next := valueResult.2
        let elements := (chainListM valueResult.1).getD [valueResult.1]
        pull { c with
          cur := none
          alts := elements.map (fun element =>
            Alt.br (Goal.eq res element :: rest) next) ++ c.alts }
    | .smatch pat =>
        let built := smatchAltsWith engine c.world c.counter state pat rest
          c.qterm
        pull { c with
          cur := none
          counter := built.2
          alts := built.1 ++ c.alts }
    | .wact op args res =>
        match wactDispatchWithState engine c.world gt c.counter state op args with
        | some (result, world, counter', next) =>
            { c with
              cur := some (Goal.eq res result :: rest, next)
              world := world
              counter := max c.counter counter' }
        | none => pull { c with cur := none }
    | .findall tmpl sub res =>
        let subConf := subConfOfWith engine c sub state tmpl
        let done := runWith engine prog gt fuel subConf none
        finishFindall c done rest res
          (rememberAnswerChain engine done state)
    | .onceg tmpl sub res =>
        let barrier := barrierDepth c + 1
        let goals := sub ++ [Goal.cutAt barrier, Goal.eq res tmpl] ++ rest
        pull { c with
          cur := none
          alts := Alt.br goals state :: (Alt.barrier :: c.alts)
          barriers := pushBarrierCache c.barriers }

/-- Fuel-bounded execution of the shared engine-polymorphic machine. -/
def runWith (engine : SubstEngine) (prog : Prog) (gt : GroundingTable) :
    Nat → Conf engine.State → Option Nat → Conf engine.State
  | 0, c, _ => c
  | fuel + 1, c, limit =>
      if c.cur.isNone && c.alts.isEmpty then c
      else if limit.any (fun maximum => c.answers.length ≥ maximum) then c
      else runWith engine prog gt fuel (stepWith engine prog gt fuel c) limit

end

@[simp] theorem stepWith_reference_wact (prog : Prog) (gt : GroundingTable)
    (fuel : Nat) (world : PWorld) (counter : Nat) (binding : Subst)
    (op : String) (args : List Atom) (res : Atom) (rest : List Goal)
    (alts : List Alt) (qterm : Atom) (answers : List Atom)
    (answerKeys : List (Option PersistentSubst.AtomExactKey))
    (answerKeys_sound : answerKeys =
      answers.map PersistentSubst.atomExactKey)
    (barriers : Option Nat) :
    stepWith reference prog gt fuel
        ({ cur := some (Goal.wact op args res :: rest, binding)
           alts := alts
           world := world
           counter := counter
           qterm := qterm
           answers := answers
           answerKeys := answerKeys
           answerKeys_sound := answerKeys_sound
           barriers := barriers } : Conf) =
      (match wactDispatch world gt counter op
          (args.map (PLeaTTa.subst binding)) with
      | some (result, nextWorld, nextCounter) =>
          ({ cur := some (Goal.eq res result :: rest, binding)
             alts := alts
             world := nextWorld
             counter := max counter nextCounter
             qterm := qterm
             answers := answers
             answerKeys := answerKeys
             answerKeys_sound := answerKeys_sound
             barriers := barriers } : Conf)
      | none =>
          pull
            ({ cur := none
               alts := alts
               world := world
               counter := counter
               qterm := qterm
               answers := answers
               answerKeys := answerKeys
               answerKeys_sound := answerKeys_sound
               barriers := barriers } : Conf)) := by
  simp only [stepWith]
  rw [wactDispatchWithState_reference]
  cases dispatched : wactDispatch world gt counter op
      (args.map (PLeaTTa.subst binding)) <;> rfl

inductive StepOutcomeWith (State : Type) where
  | progressed (conf : Conf State)
  | exhausted (conf : Conf State)
  | errored (conf : Conf State) (error : Atom)

inductive RunOutcomeWith (State : Type) where
  | done (conf : Conf State)
  | limited (conf : Conf State)
  | exhausted (conf : Conf State)
  | errored (conf : Conf State) (error : Atom)

def mapStepOutcome {Source Target : Type} (map : Source → Target) :
    StepOutcomeWith Source → StepOutcomeWith Target
  | .progressed conf => .progressed (mapConf map conf)
  | .exhausted conf => .exhausted (mapConf map conf)
  | .errored conf error => .errored (mapConf map conf) error

def mapRunOutcome {Source Target : Type} (map : Source → Target) :
    RunOutcomeWith Source → RunOutcomeWith Target
  | .done conf => .done (mapConf map conf)
  | .limited conf => .limited (mapConf map conf)
  | .exhausted conf => .exhausted (mapConf map conf)
  | .errored conf error => .errored (mapConf map conf) error

/-- Convert the result of a nested catch run into the outer clean step. -/
def finishCatchOutcome {State : Type} (conf : Conf State)
    (rest : List Goal) (res : Atom) (state : State) :
    RunOutcomeWith State → StepOutcomeWith State
  | .done done => .progressed (finishCatch conf done rest res state)
  | .limited done => .exhausted done
  | .exhausted done => .exhausted done
  | .errored done error =>
      .progressed { conf with
        cur := some (Goal.eq res error :: rest, state)
        world := done.world
        counter := advanceCounterPastAtoms done.counter [error] }

/-- Convert the result of a nested transaction into the outer clean step. -/
def finishTransactionOutcome {State : Type} (conf : Conf State)
    (rest : List Goal) (tmpl : Atom) (state : State) :
    RunOutcomeWith State → StepOutcomeWith State
  | .done done =>
      .progressed (finishTransaction conf done rest tmpl state)
  | .limited done => .exhausted done
  | .exhausted done => .exhausted done
  | .errored done error => .errored done error

/-- Convert the result of a nested soft-cut into the outer clean step. -/
def finishSoftcutOutcome {State : Type} (conf : Conf State)
    (rest thn els : List Goal) (tmpl : Atom) (state : State) :
    RunOutcomeWith State → StepOutcomeWith State
  | .done done =>
      .progressed (finishSoftcut conf done rest thn els tmpl state)
  | .limited done => .exhausted done
  | .exhausted done => .exhausted done
  | .errored done error => .errored done error

/-- Convert the result of a nested findall into the outer clean step, retaining
the nested accumulator's exact closed-root metadata in the outer branch. -/
def finishFindallOutcome (engine : SubstEngine) (conf : Conf engine.State)
    (rest : List Goal) (res : Atom) (state : engine.State) :
    RunOutcomeWith engine.State → StepOutcomeWith engine.State
  | .done done => .progressed
      (finishFindall conf done rest res
        (rememberAnswerChain engine done state))
  | .limited done => .exhausted done
  | .exhausted done => .exhausted done
  | .errored done error => .errored done error

/-- Convert the result of a newly evaluated table entry into the outer
clean step. -/
def finishTableOutcome {State : Type} (conf : Conf State) (key : Atom)
    (rest : List Goal) (res : Atom) (state : State) :
    RunOutcomeWith State → StepOutcomeWith State
  | .done done =>
      .progressed (finishTable conf done key rest res state)
  | .limited done => .exhausted done
  | .exhausted done => .exhausted done
  | .errored done error => .errored done error

theorem mapStepOutcome_finishCatchOutcome {Source Target : Type}
    (map : Source → Target) (conf : Conf Source) (rest : List Goal)
    (res : Atom) (state : Source) (outcome : RunOutcomeWith Source) :
    mapStepOutcome map (finishCatchOutcome conf rest res state outcome) =
      finishCatchOutcome (mapConf map conf) rest res (map state)
        (mapRunOutcome map outcome) := by
  cases outcome with
  | done done =>
      exact congrArg StepOutcomeWith.progressed
        (mapConf_finishCatch map conf done rest res state)
  | limited done => rfl
  | exhausted done => rfl
  | errored done error =>
      rcases conf with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
      rcases done with ⟨doneCur, doneAlts, doneWorld, doneCounter,
        doneQterm, doneAnswers, doneAnswerKeys, doneAnswerKeysSound, doneBarriers⟩
      rfl

theorem mapStepOutcome_finishTransactionOutcome {Source Target : Type}
    (map : Source → Target) (conf : Conf Source) (rest : List Goal)
    (tmpl : Atom) (state : Source) (outcome : RunOutcomeWith Source) :
    mapStepOutcome map
        (finishTransactionOutcome conf rest tmpl state outcome) =
      finishTransactionOutcome (mapConf map conf) rest tmpl (map state)
        (mapRunOutcome map outcome) := by
  cases outcome <;>
    simp [finishTransactionOutcome, mapStepOutcome, mapRunOutcome,
      mapConf_finishTransaction]

theorem mapStepOutcome_finishSoftcutOutcome {Source Target : Type}
    (map : Source → Target) (conf : Conf Source) (rest thn els : List Goal)
    (tmpl : Atom) (state : Source) (outcome : RunOutcomeWith Source) :
    mapStepOutcome map
        (finishSoftcutOutcome conf rest thn els tmpl state outcome) =
      finishSoftcutOutcome (mapConf map conf) rest thn els tmpl (map state)
        (mapRunOutcome map outcome) := by
  cases outcome <;>
    simp [finishSoftcutOutcome, mapStepOutcome, mapRunOutcome,
      mapConf_finishSoftcut]

theorem mapStepOutcome_finishFindallOutcome (engine : SubstEngine)
    (conf : Conf engine.State) (rest : List Goal) (res : Atom)
    (state : engine.State) (outcome : RunOutcomeWith engine.State) :
    mapStepOutcome engine.denote
        (finishFindallOutcome engine conf rest res state outcome) =
      finishFindallOutcome reference (mapConf engine.denote conf) rest res
        (engine.denote state) (mapRunOutcome engine.denote outcome) := by
  cases outcome with
  | done done =>
      simp only [finishFindallOutcome, mapStepOutcome, mapRunOutcome]
      rw [mapConf_finishFindall]
      simp
      congr 1
  | limited done => rfl
  | exhausted done => rfl
  | errored done error => rfl

theorem mapStepOutcome_finishTableOutcome {Source Target : Type}
    (map : Source → Target) (conf : Conf Source) (key : Atom)
    (rest : List Goal) (res : Atom) (state : Source)
    (outcome : RunOutcomeWith Source) :
    mapStepOutcome map
        (finishTableOutcome conf key rest res state outcome) =
      finishTableOutcome (mapConf map conf) key rest res (map state)
        (mapRunOutcome map outcome) := by
  cases outcome <;>
    simp [finishTableOutcome, mapStepOutcome, mapRunOutcome,
      mapConf_finishTable]

def toRunOutcome : RunOutcomeWith Subst → RunOutcome
  | .done conf => .done conf
  | .limited conf => .limited conf
  | .exhausted conf => .exhausted conf
  | .errored conf error => .errored conf error

def toStepOutcome : StepOutcomeWith Subst → StepOutcome
  | .progressed conf => .progressed conf
  | .exhausted conf => .exhausted conf
  | .errored conf error => .errored conf error

@[simp] theorem toStepOutcome_finishCatchOutcome (conf : Conf)
    (rest : List Goal) (res : Atom) (state : Subst)
    (outcome : RunOutcomeWith Subst) :
    toStepOutcome (finishCatchOutcome conf rest res state outcome) =
      finishCatchClean conf rest res state (toRunOutcome outcome) := by
  cases outcome <;>
    simp [finishCatchOutcome, finishCatchClean, finishCatch, toStepOutcome,
      toRunOutcome]
  all_goals first | rfl | (split <;> rfl)

@[simp] theorem toStepOutcome_finishTransactionOutcome (conf : Conf)
    (rest : List Goal) (tmpl : Atom) (state : Subst)
    (outcome : RunOutcomeWith Subst) :
    toStepOutcome
        (finishTransactionOutcome conf rest tmpl state outcome) =
      finishTransactionClean conf rest tmpl state
        (toRunOutcome outcome) := by
  cases outcome <;>
    simp [finishTransactionOutcome, finishTransactionClean,
      finishTransaction, toStepOutcome, toRunOutcome]
  all_goals first | rfl | (split <;> rfl)

@[simp] theorem toStepOutcome_finishSoftcutOutcome (conf : Conf)
    (rest thn els : List Goal) (tmpl : Atom) (state : Subst)
    (outcome : RunOutcomeWith Subst) :
    toStepOutcome
        (finishSoftcutOutcome conf rest thn els tmpl state outcome) =
      finishSoftcutClean conf rest thn els tmpl state
        (toRunOutcome outcome) := by
  cases outcome <;>
    simp [finishSoftcutOutcome, finishSoftcutClean, finishSoftcut,
      toStepOutcome, toRunOutcome]
  all_goals first | rfl | (split <;> rfl)

@[simp] theorem toStepOutcome_finishFindallOutcome (conf : Conf)
    (rest : List Goal) (res : Atom) (state : Subst)
    (outcome : RunOutcomeWith Subst) :
    toStepOutcome
        (finishFindallOutcome reference conf rest res state outcome) =
      finishFindallClean conf rest res state (toRunOutcome outcome) := by
  cases outcome <;>
    simp [finishFindallOutcome, finishFindallClean, finishFindall,
      toStepOutcome, toRunOutcome]
  all_goals rfl

@[simp] theorem toStepOutcome_finishTableOutcome (conf : Conf)
    (key : Atom) (rest : List Goal) (res : Atom) (state : Subst)
    (outcome : RunOutcomeWith Subst) :
    toStepOutcome
        (finishTableOutcome conf key rest res state outcome) =
      finishTableClean conf key rest res state (toRunOutcome outcome) := by
  cases outcome <;>
    simp [finishTableOutcome, finishTableClean, finishTable, toStepOutcome,
      toRunOutcome]
  all_goals first | rfl | (split <;> rfl)

mutual

/-- Exhaustion-aware execution over the same substitution engine as
`stepWith`. Nested evaluations propagate exhaustion and runtime errors rather
than constructing an outer successor from a partial inner run. -/
def stepCleanWith (engine : SubstEngine) (prog : Prog) (gt : GroundingTable) :
    Nat → Conf engine.State → StepOutcomeWith engine.State
  | 0, conf => .exhausted conf
  | fuel + 1, conf =>
      match conf.cur with
      | some (Goal.catchg tmpl sub res :: rest, state) =>
          match catchDirect? gt (engine.denote state) tmpl sub with
          | some (.error error) =>
              .progressed { conf with
                cur := some (Goal.eq res error :: rest, state)
                counter := advanceCounterPastAtoms conf.counter [error] }
          | some (.answers found) =>
              if found.isEmpty then
                .progressed (pull { conf with cur := none })
              else
                .progressed (enqueueHostAnswers conf found rest res state)
          | none =>
              let nested := subConfOfWith engine conf sub state tmpl
              finishCatchOutcome conf rest res state
                (runCleanWith engine prog gt fuel nested none)
      | some (Goal.transactiong tmpl sub :: rest, state) =>
          let nested := subConfOfWith engine conf (transactionSub tmpl sub)
            state tmpl
          finishTransactionOutcome conf rest tmpl state
            (runCleanWith engine prog gt fuel nested none)
      | some (Goal.softcut tmpl sub thn els :: rest, state) =>
          let nested := subConfOfWith engine conf sub state tmpl
          finishSoftcutOutcome conf rest thn els tmpl state
            (runCleanWith engine prog gt fuel nested none)
      | some (Goal.findall tmpl sub res :: rest, state) =>
          let nested := subConfOfWith engine conf sub state tmpl
          finishFindallOutcome engine conf rest res state
            (runCleanWith engine prog gt fuel nested none)
      | some (Goal.call f args res :: rest, state) =>
          let argsResult := engine.substMany state args
          let values := argsResult.1
          let next := argsResult.2
          let key := tableKey f values
          if conf.world.canTableCall f values then
            match conf.world.tableLookup key with
            | some found =>
                .progressed (enqueueAnswers conf found rest res next)
            | none =>
                let tres := tableFresh conf
                let nested := tableSubConfOfWith engine conf f values tres key
                finishTableOutcome conf key rest res next
                  (runCleanWith engine prog gt fuel nested none)
          else
            .progressed (stepWith engine prog gt fuel conf)
      | some (Goal.bin op args res :: rest, state) =>
          let prepared := (engine.substManyCertified state args).1
          let values := prepared.map (fun atom => atom.1.atom)
          let allGround := preparedAtomsAllGround prepared
          match localTranslatePredicateGoals? conf.world gt op values res rest with
          | some _ => .progressed (stepWith engine prog gt fuel conf)
          | none =>
              match caughtBinErrorResolvedWithGround? gt op values allGround with
              | some error => .errored conf error
              | none => .progressed (stepWith engine prog gt fuel conf)
      | _ => .progressed (stepWith engine prog gt fuel conf)

def runCleanWith (engine : SubstEngine) (prog : Prog) (gt : GroundingTable) :
    Nat → Conf engine.State → Option Nat → RunOutcomeWith engine.State
  | 0, conf, limit =>
      if conf.cur.isNone && conf.alts.isEmpty then .done conf
      else if limit.any (fun maximum => conf.answers.length ≥ maximum) then
        .limited conf
      else
        .exhausted conf
  | fuel + 1, conf, limit =>
      if conf.cur.isNone && conf.alts.isEmpty then .done conf
      else if limit.any (fun maximum => conf.answers.length ≥ maximum) then
        .limited conf
      else
        match stepCleanWith engine prog gt fuel conf with
        | .progressed next => runCleanWith engine prog gt fuel next limit
        | .exhausted done => .exhausted done
        | .errored done error => .errored done error

end

/-- The proof-carrying persistent clean executor, projected back to the public
list-denotational outcome type. -/
def runPersistentClean (prog : Prog) (gt : GroundingTable) (fuel : Nat)
    (conf : Conf) (limit : Option Nat) : RunOutcome :=
  toRunOutcome <| mapRunOutcome executablePersistent.denote <|
    runCleanWith executablePersistent prog gt fuel
      (lift executablePersistent conf) limit

/-- One engine-polymorphic step denotes exactly the reference-engine step,
provided nested runs at the same fuel already denote the reference runs. -/
theorem erase_stepWith_of_run (engine : SubstEngine) (prog : Prog)
    (gt : GroundingTable) (fuel : Nat)
    (runErase : ∀ (conf : Conf engine.State) limit,
      ConfValid engine conf →
      erase engine (runWith engine prog gt fuel conf limit) =
        runWith reference prog gt fuel (erase engine conf) limit)
    (conf : Conf engine.State) (confValid : ConfValid engine conf) :
    erase engine (stepWith engine prog gt fuel conf) =
      stepWith reference prog gt fuel (erase engine conf) := by
  rcases conf with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
  cases current : cur with
  | none =>
      simp [stepWith, erase]
      rfl
  | some branch =>
      rcases branch with ⟨goals, state⟩
      have stateValid : engine.Valid state :=
        confValid.1 goals state current
      cases goals with
      | nil =>
          have answerValue := engine.substPrepared_value state qterm stateValid
          cases answerResult : engine.substPrepared state qterm with
          | mk answer next =>
              simp only [answerResult] at answerValue
              simp only [stepWith, answerResult, erase]
              rw [mapConf_pull]
              simp [mapConf, answerValue,
                engine.preparedExactKey_value]
              apply congrArg pull
              apply Conf.ext <;> rfl
      | cons goal rest =>
          cases goal with
          | eq left right =>
              have hunify := engine.unify_denote state left right stateValid
              cases result : engine.unify state left right with
              | none =>
                  simp only [result, Option.map_none] at hunify
                  simp only [stepWith, result, erase]
                  rw [mapConf_pull]
                  simp [mapConf]
                  rw [← hunify]
                  rfl
              | some next =>
                  have nextValid := engine.unify_valid state left right
                    stateValid next result
                  have htrim := engine.trim_denote next rest qterm
                  simp only [result, Option.map_some] at hunify
                  simp only [stepWith, result, erase]
                  simp [mapConf]
                  rw [← hunify]
                  simp [htrim]
                  rfl
          | cut =>
              simp only [stepWith, erase]
              rw [mapConf_pull]
              rfl
          | cutAt count =>
              have hcut := cutToTracked_mapAlt engine.denote count barriers alts
              simp [stepWith, erase, mapConf]
              congr 1
              · exact (congrArg Prod.fst hcut).symm
              · exact (congrArg Prod.snd hcut).symm
          | ite cond thn els res =>
              have valueEq := engine.subst_value state cond stateValid
              have denoteEq := engine.subst_denote state cond stateValid
              cases valueResult : engine.subst state cond with
              | mk value next =>
                  simp only [valueResult] at valueEq denoteEq
                  simp only [stepWith, valueResult, erase]
                  split <;> simp_all [mapConf]
                  all_goals rfl
          | amb branches res =>
              simp only [stepWith, erase]
              rw [mapConf_pull]
              simp [mapConf, mapAlt, List.map_append, List.map_map,
                Function.comp_def]
              rfl
          | spread value res =>
              have valueEq := engine.subst_value state value stateValid
              have denoteEq := engine.subst_denote state value stateValid
              cases valueResult : engine.subst state value with
              | mk evaluated next =>
                  simp only [valueResult] at valueEq denoteEq
                  simp only [stepWith, valueResult, erase]
                  rw [mapConf_pull]
                  simp [valueEq, denoteEq, mapConf, mapAlt, List.map_append,
                    List.map_map, Function.comp_def]
                  rfl
          | smatch pat =>
              have builtErase := smatchAltsWith_erase engine world counter
                state pat rest qterm stateValid
              have altsEq := congrArg Prod.fst builtErase
              have counterEq := congrArg Prod.snd builtErase
              simp only at altsEq counterEq
              simp only [stepWith, erase]
              rw [mapConf_pull]
              simp [mapConf, List.map_append, altsEq, counterEq]
              rfl
          | wact op args res =>
              have mapped := mapConf_wactDispatchWithState engine world gt
                counter state op args res rest alts qterm answers answerKeys
                answerKeys_sound barriers stateValid
              simp only [erase, mapConf_fields, Option.map_some]
              rw [stepWith_reference_wact]
              simp only [stepWith]
              exact mapped
          | onceg tmpl sub res =>
              simp only [stepWith, erase]
              exact mapConf_oncePull engine.denote
                { cur := some (Goal.onceg tmpl sub res :: rest, state)
                  alts := alts
                  world := world
                  counter := counter
                  qterm := qterm
                  answers := answers
                  answerKeys := answerKeys
                  answerKeys_sound := answerKeys_sound
                  barriers := barriers }
                sub rest res tmpl state
          | call f args res =>
              let base : Conf engine.State :=
                { cur := some (Goal.call f args res :: rest, state)
                  alts := alts
                  world := world
                  counter := counter
                  qterm := qterm
                  answers := answers
                  answerKeys := answerKeys
                  answerKeys_sound := answerKeys_sound
                  barriers := barriers }
              have argsValue := engine.substMany_value state args stateValid
              have argsValid := engine.substMany_valid state args stateValid
              have argsDenote := engine.substMany_denote state args stateValid
              cases argsResult : engine.substMany state args with
              | mk values next =>
                  simp only [argsResult] at argsValue argsValid argsDenote
                  change erase engine (stepWith engine prog gt fuel base) =
                    stepWith reference prog gt fuel
                      ({ cur := some
                            (Goal.call f args res :: rest,
                              engine.denote state)
                         alts := alts.map (mapAlt engine.denote)
                         world := world
                         counter := counter
                         qterm := qterm
                         answers := answers
                         answerKeys := answerKeys
                         answerKeys_sound := answerKeys_sound
                         barriers := barriers } : Conf)
                  simp only [stepWith, base, argsResult, erase,
                    reference_substMany]
                  rw [← argsValue]
                  by_cases tabled : world.canTableCall f values
                  · simp only [tabled, if_true]
                    cases cached : world.tableLookup (tableKey f values) with
                    | some found =>
                        rw [mapConf_enqueueAnswers, argsDenote]
                        rfl
                    | none =>
                        let key := tableKey f values
                        let tres := tableFresh base
                        let nested := tableSubConfOfWith engine base f values
                          tres key
                        have nestedValid : ConfValid engine nested :=
                          tableSubConfOfWith_valid engine base f values tres key
                        have nestedErase := erase_tableSubConfOfWith engine base
                          f values tres key
                        unfold erase at nestedErase
                        have doneErase := runErase nested none nestedValid
                        unfold erase at doneErase
                        rw [mapConf_finishTable, doneErase, nestedErase,
                          argsDenote]
                        rfl
                  · have tabledFalse :
                        world.canTableCall f values = false :=
                      Bool.of_not_eq_true tabled
                    simp only [tabledFalse, Bool.false_eq_true, if_false]
                    by_cases noHead :
                        (world.clauseHeadCandidates f).isEmpty
                    · simp [noHead, mapConf, argsDenote]
                      rfl
                    · have noHeadFalse :
                          (world.clauseHeadCandidates f).isEmpty = false :=
                        Bool.of_not_eq_true noHead
                      simp only [noHeadFalse, Bool.false_eq_true, if_false]
                      let clauses := world.resolutionCandidates f args.length
                      by_cases isPartial :
                          !(clauses.any (fun clause =>
                            clause.params.length == args.length))
                      · simp [clauses, isPartial, mapConf, argsDenote]
                        rfl
                      · have partialFalse :
                            (!(clauses.any (fun clause =>
                              clause.params.length == args.length))) = false :=
                          Bool.of_not_eq_true isPartial
                        have builtErase := resolveAltsWith_erase engine
                          clauses values args res rest next qterm
                          (barrierDepth base + 1) counter argsValid
                        rw [argsDenote] at builtErase
                        simp only [clauses, partialFalse,
                          Bool.false_eq_true, if_false]
                        rw [mapConf_finishResolution]
                        rw [resolveAltsWith_reference]
                        change finishResolution (mapConf engine.denote base)
                            (List.map (mapAlt engine.denote)
                                (resolveAltsWith engine clauses values args res
                                  rest next qterm (barrierDepth base + 1)
                                  counter).1,
                              (resolveAltsWith engine clauses values args res
                                rest next qterm (barrierDepth base + 1)
                                counter).2) =
                          finishResolution
                            ({ cur := some
                                  (Goal.call f args res :: rest,
                                    engine.denote state)
                               alts := alts.map (mapAlt engine.denote)
                               world := world
                               counter := counter
                               qterm := qterm
                               answers := answers
                               answerKeys := answerKeys
                               answerKeys_sound := answerKeys_sound
                               barriers := barriers } : Conf)
                            (resolveAlts clauses values args res rest
                              (engine.denote state) qterm
                              (barrierDepth (mapConf engine.denote base) + 1)
                              counter)
                        rw [barrierDepth_mapConf, builtErase]
                        rfl
          | bin op args res =>
              have argsValue := engine.substManyCertified_value state args
              have argsValid := engine.substManyCertified_valid state args
                stateValid
              have argsDenote := engine.substManyCertified_denote state args
              cases argsResult : engine.substManyCertified state args with
              | mk preparedValues afterArgs =>
                  simp only [argsResult] at argsValue argsValid argsDenote
                  have argsGround : preparedAtomsAllGround preparedValues =
                      (args.map (PLeaTTa.subst
                        (engine.denote state))).all Metta.isGround := by
                    have ground :=
                      substManyCertified_allGround engine state args
                    simpa only [argsResult] using ground
                  by_cases isPartial :
                      binArity op != 0 && args.length < binArity op
                  · simp [stepWith, argsResult, erase, isPartial, argsValue,
                      argsDenote, mapConf]
                    all_goals rfl
                  · have resultValue := engine.subst_value afterArgs res
                      argsValid
                    have resultValid := engine.subst_valid afterArgs res
                      argsValid
                    have resultDenote := engine.subst_denote afterArgs res
                      argsValid
                    cases resultResult : engine.subst afterArgs res with
                    | mk result next =>
                        simp only [resultResult] at resultValue resultValid resultDenote
                        have unionErase :=
                          unionReverseAltsWithForOp_erase engine op args res
                            rest next resultValid
                        by_cases cacheCons :
                            op = "cons-atom" ∧ ∀ atom ∈ args,
                              Metta.isGround (PLeaTTa.subst
                                (engine.denote state) atom) = true
                        · let grounded := callGrounded gt op
                              (args.map (PLeaTTa.subst
                                (engine.denote state)))
                          let remembered := rememberConsResult engine next
                            preparedValues grounded
                          have rememberedValid : engine.Valid remembered :=
                            rememberConsResult_valid engine next
                              preparedValues grounded resultValid
                          have rememberedDenote :
                              engine.denote remembered = engine.denote next :=
                            rememberConsResult_denote engine next
                              preparedValues grounded
                          have rememberedUnionErase :=
                            unionReverseAltsWithForOp_erase engine op args res
                              rest remembered rememberedValid
                          simp [stepWith, argsResult, isPartial, resultResult,
                            erase, mapConf_fields, argsValue, argsGround]
                          split
                          · rw [mapConf_binResolvedStep]
                            simp [remembered, grounded, rememberedDenote,
                              argsDenote, resultValue, resultDenote,
                              rememberedUnionErase, mapConf]
                            rfl
                          · contradiction
                        · simp [stepWith, argsResult, isPartial,
                            resultResult, erase, mapConf_fields, argsValue,
                            argsGround]
                          split
                          · contradiction
                          · rw [mapConf_binResolvedStep]
                            simp [argsDenote, resultValue,
                              resultDenote, unionErase, mapConf]
                            rfl
          | callDyn head args res =>
              have headValue := engine.subst_value state head stateValid
              have headDenote := engine.subst_denote state head stateValid
              cases headResult : engine.subst state head with
              | mk value next =>
                  simp only [headResult] at headValue headDenote
                  simp only [stepWith, headResult, erase, mapConf_fields,
                    Option.map_some]
                  rw [headValue]
                  split
                  · split
                    · apply Conf.ext <;> simp_all [mapConf]
                      case cur => rfl
                    · split
                      · apply Conf.ext <;> simp_all [mapConf]
                        case cur => rfl
                      · apply Conf.ext <;> simp_all [mapConf]
                        case cur => rfl
                  · split
                    · apply Conf.ext <;> simp_all [mapConf]
                      case cur => rfl
                    · apply Conf.ext <;> simp_all [mapConf]
                      case cur => rfl
          | evalg value res =>
              have valueEq := engine.subst_value state value stateValid
              have valueDenote := engine.subst_denote state value stateValid
              cases valueResult : engine.subst state value with
              | mk evaluated next =>
                  simp only [valueResult] at valueEq valueDenote
                  simp only [stepWith, valueResult, erase, mapConf_fields,
                    Option.map_some, reference_subst]
                  rw [← valueEq]
                  cases compiled : compileExpr (runtimeEnv world gt)
                      (counter + 1) (unchainify 10000 evaluated) with
                  | error failure =>
                      simp [mapConf, valueDenote]
                      rfl
                  | ok output =>
                      rcases output with ⟨term, compiledGoals, nextCounter⟩
                      let profile := specializeGoals (specializationIsBin gt)
                        specializationBuildFuel world compiledGoals
                      have mapped := mapConf_barrierCurrent engine.denote
                        { cur := some (Goal.evalg value res :: rest, state)
                          alts := alts
                          world := world
                          counter := counter
                          qterm := qterm
                          answers := answers
                          answerKeys := answerKeys
                          answerKeys_sound := answerKeys_sound
                          barriers := barriers }
                        (fun barrier =>
                          tagCutsGoals (barrier + 1) profile.2 ++
                            [Goal.eq res term] ++ rest)
                        next profile.1
                        (advanceCounterPastGoals (max counter nextCounter)
                          (profile.2 ++ [Goal.eq res term] ++ rest))
                      rw [valueDenote] at mapped
                      exact mapped
          | catchg tmpl sub res =>
              let base : Conf engine.State :=
                { cur := some (Goal.catchg tmpl sub res :: rest, state)
                  alts := alts
                  world := world
                  counter := counter
                  qterm := qterm
                  answers := answers
                  answerKeys := answerKeys
                  answerKeys_sound := answerKeys_sound
                  barriers := barriers }
              change erase engine (stepWith engine prog gt fuel base) =
                stepWith reference prog gt fuel (erase engine base)
              cases direct : catchDirect? gt (engine.denote state) tmpl sub with
              | some result =>
                  cases result with
                  | error err =>
                      simp [stepWith, base, direct, erase, mapConf]
                      rfl
                  | answers caught =>
                      by_cases empty : caught.isEmpty
                      · simp only [stepWith, base, direct, erase,
                          mapConf_fields, Option.map_some,
                          reference_denote]
                        simp only [empty, if_true]
                        rw [mapConf_pull]
                        rfl
                      · simp only [stepWith, base, direct, erase,
                          mapConf_fields, Option.map_some,
                          reference_denote]
                        have emptyFalse : caught.isEmpty = false :=
                          Bool.of_not_eq_true empty
                        simp only [emptyFalse, Bool.false_eq_true, if_false]
                        change mapConf engine.denote
                            (enqueueHostAnswers base caught rest res state) =
                          enqueueHostAnswers (mapConf engine.denote base)
                            caught rest res (engine.denote state)
                        exact mapConf_enqueueHostAnswers engine.denote base
                          caught rest res state
              | none =>
                  let nested := subConfOfWith engine base sub state tmpl
                  have nestedValid : ConfValid engine nested := by
                    exact subConfOfWith_valid engine base sub state tmpl
                      stateValid
                  have nestedErase := erase_subConfOfWith engine base sub
                    state tmpl
                  unfold erase at nestedErase
                  have doneErase := runErase nested none nestedValid
                  unfold erase at doneErase
                  simp only [stepWith, base, direct, erase,
                    reference_denote]
                  rw [mapConf_finishCatch]
                  rw [doneErase]
                  rw [nestedErase]
                  simp [base, direct]
                  rfl
          | softcut tmpl sub thn els =>
              let base : Conf engine.State :=
                { cur := some (Goal.softcut tmpl sub thn els :: rest, state)
                  alts := alts
                  world := world
                  counter := counter
                  qterm := qterm
                  answers := answers
                  answerKeys := answerKeys
                  answerKeys_sound := answerKeys_sound
                  barriers := barriers }
              let nested := subConfOfWith engine base sub state tmpl
              have nestedValid : ConfValid engine nested :=
                subConfOfWith_valid engine base sub state tmpl stateValid
              have doneErase := runErase nested none nestedValid
              unfold erase at doneErase
              change erase engine (stepWith engine prog gt fuel base) =
                stepWith reference prog gt fuel (erase engine base)
              simp only [stepWith, base, erase, reference_denote]
              rw [mapConf_finishSoftcut]
              rw [doneErase]
              rfl
          | findall tmpl sub res =>
              let base : Conf engine.State :=
                { cur := some (Goal.findall tmpl sub res :: rest, state)
                  alts := alts
                  world := world
                  counter := counter
                  qterm := qterm
                  answers := answers
                  answerKeys := answerKeys
                  answerKeys_sound := answerKeys_sound
                  barriers := barriers }
              let nested := subConfOfWith engine base sub state tmpl
              have nestedValid : ConfValid engine nested :=
                subConfOfWith_valid engine base sub state tmpl stateValid
              have nestedErase := erase_subConfOfWith engine base sub state
                tmpl
              unfold erase at nestedErase
              have doneErase := runErase nested none nestedValid
              unfold erase at doneErase
              change erase engine (stepWith engine prog gt fuel base) =
                stepWith reference prog gt fuel (erase engine base)
              simp only [stepWith, base, erase, reference_denote]
              rw [mapConf_finishFindall]
              rw [doneErase]
              rw [nestedErase]
              apply Conf.ext
              · simp [base, mapConf, finishFindall]
                congr 1
              all_goals simp [base, mapConf, finishFindall]
          | transactiong tmpl sub =>
              let base : Conf engine.State :=
                { cur := some (Goal.transactiong tmpl sub :: rest, state)
                  alts := alts
                  world := world
                  counter := counter
                  qterm := qterm
                  answers := answers
                  answerKeys := answerKeys
                  answerKeys_sound := answerKeys_sound
                  barriers := barriers }
              let nested := subConfOfWith engine base
                (transactionSub tmpl sub) state tmpl
              have nestedValid : ConfValid engine nested :=
                subConfOfWith_valid engine base (transactionSub tmpl sub)
                  state tmpl stateValid
              have doneErase := runErase nested none nestedValid
              unfold erase at doneErase
              change erase engine (stepWith engine prog gt fuel base) =
                stepWith reference prog gt fuel (erase engine base)
              simp only [stepWith, erase, reference_denote]
              rw [mapConf_finishTransaction]
              rw [doneErase]
              rfl

/-- Fuel-bounded execution over a proof-carrying substitution engine refines
the list-denotational reference machine. The checked state makes the engine
invariant available at every recursive configuration. -/
theorem checked_run_step_simulation (engine : SubstEngine) (prog : Prog)
    (gt : GroundingTable) :
    ∀ fuel,
      (∀ (conf : Conf (checked engine).State) limit,
        erase (checked engine)
            (runWith (checked engine) prog gt fuel conf limit) =
          runWith reference prog gt fuel (erase (checked engine) conf) limit) ∧
      (∀ conf : Conf (checked engine).State,
        erase (checked engine) (stepWith (checked engine) prog gt fuel conf) =
          stepWith reference prog gt fuel (erase (checked engine) conf)) := by
  intro fuel
  induction fuel with
  | zero =>
      have runZero : ∀ (conf : Conf (checked engine).State) limit,
          erase (checked engine)
              (runWith (checked engine) prog gt 0 conf limit) =
            runWith reference prog gt 0 (erase (checked engine) conf)
              limit := by
        intro conf limit
        simp [runWith]
      constructor
      · exact runZero
      · intro conf
        exact erase_stepWith_of_run (checked engine) prog gt 0
          (fun nested limit _ => runZero nested limit) conf
          (checked_confValid engine conf)
  | succ fuel induction =>
      have runCurrent : ∀ (conf : Conf (checked engine).State) limit,
          erase (checked engine)
              (runWith (checked engine) prog gt (fuel + 1) conf limit) =
            runWith reference prog gt (fuel + 1)
              (erase (checked engine) conf) limit := by
        intro conf limit
        rcases conf with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
        let source : Conf (checked engine).State :=
          { cur := cur
            alts := alts
            world := world
            counter := counter
            qterm := qterm
            answers := answers
            answerKeys := answerKeys
            answerKeys_sound := answerKeys_sound
            barriers := barriers }
        unfold reference
        by_cases finished : cur.isNone && alts.isEmpty
        · simp [runWith, finished, erase, mapConf]
        · by_cases reached :
              limit.any (fun maximum => answers.length ≥ maximum)
          · simp [runWith, finished, reached, erase, mapConf]
          · have runNext := induction.1
                (stepWith (checked engine) prog gt fuel source) limit
            have stepNext := induction.2 source
            unfold reference at runNext stepNext
            unfold erase mapConf at runNext stepNext
            simp only [runWith]
            simp [finished, reached, erase, mapConf]
            rw [runNext, stepNext]
      constructor
      · exact runCurrent
      · intro conf
        exact erase_stepWith_of_run (checked engine) prog gt (fuel + 1)
          (fun nested limit _ => runCurrent nested limit) conf
          (checked_confValid engine conf)

/-- The exhaustion-aware proof-carrying executor preserves the complete
reference outcome: success, answer limit, exhaustion, and runtime error. -/
theorem checked_clean_run_step_simulation (engine : SubstEngine) (prog : Prog)
    (gt : GroundingTable) :
    ∀ fuel,
      (∀ (conf : Conf (checked engine).State) limit,
        mapRunOutcome (checked engine).denote
            (runCleanWith (checked engine) prog gt fuel conf limit) =
          runCleanWith reference prog gt fuel
            (erase (checked engine) conf) limit) ∧
      (∀ conf : Conf (checked engine).State,
        mapStepOutcome (checked engine).denote
            (stepCleanWith (checked engine) prog gt fuel conf) =
          stepCleanWith reference prog gt fuel
            (erase (checked engine) conf)) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro conf limit
        rcases conf with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
        unfold reference
        by_cases finished : cur.isNone && alts.isEmpty
        · simp [runCleanWith, mapRunOutcome, erase, mapConf, finished]
        · by_cases reached :
              limit.any (fun maximum => answers.length ≥ maximum)
          · simp [runCleanWith, mapRunOutcome, erase, mapConf, finished,
              reached]
          · simp [runCleanWith, mapRunOutcome, erase, mapConf, finished,
              reached]
      · intro conf
        unfold reference
        simp [stepCleanWith, mapStepOutcome, erase]
  | succ fuel induction =>
      have rawStep := (checked_run_step_simulation engine prog gt fuel).2
      unfold reference at rawStep ⊢
      have rawMapped : ∀ source : Conf (checked engine).State,
          mapConf (checked engine).denote
              (stepWith (checked engine) prog gt fuel source) =
            stepWith reference prog gt fuel
              (mapConf (checked engine).denote source) := by
        intro source
        have equality := rawStep source
        unfold erase at equality
        exact equality
      have rawProgressed : ∀ source : Conf (checked engine).State,
          mapStepOutcome (checked engine).denote
              (.progressed
                (stepWith (checked engine) prog gt fuel source)) =
            .progressed
              (stepWith reference prog gt fuel
                (erase (checked engine) source)) := by
        intro source
        change StepOutcomeWith.progressed
              (erase (checked engine)
                (stepWith (checked engine) prog gt fuel source)) =
            StepOutcomeWith.progressed
              (stepWith reference prog gt fuel
                (erase (checked engine) source))
        exact congrArg StepOutcomeWith.progressed (rawStep source)
      have stepCurrent : ∀ conf : Conf (checked engine).State,
          mapStepOutcome (checked engine).denote
              (stepCleanWith (checked engine) prog gt (fuel + 1) conf) =
            stepCleanWith reference prog gt (fuel + 1)
              (erase (checked engine) conf) := by
        intro conf
        try unfold reference at induction
        try unfold reference at rawMapped
        try unfold reference at rawProgressed
        try unfold reference
        rcases conf with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
        cases cur with
        | none =>
            simpa [stepCleanWith, erase, mapConf] using
              rawProgressed
                ({ cur := none
                   alts := alts
                   world := world
                   counter := counter
                   qterm := qterm
                   answers := answers
                   answerKeys := answerKeys
                   answerKeys_sound := answerKeys_sound
                   barriers := barriers } : Conf (checked engine).State)
        | some branch =>
            rcases branch with ⟨goals, state⟩
            cases goals with
            | nil =>
                simpa [stepCleanWith, erase, mapConf] using
                  rawProgressed
                    ({ cur := some ([], state)
                       alts := alts
                       world := world
                       counter := counter
                       qterm := qterm
                       answers := answers
                       answerKeys := answerKeys
                       answerKeys_sound := answerKeys_sound
                       barriers := barriers } :
                      Conf (checked engine).State)
            | cons goal rest =>
                cases goal with
                | call f args res =>
                    let source : Conf (checked engine).State :=
                      { cur := some (Goal.call f args res :: rest, state)
                        alts := alts
                        world := world
                        counter := counter
                        qterm := qterm
                        answers := answers
                        answerKeys := answerKeys
                        answerKeys_sound := answerKeys_sound
                        barriers := barriers }
                    have argsValue :=
                      (checked engine).substMany_value state args True.intro
                    have argsDenote :=
                      (checked engine).substMany_denote state args True.intro
                    cases argsResult : (checked engine).substMany state args with
                    | mk values next =>
                        simp only [argsResult] at argsValue argsDenote
                        by_cases tabled : world.canTableCall f values
                        · cases cached : world.tableLookup (tableKey f values) with
                          | none =>
                              let key := tableKey f values
                              let nested := tableSubConfOfWith
                                (checked engine) source f values
                                (tableFresh source) key
                              have nestedRun := induction.1 nested none
                              change mapStepOutcome (checked engine).denote
                                  (stepCleanWith (checked engine) prog gt
                                    (fuel + 1) source) =
                                stepCleanWith reference prog gt (fuel + 1)
                                  (mapConf (checked engine).denote source)
                              calc
                                _ = mapStepOutcome (checked engine).denote
                                    (finishTableOutcome source key rest res
                                      next
                                      (runCleanWith (checked engine) prog gt
                                        fuel nested none)) := by
                                      simp [stepCleanWith, source, key,
                                        nested, argsResult, tabled, cached]
                                _ = finishTableOutcome
                                    (mapConf (checked engine).denote source)
                                    key rest res
                                    ((checked engine).denote next)
                                    (mapRunOutcome (checked engine).denote
                                      (runCleanWith (checked engine) prog gt
                                        fuel nested none)) :=
                                      mapStepOutcome_finishTableOutcome
                                        (checked engine).denote source key
                                        rest res next _
                                _ = finishTableOutcome
                                    (mapConf (checked engine).denote source)
                                    key rest res
                                    ((checked engine).denote next)
                                    (runCleanWith reference prog gt fuel
                                      (erase (checked engine) nested) none) := by
                                      unfold reference
                                      rw [nestedRun]
                                _ = finishTableOutcome
                                    (mapConf (checked engine).denote source)
                                    key rest res
                                    ((checked engine).denote next)
                                    (runCleanWith reference prog gt fuel
                                      (tableSubConfOfWith reference
                                        (mapConf (checked engine).denote
                                          source)
                                        f values (tableFresh source) key)
                                      none) := by
                                      unfold reference
                                      rw [erase_tableSubConfOfWith]
                                      rfl
                                _ = stepCleanWith reference prog gt
                                    (fuel + 1)
                                    (mapConf (checked engine).denote
                                      source) := by
                                      unfold reference
                                      simp [stepCleanWith, source,
                                        referenceSubstMany, ← argsValue,
                                        argsDenote, tabled, cached, key,
                                        tableFresh]
                          | some found =>
                              have mapped := mapConf_enqueueAnswers
                                (checked engine).denote source found rest res
                                next
                              simpa [stepCleanWith, source, argsResult,
                                ← argsValue, argsDenote, tabled, cached,
                                referenceSubstMany, mapStepOutcome,
                                erase] using mapped
                        · simpa [stepCleanWith, source, argsResult,
                            ← argsValue, argsDenote, tabled,
                            referenceSubstMany, erase, mapConf] using
                            rawProgressed source
                | bin op args res =>
                    let source : Conf (checked engine).State :=
                      { cur := some (Goal.bin op args res :: rest, state)
                        alts := alts
                        world := world
                        counter := counter
                        qterm := qterm
                        answers := answers
                        answerKeys := answerKeys
                        answerKeys_sound := answerKeys_sound
                        barriers := barriers }
                    have argsValue :=
                      (checked engine).substManyCertified_value state args
                    cases argsResult :
                        (checked engine).substManyCertified state args with
                    | mk prepared next =>
                        simp only [argsResult] at argsValue
                        have referenceArgsValue :
                            (referenceSubstManyCertified
                                ((checked engine).denote state) args).1.map
                                (fun atom => atom.1.atom) =
                              args.map (PLeaTTa.subst
                                ((checked engine).denote state)) := by
                          simpa only [reference, id_eq] using
                            reference.substManyCertified_value
                              ((checked engine).denote state) args
                        have localArgs :
                            prepared.unattach.map
                                PersistentSubst.PreparedAtom.atom =
                              (referenceSubstManyCertified
                                  ((checked engine).denote state) args).1.unattach.map
                                PersistentSubst.PreparedAtom.atom := by
                          calc
                            _ = prepared.map (fun atom => atom.1.atom) :=
                              certifiedAtoms_eq prepared
                            _ = args.map (PLeaTTa.subst
                                  ((checked engine).denote state)) := argsValue
                            _ = (referenceSubstManyCertified
                                  ((checked engine).denote state) args).1.map
                                  (fun atom => atom.1.atom) :=
                              referenceArgsValue.symm
                            _ = _ := (certifiedAtoms_eq _).symm
                        have localDenote := congrArg
                          (fun values => localTranslatePredicateGoals? world gt op
                            values res rest) localArgs
                        have errorDenote :=
                          caughtBinErrorResolvedWithGround_substManyCertified
                            (checked engine) gt state op args
                        simp only [argsResult] at errorDenote
                        cases errorResult :
                            caughtBinErrorResolvedWithGround? gt op
                              (prepared.unattach.map
                                PersistentSubst.PreparedAtom.atom)
                              (preparedAtomsAllGround prepared) with
                        | none =>
                            have normalizedError :
                                caughtBinErrorResolvedWithGround? gt op
                                    (prepared.map
                                      (fun atom => atom.1.atom))
                                    (preparedAtomsAllGround prepared) =
                                  none := by
                              rw [← certifiedAtoms_eq]
                              exact errorResult
                            have referenceError :
                                caughtBinErrorResolved? gt op
                                    (args.map (PLeaTTa.subst
                                      ((checked engine).denote state))) =
                                  none :=
                              errorDenote.symm.trans normalizedError
                            cases localResult :
                                localTranslatePredicateGoals? world gt op
                                  (prepared.unattach.map
                                    PersistentSubst.PreparedAtom.atom)
                                  res rest with
                            | none =>
                                have referenceLocal :
                                    localTranslatePredicateGoals? world gt op
                                        ((referenceSubstManyCertified
                                          ((checked engine).denote state)
                                          args).1.unattach.map
                                            PersistentSubst.PreparedAtom.atom)
                                        res rest = none := by
                                  rw [← localDenote, localResult]
                                simpa [stepCleanWith, source, argsResult,
                                  localResult, referenceLocal, errorResult,
                                  referenceError, erase, mapConf] using
                                  rawProgressed source
                            | some goals =>
                                have referenceLocal :
                                    localTranslatePredicateGoals? world gt op
                                        ((referenceSubstManyCertified
                                          ((checked engine).denote state)
                                          args).1.unattach.map
                                            PersistentSubst.PreparedAtom.atom)
                                        res rest = some goals := by
                                  rw [← localDenote, localResult]
                                simpa [stepCleanWith, source, argsResult,
                                  localResult, referenceLocal, errorResult,
                                  referenceError, erase, mapConf] using
                                  rawProgressed source
                        | some error =>
                            have normalizedError :
                                caughtBinErrorResolvedWithGround? gt op
                                    (prepared.map
                                      (fun atom => atom.1.atom))
                                    (preparedAtomsAllGround prepared) =
                                  some error := by
                              rw [← certifiedAtoms_eq]
                              exact errorResult
                            have referenceError :
                                caughtBinErrorResolved? gt op
                                    (args.map (PLeaTTa.subst
                                      ((checked engine).denote state))) =
                                  some error :=
                              errorDenote.symm.trans normalizedError
                            cases localResult :
                                localTranslatePredicateGoals? world gt op
                                  (prepared.unattach.map
                                    PersistentSubst.PreparedAtom.atom)
                                  res rest with
                            | none =>
                                have referenceLocal :
                                    localTranslatePredicateGoals? world gt op
                                        ((referenceSubstManyCertified
                                          ((checked engine).denote state)
                                          args).1.unattach.map
                                            PersistentSubst.PreparedAtom.atom)
                                        res rest = none := by
                                  rw [← localDenote, localResult]
                                simp [stepCleanWith, argsResult, localResult,
                                  referenceLocal, errorResult, referenceError,
                                  mapStepOutcome, erase, mapConf]
                            | some goals =>
                                have referenceLocal :
                                    localTranslatePredicateGoals? world gt op
                                        ((referenceSubstManyCertified
                                          ((checked engine).denote state)
                                          args).1.unattach.map
                                            PersistentSubst.PreparedAtom.atom)
                                        res rest = some goals := by
                                  rw [← localDenote, localResult]
                                simpa [stepCleanWith, source, argsResult,
                                  localResult, referenceLocal, errorResult,
                                  referenceError, erase, mapConf] using
                                  rawProgressed source
                | callDyn head args res =>
                    simpa [stepCleanWith, erase, mapConf] using
                      rawProgressed
                        ({ cur := some
                            (Goal.callDyn head args res :: rest, state)
                           alts := alts
                           world := world
                           counter := counter
                           qterm := qterm
                           answers := answers
                           answerKeys := answerKeys
                           answerKeys_sound := answerKeys_sound
                           barriers := barriers } :
                          Conf (checked engine).State)
                | evalg value res =>
                    simpa [stepCleanWith, erase, mapConf] using
                      rawProgressed
                        ({ cur := some
                            (Goal.evalg value res :: rest, state)
                           alts := alts
                           world := world
                           counter := counter
                           qterm := qterm
                           answers := answers
                           answerKeys := answerKeys
                           answerKeys_sound := answerKeys_sound
                           barriers := barriers } :
                          Conf (checked engine).State)
                | catchg tmpl sub res =>
                    let source : Conf (checked engine).State :=
                      { cur := some (Goal.catchg tmpl sub res :: rest, state)
                        alts := alts
                        world := world
                        counter := counter
                        qterm := qterm
                        answers := answers
                        answerKeys := answerKeys
                        answerKeys_sound := answerKeys_sound
                        barriers := barriers }
                    cases direct : catchDirect? gt
                        ((checked engine).denote state) tmpl sub with
                    | none =>
                        let nested := subConfOfWith (checked engine) source
                          sub state tmpl
                        have nestedRun := induction.1 nested none
                        change mapStepOutcome (checked engine).denote
                            (stepCleanWith (checked engine) prog gt
                              (fuel + 1) source) =
                          stepCleanWith reference prog gt (fuel + 1)
                            (mapConf (checked engine).denote source)
                        calc
                          _ = mapStepOutcome (checked engine).denote
                              (finishCatchOutcome source rest res state
                                (runCleanWith (checked engine) prog gt fuel
                                  nested none)) := by
                                simp [stepCleanWith, source, direct, nested]
                          _ = finishCatchOutcome
                              (mapConf (checked engine).denote source) rest
                              res ((checked engine).denote state)
                              (mapRunOutcome (checked engine).denote
                                (runCleanWith (checked engine) prog gt fuel
                                  nested none)) :=
                                mapStepOutcome_finishCatchOutcome
                                  (checked engine).denote source rest res
                                  state _
                          _ = finishCatchOutcome
                              (mapConf (checked engine).denote source) rest
                              res ((checked engine).denote state)
                              (runCleanWith reference prog gt fuel
                                (erase (checked engine) nested) none) := by
                                unfold reference
                                rw [nestedRun]
                          _ = finishCatchOutcome
                              (mapConf (checked engine).denote source) rest
                              res ((checked engine).denote state)
                              (runCleanWith reference prog gt fuel
                                (subConfOfWith reference
                                  (mapConf (checked engine).denote source)
                                  sub ((checked engine).denote state) tmpl)
                                none) := by
                                unfold reference
                                rw [erase_subConfOfWith]
                                rfl
                          _ = stepCleanWith reference prog gt (fuel + 1)
                              (mapConf (checked engine).denote source) := by
                                unfold reference
                                simp [stepCleanWith, source, direct]
                    | some result =>
                        cases result with
                        | error error =>
                            simp [stepCleanWith, direct,
                              mapStepOutcome, erase, mapConf]
                        | answers found =>
                            by_cases empty : found.isEmpty
                            · simp [stepCleanWith, direct, empty,
                                mapStepOutcome, erase]
                            · have mapped := mapConf_enqueueHostAnswers
                                (checked engine).denote source found rest res
                                state
                              simpa [stepCleanWith, source, direct, empty,
                                mapStepOutcome, erase] using mapped
                | softcut tmpl sub thn els =>
                    let source : Conf (checked engine).State :=
                      { cur := some
                          (Goal.softcut tmpl sub thn els :: rest, state)
                        alts := alts
                        world := world
                        counter := counter
                        qterm := qterm
                        answers := answers
                        answerKeys := answerKeys
                        answerKeys_sound := answerKeys_sound
                        barriers := barriers }
                    let nested := subConfOfWith (checked engine) source sub
                      state tmpl
                    have nestedRun := induction.1 nested none
                    change mapStepOutcome (checked engine).denote
                        (stepCleanWith (checked engine) prog gt (fuel + 1)
                          source) =
                      stepCleanWith reference prog gt (fuel + 1)
                        (mapConf (checked engine).denote source)
                    calc
                      _ = mapStepOutcome (checked engine).denote
                          (finishSoftcutOutcome source rest thn els tmpl
                            state
                            (runCleanWith (checked engine) prog gt fuel
                              nested none)) := by rfl
                      _ = finishSoftcutOutcome
                          (mapConf (checked engine).denote source) rest thn
                          els tmpl ((checked engine).denote state)
                          (mapRunOutcome (checked engine).denote
                            (runCleanWith (checked engine) prog gt fuel
                              nested none)) :=
                            mapStepOutcome_finishSoftcutOutcome
                              (checked engine).denote source rest thn els
                              tmpl state _
                      _ = finishSoftcutOutcome
                          (mapConf (checked engine).denote source) rest thn
                          els tmpl ((checked engine).denote state)
                          (runCleanWith reference prog gt fuel
                            (erase (checked engine) nested) none) := by
                            unfold reference
                            rw [nestedRun]
                      _ = finishSoftcutOutcome
                          (mapConf (checked engine).denote source) rest thn
                          els tmpl ((checked engine).denote state)
                          (runCleanWith reference prog gt fuel
                            (subConfOfWith reference
                              (mapConf (checked engine).denote source) sub
                              ((checked engine).denote state) tmpl)
                            none) := by
                            unfold reference
                            rw [erase_subConfOfWith]
                            rfl
                      _ = stepCleanWith reference prog gt (fuel + 1)
                          (mapConf (checked engine).denote source) := by
                            unfold reference
                            rfl
                | eq left right =>
                    simpa [stepCleanWith, erase, mapConf] using
                      rawProgressed
                        ({ cur := some (Goal.eq left right :: rest, state)
                           alts := alts
                           world := world
                           counter := counter
                           qterm := qterm
                           answers := answers
                           answerKeys := answerKeys
                           answerKeys_sound := answerKeys_sound
                           barriers := barriers } :
                          Conf (checked engine).State)
                | cut =>
                    simpa [stepCleanWith, erase, mapConf] using
                      rawProgressed
                        ({ cur := some (Goal.cut :: rest, state)
                           alts := alts
                           world := world
                           counter := counter
                           qterm := qterm
                           answers := answers
                           answerKeys := answerKeys
                           answerKeys_sound := answerKeys_sound
                           barriers := barriers } :
                          Conf (checked engine).State)
                | cutAt count =>
                    simpa [stepCleanWith, erase, mapConf] using
                      rawProgressed
                        ({ cur := some (Goal.cutAt count :: rest, state)
                           alts := alts
                           world := world
                           counter := counter
                           qterm := qterm
                           answers := answers
                           answerKeys := answerKeys
                           answerKeys_sound := answerKeys_sound
                           barriers := barriers } :
                          Conf (checked engine).State)
                | findall tmpl sub res =>
                    let source : Conf (checked engine).State :=
                      { cur := some (Goal.findall tmpl sub res :: rest, state)
                        alts := alts
                        world := world
                        counter := counter
                        qterm := qterm
                        answers := answers
                        answerKeys := answerKeys
                        answerKeys_sound := answerKeys_sound
                        barriers := barriers }
                    let nested := subConfOfWith (checked engine) source sub
                      state tmpl
                    have nestedRun := induction.1 nested none
                    change mapStepOutcome (checked engine).denote
                        (stepCleanWith (checked engine) prog gt (fuel + 1)
                          source) =
                      stepCleanWith reference prog gt (fuel + 1)
                        (mapConf (checked engine).denote source)
                    calc
                      _ = mapStepOutcome (checked engine).denote
                          (finishFindallOutcome (checked engine) source rest res state
                            (runCleanWith (checked engine) prog gt fuel
                              nested none)) := by rfl
                      _ = finishFindallOutcome reference
                          (mapConf (checked engine).denote source) rest res
                          ((checked engine).denote state)
                          (mapRunOutcome (checked engine).denote
                          (runCleanWith (checked engine) prog gt fuel
                              nested none)) :=
                            mapStepOutcome_finishFindallOutcome
                              (checked engine) source rest res state _
                      _ = finishFindallOutcome reference
                          (mapConf (checked engine).denote source) rest res
                          ((checked engine).denote state)
                          (runCleanWith reference prog gt fuel
                            (erase (checked engine) nested) none) := by
                            unfold reference
                            rw [nestedRun]
                      _ = finishFindallOutcome reference
                          (mapConf (checked engine).denote source) rest res
                          ((checked engine).denote state)
                          (runCleanWith reference prog gt fuel
                            (subConfOfWith reference
                              (mapConf (checked engine).denote source) sub
                              ((checked engine).denote state) tmpl)
                            none) := by
                            unfold reference
                            rw [erase_subConfOfWith]
                            rfl
                      _ = stepCleanWith reference prog gt (fuel + 1)
                          (mapConf (checked engine).denote source) := by
                            unfold reference
                            rfl
                | onceg tmpl sub res =>
                    simpa [stepCleanWith, erase, mapConf] using
                      rawProgressed
                        ({ cur := some
                            (Goal.onceg tmpl sub res :: rest, state)
                           alts := alts
                           world := world
                           counter := counter
                           qterm := qterm
                           answers := answers
                           answerKeys := answerKeys
                           answerKeys_sound := answerKeys_sound
                           barriers := barriers } :
                          Conf (checked engine).State)
                | transactiong tmpl sub =>
                    let source : Conf (checked engine).State :=
                      { cur := some
                          (Goal.transactiong tmpl sub :: rest, state)
                        alts := alts
                        world := world
                        counter := counter
                        qterm := qterm
                        answers := answers
                        answerKeys := answerKeys
                        answerKeys_sound := answerKeys_sound
                        barriers := barriers }
                    let txSub := transactionSub tmpl sub
                    let nested := subConfOfWith (checked engine) source txSub
                      state tmpl
                    have nestedRun := induction.1 nested none
                    change mapStepOutcome (checked engine).denote
                        (stepCleanWith (checked engine) prog gt (fuel + 1)
                          source) =
                      stepCleanWith reference prog gt (fuel + 1)
                        (mapConf (checked engine).denote source)
                    calc
                      _ = mapStepOutcome (checked engine).denote
                          (finishTransactionOutcome source rest tmpl state
                            (runCleanWith (checked engine) prog gt fuel
                              nested none)) := by rfl
                      _ = finishTransactionOutcome
                          (mapConf (checked engine).denote source) rest tmpl
                          ((checked engine).denote state)
                          (mapRunOutcome (checked engine).denote
                            (runCleanWith (checked engine) prog gt fuel
                              nested none)) :=
                            mapStepOutcome_finishTransactionOutcome
                              (checked engine).denote source rest tmpl state _
                      _ = finishTransactionOutcome
                          (mapConf (checked engine).denote source) rest tmpl
                          ((checked engine).denote state)
                          (runCleanWith reference prog gt fuel
                            (erase (checked engine) nested) none) := by
                            unfold reference
                            rw [nestedRun]
                      _ = finishTransactionOutcome
                          (mapConf (checked engine).denote source) rest tmpl
                          ((checked engine).denote state)
                          (runCleanWith reference prog gt fuel
                            (subConfOfWith reference
                              (mapConf (checked engine).denote source) txSub
                              ((checked engine).denote state) tmpl)
                            none) := by
                            unfold reference
                            rw [erase_subConfOfWith]
                            rfl
                      _ = stepCleanWith reference prog gt (fuel + 1)
                          (mapConf (checked engine).denote source) := by
                            unfold reference
                            rfl
                | amb branches res =>
                    simpa [stepCleanWith, erase, mapConf] using
                      rawProgressed
                        ({ cur := some
                            (Goal.amb branches res :: rest, state)
                           alts := alts
                           world := world
                           counter := counter
                           qterm := qterm
                           answers := answers
                           answerKeys := answerKeys
                           answerKeys_sound := answerKeys_sound
                           barriers := barriers } :
                          Conf (checked engine).State)
                | spread value res =>
                    simpa [stepCleanWith, erase, mapConf] using
                      rawProgressed
                        ({ cur := some
                            (Goal.spread value res :: rest, state)
                           alts := alts
                           world := world
                           counter := counter
                           qterm := qterm
                           answers := answers
                           answerKeys := answerKeys
                           answerKeys_sound := answerKeys_sound
                           barriers := barriers } :
                          Conf (checked engine).State)
                | ite cond thn els res =>
                    simpa [stepCleanWith, erase, mapConf] using
                      rawProgressed
                        ({ cur := some
                            (Goal.ite cond thn els res :: rest, state)
                           alts := alts
                           world := world
                           counter := counter
                           qterm := qterm
                           answers := answers
                           answerKeys := answerKeys
                           answerKeys_sound := answerKeys_sound
                           barriers := barriers } :
                          Conf (checked engine).State)
                | smatch pattern =>
                    simpa [stepCleanWith, erase, mapConf] using
                      rawProgressed
                        ({ cur := some (Goal.smatch pattern :: rest, state)
                           alts := alts
                           world := world
                           counter := counter
                           qterm := qterm
                           answers := answers
                           answerKeys := answerKeys
                           answerKeys_sound := answerKeys_sound
                           barriers := barriers } :
                          Conf (checked engine).State)
                | wact op args res =>
                    simpa [stepCleanWith, erase, mapConf] using
                      rawProgressed
                        ({ cur := some
                            (Goal.wact op args res :: rest, state)
                           alts := alts
                           world := world
                           counter := counter
                           qterm := qterm
                           answers := answers
                           answerKeys := answerKeys
                           answerKeys_sound := answerKeys_sound
                           barriers := barriers } :
                          Conf (checked engine).State)
      have runCurrent : ∀ (conf : Conf (checked engine).State) limit,
          mapRunOutcome (checked engine).denote
              (runCleanWith (checked engine) prog gt (fuel + 1) conf limit) =
            runCleanWith reference prog gt (fuel + 1)
              (erase (checked engine) conf) limit := by
        intro conf limit
        try unfold reference
        rcases conf with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
        let source : Conf (checked engine).State :=
          { cur := cur
            alts := alts
            world := world
            counter := counter
            qterm := qterm
            answers := answers
            answerKeys := answerKeys
            answerKeys_sound := answerKeys_sound
            barriers := barriers }
        by_cases finished : cur.isNone && alts.isEmpty
        · simp [runCleanWith, mapRunOutcome, finished, erase]
        · by_cases reached :
              limit.any (fun maximum => answers.length ≥ maximum)
          · simp [runCleanWith, mapRunOutcome, finished, reached, erase]
          · have stepNext := induction.2 source
            cases nextStep :
                stepCleanWith (checked engine) prog gt fuel source with
            | progressed next =>
                simp only [nextStep, mapStepOutcome] at stepNext
                have runNext := induction.1 next limit
                try unfold reference at stepNext
                try unfold reference at runNext
                unfold erase at stepNext runNext
                simp only [source, mapConf_fields] at stepNext
                simp [runCleanWith, mapRunOutcome, source, finished, reached,
                  nextStep, erase]
                rw [← stepNext]
                exact runNext
            | exhausted done =>
                simp only [nextStep, mapStepOutcome] at stepNext
                try unfold reference at stepNext
                unfold erase at stepNext
                simp only [source, mapConf_fields] at stepNext
                simp [runCleanWith, mapRunOutcome, source, finished, reached,
                  nextStep, erase]
                rw [← stepNext]
            | errored done error =>
                simp only [nextStep, mapStepOutcome] at stepNext
                try unfold reference at stepNext
                unfold erase at stepNext
                simp only [source, mapConf_fields] at stepNext
                simp [runCleanWith, mapRunOutcome, source, finished, reached,
                  nextStep, erase]
                rw [← stepNext]
      exact ⟨runCurrent, stepCurrent⟩

/-- The generic machine instantiated with list substitutions is exactly the
historical reference machine at every fuel, including nested runs. -/
theorem reference_run_step (prog : Prog) (gt : GroundingTable) :
    ∀ fuel,
      (∀ (c : Conf) limit,
        runWith reference prog gt fuel c limit = run prog gt fuel c limit) ∧
      (∀ c : Conf,
        stepWith reference prog gt fuel c = step prog gt fuel c) := by
  intro fuel
  induction fuel with
  | zero =>
      have runZero : ∀ (c : Conf) limit,
          runWith reference prog gt 0 c limit = run prog gt 0 c limit := by
        intro c limit
        simp [runWith, run]
      constructor
      · exact runZero
      · intro c
        rcases c with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
        cases current : cur with
        | none => (simp [stepWith, step]; rfl)
        | some branch =>
            rcases branch with ⟨goals, binding⟩
            cases goals with
            | nil =>
                (simp [stepWith, step]; rfl)
            | cons goal rest =>
                cases goal <;>
                  simp [stepWith, step, runZero, subConfOfWith,
                    tableSubConfOfWith, finishCatch, finishSoftcut,
                    finishFindall, finishTransaction, enqueueAnswers,
                    finishTable, finishResolution] <;>
                  repeat first | rfl | (split <;> simp_all)
  | succ fuel induction =>
      have runCurrent : ∀ (c : Conf) limit,
          runWith reference prog gt (fuel + 1) c limit =
            run prog gt (fuel + 1) c limit := by
        intro c limit
        rcases c with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
        cases cur with
        | none =>
            cases alts with
            | nil =>
                simp only [runWith, run]
                rfl
            | cons alt remaining =>
                by_cases reached :
                    limit.any (fun maximum => answers.length ≥ maximum) = true
                · simp [runWith, run, reached]
                · simp [runWith, run, reached, induction.2, induction.1]
        | some branch =>
            by_cases reached :
                limit.any (fun maximum => answers.length ≥ maximum) = true
            · simp [runWith, run, reached]
            · simp [runWith, run, reached, induction.2, induction.1]
      constructor
      · exact runCurrent
      · intro c
        rcases c with ⟨cur, alts, world, counter, qterm, answers,
    answerKeys, answerKeys_sound, barriers⟩
        cases current : cur with
        | none => (simp [stepWith, step]; rfl)
        | some branch =>
            rcases branch with ⟨goals, binding⟩
            cases goals with
            | nil =>
                (simp [stepWith, step]; rfl)
            | cons goal rest =>
                cases goal <;>
                  simp [stepWith, step, runCurrent, subConfOfWith,
                    tableSubConfOfWith, finishCatch, finishSoftcut,
                    finishFindall, finishTransaction, enqueueAnswers,
                    finishTable, finishResolution] <;>
                  repeat first | rfl | (split <;> simp_all)

theorem runWith_reference (prog : Prog) (gt : GroundingTable) (fuel : Nat)
    (c : Conf) (limit : Option Nat) :
    runWith reference prog gt fuel c limit = run prog gt fuel c limit :=
  (reference_run_step prog gt fuel).1 c limit

theorem stepWith_reference (prog : Prog) (gt : GroundingTable) (fuel : Nat)
    (c : Conf) :
    stepWith reference prog gt fuel c = step prog gt fuel c :=
  (reference_run_step prog gt fuel).2 c

/-- The proof-carrying persistent clean executor has exactly the complete
list-denotational reference outcome: success, answer limit, exhaustion, or
runtime error, with the same answers and world. -/
theorem runPersistentClean_eq_referenceClean (prog : Prog)
    (gt : GroundingTable) (fuel : Nat) (conf : Conf)
    (limit : Option Nat) :
    runPersistentClean prog gt fuel conf limit =
      toRunOutcome (runCleanWith reference prog gt fuel conf limit) := by
  unfold runPersistentClean
  unfold executablePersistent
  rw [(checked_clean_run_step_simulation (preparedChecked persistent)
    prog gt fuel).1
    (lift (checked (preparedChecked persistent)) conf) limit]
  rw [erase_lift]

end SubstEngine

end PLeaTTa
