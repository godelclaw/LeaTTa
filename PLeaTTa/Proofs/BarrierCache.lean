import PLeaTTa.Semantics

namespace PLeaTTa

open Metta (Atom Subst GroundingTable)

/-- An enabled barrier cache exactly represents the markers in the
alternative stack. `none` is the uncached reference lane. -/
def BarrierCacheCoherent {Binding : Type} (conf : Conf Binding) : Prop :=
  match conf.barriers with
  | none => True
  | some depth => depth = barrierCount conf.alts

theorem BarrierCacheCoherent.depth_eq {Binding : Type} {conf : Conf Binding}
    (coherent : BarrierCacheCoherent conf) {depth : Nat}
    (cached : conf.barriers = some depth) :
    depth = barrierCount conf.alts := by
  unfold BarrierCacheCoherent at coherent
  rw [cached] at coherent
  exact coherent

theorem BarrierCacheCoherent.barrierDepth_eq {Binding : Type}
    {conf : Conf Binding} (coherent : BarrierCacheCoherent conf) :
    barrierDepth conf = barrierCount conf.alts := by
  cases cached : conf.barriers with
  | none => simp [barrierDepth, cached]
  | some depth =>
      simp [barrierDepth, cached, coherent.depth_eq cached]

@[simp] theorem reset_conf_barrierCacheCoherent {Binding : Type}
    (conf : Conf Binding) :
    BarrierCacheCoherent
      { conf with alts := [], barriers := resetBarrierCache conf.barriers } := by
  cases cached : conf.barriers <;>
    simp [BarrierCacheCoherent, barrierCount]

@[simp] theorem enabled_empty_barrierCacheCoherent {Binding : Type}
    (conf : Conf Binding) :
    BarrierCacheCoherent { conf with alts := [], barriers := some 0 } := by
  simp [BarrierCacheCoherent, barrierCount]

private theorem barrierCount_foldl_raw {Binding : Type}
    (alts : List (Alt Binding)) (count : Nat) :
    alts.foldl barrierCountStep count =
      count + alts.foldl barrierCountStep 0 := by
  induction alts generalizing count with
  | nil => simp
  | cons alt rest ih =>
      rw [List.foldl_cons, ih]
      cases alt with
      | br goals binding => simp [barrierCountStep]
      | barrier =>
          simp only [barrierCountStep]
          calc
            count + 1 + rest.foldl barrierCountStep 0 =
                count + (1 + rest.foldl barrierCountStep 0) := by
                  simp [Nat.add_assoc]
            _ = count + rest.foldl barrierCountStep 1 :=
              congrArg (count + ·) (ih 1).symm

theorem barrierCount_foldl {Binding : Type}
    (alts : List (Alt Binding)) (count : Nat) :
    alts.foldl barrierCountStep count = count + barrierCount alts := by
  simpa [barrierCount] using barrierCount_foldl_raw alts count

@[simp] theorem barrierCount_nil {Binding : Type} :
    barrierCount ([] : List (Alt Binding)) = 0 := rfl

@[simp] theorem barrierCount_append {Binding : Type}
    (left right : List (Alt Binding)) :
    barrierCount (left ++ right) = barrierCount left + barrierCount right := by
  unfold barrierCount
  rw [List.foldl_append, barrierCount_foldl_raw]

@[simp] theorem barrierCount_cons_barrier {Binding : Type}
    (rest : List (Alt Binding)) :
    barrierCount (Alt.barrier :: rest) = barrierCount rest + 1 := by
  unfold barrierCount
  rw [List.foldl_cons, barrierCount_foldl_raw]
  simp [barrierCountStep, Nat.add_comm]

@[simp] theorem barrierCount_cons_branch {Binding : Type}
    (goals : List Goal) (binding : Binding)
    (rest : List (Alt Binding)) :
    barrierCount (Alt.br goals binding :: rest) = barrierCount rest := by
  unfold barrierCount
  rw [List.foldl_cons, barrierCount_foldl_raw]
  simp [barrierCountStep]

@[simp] theorem barrierCount_map_branch {Binding Item : Type}
    (items : List Item) (goals : Item → List Goal)
    (binding : Item → Binding) :
    barrierCount (items.map fun item => Alt.br (goals item) (binding item)) = 0 := by
  induction items with
  | nil => rfl
  | cons item rest => simp [barrierCount_cons_branch, *]

@[simp] theorem barrierCount_reverse {Binding : Type}
    (alts : List (Alt Binding)) :
    barrierCount alts.reverse = barrierCount alts := by
  induction alts with
  | nil => rfl
  | cons alt rest =>
      rw [List.reverse_cons, barrierCount_append]
      cases alt <;> simp [*]

private theorem barrierCount_foldl_branch_zero {Binding Item : Type}
    (items : List Item) (initial : List (Alt Binding))
    (selected : Item → Bool) (goals : Item → List Goal)
    (binding : Item → Binding) (initialZero : barrierCount initial = 0) :
    barrierCount
      (items.foldl (fun acc item =>
        if selected item then Alt.br (goals item) (binding item) :: acc
        else acc) initial) = 0 := by
  induction items generalizing initial with
  | nil => exact initialZero
  | cons item rest ih =>
      rw [List.foldl_cons]
      apply ih
      split <;> simp_all

theorem unionReverseAlts_barrierCount_zero (args : List Atom) (res : Atom)
    (rest : List Goal) (binding : Subst) (alts : List Alt)
    (generated : unionReverseAlts args res rest binding = some alts) :
    barrierCount alts = 0 := by
  cases args with
  | nil => simp [unionReverseAlts] at generated
  | cons left tail =>
      cases tail with
      | nil => simp [unionReverseAlts] at generated
      | cons right extra =>
          cases extra with
          | cons third remaining => simp [unionReverseAlts] at generated
          | nil =>
              cases chained : chainListM (subst binding res) with
              | none => simp [unionReverseAlts, chained] at generated
              | some items =>
                  simp [unionReverseAlts, chained] at generated
                  subst alts
                  exact barrierCount_map_branch _ _ _

theorem smatchAlts_barrierCount_zero (world : PWorld) (counter : Nat)
    (binding : Subst) (pattern : Atom) (rest : List Goal) (qterm : Atom) :
    barrierCount (smatchAlts world counter binding pattern rest qterm).1 = 0 := by
  unfold smatchAlts
  rcases spacePatView pattern with ⟨spacePattern, queryPattern⟩
  simp only
  let query := subst binding queryPattern
  let space := subst binding spacePattern
  let suffix := resolutionFreshSuffix [query] queryPattern rest binding qterm counter
  rw [barrierCount_reverse]
  simpa [query, space, suffix] using
    (barrierCount_foldl_branch_zero
      (world.atomCandidates space query) []
      (fun atom =>
        matchCompat query (renameAtomSuffixShared suffix atom))
      (fun atom =>
        Goal.eq queryPattern (renameAtomSuffixShared suffix atom) :: rest)
      (fun _ => binding) rfl)

theorem resolveAlts_barrierCount_zero (clauses : List Clause)
    (argsv args : List Atom) (res : Atom) (rest : List Goal)
    (binding : Subst) (qterm : Atom) (barrier counter : Nat) :
    barrierCount
      (resolveAlts clauses argsv args res rest binding qterm barrier counter).1 = 0 := by
  let resv := subst binding res
  let next := fun (acc : List Alt × Nat) (clause : Clause) =>
    if clause.params.length != argsv.length then acc
    else if !matchCompatList argsv clause.params then acc
    else if !matchCompat resv clause.result then acc
    else
      let copied := freshenResolutionClause argsv args res rest binding qterm
        acc.2 barrier clause
      let goals := Goal.eq (Atom.expr (args ++ [res]))
        (Atom.expr (copied.params ++ [copied.result])) :: copied.body ++ rest
      (Alt.br goals binding :: acc.1, acc.2 + 1)
  have nextZero : ∀ (acc : List Alt × Nat) (clause : Clause),
      barrierCount acc.1 = 0 → barrierCount (next acc clause).1 = 0 := by
    intro acc clause zero
    simp only [next]
    split <;> try exact zero
    split <;> try exact zero
    split <;> simp_all
  have foldZero : ∀ (remaining : List Clause) (acc : List Alt × Nat),
      barrierCount acc.1 = 0 →
        barrierCount (remaining.foldl next acc).1 = 0 := by
    intro remaining
    induction remaining with
    | nil => exact fun _ zero => zero
    | cons clause tail ih =>
        intro acc zero
        rw [List.foldl_cons]
        exact ih (next acc clause) (nextZero acc clause zero)
  unfold resolveAlts
  change barrierCount ((clauses.foldl next ([], counter)).1.reverse) = 0
  rw [barrierCount_reverse]
  exact foldZero clauses ([], counter) rfl

theorem BarrierCacheCoherent.prepend_zero {Binding : Type}
    (conf : Conf Binding) (newAlts : List (Alt Binding))
    (coherent : BarrierCacheCoherent conf)
    (newAltsZero : barrierCount newAlts = 0) :
    BarrierCacheCoherent { conf with alts := newAlts ++ conf.alts } := by
  cases cached : conf.barriers with
  | none => trivial
  | some depth =>
      have exactDepth := coherent.depth_eq cached
      simpa [BarrierCacheCoherent, cached, newAltsZero] using exactDepth

theorem BarrierCacheCoherent.push {Binding : Type}
    (conf : Conf Binding) (newAlts : List (Alt Binding))
    (coherent : BarrierCacheCoherent conf)
    (newAltsZero : barrierCount newAlts = 0) :
    BarrierCacheCoherent
      { conf with
        alts := newAlts ++ Alt.barrier :: conf.alts
        barriers := pushBarrierCache conf.barriers } := by
  cases cached : conf.barriers with
  | none => trivial
  | some depth =>
      have exactDepth := coherent.depth_eq cached
      simp [BarrierCacheCoherent, newAltsZero, exactDepth, Nat.add_comm]

@[simp] theorem resetBarrierCache_coherent (cache : Option Nat) :
    match resetBarrierCache cache with
    | none => True
    | some depth => depth = barrierCount ([] : List Alt) := by
  cases cache <;> simp

theorem cutToCached_count_exact {Binding : Type} (cut : Nat) :
    ∀ alts : List (Alt Binding),
      (cutToCached cut (barrierCount alts) alts).2 =
        barrierCount (cutToCached cut (barrierCount alts) alts).1
  | [] => rfl
  | .barrier :: rest => by
      unfold cutToCached
      split
      · simpa using cutToCached_count_exact cut rest
      · rfl
  | .br goals binding :: rest => by
      unfold cutToCached
      split
      · simpa using cutToCached_count_exact cut rest
      · rfl

theorem cutToCached_fst_exact {Binding : Type} (cut : Nat) :
    ∀ alts : List (Alt Binding),
      (cutToCached cut (barrierCount alts) alts).1 = cutTo cut alts
  | [] => rfl
  | .barrier :: rest => by
      unfold cutToCached cutTo
      simp only [barrierCount_cons_barrier]
      split
      · simpa using cutToCached_fst_exact cut rest
      · rfl
  | .br goals binding :: rest => by
      unfold cutToCached cutTo
      simp only [barrierCount_cons_branch]
      split
      · simpa using cutToCached_fst_exact cut rest
      · rfl

theorem cutToTracked_fst_of_coherent {Binding : Type} (cut : Nat)
    (cache : Option Nat) (alts : List (Alt Binding))
    (coherent : match cache with
      | none => True
      | some depth => depth = barrierCount alts) :
    (cutToTracked cut cache alts).1 = cutTo cut alts := by
  cases cache with
  | none => rfl
  | some depth =>
      subst depth
      simpa [cutToTracked] using cutToCached_fst_exact cut alts

theorem cutToTracked_coherent {Binding : Type} (cut : Nat)
    (cache : Option Nat) (alts : List (Alt Binding))
    (coherent : match cache with
      | none => True
      | some depth => depth = barrierCount alts) :
    match (cutToTracked cut cache alts).2 with
    | none => True
    | some depth => depth = barrierCount (cutToTracked cut cache alts).1 := by
  cases cache with
  | none => trivial
  | some depth =>
      subst depth
      exact cutToCached_count_exact cut alts

theorem pullAuxCached_exact {Binding : Type} : ∀ alts : List (Alt Binding),
    pullAuxCached (barrierCount alts) alts =
      (pullAux alts, match pullAux alts with
        | none => 0
        | some (_, rest) => barrierCount rest)
  | [] => rfl
  | .barrier :: rest => by
      simpa [pullAuxCached, pullAux] using
        pullAuxCached_exact rest
  | .br goals binding :: rest => rfl

theorem BarrierCacheCoherent.pull {Binding : Type} (conf : Conf Binding)
    (coherent : BarrierCacheCoherent conf) :
    BarrierCacheCoherent (pull conf) := by
  cases cached : conf.barriers with
  | none =>
      unfold BarrierCacheCoherent PLeaTTa.pull
      rw [cached]
      simp only [pullAuxTracked]
      cases pullAux conf.alts <;> simp
  | some depth =>
      have exactDepth := coherent.depth_eq cached
      subst depth
      unfold PLeaTTa.pull
      simp only [cached, pullAuxTracked]
      rw [pullAuxCached_exact]
      cases pulled : pullAux conf.alts with
      | none => simp [BarrierCacheCoherent, barrierCount]
      | some result =>
          rcases result with ⟨branch, rest⟩
          simp [BarrierCacheCoherent]

theorem BarrierCacheCoherent.cut {Binding : Type} (conf : Conf Binding)
    (cut : Nat) (coherent : BarrierCacheCoherent conf) :
    BarrierCacheCoherent
      { conf with
        alts := (cutToTracked cut conf.barriers conf.alts).1
        barriers := (cutToTracked cut conf.barriers conf.alts).2 } := by
  exact cutToTracked_coherent cut conf.barriers conf.alts coherent

/-- Every formal transition preserves exactness of an enabled barrier cache. -/
theorem Step.preserves_barrierCacheCoherent {prog : Prog}
    {gt : GroundingTable} {source target : Conf}
    (transition : Step prog gt source target)
    (coherent : BarrierCacheCoherent source) :
    BarrierCacheCoherent target := by
  revert coherent
  apply Step.rec
    (motive_1 := fun source target _ =>
      BarrierCacheCoherent source → BarrierCacheCoherent target)
    (motive_2 := fun source target _ =>
      BarrierCacheCoherent source → BarrierCacheCoherent target)
    (motive_3 := fun source target _ _ =>
      BarrierCacheCoherent source → BarrierCacheCoherent target)
    (t := transition)
  case call_resolve =>
    intro c function args res rest binding branches counter hcur hdefined
      harity hresolve coherent
    apply BarrierCacheCoherent.pull
    apply BarrierCacheCoherent.push c branches coherent
    have branchesZero := resolveAlts_barrierCount_zero
      (c.world.resolutionCandidates function args.length)
      (args.map (subst binding)) args res rest binding c.qterm
      (barrierDepth c + 1) c.counter
    rw [hresolve] at branchesZero
    exact branchesZero
  case bin_local_translate =>
    intro c op args res rest binding goals hcur hpartial hlocal coherent
    exact coherent
  case bin_union_reverse =>
    intro c args res rest binding alts hcur hpartial hlocal hspecial hmode
      hground hreverse coherent
    apply BarrierCacheCoherent.pull
    exact BarrierCacheCoherent.prepend_zero c alts coherent
      (unionReverseAlts_barrierCount_zero args res rest binding alts hreverse)
  case smatch =>
    intro c pattern rest binding alts counter hcur hmatch coherent
    apply BarrierCacheCoherent.pull
    apply BarrierCacheCoherent.prepend_zero c alts coherent
    have altsZero := smatchAlts_barrierCount_zero c.world c.counter binding
      pattern rest c.qterm
    rw [hmatch] at altsZero
    exact altsZero
  case onceg =>
    intro c template sub res rest binding hcur coherent
    apply BarrierCacheCoherent.pull
    exact BarrierCacheCoherent.push c
      [Alt.br (sub ++ [Goal.cutAt (barrierDepth c + 1),
        Goal.eq res template] ++ rest) binding] coherent (by simp)
  case findall =>
    intro c d template sub res rest binding hcur hrun hdone ih coherent
    simpa [BarrierCacheCoherent] using coherent
  case transaction =>
    intro c d template sub rest binding err hcur hraise ih coherent
    apply ih
    cases c.barriers <;> simp [BarrierCacheCoherent]
  case softcut =>
    intro c d template sub thenGoals elseGoals rest binding err hcur hraise ih
      coherent
    apply ih
    cases c.barriers <;> simp [BarrierCacheCoherent]
  case findall =>
    intro c d template sub res rest binding err hcur hraise ih coherent
    apply ih
    cases c.barriers <;> simp [BarrierCacheCoherent]
  case table =>
    intro c d function args res rest binding tableResult err hcur hcan hcache
      hfresh hraise ih coherent
    apply ih
    cases c.barriers <;> simp [BarrierCacheCoherent]
  all_goals intros
  all_goals try assumption
  all_goals try
    { apply BarrierCacheCoherent.pull
      simp_all [BarrierCacheCoherent] }
  all_goals try
    { apply BarrierCacheCoherent.cut
      assumption }
  all_goals simp_all [BarrierCacheCoherent]

/-- A coherent enabled cache remains exact over any finite execution. -/
theorem StepStar.preserves_barrierCacheCoherent {prog : Prog}
    {gt : GroundingTable} {source target : Conf}
    (run : StepStar prog gt source target)
    (coherent : BarrierCacheCoherent source) :
    BarrierCacheCoherent target := by
  revert coherent
  apply StepStar.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun source target _ =>
      BarrierCacheCoherent source → BarrierCacheCoherent target)
    (motive_3 := fun _ _ _ _ => True)
    (t := run)
  all_goals try { intros; trivial }
  case tail =>
    intro first middle last step tail _ ih coherent
    exact ih (step.preserves_barrierCacheCoherent coherent)

/-- Exceptional execution preserves an enabled cache up to its escape point. -/
theorem Raises.preserves_barrierCacheCoherent {prog : Prog}
    {gt : GroundingTable} {source target : Conf} {err : Atom}
    (run : Raises prog gt source target err)
    (coherent : BarrierCacheCoherent source) :
    BarrierCacheCoherent target := by
  revert coherent
  apply Raises.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun source target _ _ =>
      BarrierCacheCoherent source → BarrierCacheCoherent target)
    (t := run)
  all_goals try { intros; trivial }
  case step =>
    intro first middle last error step raise _ ih coherent
    exact ih (step.preserves_barrierCacheCoherent coherent)
  case transaction =>
    intro c d template sub rest binding error hcur raise ih coherent
    apply ih
    cases c.barriers <;> simp [BarrierCacheCoherent, barrierCount]
  case softcut =>
    intro c d template sub thenGoals elseGoals rest binding error hcur raise ih
      coherent
    apply ih
    cases c.barriers <;> simp [BarrierCacheCoherent, barrierCount]
  case findall =>
    intro c d template sub res rest binding error hcur raise ih coherent
    apply ih
    cases c.barriers <;> simp [BarrierCacheCoherent, barrierCount]
  case table =>
    intro c d function args res rest binding tableResult error hcur hcan hcache
      hfresh raise ih coherent
    apply ih
    cases c.barriers <;> simp [BarrierCacheCoherent, barrierCount]

end PLeaTTa
