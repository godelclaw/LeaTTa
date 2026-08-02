-- SPDX-License-Identifier: Apache-2.0

/-
Substitution acyclicity as a configuration invariant of the actual PLeaTTa
small-step semantics.  The invariant covers both the active branch and every
stored alternative, because `pull` can make any stored branch active.
-/
import PLeaTTa.Semantics
import PLeaTTa.Proofs.Unification

namespace PLeaTTa

open Metta (Atom Subst GroundingTable)

/-- Proposition-valued packaging of the constructional topological witness. -/
def HasTopologicalSubst (b : Subst) : Prop :=
  Nonempty (SubstTopological b)

/- Every substitution owned by an alternative is topological.  Dormant
    catch resumptions recursively own their protected alternative prefix;
    active and dormant frames own the entry substitution that exception
    unwind may later restore.  Keeping this structural prevents hidden
    resumption state from escaping the reachability invariant. -/
mutual

def AltTopological : Alt → Prop
  | .br _ binding => HasTopologicalSubst binding
  | .barrier => True
  | .catchActive frame => HasTopologicalSubst frame.entry
  | .catchDormant frame protectedAlts =>
      HasTopologicalSubst frame.entry ∧ AltsTopological protectedAlts

def AltsTopological : List Alt → Prop
  | [] => True
  | alternative :: rest =>
      AltTopological alternative ∧ AltsTopological rest

end

/-- Compatibility projection used by the older branch-oriented proofs. -/
theorem AltsTopological.branch {alts : List Alt}
    (halts : AltsTopological alts) (goals : List Goal) (binding : Subst)
    (member : Alt.br goals binding ∈ alts) :
    HasTopologicalSubst binding := by
  induction alts with
  | nil => simp at member
  | cons alternative rest inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with head | tail
      · cases head
        exact halts.1
      · exact inductionHypothesis halts.2 tail

instance {alts : List Alt} :
    CoeFun (AltsTopological alts)
      (fun _ => ∀ goals binding, Alt.br goals binding ∈ alts →
        HasTopologicalSubst binding) where
  coe halts := halts.branch

/-- The active branch and all stored alternatives carry topological
    substitutions. -/
def ConfTopological (c : Conf) : Prop :=
  (∀ goals b, c.cur = some (goals, b) → HasTopologicalSubst b) ∧
  AltsTopological c.alts

@[simp] theorem hasTopologicalSubst_nil :
    HasTopologicalSubst ([] : Subst) := by
  refine ⟨{
    order := []
    nodup := List.nodup_nil
    domain := ?_
    decreases := ?_ }⟩
  · intro name
    simp [Metta.Subst.lookup]
  · intro source value dependency hsource
    simp [Metta.Subst.lookup] at hsource

theorem AltsTopological.append {left right : List Alt}
    (hleft : AltsTopological left) (hright : AltsTopological right) :
    AltsTopological (left ++ right) := by
  induction left with
  | nil => simpa [AltsTopological] using hright
  | cons alternative rest inductionHypothesis =>
      exact ⟨hleft.1, inductionHypothesis hleft.2⟩

theorem AltsTopological.reverse {alts : List Alt}
    (halts : AltsTopological alts) :
    AltsTopological alts.reverse := by
  induction alts with
  | nil => trivial
  | cons alternative rest inductionHypothesis =>
      have tail := inductionHypothesis halts.2
      have head : AltsTopological [alternative] := ⟨halts.1, trivial⟩
      simpa using tail.append head

theorem AltsTopological.of_append_left {left right : List Alt}
    (halts : AltsTopological (left ++ right)) : AltsTopological left := by
  induction left with
  | nil => trivial
  | cons alternative rest inductionHypothesis =>
      exact ⟨halts.1, inductionHypothesis halts.2⟩

theorem AltsTopological.of_append_right {left right : List Alt}
    (halts : AltsTopological (left ++ right)) : AltsTopological right := by
  induction left with
  | nil => simpa using halts
  | cons alternative rest inductionHypothesis =>
      exact inductionHypothesis halts.2

/-- A successful nearest-delimiter split exposes topological ownership for
    the frame entry, the protected prefix, and the outer suffix separately. -/
theorem AltsTopological.splitCatchActive {alts : List Alt}
    {split : CatchSplit Subst} (halts : AltsTopological alts)
    (found : PLeaTTa.splitCatchActive alts = some split) :
    HasTopologicalSubst split.frame.entry ∧
      AltsTopological split.protectedAlts ∧
      AltsTopological split.outer := by
  have reassembled := PLeaTTa.splitCatchActive_reassembles alts
  rw [found] at reassembled
  rw [reassembled] at halts
  have protectedTopological : AltsTopological split.protectedAlts :=
    halts.of_append_left
  have suffixTopological :
      AltsTopological (.catchActive split.frame :: split.outer) :=
    halts.of_append_right
  exact ⟨suffixTopological.1, protectedTopological, suffixTopological.2⟩

theorem AltsTopological.cons_barrier {alts : List Alt}
    (halts : AltsTopological alts) :
    AltsTopological (Alt.barrier :: alts) := by
  exact ⟨trivial, halts⟩

theorem AltsTopological.cons_branch {goals : List Goal} {b : Subst}
    {alts : List Alt} (hb : HasTopologicalSubst b)
    (halts : AltsTopological alts) :
    AltsTopological (Alt.br goals b :: alts) := by
  exact ⟨hb, halts⟩

theorem AltsTopological.cons_catchActive {frame : CatchFrame}
    {alts : List Alt} (hentry : HasTopologicalSubst frame.entry)
    (halts : AltsTopological alts) :
    AltsTopological (.catchActive frame :: alts) := by
  exact ⟨hentry, halts⟩

theorem AltsTopological.cons_catchDormant {frame : CatchFrame}
    {protectedAlts alts : List Alt}
    (hentry : HasTopologicalSubst frame.entry)
    (hprotected : AltsTopological protectedAlts)
    (halts : AltsTopological alts) :
    AltsTopological (.catchDormant frame protectedAlts :: alts) := by
  exact ⟨⟨hentry, hprotected⟩, halts⟩

theorem altsTopological_map_branch {α : Type} (items : List α)
    (goals : α → List Goal) (b : Subst)
    (hb : HasTopologicalSubst b) :
    AltsTopological (items.map (fun item => Alt.br (goals item) b)) := by
  induction items with
  | nil => trivial
  | cons item rest inductionHypothesis =>
      exact ⟨hb, inductionHypothesis⟩

theorem AltsTopological.cutTo (alts : List Alt) (k : Nat)
    (halts : AltsTopological alts) :
    AltsTopological (PLeaTTa.cutTo k alts) := by
  induction alts with
  | nil => simp [PLeaTTa.cutTo, AltsTopological]
  | cons alt rest ih =>
      unfold PLeaTTa.cutTo
      split
      · exact ih halts.2
      · exact halts

theorem AltsTopological.cutToCached (alts : List Alt) (k barriers : Nat)
    (halts : AltsTopological alts) :
    AltsTopological (PLeaTTa.cutToCached k barriers alts).1 := by
  induction alts generalizing barriers with
  | nil => simp [PLeaTTa.cutToCached, AltsTopological]
  | cons alt rest ih =>
      unfold PLeaTTa.cutToCached
      split
      · exact ih _ halts.2
      · exact halts

theorem AltsTopological.cutToTracked (alts : List Alt) (k : Nat)
    (barriers : Option Nat) (halts : AltsTopological alts) :
    AltsTopological (PLeaTTa.cutToTracked k barriers alts).1 := by
  cases barriers with
  | none => exact halts.cutTo alts k
  | some depth => exact halts.cutToCached alts k depth

private theorem pull_preserves_topological_alts (alts : List Alt) :
    ∀ c, c.alts = alts → ConfTopological c → ConfTopological (pull c) := by
  induction alts with
  | nil =>
      intro c halts htop
      have hpull : pull c =
          { c with cur := none, alts := [], barriers :=
              resetBarrierCache c.barriers } := by
        unfold pull
        rw [halts]
        cases c.barriers <;> rfl
      rw [hpull]
      constructor
      · intro goals b hactive
        simp at hactive
      · simp [AltsTopological]
  | cons alt rest ih =>
      intro c halts htop
      rcases htop with ⟨hcur, haltsTopo⟩
      rw [halts] at haltsTopo
      cases alt with
      | barrier =>
          have hrest : AltsTopological rest := haltsTopo.2
          have hc : ConfTopological
              { c with alts := rest, barriers :=
                  popBarrierCache c.barriers } := by
            constructor
            · intro goals b hactive
              exact hcur goals b (by simpa using hactive)
            · exact hrest
          have hpull := ih
            { c with alts := rest, barriers :=
                popBarrierCache c.barriers } rfl hc
          have hpullEq : pull c =
              pull { c with alts := rest, barriers :=
                popBarrierCache c.barriers } := by
            unfold pull
            rw [halts]
            cases c.barriers <;> rfl
          rw [hpullEq]
          exact hpull
      | br goals b =>
          have hb : HasTopologicalSubst b := haltsTopo.1
          have hrest : AltsTopological rest := haltsTopo.2
          rw [pull_of_alts_branch c goals b rest halts]
          constructor
          · intro activeGoals activeSubst hactive
            simp at hactive
            rcases hactive with ⟨rfl, rfl⟩
            exact hb
          · exact hrest
      | catchActive frame =>
          have hrest : AltsTopological rest := haltsTopo.2
          have hc : ConfTopological
              { c with alts := rest, barriers :=
                  popBarrierCache c.barriers } := by
            constructor
            · intro goals b hactive
              exact hcur goals b (by simpa using hactive)
            · exact hrest
          have hpull := ih
            { c with alts := rest, barriers :=
                popBarrierCache c.barriers } rfl hc
          have hpullEq : pull c =
              pull { c with alts := rest, barriers :=
                popBarrierCache c.barriers } := by
            unfold pull
            rw [halts]
            cases c.barriers <;> rfl
          rw [hpullEq]
          exact hpull
      | catchDormant frame protectedAlts =>
          have hentry : HasTopologicalSubst frame.entry := haltsTopo.1.1
          have hprotected : AltsTopological protectedAlts := haltsTopo.1.2
          have hrest : AltsTopological rest := haltsTopo.2
          have hnew : AltsTopological
              (protectedAlts ++ .catchActive frame :: rest) :=
            hprotected.append (hrest.cons_catchActive hentry)
          unfold pull
          rw [halts]
          cases c.barriers <;>
            simp only [pullAuxTracked, pullAuxCached, pullAux,
              addBarrierCache, Option.map]
          all_goals
            constructor
            · intro goals b hactive
              simp at hactive
            · exact hnew

theorem ConfTopological.pull (c : Conf) (htop : ConfTopological c) :
    ConfTopological (pull c) := by
  exact pull_preserves_topological_alts c.alts c rfl htop

theorem ConfTopological.active {c : Conf} {goals : List Goal} {b : Subst}
    (htop : ConfTopological c) (hcur : c.cur = some (goals, b)) :
    HasTopologicalSubst b :=
  htop.1 goals b hcur

theorem confTopological_of_fields (c : Conf)
    (hcur : ∀ goals b, c.cur = some (goals, b) → HasTopologicalSubst b)
    (halts : AltsTopological c.alts) : ConfTopological c :=
  ⟨hcur, halts⟩

theorem ConfTopological.frame {source target : Conf}
    (htop : ConfTopological source) (hcur : target.cur = source.cur)
    (halts : target.alts = source.alts) : ConfTopological target := by
  constructor
  · intro goals b hactive
    exact htop.1 goals b (by simpa [hcur] using hactive)
  · simpa [halts] using htop.2

theorem ConfTopological.replaceActive {c : Conf} {oldGoals newGoals : List Goal}
    {b : Subst} (htop : ConfTopological c)
    (hactive : c.cur = some (oldGoals, b)) :
    ConfTopological { c with cur := some (newGoals, b) } := by
  have hb := htop.active hactive
  constructor
  · intro goals branchSubst hcur
    simp only [Option.some.injEq, Prod.mk.injEq] at hcur
    rcases hcur with ⟨rfl, rfl⟩
    exact hb
  · exact htop.2

theorem ConfTopological.clearActive {c : Conf}
    (htop : ConfTopological c) :
    ConfTopological { c with cur := none } := by
  constructor
  · intro goals b hcur
    simp at hcur
  · exact htop.2

theorem confTopological_clear_with_alts (c : Conf) (alts : List Alt)
    (halts : AltsTopological alts) :
    ConfTopological { c with cur := none, alts := alts } := by
  constructor
  · intro goals b hcur
    simp at hcur
  · exact halts

theorem resolveAlts_topological (cs : List Clause) (argsv args : List Atom)
    (res : Atom) (rest : List Goal) (b : Subst) (qterm : Atom)
    (bc counter : Nat)
    (hb : HasTopologicalSubst b) :
    AltsTopological
      (resolveAlts cs argsv args res rest b qterm bc counter).1 := by
  unfold resolveAlts
  let resv := subst b res
  let addClause := fun (acc : List Alt × Nat) (cl : Clause) =>
    if cl.params.length != argsv.length then acc
    else if !prologMatchCompatList argsv cl.params then acc
    else if !prologMatchCompat resv cl.result then acc
    else
      let k := acc.2
      let copied := freshenResolutionClause argsv args res rest b qterm k bc cl
      let ps := copied.params
      let rt := copied.result
      let body := copied.body
      let gs := Goal.eq (Atom.expr (args ++ [res]))
          (Atom.expr (ps ++ [rt])) :: body ++ rest
      (Alt.br gs b :: acc.1, k + 1)
  have preserve : ∀ (clauses : List Clause) (acc : List Alt × Nat),
      AltsTopological acc.1 →
      AltsTopological (clauses.foldl addClause acc).1 := by
    intro clauses
    induction clauses with
    | nil =>
        intro acc hacc
        exact hacc
    | cons cl tail ih =>
        intro acc hacc
        simp only [List.foldl_cons]
        apply ih
        dsimp [addClause]
        split
        · exact hacc
        · split
          · exact hacc
          · split
            · exact hacc
            · exact AltsTopological.cons_branch hb hacc
  change AltsTopological
    (cs.foldl addClause ([], counter)).1.reverse
  exact (preserve cs ([], counter) (by
    trivial)).reverse

theorem smatchAlts_topological (w : PWorld) (counter : Nat) (b : Subst)
    (pat : Atom) (rest : List Goal) (qterm : Atom)
    (hb : HasTopologicalSubst b) :
    AltsTopological (smatchAlts w counter b pat rest qterm).1 := by
  unfold smatchAlts
  split
  rename_i sp q hview
  let query := subst b q
  let space := subst b sp
  let addAtom := fun (acc : List Alt) (a : Atom) =>
    let suffix := resolutionFreshSuffix [query] q rest b qterm counter
    let a' := renameAtomSuffixShared suffix a
    if matchCompat query a' then
      Alt.br (Goal.eq q a' :: rest) b :: acc
    else
      acc
  have preserve : ∀ (atoms : List Atom) (acc : List Alt),
      AltsTopological acc →
      AltsTopological (atoms.foldl addAtom acc) := by
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
        · exact AltsTopological.cons_branch hb hacc
        · exact hacc
  have hfold := preserve (w.atomCandidates space query) [] (by trivial)
  change AltsTopological
    ((w.atomCandidates space query).foldl addAtom []).reverse
  exact hfold.reverse

theorem unionReverseAlts_topological (args : List Atom) (res : Atom)
    (rest : List Goal) (b : Subst) (branches : List Alt)
    (hb : HasTopologicalSubst b)
    (hbranches : unionReverseAlts args res rest b = some branches) :
    AltsTopological branches := by
  cases args with
  | nil => simp [unionReverseAlts] at hbranches
  | cons x tail =>
      cases tail with
      | nil => simp [unionReverseAlts] at hbranches
      | cons y extra =>
          cases extra with
          | cons z zs => simp [unionReverseAlts] at hbranches
          | nil =>
              cases hchain : chainListM (subst b res) with
              | none => simp [unionReverseAlts, hchain] at hbranches
              | some items =>
                  simp only [unionReverseAlts, hchain, Option.some.injEq]
                    at hbranches
                  subst branches
                  exact altsTopological_map_branch (chainSplits items)
                    (fun split => Goal.eq x (chainOf split.1) ::
                      Goal.eq y (chainOf split.2) :: rest) b hb

/-- Every actual semantic step preserves topological substitutions in both
    the active branch and all stored alternatives. -/
theorem Step.preserves_confTopological {prog : Prog} {gt : GroundingTable}
    {c d : Conf} (hstep : Step prog gt c d)
    (htop : ConfTopological c) : ConfTopological d := by
  cases hstep with
  | pull_next c h hne =>
      exact htop.pull
  | answer c b h =>
      apply ConfTopological.pull
      constructor
      · intro goals branchSubst hcur
        simp at hcur
      · exact htop.2
  | eq_ok c x y rest b b' h hu =>
      have hb := htop.active h
      rcases hb with ⟨topological⟩
      have hnext : HasTopologicalSubst (trimFor rest c.qterm b') := by
        exact ⟨SubstTopological.trimFor rest c.qterm b'
          (unifyB_topological b x y b' topological hu)⟩
      constructor
      · intro goals branchSubst hcur
        simp only [Option.some.injEq, Prod.mk.injEq] at hcur
        rcases hcur with ⟨rfl, rfl⟩
        exact hnext
      · exact htop.2
  | eq_fail c x y rest b h hu =>
      apply ConfTopological.pull
      constructor
      · intro goals branchSubst hcur
        simp at hcur
      · exact htop.2
  | compileAlias_ok c x y rest b b' h hu =>
      have hb := htop.active h
      rcases hb with ⟨topological⟩
      have hnext : HasTopologicalSubst (trimFor rest c.qterm b') := by
        exact ⟨SubstTopological.trimFor rest c.qterm b'
          (unifyB_topological b x y b' topological hu)⟩
      constructor
      · intro goals branchSubst hcur
        simp only [Option.some.injEq, Prod.mk.injEq] at hcur
        rcases hcur with ⟨rfl, rfl⟩
        exact hnext
      · exact htop.2
  | compileAlias_fail c x y rest b h hu =>
      apply ConfTopological.pull
      constructor
      · intro goals branchSubst hcur
        simp at hcur
      · exact htop.2
  | cut_at c k rest b h =>
      have hb := htop.active h
      constructor
      · intro goals branchSubst hcur
        simp only [Option.some.injEq, Prod.mk.injEq] at hcur
        rcases hcur with ⟨rfl, rfl⟩
        exact hb
      · exact htop.2.cutToTracked c.alts k c.barriers
  | cut_untagged c rest b h =>
      apply ConfTopological.pull
      constructor
      · intro goals branchSubst hcur
        simp at hcur
      · exact htop.2
  | call_data c f args res rest b h he g hg =>
      exact htop.replaceActive h
  | call_partial c f args res rest b h hne hna g hg =>
      exact htop.replaceActive h
  | call_table_cached c f args res rest b answers h hcan hcache =>
      have hb := htop.active h
      have hnew := (altsTopological_map_branch answers
        (fun ans => Goal.eq res ans :: rest) b hb).append htop.2
      apply ConfTopological.pull
      constructor
      · intro goals branchSubst hcur
        simp at hcur
      · exact hnew
  | call_resolve c f args res rest b branches counter' h hne ha hres =>
      have hb := htop.active h
      have hbranches := resolveAlts_topological
        (c.world.resolutionCandidates f args.length)
        (args.map (subst b)) args res rest b c.qterm
        (barrierDepth c + 1) c.counter hb
      rw [hres] at hbranches
      have hnew := hbranches.append htop.2.cons_barrier
      apply ConfTopological.pull
      constructor
      · intro goals branchSubst hcur
        simp at hcur
      · exact hnew
  | bin_partial c op args res rest b hunder h g hg =>
      exact htop.replaceActive h
  | bin_local_translate c op args res rest b goals h hnp hlocal =>
      exact htop.replaceActive h
  | bin_gettype c args res rest b ts counter' h hnp hlocal ho =>
      have hb := htop.active h
      have hext : AltsTopological
          (localGetTypeExtensionAlts c.world
            ((args.map (subst b)).headD (Atom.sym "?")) res rest b) := by
        unfold localGetTypeExtensionAlts
        split
        · simp [AltsTopological]
        · exact AltsTopological.cons_branch hb (by
            simp [AltsTopological])
      have hnew := (altsTopological_map_branch ts
        (fun t => Goal.eq res t :: rest) b hb).append
          (hext.append htop.2)
      apply ConfTopological.pull
      constructor
      · intro goals branchSubst hcur
        simp at hcur
      · simpa [List.append_assoc] using hnew
  | bin_getmetatype c args res rest b mt h hnp hlocal hmt g hg =>
      exact htop.replaceActive h
  | bin_nonstrict_ok c op args res rest b rs h hnp hlocal hns hnso hr =>
      have hb := htop.active h
      have hnew := (altsTopological_map_branch rs
        (fun r => Goal.eq res (canonBool r) :: rest) b hb).append htop.2
      apply ConfTopological.pull
      constructor
      · intro goals branchSubst hcur
        simp at hcur
      · exact hnew
  | bin_nonstrict_fail c op args res rest b h hnp hlocal hns hnso hr =>
      apply ConfTopological.pull
      constructor
      · intro goals branchSubst hcur
        simp at hcur
      · exact htop.2
  | bin_ok c op args res rest b rs h hg hnp hlocal hspecial hnm hr =>
      have hb := htop.active h
      have hnew := (altsTopological_map_branch rs
        (fun r => Goal.eq res (canonBool r) :: rest) b hb).append htop.2
      apply ConfTopological.pull
      constructor
      · intro goals branchSubst hcur
        simp at hcur
      · exact hnew
  | bin_mode c op args res rest b x y h hnp hlocal hns hop hav hng hrv g hg =>
      exact htop.replaceActive h
  | bin_mode_fail c op args res rest b h hnp hlocal hns hop hng hrv hnav =>
      apply ConfTopological.pull
      constructor
      · intro goals branchSubst hcur
        simp at hcur
      · exact htop.2
  | bin_fail c op args res rest b h hnp hlocal hns hnmode hgnd hr =>
      apply ConfTopological.pull
      constructor
      · intro goals branchSubst hcur
        simp at hcur
      · exact htop.2
  | bin_union_reverse c args res rest b alts h hnp hlocal hns hnmode hgnd hur =>
      have hb := htop.active h
      have hnew := (unionReverseAlts_topological args res rest b alts hb hur)
        |>.append htop.2
      apply ConfTopological.pull
      constructor
      · intro goals branchSubst hcur
        simp at hcur
      · exact hnew
  | bin_delay c op args res rest b h hnp hlocal hns hnmode hgnd hrest =>
      exact htop.replaceActive h
  | bin_flounder c op args res rest b h hnp hlocal hns hnmode hgnd hrest =>
      apply ConfTopological.pull
      constructor
      · intro goals branchSubst hcur
        simp at hcur
      · exact htop.2
  | ite_true c cond thn els res rest b h hc =>
      exact htop.replaceActive h
  | ite_else c cond thn els res rest b h hc =>
      exact htop.replaceActive h
  | amb c branches res rest b h =>
      have hb := htop.active h
      have hnew := (altsTopological_map_branch branches
        (fun branch => ambBranchGoals res branch ++ rest) b hb)
        |>.append htop.2
      apply ConfTopological.pull
      constructor
      · intro goals branchSubst hcur
        simp at hcur
      · exact hnew
  | smatch c pat rest b alts counter' h hs =>
      have hb := htop.active h
      have hbranches := smatchAlts_topological c.world c.counter b pat rest
        c.qterm hb
      rw [hs] at hbranches
      have hnew := hbranches.append htop.2
      apply ConfTopological.pull
      constructor
      · intro goals branchSubst hcur
        simp at hcur
      · exact hnew
  | spread c v res rest b elems h he =>
      have hb := htop.active h
      have hnew := (altsTopological_map_branch elems
        (fun item => Goal.eq res item :: rest) b hb).append htop.2
      apply ConfTopological.pull
      constructor
      · intro goals branchSubst hcur
        simp at hcur
      · exact hnew
  | callDyn_call c hd f args res rest b h hf hdef =>
      exact htop.replaceActive h
  | callDyn_bin c hd f args res rest b h hf he hbin =>
      exact htop.replaceActive h
  | callDyn_symdata c hd f args res rest b h hf he hnb g hg =>
      exact htop.replaceActive h
  | callDyn_partial c hd args res rest b base boundList bound h hns hp hbd g hg =>
      exact htop.replaceActive h
  | callDyn_data c hd args res rest b h hns hnp g hg =>
      exact htop.replaceActive h
  | evalg_ok c v res rest b t gs m profileWorld profileGoals newgoals h ho hs hng =>
      apply ConfTopological.frame (htop.replaceActive h) <;> rfl
  | evalg_err c v res rest b e h ho g hg =>
      exact htop.replaceActive h
  | catch_direct_error c tmpl sub res rest b err h hc =>
      apply ConfTopological.frame (htop.replaceActive h) <;> rfl
  | catch_direct_answers c tmpl sub res rest b answers h hc =>
      have hb := htop.active h
      have hnew := (altsTopological_map_branch answers
        (fun inst => Goal.eq res inst :: rest) b hb).append htop.2
      apply ConfTopological.pull
      constructor
      · intro goals branchSubst hcur
        simp at hcur
      · exact hnew
  | catch_stream_enter c tmpl sub res rest b h hc =>
      have hb := htop.active h
      constructor
      · intro goals binding hcur
        simp only [enterStreamingCatch, Option.some.injEq, Prod.mk.injEq]
          at hcur
        rcases hcur with ⟨rfl, rfl⟩
        exact hb
      · exact htop.2.cons_catchActive hb
  | catch_stream_exit c template result rest b b' h hu =>
      have hb := htop.active h
      rcases hb with ⟨topological⟩
      have hb' : HasTopologicalSubst b' :=
        ⟨unifyB_topological b result template b' topological hu⟩
      cases found : splitCatchActive c.alts with
      | none =>
          simp only [exitStreamingCatch, found]
          exact ConfTopological.pull _ htop.clearActive
      | some split =>
          have pieces := htop.2.splitCatchActive found
          simp only [exitStreamingCatch, found]
          constructor
          · intro goals binding hcur
            simp only [Option.some.injEq, Prod.mk.injEq] at hcur
            rcases hcur with ⟨rfl, rfl⟩
            exact hb'
          · exact AltsTopological.cons_catchDormant
              (frame := split.frame)
              (protectedAlts := split.protectedAlts)
              (alts := split.outer) pieces.1 pieces.2.1 pieces.2.2
  | catch_stream_exit_fail c template result rest b h hu =>
      exact ConfTopological.pull _ htop.clearActive
  | catch_stream_error c _ op args res rest b err h herr hc =>
      cases found : splitCatchActive c.alts with
      | none => simp [catchErrorSuccessor?, found] at hc
      | some split =>
          have pieces := htop.2.splitCatchActive found
          simp only [catchErrorSuccessor?, found, Option.map_some,
            Option.some.injEq] at hc
          cases hc
          constructor
          · intro goals binding hcur
            simp only [Option.some.injEq, Prod.mk.injEq] at hcur
            rcases hcur with ⟨rfl, rfl⟩
            exact pieces.1
          · exact pieces.2.2
  | softcut_some c d tmpl sub thn els rest b h hrun hdone hne =>
      have hb := htop.active h
      have hnew := (altsTopological_map_branch d.answerValues
        (fun inst => Goal.eq tmpl inst :: thn ++ rest) b hb).append htop.2
      apply ConfTopological.pull
      constructor
      · intro goals branchSubst hcur
        simp at hcur
      · exact hnew
  | softcut_none c d tmpl sub thn els rest b h hrun hdone he =>
      apply ConfTopological.frame (htop.replaceActive h) <;> rfl
  | transaction_some c d tmpl sub rest b h hrun hdone hne =>
      have hb := htop.active h
      have hnew := (altsTopological_map_branch d.answerValues
        (fun inst => Goal.eq tmpl inst :: rest) b hb).append htop.2
      apply ConfTopological.pull
      constructor
      · intro goals branchSubst hcur
        simp at hcur
      · exact hnew
  | transaction_none c d tmpl sub rest b h hrun hdone he =>
      apply ConfTopological.pull
      constructor
      · intro goals branchSubst hcur
        simp at hcur
      · exact htop.2
  | retract_matched c payload res rest b result functor before selected after
      counter' h scan =>
      have active := htop.active h
      rcases active with ⟨topological⟩
      rcases retractPredicateDispatch_matched_unify c.world gt c.counter b
          payload functor before selected after result counter' scan with
        ⟨left, right, unified⟩
      have resultTopological : HasTopologicalSubst result :=
        ⟨unifyB_topological b left right result topological unified⟩
      constructor
      · intro goals branchSubst hcur
        simp only [Option.some.injEq, Prod.mk.injEq] at hcur
        rcases hcur with ⟨rfl, rfl⟩
        exact resultTopological
      · exact htop.2
  | retract_missing c payload res rest b counter' h scan =>
      apply ConfTopological.frame (htop.replaceActive h) <;> rfl
  | retract_malformed c payload res rest b h scan =>
      apply ConfTopological.pull
      constructor
      · intro goals branchSubst hcur
        simp at hcur
      · exact htop.2
  | wact_ok c op args res r rest b world' counter' h notRetract hw =>
      apply ConfTopological.frame (htop.replaceActive h) <;> rfl
  | wact_fail c op args res rest b h notRetract hw =>
      apply ConfTopological.pull
      constructor
      · intro goals branchSubst hcur
        simp at hcur
      · exact htop.2
  | onceg c tmpl sub res rest b h =>
      have hb := htop.active h
      have hnew : AltsTopological
          (Alt.br (sub ++ [Goal.cutAt (barrierDepth c + 1),
              Goal.eq res tmpl] ++ rest) b :: Alt.barrier :: c.alts) :=
        AltsTopological.cons_branch hb htop.2.cons_barrier
      apply ConfTopological.pull
      constructor
      · intro goals branchSubst hcur
        simp at hcur
      · exact hnew
  | findall c d tmpl sub res rest b h hrun hdone =>
      apply ConfTopological.frame (htop.replaceActive h) <;> rfl
  | call_table_compute c d f args res rest b tres h hcan hcache htres hrun hdone =>
      have hb := htop.active h
      have hnew := (altsTopological_map_branch d.answerValues
        (fun ans => Goal.eq res ans :: rest) b hb).append htop.2
      apply ConfTopological.pull
      constructor
      · intro goals branchSubst hcur
        simp at hcur
      · exact hnew

theorem StepStar.preserves_confTopological {prog : Prog} {gt : GroundingTable}
    {c d : Conf} (hrun : StepStar prog gt c d)
    (htop : ConfTopological c) : ConfTopological d := by
  revert htop
  apply StepStar.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun source target _ =>
      ConfTopological source → ConfTopological target)
    (motive_3 := fun _ _ _ _ => True)
    (t := hrun)
  all_goals try { intros; trivial }
  case tail =>
    intro source middle target hstep htail hstepTrivial htailTopological
      hsource
    exact htailTopological (hstep.preserves_confTopological hsource)

theorem confTopological_of_empty (c : Conf) (goals : List Goal)
    (hcur : c.cur = some (goals, ([] : Subst)))
    (halts : c.alts = []) : ConfTopological c := by
  constructor
  · intro activeGoals b hactive
    rw [hcur] at hactive
    simp only [Option.some.injEq, Prod.mk.injEq] at hactive
    rcases hactive with ⟨rfl, rfl⟩
    exact hasTopologicalSubst_nil
  · rw [halts]
    trivial

/-- Every active substitution reachable from the standard empty-substitution,
    empty-alternative start has a constructional topological witness. -/
theorem StepStar.active_topological_of_empty {prog : Prog}
    {gt : GroundingTable} {initial final : Conf} (goals : List Goal)
    (hrun : StepStar prog gt initial final)
    (hcur : initial.cur = some (goals, ([] : Subst)))
    (halts : initial.alts = []) {finalGoals : List Goal} {b : Subst}
    (hfinal : final.cur = some (finalGoals, b)) :
    HasTopologicalSubst b := by
  exact (hrun.preserves_confTopological
    (confTopological_of_empty initial goals hcur halts)).active hfinal

end PLeaTTa
