-- SPDX-License-Identifier: Apache-2.0

/-
Per-goal correspondence lemmas: for each goal head, the executable `step`
takes a `Step`. These compose into machineMirrorsSpec. Zero sorry — each is
a real proven case (the machine and the relation share their constructions,
so the proof is: unfold `step`, case on the inner matches, apply the matching
`Step` constructor).
-/
import PLeaTTa.Semantics

namespace PLeaTTa

open Metta (Atom Subst GroundingTable ReduceResult callGrounded)

attribute [local simp] finishCatchClean finishTransactionClean
  finishSoftcutClean finishFindallClean finishTableClean

variable (prog : Prog) (gt : GroundingTable) (fuel : Nat)

theorem step_eq (c : Conf) (x y : Atom) (rest : List Goal) (b : Subst)
    (h : c.cur = some (Goal.eq x y :: rest, b)) :
    Step prog gt c (step prog gt fuel c) := by
  cases hu : unifyB b x y with
  | some b' =>
      have : step prog gt fuel c =
          { c with cur := some (rest, trimFor rest c.qterm b') } := by
        unfold step; rw [h]; simp only [hu]
      rw [this]; exact Step.eq_ok c x y rest b b' h hu
  | none =>
      have : step prog gt fuel c = pull { c with cur := none } := by
        unfold step; rw [h]; simp only [hu]
      rw [this]; exact Step.eq_fail c x y rest b h hu

theorem step_pull (c : Conf) (h : c.cur = none) (hne : c.alts ≠ []) :
    Step prog gt c (step prog gt fuel c) := by
  have : step prog gt fuel c = pull c := by unfold step; rw [h]
  rw [this]; exact Step.pull_next c h hne

theorem step_answer (c : Conf) (b : Subst) (h : c.cur = some ([], b)) :
    Step prog gt c (step prog gt fuel c) := by
  have : step prog gt fuel c
      = pull { c with
          cur := none
          answers := subst b c.qterm :: c.answers
          answerKeys :=
            PersistentSubst.atomExactKey (subst b c.qterm) :: c.answerKeys
          answerKeys_sound := by
            simp only [List.map_cons]
            rw [c.answerKeys_sound] } := by
    unfold step; rw [h]
  rw [this]; exact Step.answer c b h

theorem step_cutAt (c : Conf) (k : Nat) (rest : List Goal) (b : Subst)
    (h : c.cur = some (Goal.cutAt k :: rest, b)) :
    Step prog gt c (step prog gt fuel c) := by
  have : step prog gt fuel c
      = { c with
          cur := some (rest, b)
          alts := (cutToTracked k c.barriers c.alts).1
          barriers := (cutToTracked k c.barriers c.alts).2 } := by
    unfold step; rw [h]
  rw [this]; exact Step.cut_at c k rest b h

theorem step_amb (c : Conf) (branches : List (Atom × List Goal)) (res : Atom)
    (rest : List Goal) (b : Subst)
    (h : c.cur = some (Goal.amb branches res :: rest, b)) :
    Step prog gt c (step prog gt fuel c) := by
  have : step prog gt fuel c
      = pull { c with cur := none,
                      alts := branches.map (fun (t, gs) =>
                        Alt.br (gs ++ [Goal.eq res t] ++ rest) b) ++ c.alts } := by
    unfold step; rw [h]
  rw [this]; exact Step.amb c branches res rest b h

theorem step_smatch (c : Conf) (pat : Atom) (rest : List Goal) (b : Subst)
    (h : c.cur = some (Goal.smatch pat :: rest, b)) :
    Step prog gt c (step prog gt fuel c) := by
  cases hs : smatchAlts c.world c.counter b pat rest c.qterm with
  | mk alts counter' =>
      have : step prog gt fuel c
          = pull { c with cur := none, counter := counter',
                          alts := alts ++ c.alts } := by
        unfold step; rw [h]; simp only [hs]
      rw [this]; exact Step.smatch c pat rest b alts counter' h hs

/-! ### The BEq bridge

`Atom`'s Boolean equality is hand-written and kernel-reducible but NOT
lawful in general (grounded floats carry IEEE `==`). Against a literal
SYMBOL, however, it coincides with propositional equality — which is what
the `ite` dispatch tests [SPEC translator.pl:156-162]. -/

theorem beq_symTrue_iff (x : Atom) :
    (x == Atom.sym "True") = true ↔ x = Atom.sym "True" := by
  cases x <;> simp [BEq.beq, Atom.beq]

theorem beq_symTrue_eq_false {x : Atom} (h : x ≠ Atom.sym "True") :
    (x == Atom.sym "True") = false :=
  Bool.eq_false_iff.mpr (fun ht => h ((beq_symTrue_iff x).mp ht))

/-! ### The remaining case lemmas -/

theorem step_cut (c : Conf) (rest : List Goal) (b : Subst)
    (h : c.cur = some (Goal.cut :: rest, b)) :
    Step prog gt c (step prog gt fuel c) := by
  have hstep : step prog gt fuel c = pull { c with cur := none } := by
    unfold step; rw [h]
  rw [hstep]; exact Step.cut_untagged c rest b h

theorem step_onceg (c : Conf) (tmpl : Atom) (sub : List Goal) (res : Atom)
    (rest : List Goal) (b : Subst)
    (h : c.cur = some (Goal.onceg tmpl sub res :: rest, b)) :
    Step prog gt c (step prog gt fuel c) := by
  have hstep : step prog gt fuel c
      = pull { c with cur := none,
                      alts := Alt.br (sub ++ [Goal.cutAt (barrierDepth c + 1),
                                Goal.eq res tmpl] ++ rest) b ::
                              (Alt.barrier :: c.alts),
                      barriers := pushBarrierCache c.barriers } := by
    unfold step; rw [h]
  rw [hstep]; exact Step.onceg c tmpl sub res rest b h

theorem step_spread (c : Conf) (v res : Atom) (rest : List Goal) (b : Subst)
    (h : c.cur = some (Goal.spread v res :: rest, b)) :
    Step prog gt c (step prog gt fuel c) := by
  have hstep : step prog gt fuel c
      = pull { c with cur := none,
                      alts := ((chainListM (subst b v)).getD [subst b v]).map
                        (fun e => Alt.br (Goal.eq res e :: rest) b) ++ c.alts } := by
    unfold step; rw [h]
  rw [hstep]; exact Step.spread c v res rest b _ h rfl

theorem step_wact (c : Conf) (op : String) (args : List Atom) (res : Atom)
    (rest : List Goal) (b : Subst)
    (h : c.cur = some (Goal.wact op args res :: rest, b)) :
    Step prog gt c (step prog gt fuel c) := by
  cases hw : wactDispatch c.world gt c.counter op (args.map (subst b)) with
  | some triple =>
      obtain ⟨r, w', k'⟩ := triple
      have hstep : step prog gt fuel c
          = { c with cur := some (Goal.eq res r :: rest, b),
                     world := w', counter := max c.counter k' } := by
        unfold step; rw [h]; simp only [hw]
      rw [hstep]; exact Step.wact_ok c op args res r rest b w' k' h hw
  | none =>
      have hstep : step prog gt fuel c = pull { c with cur := none } := by
        unfold step; rw [h]; simp only [hw]
      rw [hstep]; exact Step.wact_fail c op args res rest b h hw

theorem step_evalg (c : Conf) (v res : Atom) (rest : List Goal) (b : Subst)
    (h : c.cur = some (Goal.evalg v res :: rest, b)) :
    Step prog gt c (step prog gt fuel c) := by
  cases hce : compileExprFresh (runtimeEnv c.world gt) (c.counter + 1)
      (unchainify 10000 (subst b v)) with
  | ok val =>
      obtain ⟨t, gs, m⟩ := val
      cases hsp : specializeGoals (specializationIsBin gt)
          specializationBuildFuel c.world gs with
      | mk profileWorld profileGoals =>
          let newgoals := tagCutsGoals (barrierDepth c + 1) profileGoals
            ++ [Goal.eq res t] ++ rest
          have hstep : step prog gt fuel c
              = { cur := some (newgoals, b), alts := c.alts,
                  world := profileWorld,
                  counter := advanceCounterPastGoals (max c.counter m)
                    (profileGoals ++ [Goal.eq res t] ++ rest),
                  qterm := c.qterm,
                  answers := c.answers,
                  answerKeys := c.answerKeys,
                  answerKeys_sound := c.answerKeys_sound,
                  barriers := c.barriers } := by
            unfold step; rw [h]; simp only [hce, hsp, newgoals]
          rw [hstep]
          exact Step.evalg_ok c v res rest b t gs m profileWorld profileGoals
            newgoals h hce hsp rfl
  | error e =>
      have hstep : step prog gt fuel c
          = { c with cur := some (Goal.eq res (chainify (unchainify 10000 (subst b v)))
                       :: rest, b),
                     counter := advanceCounterPastAtoms c.counter
                       [chainify (unchainify 10000 (subst b v))] } := by
        unfold step; rw [h]; simp only [hce]
      rw [hstep]
      exact Step.evalg_err c v res rest b e h hce _ rfl

theorem step_ite (c : Conf) (cond : Atom) (thn els : Atom × List Goal)
    (res : Atom) (rest : List Goal) (b : Subst)
    (h : c.cur = some (Goal.ite cond thn els res :: rest, b)) :
    Step prog gt c (step prog gt fuel c) := by
  by_cases hc : subst b cond = Atom.sym "True"
  · have hb : (subst b cond == trueA) = true := by rw [hc]; rfl
    have hstep : step prog gt fuel c
        = { c with cur := some (iteBranchGoals res thn ++ rest, b) } := by
      unfold step; rw [h]; simp only [hb, if_true]
    rw [hstep]; exact Step.ite_true c cond thn els res rest b h hc
  · have hb : (subst b cond == trueA) = false := beq_symTrue_eq_false hc
    have hstep : step prog gt fuel c
        = { c with cur := some (iteBranchGoals res els ++ rest, b) } := by
      unfold step; rw [h]; simp only [hb, Bool.false_eq_true, if_false]
    rw [hstep]; exact Step.ite_else c cond thn els res rest b h hc

theorem step_call (c : Conf) (f : String) (args : List Atom) (res : Atom)
    (rest : List Goal) (b : Subst)
    (h : c.cur = some (Goal.call f args res :: rest, b)) :
    Step prog gt c (step prog gt fuel c) ∨ nestedRunHead c := by
  cases hcan : c.world.canTableCall f (args.map (subst b)) with
  | true =>
      cases hcache : c.world.tableLookup (tableKey f (args.map (subst b))) with
      | some answers =>
          have hstep : step prog gt fuel c =
              pull { c with cur := none,
                            counter := advanceCounterPastAtoms c.counter answers,
                            alts := answers.map (fun ans =>
                              Alt.br (Goal.eq res ans :: rest) b) ++ c.alts } := by
            unfold step; rw [h]; simp only [hcan, if_true, hcache]
          rw [hstep]
          exact Or.inl (Step.call_table_cached c f args res rest b answers h hcan hcache)
      | none =>
          have ht : tableRunHead c :=
            ⟨f, args, res, rest, b, h, by
              simp [PWorld.needsTableCompute, hcan, hcache]⟩
          have hn : nestedRunHead c :=
            Or.inr (Or.inr (Or.inr (Or.inl ht)))
          exact Or.inr hn
  | false =>
      cases he : (c.world.clauseHeadCandidates f).isEmpty with
      | true =>
          have hstep : step prog gt fuel c
              = { c with cur := some (Goal.eq res (chainOf (Atom.sym f :: args))
                           :: rest, b) } := by
            unfold step; rw [h]; simp [hcan, he]
          rw [hstep]
          exact Or.inl (Step.call_data c f args res rest b h (by simpa using he) _ rfl)
      | false =>
          cases ha : (c.world.resolutionCandidates f args.length).any
              (fun cl => cl.params.length == args.length) with
          | false =>
              have hstep : step prog gt fuel c
                  = { c with cur := some (Goal.eq res
                        (chainOf [Atom.sym "partial", Atom.sym f, chainOf args])
                        :: rest, b) } := by
                unfold step; rw [h]
                simp [hcan, he, ha]
              rw [hstep]
              exact Or.inl (Step.call_partial c f args res rest b h
                (by simpa using he) (by simp [ha]) _ rfl)
          | true =>
              rcases hres : resolveAlts
                  (c.world.resolutionCandidates f args.length)
                  (args.map (subst b))
                  args res rest b c.qterm (barrierDepth c + 1) c.counter
                with ⟨branches, counter'⟩
              have hstep : step prog gt fuel c
                  = pull { c with cur := none, counter := counter',
                                  alts := branches ++ (Alt.barrier :: c.alts),
                                  barriers := pushBarrierCache c.barriers } := by
                unfold step; rw [h]
                simp [hcan, he, ha, hres]
              rw [hstep]
              exact Or.inl (Step.call_resolve c f args res rest b branches counter' h
                (by simpa using he) ha hres)

theorem step_callDyn (c : Conf) (hd : Atom) (args : List Atom) (res : Atom)
    (rest : List Goal) (b : Subst)
    (h : c.cur = some (Goal.callDyn hd args res :: rest, b)) :
    Step prog gt c (step prog gt fuel c) := by
  cases hhd : subst b hd with
  | sym f =>
      cases he : (c.world.clauseHeadCandidates f).isEmpty with
      | false =>
          have hstep : step prog gt fuel c
              = { c with cur := some (Goal.call f args res :: rest, b) } := by
            unfold step; rw [h]; simp only [hhd, he, Bool.not_false, if_true]
          rw [hstep]
          exact Step.callDyn_call c hd f args res rest b h hhd (by simpa using he)
      | true =>
          cases hbin : (Metta.GroundingTable.lookup gt f).isSome with
          | true =>
              have hstep : step prog gt fuel c
                  = { c with cur := some (Goal.bin f args res :: rest, b) } := by
                unfold step; rw [h]
                simp only [hhd, he, Bool.not_true, Bool.false_eq_true, if_false,
                  hbin, if_true]
              rw [hstep]
              exact Step.callDyn_bin c hd f args res rest b h hhd
                (by simpa using he) hbin
          | false =>
              have hnb : Metta.GroundingTable.lookup gt f = none := by
                cases hlk : Metta.GroundingTable.lookup gt f with
                | none => rfl
                | some v => rw [hlk] at hbin; simp at hbin
              have hstep : step prog gt fuel c
                  = { c with cur := some (Goal.eq res
                        (chainOf (Atom.sym f :: args)) :: rest, b) } := by
                unfold step; rw [h]
                simp only [hhd, he, Bool.not_true, Bool.false_eq_true, if_false,
                  hbin]
              rw [hstep]
              exact Step.callDyn_symdata c hd f args res rest b h hhd
                (by simpa using he) hnb _ rfl
  | var w =>
      have hcl : chainListM (Atom.var w) = none := rfl
      have hstep : step prog gt fuel c
          = { c with cur := some (Goal.eq res
                (chainOf (Atom.var w :: args)) :: rest, b) } := by
        unfold step; rw [h]; simp only [hhd, hcl]
      rw [hstep]
      refine Step.callDyn_data c hd args res rest b h ?_ ?_ _ ?_
      · intro f; rw [hhd]; simp
      · intro base boundList; rw [hhd]; simp [chainListM]
      · rw [hhd]
  | gnd gr =>
      have hcl : chainListM (Atom.gnd gr) = none := rfl
      have hstep : step prog gt fuel c
          = { c with cur := some (Goal.eq res
                (chainOf (Atom.gnd gr :: args)) :: rest, b) } := by
        unfold step; rw [h]; simp only [hhd, hcl]
      rw [hstep]
      refine Step.callDyn_data c hd args res rest b h ?_ ?_ _ ?_
      · intro f; rw [hhd]; simp
      · intro base boundList; rw [hhd]; simp [chainListM]
      · rw [hhd]
  | expr es =>
      unfold step; rw [h]; simp only [hhd]
      split
      · rename_i base boundList heq
        refine Step.callDyn_partial c hd args res rest b base boundList _ h
          ?_ ?_ rfl _ ?_
        · intro f; rw [hhd]; simp
        · rw [hhd]; exact heq
        · rfl
      · rename_i x hno
        refine Step.callDyn_data c hd args res rest b h ?_ ?_ _ ?_
        · intro f; rw [hhd]; simp
        · intro base boundList; rw [hhd]
          intro hcontra
          exact hno base boundList hcontra
        · rw [hhd]

set_option maxHeartbeats 1600000 in
theorem step_bin_nonlocal (c : Conf) (op : String) (args : List Atom)
    (res : Atom)
    (rest : List Goal) (b : Subst)
    (h : c.cur = some (Goal.bin op args res :: rest, b))
    (hlocal : localTranslatePredicateGoals? c.world gt op
      (args.map (subst b)) res rest = none) :
    Step prog gt c (step prog gt fuel c) := by
  cases h1 : (binArity op != 0
      && decide ((args.map (subst b)).length < binArity op)) with
  | true =>
      have hb : binArity op ≠ 0 ∧ (args.map (subst b)).length < binArity op := by
        rw [Bool.and_eq_true] at h1
        exact ⟨by simpa using h1.1, by simpa using h1.2⟩
      have hstep : step prog gt fuel c
          = { c with cur := some (Goal.eq res (chainOf [Atom.sym "partial",
                Atom.sym op, chainOf (args.map (subst b))]) :: rest, b) } := by
        unfold step; rw [h]; simp only [h1, if_true]
      rw [hstep]
      exact Step.bin_partial c op args res rest b hb h _ rfl
  | false =>
      have hnp : ¬ (binArity op ≠ 0
          ∧ (args.map (subst b)).length < binArity op) := by
        intro hc
        have ht : (binArity op != 0
            && decide ((args.map (subst b)).length < binArity op)) = true := by
          rw [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
          exact hc
        rw [h1] at ht; exact Bool.false_ne_true ht
      by_cases hgt : op = "get-type"
      · subst hgt
        rcases hty : getTypeP c.world 100 c.counter
            ((args.map (subst b)).headD (Atom.sym "?")) with ⟨ts, c'⟩
        have hstep : step prog gt fuel c
            = pull { c with cur := none,
                            counter := advanceCounterPastAtoms (max c.counter c') ts,
                            alts := ts.map (fun t =>
                              Alt.br (Goal.eq res t :: rest) b) ++
                              localGetTypeExtensionAlts c.world
                                ((args.map (subst b)).headD (Atom.sym "?"))
                                res rest b ++ c.alts } := by
          unfold step; rw [h]
          simp only [binResolvedStep, hlocal, h1, Bool.false_eq_true, if_false, beq_self_eq_true,
            if_true, hty]
        rw [hstep]
        exact Step.bin_gettype c args res rest b ts c' h hnp hlocal hty
      · have hgt' : (op == "get-type") = false := by
          simp [hgt]
        by_cases hgm : op = "get-metatype"
        · subst hgm
          have hstep : Step prog gt c (step prog gt fuel c) := by
            unfold step; rw [h]
            simp only [binResolvedStep, hlocal, h1, Bool.false_eq_true, if_false, hgt',
              beq_self_eq_true, if_true]
            exact Step.bin_getmetatype c args res rest b _ h hnp hlocal rfl _ rfl
          exact hstep
        · have hgm' : (op == "get-metatype") = false := by
            simp [hgm]
          cases hns2 : nonstrictOps.contains op with
          | true =>
              cases hcg : callGrounded gt op (args.map (subst b)) with
              | ok rs =>
                  have hstep : step prog gt fuel c
                      = pull { c with cur := none,
                                      counter := advanceCounterPastAtoms c.counter rs,
                                      alts := rs.map (fun r =>
                                        Alt.br (Goal.eq res (canonBool r) :: rest) b) ++ c.alts } := by
                    unfold step; rw [h]
                    simp only [binResolvedStep, hlocal, h1, Bool.false_eq_true, if_false, hgt', hgm',
                      hns2, if_true, hcg]
                  rw [hstep]
                  exact Step.bin_nonstrict_ok c op args res rest b rs h hnp
                    hlocal ⟨hgt, hgm⟩ hns2 hcg
              | noReduce =>
                  have hstep : step prog gt fuel c = pull { c with cur := none } := by
                    unfold step; rw [h]
                    simp only [binResolvedStep, hlocal, h1, Bool.false_eq_true, if_false, hgt', hgm',
                      hns2, if_true, hcg]
                  rw [hstep]
                  refine Step.bin_nonstrict_fail c op args res rest b h hnp
                    hlocal ⟨hgt, hgm⟩ hns2 ?_
                  rintro ⟨rs, hrs⟩; rw [hcg] at hrs; simp at hrs
              | incorrectArgument e =>
                  have hstep : step prog gt fuel c = pull { c with cur := none } := by
                    unfold step; rw [h]
                    simp only [binResolvedStep, hlocal, h1, Bool.false_eq_true, if_false, hgt', hgm',
                      hns2, if_true, hcg]
                  rw [hstep]
                  refine Step.bin_nonstrict_fail c op args res rest b h hnp
                    hlocal ⟨hgt, hgm⟩ hns2 ?_
                  rintro ⟨rs, hrs⟩; rw [hcg] at hrs; simp at hrs
              | runtimeError e =>
                  have hstep : step prog gt fuel c = pull { c with cur := none } := by
                    unfold step; rw [h]
                    simp only [binResolvedStep, hlocal, h1, Bool.false_eq_true, if_false, hgt', hgm',
                      hns2, if_true, hcg]
                  rw [hstep]
                  refine Step.bin_nonstrict_fail c op args res rest b h hnp
                    hlocal ⟨hgt, hgm⟩ hns2 ?_
                  rintro ⟨rs, hrs⟩; rw [hcg] at hrs; simp at hrs
          | false =>
              have hns3 : op ≠ "get-type" ∧ op ≠ "get-metatype"
                  ∧ ¬ (nonstrictOps.contains op = true) :=
                ⟨hgt, hgm, fun hc => Bool.false_ne_true (hns2 ▸ hc)⟩
              cases h5 : (["+", "-", "*"].contains op
                  && !(args.map (subst b)).all Metta.isGround
                  && Metta.isGround (subst b res)) with
              | true =>
                  have h5' := h5
                  rw [Bool.and_eq_true, Bool.and_eq_true] at h5'
                  obtain ⟨⟨hop, hnall⟩, hrv⟩ := h5'
                  have hng : ¬ ((args.map (subst b)).all Metta.isGround = true) := by
                    intro hall; rw [hall] at hnall; simp at hnall
                  have hop3 : op = "+" ∨ op = "-" ∨ op = "*" := by
                    simpa using hop
                  have ha2 : binArity op = 2 := by
                    rcases hop3 with h' | h' | h' <;> subst h' <;> rfl
                  rcases hsh : args.map (subst b) with _ | ⟨x, _ | ⟨y, _ | ⟨z, zs⟩⟩⟩
                  · exfalso; rw [hsh] at hnp
                    exact hnp ⟨by simp [ha2], by simp [ha2]⟩
                  · exfalso; rw [hsh] at hnp
                    exact hnp ⟨by simp [ha2], by simp [ha2]⟩
                  · have h1x := h1; rw [hsh] at h1x
                    have h5x := h5; rw [hsh] at h5x
                    rcases hop3 with h' | h' | h'
                    · subst h'
                      have hstep : step prog gt fuel c = { c with cur := some ((if Metta.isGround x then Goal.bin "-" [subst b res, x] y else Goal.bin "-" [subst b res, y] x) :: rest, b) } := by
                        unfold step; rw [h]
                        simp only [binResolvedStep, hsh, h1x, Bool.false_eq_true, if_false, hgt',
                          hgm', hns2, h5x, if_true]
                        all_goals rfl
                      rw [hstep]
                      exact Step.bin_mode c "+" args res rest b x y h hnp hlocal hns3
                        hop hsh hng hrv _ rfl
                    · subst h'
                      have hstep : step prog gt fuel c = { c with cur := some ((if Metta.isGround x then Goal.bin "-" [x, subst b res] y else Goal.bin "+" [subst b res, y] x) :: rest, b) } := by
                        unfold step; rw [h]
                        simp only [binResolvedStep, hsh, h1x, Bool.false_eq_true, if_false, hgt',
                          hgm', hns2, h5x, if_true]
                        all_goals rfl
                      rw [hstep]
                      exact Step.bin_mode c "-" args res rest b x y h hnp hlocal hns3
                        hop hsh hng hrv _ rfl
                    · subst h'
                      have hstep : step prog gt fuel c = { c with cur := some ((if Metta.isGround x then Goal.bin "/" [subst b res, x] y else Goal.bin "/" [subst b res, y] x) :: rest, b) } := by
                        unfold step; rw [h]
                        simp only [binResolvedStep, hsh, h1x, Bool.false_eq_true, if_false, hgt',
                          hgm', hns2, h5x, if_true]
                        all_goals rfl
                      rw [hstep]
                      exact Step.bin_mode c "*" args res rest b x y h hnp hlocal hns3
                        hop hsh hng hrv _ rfl
                  · have h1x := h1; rw [hsh] at h1x
                    have h5x := h5; rw [hsh] at h5x
                    have hstep : step prog gt fuel c = pull { c with cur := none } := by
                      unfold step; rw [h]
                      simp only [binResolvedStep, hsh, h1x, Bool.false_eq_true, if_false, hgt',
                        hgm', hns2, h5x, if_true]
                      all_goals (rcases hop3 with h' | h' | h' <;> subst h' <;> rfl)
                    rw [hstep]
                    exact Step.bin_mode_fail c op args res rest b h hnp hlocal hns3
                      hop hng hrv (by simp [hsh])
              | false =>
                  have hnmode : ¬ (["+", "-", "*"].contains op = true
                      ∧ ¬ ((args.map (subst b)).all Metta.isGround = true)
                      ∧ Metta.isGround (subst b res) = true) := by
                    rintro ⟨hcp, hcn, hcr⟩
                    have hall : (args.map (subst b)).all Metta.isGround = false := by
                      cases hx : (args.map (subst b)).all Metta.isGround
                      · rfl
                      · exact absurd hx hcn
                    have ht : (["+", "-", "*"].contains op
                        && !(args.map (subst b)).all Metta.isGround
                        && Metta.isGround (subst b res)) = true := by
                      rw [hcp, hall, hcr]; rfl
                    rw [h5] at ht; exact Bool.false_ne_true ht
                  cases h6 : (args.map (subst b)).all Metta.isGround with
                  | true =>
                      cases hcg : callGrounded gt op (args.map (subst b)) with
                      | ok rs =>
                          have hstep : step prog gt fuel c
                              = pull { c with cur := none,
                                              counter := advanceCounterPastAtoms c.counter rs,
                                              alts := rs.map (fun r =>
                                                Alt.br (Goal.eq res (canonBool r) :: rest) b) ++ c.alts } := by
                            unfold step; rw [h]
                            simp only [binResolvedStep, hlocal, h1, Bool.false_eq_true, if_false, hgt', hgm',
                              hns2, h6, Bool.not_true, Bool.and_false, Bool.false_and,
                              if_true, hcg]
                          rw [hstep]
                          exact Step.bin_ok c op args res rest b rs h h6 hnp hlocal hns3
                            (fun hc => hc.2 h6) hcg
                      | noReduce =>
                          have hstep : step prog gt fuel c = pull { c with cur := none } := by
                            unfold step; rw [h]
                            simp only [binResolvedStep, hlocal, h1, Bool.false_eq_true, if_false, hgt', hgm',
                              hns2, h6, Bool.not_true, Bool.and_false, Bool.false_and,
                              if_true, hcg]
                          rw [hstep]
                          refine Step.bin_fail c op args res rest b h hnp hlocal hns3
                            hnmode h6 ?_
                          rintro ⟨rs, hrs⟩; rw [hcg] at hrs; simp at hrs
                      | incorrectArgument e =>
                          have hstep : step prog gt fuel c = pull { c with cur := none } := by
                            unfold step; rw [h]
                            simp only [binResolvedStep, hlocal, h1, Bool.false_eq_true, if_false, hgt', hgm',
                              hns2, h6, Bool.not_true, Bool.and_false, Bool.false_and,
                              if_true, hcg]
                          rw [hstep]
                          refine Step.bin_fail c op args res rest b h hnp hlocal hns3
                            hnmode h6 ?_
                          rintro ⟨rs, hrs⟩; rw [hcg] at hrs; simp at hrs
                      | runtimeError e =>
                          have hstep : step prog gt fuel c = pull { c with cur := none } := by
                            unfold step; rw [h]
                            simp only [binResolvedStep, hlocal, h1, Bool.false_eq_true, if_false, hgt', hgm',
                              hns2, h6, Bool.not_true, Bool.and_false, Bool.false_and,
                              if_true, hcg]
                          rw [hstep]
                          refine Step.bin_fail c op args res rest b h hnp hlocal hns3
                            hnmode h6 ?_
                          rintro ⟨rs, hrs⟩; rw [hcg] at hrs; simp at hrs
                  | false =>
                      have hgnd : ¬ ((args.map (subst b)).all Metta.isGround = true) := by
                        simp [h6]
                      have h5x := h5
                      rw [h6, Bool.not_false, Bool.and_true] at h5x
                      by_cases hu : op = "union-atom"
                      · subst hu
                        cases hur : unionReverseAlts args res rest b with
                        | some alts =>
                            have hstep : step prog gt fuel c =
                                pull { c with cur := none, alts := alts ++ c.alts } := by
                              unfold step; rw [h]
                              simp only [binResolvedStep, hlocal, unionReverseAltsForOp,
                                h1, Bool.false_eq_true, if_false,
                                hgt', hgm', hns2, h6, Bool.not_false,
                                Bool.and_true, h5x, beq_self_eq_true,
                                if_true, hur]
                            rw [hstep]
                            exact Step.bin_union_reverse c args res rest b alts h
                              hnp hlocal (by simp [nonstrictOps]) hnmode hgnd hur
                        | none =>
                            cases rest with
                            | nil =>
                                have hstep : step prog gt fuel c =
                                    pull { c with cur := none } := by
                                  unfold step; rw [h]
                                  simp only [binResolvedStep, hlocal, unionReverseAltsForOp,
                                    h1, Bool.false_eq_true, if_false,
                                    hgt', hgm', hns2, h6, Bool.not_false,
                                    Bool.and_true, h5x, beq_self_eq_true,
                                    if_true, hur]
                                rw [hstep]
                                exact Step.bin_flounder c "union-atom" args res []
                                  b h hnp hlocal (by simp [nonstrictOps]) hnmode hgnd rfl
                            | cons r rs =>
                                have hstep : step prog gt fuel c
                                    = { c with cur := some ((r :: rs) ++
                                        [Goal.bin "union-atom" args res], b) } := by
                                  unfold step; rw [h]
                                  simp only [binResolvedStep, hlocal, unionReverseAltsForOp,
                                    h1, Bool.false_eq_true, if_false,
                                    hgt', hgm', hns2, h6, Bool.not_false,
                                    Bool.and_true, h5x, beq_self_eq_true,
                                    if_true, hur]
                                rw [hstep]
                                exact Step.bin_delay c "union-atom" args res
                                  (r :: rs) b h hnp hlocal (by simp [nonstrictOps])
                                  hnmode hgnd (by simp)
                      · have hu' : (op == "union-atom") = false := by
                          simp [hu]
                        cases rest with
                        | nil =>
                            have hstep : step prog gt fuel c = pull { c with cur := none } := by
                              unfold step; rw [h]
                              simp only [binResolvedStep, hlocal, unionReverseAltsForOp,
                                h1, Bool.false_eq_true, if_false, hgt', hgm',
                                hns2, h6, Bool.not_false, Bool.and_true, h5x, hu']
                            rw [hstep]
                            exact Step.bin_flounder c op args res [] b h hnp hlocal hns3
                              hnmode hgnd rfl
                        | cons r rs =>
                            have hstep : step prog gt fuel c
                                = { c with cur := some ((r :: rs) ++ [Goal.bin op args res], b) } := by
                              unfold step; rw [h]
                              simp only [binResolvedStep, hlocal, unionReverseAltsForOp,
                                h1, Bool.false_eq_true, if_false, hgt', hgm',
                                hns2, h6, Bool.not_false, Bool.and_true, h5x, hu']
                            rw [hstep]
                            exact Step.bin_delay c op args res (r :: rs) b h hnp hlocal hns3
                              hnmode hgnd (by simp)

set_option maxHeartbeats 1600000 in
theorem step_bin (c : Conf) (op : String) (args : List Atom) (res : Atom)
    (rest : List Goal) (b : Subst)
    (h : c.cur = some (Goal.bin op args res :: rest, b)) :
    Step prog gt c (step prog gt fuel c) := by
  cases h1 : (binArity op != 0
      && decide ((args.map (subst b)).length < binArity op)) with
  | true =>
      have hb : binArity op ≠ 0 ∧
          (args.map (subst b)).length < binArity op := by
        rw [Bool.and_eq_true] at h1
        exact ⟨by simpa using h1.1, by simpa using h1.2⟩
      have hstep : step prog gt fuel c =
          { c with cur := some (Goal.eq res
              (chainOf [Atom.sym "partial", Atom.sym op,
                chainOf (args.map (subst b))]) :: rest, b) } := by
        unfold step
        rw [h]
        simp only [h1, if_true]
      rw [hstep]
      exact Step.bin_partial c op args res rest b hb h _ rfl
  | false =>
      have hnp : ¬ (binArity op ≠ 0 ∧
          (args.map (subst b)).length < binArity op) := by
        intro contradiction
        have truth : (binArity op != 0 && decide
            ((args.map (subst b)).length < binArity op)) = true := by
          rw [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
          exact contradiction
        rw [h1] at truth
        exact Bool.false_ne_true truth
      cases hlocal : localTranslatePredicateGoals? c.world gt op
          (args.map (subst b)) res rest with
      | none =>
          exact step_bin_nonlocal prog gt fuel c op args res rest b h hlocal
      | some goals =>
          have hstep : step prog gt fuel c =
              { c with
                cur := some (goals, b)
                counter := advanceCounterPastGoals c.counter goals } := by
            unfold step
            rw [h]
            simp only [h1, Bool.false_eq_true, if_false, binResolvedStep,
              hlocal]
          rw [hstep]
          exact Step.bin_local_translate c op args res rest b goals h hnp
            hlocal

/-! ### The correspondence theorem (the Phase-1 gate) -/

/-- Every machine step on a live configuration is licensed by the `Step`
    relation — except when the head goal nests a fuel-bounded sub-run
    (`findall`/`softcut`/`catchg`), which the relation licenses only for
    TERMINAL sub-runs (the fuel-honesty boundary, `nestedRunHead`). By cases
    on the current goal; each non-nested case is its lemma above. Zero sorry. -/
theorem machineMirrorsSpec_proved : machineMirrorsSpec := by
  intro prog gt fuel c hne
  match hcur : c.cur with
  | none =>
      have ha : c.alts ≠ [] := by
        rcases hne with hs | ha
        · rw [hcur] at hs; simp at hs
        · exact ha
      exact Or.inl (step_pull prog gt fuel c hcur ha)
  | some ([], b) => exact Or.inl (step_answer prog gt fuel c b hcur)
  | some (Goal.eq x y :: rest, b) =>
      exact Or.inl (step_eq prog gt fuel c x y rest b hcur)
  | some (Goal.cut :: rest, b) =>
      exact Or.inl (step_cut prog gt fuel c rest b hcur)
  | some (Goal.cutAt k :: rest, b) =>
      exact Or.inl (step_cutAt prog gt fuel c k rest b hcur)
  | some (Goal.call f args res :: rest, b) =>
      exact step_call prog gt fuel c f args res rest b hcur
  | some (Goal.bin op args res :: rest, b) =>
      exact Or.inl (step_bin prog gt fuel c op args res rest b hcur)
  | some (Goal.callDyn hd args res :: rest, b) =>
      exact Or.inl (step_callDyn prog gt fuel c hd args res rest b hcur)
  | some (Goal.evalg v res :: rest, b) =>
      exact Or.inl (step_evalg prog gt fuel c v res rest b hcur)
  | some (Goal.catchg tmpl sub res :: rest, b) =>
      have hc : catchRunHead c := ⟨tmpl, sub, res, rest, b, hcur⟩
      have hn : nestedRunHead c := Or.inr (Or.inr (Or.inl hc))
      exact Or.inr hn
  | some (Goal.softcut tmpl sub thn els :: rest, b) =>
      have hs : softcutRunHead c := ⟨tmpl, sub, thn, els, rest, b, hcur⟩
      have hn : nestedRunHead c := Or.inr (Or.inl hs)
      exact Or.inr hn
  | some (Goal.findall tmpl sub res :: rest, b) =>
      have hf : findallRunHead c := ⟨tmpl, sub, res, rest, b, hcur⟩
      have hn : nestedRunHead c := Or.inl hf
      exact Or.inr hn
  | some (Goal.onceg tmpl sub res :: rest, b) =>
      exact Or.inl (step_onceg prog gt fuel c tmpl sub res rest b hcur)
  | some (Goal.transactiong tmpl sub :: rest, b) =>
      have ht : transactionRunHead c := ⟨tmpl, sub, rest, b, hcur⟩
      have hn : nestedRunHead c :=
        Or.inr (Or.inr (Or.inr (Or.inr ht)))
      exact Or.inr hn
  | some (Goal.amb branches res :: rest, b) =>
      exact Or.inl (step_amb prog gt fuel c branches res rest b hcur)
  | some (Goal.spread v res :: rest, b) =>
      exact Or.inl (step_spread prog gt fuel c v res rest b hcur)
  | some (Goal.ite cond thn els res :: rest, b) =>
      exact Or.inl (step_ite prog gt fuel c cond thn els res rest b hcur)
  | some (Goal.smatch pat :: rest, b) =>
      exact Or.inl (step_smatch prog gt fuel c pat rest b hcur)
  | some (Goal.wact op args res :: rest, b) =>
      exact Or.inl (step_wact prog gt fuel c op args res rest b hcur)

/-! ### Clean-machine soundness

`runClean`/`stepClean` are the executable lane. They expose fuel exhaustion
instead of fabricating a nested-run result; when they do return a progressed
or done outcome, the outcome is licensed by the same `Step` relation. -/

theorem terminal_of_isTerminalB {c : Conf} (h : c.isTerminalB = true) :
    Terminal c := by
  cases hcur : c.cur <;> cases halts : c.alts <;>
    simp [Conf.isTerminalB, Terminal, hcur, halts] at h ⊢

theorem live_of_isTerminalB_false {c : Conf} (h : c.isTerminalB = false) :
    c.cur.isSome ∨ c.alts ≠ [] := by
  cases hcur : c.cur <;> cases halts : c.alts <;>
    simp [Conf.isTerminalB, hcur, halts] at h ⊢

theorem step_of_machineMirrors_non_nested (prog : Prog) (gt : GroundingTable)
    (fuel : Nat) (c : Conf)
    (hlive : c.cur.isSome ∨ c.alts ≠ [])
    (hn : ¬ nestedRunHead c) :
    Step prog gt c (step prog gt fuel c) := by
  have hs := machineMirrorsSpec_proved prog gt fuel c hlive
  cases hs with
  | inl hstep => exact hstep
  | inr hnest => exact False.elim (hn hnest)

theorem not_nested_call_of_not_table (c : Conf) (f : String)
    (args : List Atom) (res : Atom) (rest : List Goal) (b : Subst)
    (hcur : c.cur = some (Goal.call f args res :: rest, b))
    (hcan : c.world.canTableCall f (args.map (subst b)) = false) :
    ¬ nestedRunHead c := by
  intro hn
  simp [nestedRunHead, findallRunHead, softcutRunHead, catchRunHead,
    tableRunHead, transactionRunHead, PWorld.needsTableCompute, hcur] at hn
  rcases hn with ⟨f1, args1, res1, rest1, b1, heq, hcan1, _hcache⟩
  rcases heq with ⟨⟨⟨hf, hargsres⟩, _hrest⟩, hb⟩
  rcases hargsres with ⟨hargs, _hres⟩
  subst f1
  subst args1
  subst b1
  rw [hcan] at hcan1
  simp at hcan1

theorem not_nested_call_of_cache (c : Conf) (f : String)
    (args : List Atom) (res : Atom) (rest : List Goal) (b : Subst)
    (answers : List Atom)
    (hcur : c.cur = some (Goal.call f args res :: rest, b))
    (hcache : c.world.tableLookup (tableKey f (args.map (subst b))) = some answers) :
    ¬ nestedRunHead c := by
  intro hn
  simp [nestedRunHead, findallRunHead, softcutRunHead, catchRunHead,
    tableRunHead, transactionRunHead, PWorld.needsTableCompute, hcur] at hn
  rcases hn with ⟨f1, args1, res1, rest1, b1, heq, _hcan1, hcache1⟩
  rcases heq with ⟨⟨⟨hf, hargsres⟩, _hrest⟩, hb⟩
  rcases hargsres with ⟨hargs, _hres⟩
  subst f1
  subst args1
  subst b1
  rw [hcache] at hcache1
  simp at hcache1

/-- Simultaneous semantic account of every non-fuel clean-machine outcome.
    The four fields must be proved together: a caught exceptional sub-run
    becomes an ordinary `Step`, while an uncaught one remains `Raises`. -/
structure CleanSoundAtFuel (prog : Prog) (gt : GroundingTable)
    (fuel : Nat) : Prop where
  done : ∀ (c : Conf) (limit : Option Nat) (d : Conf),
    runClean prog gt fuel c limit = .done d →
    StepStar prog gt c d ∧ Terminal d
  runError : ∀ (c : Conf) (limit : Option Nat) (d : Conf) (err : Atom),
    runClean prog gt fuel c limit = .errored d err →
    Raises prog gt c d err
  progressed : ∀ (c c' : Conf), (c.cur.isSome ∨ c.alts ≠ []) →
    stepClean prog gt fuel c = .progressed c' →
    Step prog gt c c'
  stepError : ∀ (c d : Conf) (err : Atom),
    stepClean prog gt fuel c = .errored d err →
    Raises prog gt c d err

set_option maxHeartbeats 3000000 in
theorem clean_sound_fuel (prog : Prog) (gt : GroundingTable) :
    ∀ fuel, CleanSoundAtFuel prog gt fuel := by
  intro fuel
  induction fuel with
  | zero =>
      refine {
        done := ?_
        runError := ?_
        progressed := ?_
        stepError := ?_ }
      · intro c limit d h
        cases ht : c.isTerminalB
        · cases hl : c.limitReachedB limit <;> simp [runClean, ht, hl] at h
        · simp [runClean, ht] at h
          subst d
          exact ⟨StepStar.refl c, terminal_of_isTerminalB ht⟩
      · intro c limit d err h
        cases ht : c.isTerminalB
        · cases hl : c.limitReachedB limit <;> simp [runClean, ht, hl] at h
        · simp [runClean, ht] at h
      · intro c c' hlive hprog
        simp [stepClean] at hprog
      · intro c d err h
        simp [stepClean] at h
  | succ fuel ih =>
      refine {
        done := ?_
        runError := ?_
        progressed := ?_
        stepError := ?_ }
      · intro c limit d h
        cases ht : c.isTerminalB
        · cases hl : c.limitReachedB limit
          · cases hs : stepClean prog gt fuel c with
            | progressed cnext =>
                have hdone : runClean prog gt fuel cnext limit = .done d := by
                  simpa [runClean, ht, hl, hs] using h
                have hstep : Step prog gt c cnext :=
                  ih.progressed c cnext (live_of_isTerminalB_false ht) hs
                have htail := ih.done cnext limit d hdone
                exact ⟨StepStar.tail c cnext d hstep htail.1, htail.2⟩
            | exhausted e =>
                simp [runClean, ht, hl, hs] at h
            | errored e err =>
                simp [runClean, ht, hl, hs] at h
          · simp [runClean, ht, hl] at h
        · simp [runClean, ht] at h
          subst d
          exact ⟨StepStar.refl c, terminal_of_isTerminalB ht⟩
      · intro c limit d err h
        cases ht : c.isTerminalB
        · cases hl : c.limitReachedB limit
          · cases hs : stepClean prog gt fuel c with
            | progressed cnext =>
                have htail : runClean prog gt fuel cnext limit =
                    .errored d err := by
                  simpa [runClean, ht, hl, hs] using h
                exact Raises.step c cnext d err
                  (ih.progressed c cnext (live_of_isTerminalB_false ht) hs)
                  (ih.runError cnext limit d err htail)
            | exhausted e =>
                simp [runClean, ht, hl, hs] at h
            | errored e raised =>
                have hout : RunOutcome.errored e raised =
                    RunOutcome.errored d err := by
                  simpa [runClean, ht, hl, hs] using h
                cases hout
                exact ih.stepError c d err hs
          · simp [runClean, ht, hl] at h
        · simp [runClean, ht] at h
      · intro c c' hlive hprog
        cases hcur : c.cur with
        | none =>
            have hstepEq : step prog gt fuel c = c' := by
              simpa [stepClean, hcur] using hprog
            have halts : c.alts ≠ [] := by
              rcases hlive with hs | ha
              · rw [hcur] at hs; simp at hs
              · exact ha
            have hs := step_pull prog gt fuel c hcur halts
            rw [hstepEq] at hs
            exact hs
        | some br =>
            rcases br with ⟨goals, b⟩
            cases goals with
            | nil =>
                have hstepEq : step prog gt fuel c = c' := by
                  simpa [stepClean, hcur] using hprog
                have hs := step_answer prog gt fuel c b hcur
                rw [hstepEq] at hs
                exact hs
            | cons g rest =>
                cases g with
                | catchg tmpl sub res =>
                    cases hc : catchDirect? gt b tmpl sub with
                    | some cr =>
                        cases cr with
                        | error err =>
                            have hstepEq :
                                { c with cur := some (Goal.eq res err :: rest, b),
                                         world := c.world,
                                         counter := advanceCounterPastAtoms c.counter [err] } = c' := by
                              simpa [stepClean, hcur, hc] using hprog
                            have hs := Step.catch_direct_error (prog := prog) (gt := gt)
                              c tmpl sub res rest b err hcur hc
                            rw [hstepEq] at hs
                            exact hs
                        | answers answers =>
                            have hs0 := Step.catch_direct_answers (prog := prog) (gt := gt)
                              c tmpl sub res rest b answers hcur hc
                            cases answers with
                            | nil =>
                                have hstepEq := by
                                  simpa [stepClean, hcur, hc] using hprog
                                simpa [hstepEq, advanceCounterPastAtoms,
                                  resolutionSeedHighWaterAtoms] using hs0
                            | cons a as =>
                                have hstepEq := by
                                  simpa [stepClean, hcur, hc] using hprog
                                simpa [hstepEq] using hs0
                    | none =>
                        cases hr : runClean prog gt fuel
                            (subConfOf c sub b tmpl) none with
                        | done d =>
                            have hrd0 := ih.done (subConfOf c sub b tmpl) none d hr
                            have hrd :
                                StepStar prog gt
                                  { cur := some (sub, b), alts := [], world := c.world,
                                    counter := c.counter, qterm := tmpl,
                                    barriers := resetBarrierCache c.barriers } d ∧
                                Terminal d := by
                              simpa [subConfOf] using hrd0
                            have hs0 := Step.catch_run (prog := prog) (gt := gt)
                              c d tmpl sub res rest b hcur hc hrd.1 hrd.2
                            cases he : d.answers with
                            | nil =>
                                have hstepEq := by
                                  simpa [stepClean, hcur, hc, hr, he] using hprog
                                simpa [Conf.answerValues, he, hstepEq] using hs0
                            | cons a as =>
                                have hstepEq := by
                                  simpa [stepClean, hcur, hc, hr, he] using hprog
                                simpa [he, hstepEq] using hs0
                        | limited d =>
                            simp [stepClean, hcur, hc, hr] at hprog
                        | exhausted d =>
                            simp [stepClean, hcur, hc, hr] at hprog
                        | errored d err =>
                            have hraise0 := ih.runError
                              (subConfOf c sub b tmpl) none d err hr
                            have hraise :
                                Raises prog gt
                                  { cur := some (sub, b), alts := [],
                                    world := c.world, counter := c.counter,
                                    qterm := tmpl,
                                    barriers := resetBarrierCache c.barriers } d err := by
                              simpa [subConfOf] using hraise0
                            have hs0 := Step.catch_run_error
                              (prog := prog) (gt := gt) c d tmpl sub res rest b err
                              hcur hc hraise
                            have hstepEq := by
                              simpa [stepClean, hcur, hc, hr] using hprog
                            simpa [hstepEq] using hs0
                | transactiong tmpl sub =>
                    let txSub := transactionSub tmpl sub
                    cases hr : runClean prog gt fuel
                        (subConfOf c txSub b tmpl) none with
                    | done d =>
                        have hrd0 := ih.done (subConfOf c txSub b tmpl) none d hr
                        have hrd :
                            StepStar prog gt
                              { cur := some (transactionSub tmpl sub, b),
                                alts := [], world := c.world,
                                counter := c.counter, qterm := tmpl,
                                barriers := resetBarrierCache c.barriers } d ∧
                            Terminal d := by
                          simpa [txSub, subConfOf] using hrd0
                        cases he : d.answers with
                        | nil =>
                            have hstepEq := by
                              simpa [stepClean, hcur, txSub, hr, he] using hprog
                            have hs := Step.transaction_none
                              (prog := prog) (gt := gt)
                              c d tmpl sub rest b hcur hrd.1 hrd.2 he
                            simpa [hstepEq] using hs
                        | cons a as =>
                            have hne : d.answers ≠ [] := by simp [he]
                            have hstepEq := by
                              simpa [stepClean, hcur, txSub, hr, he] using hprog
                            have hs := Step.transaction_some
                              (prog := prog) (gt := gt)
                              c d tmpl sub rest b hcur hrd.1 hrd.2 hne
                            simpa [he, hstepEq] using hs
                    | limited d =>
                        simp [stepClean, hcur, txSub, hr] at hprog
                    | exhausted d =>
                        simp [stepClean, hcur, txSub, hr] at hprog
                    | errored d err =>
                        simp [stepClean, hcur, txSub, hr] at hprog
                | softcut tmpl sub thn els =>
                    cases hr : runClean prog gt fuel
                        (subConfOf c sub b tmpl) none with
                    | done d =>
                        have hrd0 := ih.done (subConfOf c sub b tmpl) none d hr
                        have hrd :
                            StepStar prog gt
                              { cur := some (sub, b), alts := [], world := c.world,
                                counter := c.counter, qterm := tmpl,
                                barriers := resetBarrierCache c.barriers } d ∧
                            Terminal d := by
                          simpa [subConfOf] using hrd0
                        cases he : d.answers with
                        | nil =>
                            have hstepEq := by
                              simpa [stepClean, hcur, hr, he] using hprog
                            have hs := Step.softcut_none (prog := prog) (gt := gt)
                              c d tmpl sub thn els rest b hcur hrd.1 hrd.2 he
                            simpa [hstepEq] using hs
                        | cons a as =>
                            have hne : d.answers ≠ [] := by simp [he]
                            have hstepEq := by
                              simpa [stepClean, hcur, hr, he] using hprog
                            have hs := Step.softcut_some (prog := prog) (gt := gt)
                              c d tmpl sub thn els rest b hcur hrd.1 hrd.2 hne
                            simpa [he, hstepEq] using hs
                    | limited d =>
                        simp [stepClean, hcur, hr] at hprog
                    | exhausted d =>
                        simp [stepClean, hcur, hr] at hprog
                    | errored d err =>
                        simp [stepClean, hcur, hr] at hprog
                | findall tmpl sub res =>
                    cases hr : runClean prog gt fuel
                        (subConfOf c sub b tmpl) none with
                    | done d =>
                        have hrd0 := ih.done (subConfOf c sub b tmpl) none d hr
                        have hrd :
                            StepStar prog gt
                              { cur := some (sub, b), alts := [], world := c.world,
                                counter := c.counter, qterm := tmpl,
                                barriers := resetBarrierCache c.barriers } d ∧
                            Terminal d := by
                          simpa [subConfOf] using hrd0
                        have hstepEq := by
                          simpa [stepClean, hcur, hr] using hprog
                        have hs := Step.findall (prog := prog) (gt := gt)
                          c d tmpl sub res rest b hcur hrd.1 hrd.2
                        simpa [hstepEq] using hs
                    | limited d =>
                        simp [stepClean, hcur, hr] at hprog
                    | exhausted d =>
                        simp [stepClean, hcur, hr] at hprog
                    | errored d err =>
                        simp [stepClean, hcur, hr] at hprog
                | call f args res =>
                    cases hcan : c.world.canTableCall f (args.map (subst b)) with
                    | false =>
                        have hstepEq : step prog gt fuel c = c' := by
                          simpa [stepClean, hcur, hcan] using hprog
                        have hn := not_nested_call_of_not_table c f args res rest b hcur hcan
                        have hs := step_of_machineMirrors_non_nested prog gt fuel c hlive hn
                        rw [hstepEq] at hs
                        exact hs
                    | true =>
                        cases hcache : c.world.tableLookup (tableKey f (args.map (subst b))) with
                        | some answers =>
                            have hstepEq : step prog gt fuel c = c' := by
                              simpa [stepClean, hcur, hcan, hcache] using hprog
                            have hn := not_nested_call_of_cache c f args res rest b
                              answers hcur hcache
                            have hs := step_of_machineMirrors_non_nested prog gt fuel c hlive hn
                            rw [hstepEq] at hs
                            exact hs
                        | none =>
                            let tres := tableFresh c
                            let key := tableKey f (args.map (subst b))
                            cases hr : runClean prog gt fuel
                                (tableSubConfOf c f (args.map (subst b)) tres key) none with
                            | done d =>
                                have hrd0 := ih.done
                                  (tableSubConfOf c f (args.map (subst b)) tres key)
                                  none d hr
                                have hrd :
                                    StepStar prog gt
                                      { cur := some ([Goal.call f (args.map (subst b)) tres], []),
                                        alts := [],
                                        world := { c.world with
                                          tableActive := tableKey f (args.map (subst b)) ::
                                            c.world.tableActive },
                                        counter := advanceCounterPastAtoms (c.counter + 1) [tres],
                                        qterm := tres,
                                        barriers := resetBarrierCache c.barriers } d ∧
                                    Terminal d := by
                                  simpa [tableSubConfOf, key] using hrd0
                                have hs0 := Step.call_table_compute (prog := prog) (gt := gt)
                                  c d f args res rest b tres hcur hcan hcache rfl hrd.1 hrd.2
                                cases he : d.answers with
                                | nil =>
                                    have hstepEq :
                                        pull { c with
                                          cur := none
                                          world :=
                                            (d.world.deactivateTable
                                              (tableKey f (args.map (subst b)))).tableInsert
                                                (tableKey f (args.map (subst b))) []
                                          counter := d.counter } = c' := by
                                      simpa [stepClean, hcur, hcan, hcache, hr,
                                        tres, key, he, Conf.answerValues] using hprog
                                    have hs : Step prog gt c
                                        (pull { c with
                                          cur := none
                                          world :=
                                            (d.world.deactivateTable
                                              (tableKey f (args.map (subst b)))).tableInsert
                                                (tableKey f (args.map (subst b))) []
                                          counter := d.counter }) := by
                                      simpa [Conf.answerValues, he] using hs0
                                    rw [hstepEq] at hs
                                    exact hs
                                | cons a as =>
                                    have hstepEq := by
                                      simpa [stepClean, hcur, hcan, hcache, hr,
                                        tres, key, he] using hprog
                                    simpa [he, hstepEq] using hs0
                            | limited d =>
                                simp [stepClean, hcur, hcan, hcache, hr, tres, key]
                                  at hprog
                            | exhausted d =>
                                simp [stepClean, hcur, hcan, hcache, hr, tres, key]
                                  at hprog
                            | errored d err =>
                                simp [stepClean, hcur, hcan, hcache, hr, tres, key]
                                  at hprog
                | eq x y =>
                    have hstepEq : step prog gt fuel c = c' := by
                      simpa [stepClean, hcur] using hprog
                    have hs := step_eq prog gt fuel c x y rest b hcur
                    rw [hstepEq] at hs
                    exact hs
                | cut =>
                    have hstepEq : step prog gt fuel c = c' := by
                      simpa [stepClean, hcur] using hprog
                    have hs := step_cut prog gt fuel c rest b hcur
                    rw [hstepEq] at hs
                    exact hs
                | cutAt k =>
                    have hstepEq : step prog gt fuel c = c' := by
                      simpa [stepClean, hcur] using hprog
                    have hs := step_cutAt prog gt fuel c k rest b hcur
                    rw [hstepEq] at hs
                    exact hs
                | bin op args res =>
                    cases hlocal : localTranslatePredicateGoals? c.world gt op
                        (args.map (subst b)) res rest with
                    | some goals =>
                        have hstepEq : step prog gt fuel c = c' := by
                          simpa [stepClean, hcur, hlocal] using hprog
                        have hs := step_bin prog gt fuel c op args res rest b hcur
                        rw [hstepEq] at hs
                        exact hs
                    | none =>
                        cases hc : caughtBinErrorResolved? gt op
                            (args.map (subst b)) with
                        | none =>
                            have hstepEq : step prog gt fuel c = c' := by
                              simpa [stepClean, hcur, hlocal, hc] using hprog
                            have hs := step_bin prog gt fuel c op args res rest b hcur
                            rw [hstepEq] at hs
                            exact hs
                        | some err =>
                            simp [stepClean, hcur, hlocal, hc] at hprog
                | callDyn hd args res =>
                    have hstepEq : step prog gt fuel c = c' := by
                      simpa [stepClean, hcur] using hprog
                    have hs := step_callDyn prog gt fuel c hd args res rest b hcur
                    rw [hstepEq] at hs
                    exact hs
                | evalg v res =>
                    have hstepEq : step prog gt fuel c = c' := by
                      simpa [stepClean, hcur] using hprog
                    have hs := step_evalg prog gt fuel c v res rest b hcur
                    rw [hstepEq] at hs
                    exact hs
                | onceg tmpl sub res =>
                    have hstepEq : step prog gt fuel c = c' := by
                      simpa [stepClean, hcur] using hprog
                    have hs := step_onceg prog gt fuel c tmpl sub res rest b hcur
                    rw [hstepEq] at hs
                    exact hs
                | amb branches res =>
                    have hstepEq : step prog gt fuel c = c' := by
                      simpa [stepClean, hcur] using hprog
                    have hs := step_amb prog gt fuel c branches res rest b hcur
                    rw [hstepEq] at hs
                    exact hs
                | spread v res =>
                    have hstepEq : step prog gt fuel c = c' := by
                      simpa [stepClean, hcur] using hprog
                    have hs := step_spread prog gt fuel c v res rest b hcur
                    rw [hstepEq] at hs
                    exact hs
                | ite cond thn els res =>
                    have hstepEq : step prog gt fuel c = c' := by
                      simpa [stepClean, hcur] using hprog
                    have hs := step_ite prog gt fuel c cond thn els res rest b hcur
                    rw [hstepEq] at hs
                    exact hs
                | smatch pat =>
                    have hstepEq : step prog gt fuel c = c' := by
                      simpa [stepClean, hcur] using hprog
                    have hs := step_smatch prog gt fuel c pat rest b hcur
                    rw [hstepEq] at hs
                    exact hs
                | wact op args res =>
                    have hstepEq : step prog gt fuel c = c' := by
                      simpa [stepClean, hcur] using hprog
                    have hs := step_wact prog gt fuel c op args res rest b hcur
                    rw [hstepEq] at hs
                    exact hs
      · intro c d err herror
        cases hcur : c.cur with
        | none => simp [stepClean, hcur] at herror
        | some br =>
            rcases br with ⟨goals, b⟩
            cases goals with
            | nil => simp [stepClean, hcur] at herror
            | cons g rest =>
                cases g with
                | catchg tmpl sub res =>
                    cases hc : catchDirect? gt b tmpl sub with
                    | some cr =>
                        cases cr with
                        | error raised =>
                            simp [stepClean, hcur, hc] at herror
                        | answers answers =>
                            by_cases he : answers = [] <;>
                              simp [stepClean, hcur, hc, he] at herror
                    | none =>
                        cases hr : runClean prog gt fuel
                            (subConfOf c sub b tmpl) none with
                        | done result =>
                            by_cases he : result.answers = [] <;>
                              simp [stepClean, hcur, hc, hr, he] at herror
                        | limited result =>
                            simp [stepClean, hcur, hc, hr] at herror
                        | exhausted result =>
                            simp [stepClean, hcur, hc, hr] at herror
                        | errored result raised =>
                            simp [stepClean, hcur, hc, hr] at herror
                | transactiong tmpl sub =>
                    let txSub := transactionSub tmpl sub
                    cases hr : runClean prog gt fuel
                        (subConfOf c txSub b tmpl) none with
                    | done result =>
                        by_cases he : result.answers = [] <;>
                          simp [stepClean, hcur, txSub, hr, he] at herror
                    | limited result =>
                        simp [stepClean, hcur, txSub, hr] at herror
                    | exhausted result =>
                        simp [stepClean, hcur, txSub, hr] at herror
                    | errored result raised =>
                        have hout : StepOutcome.errored result raised =
                            StepOutcome.errored d err := by
                          simpa [stepClean, hcur, txSub, hr] using herror
                        cases hout
                        have hraise0 := ih.runError
                          (subConfOf c txSub b tmpl) none d err hr
                        exact Raises.transaction c d tmpl sub rest b err hcur
                          (by simpa [txSub, subConfOf] using hraise0)
                | softcut tmpl sub thn els =>
                    cases hr : runClean prog gt fuel
                        (subConfOf c sub b tmpl) none with
                    | done result =>
                        by_cases he : result.answers = [] <;>
                          simp [stepClean, hcur, hr, he] at herror
                    | limited result => simp [stepClean, hcur, hr] at herror
                    | exhausted result => simp [stepClean, hcur, hr] at herror
                    | errored result raised =>
                        have hout : StepOutcome.errored result raised =
                            StepOutcome.errored d err := by
                          simpa [stepClean, hcur, hr] using herror
                        cases hout
                        have hraise0 := ih.runError
                          (subConfOf c sub b tmpl) none d err hr
                        exact Raises.softcut c d tmpl sub thn els rest b err hcur
                          (by simpa [subConfOf] using hraise0)
                | findall tmpl sub res =>
                    cases hr : runClean prog gt fuel
                        (subConfOf c sub b tmpl) none with
                    | done result => simp [stepClean, hcur, hr] at herror
                    | limited result => simp [stepClean, hcur, hr] at herror
                    | exhausted result => simp [stepClean, hcur, hr] at herror
                    | errored result raised =>
                        have hout : StepOutcome.errored result raised =
                            StepOutcome.errored d err := by
                          simpa [stepClean, hcur, hr] using herror
                        cases hout
                        have hraise0 := ih.runError
                          (subConfOf c sub b tmpl) none d err hr
                        exact Raises.findall c d tmpl sub res rest b err hcur
                          (by simpa [subConfOf] using hraise0)
                | call f args res =>
                    cases hcan : c.world.canTableCall f
                        (args.map (subst b)) with
                    | false => simp [stepClean, hcur, hcan] at herror
                    | true =>
                        cases hcache : c.world.tableLookup
                            (tableKey f (args.map (subst b))) with
                        | some answers =>
                            simp [stepClean, hcur, hcan, hcache] at herror
                        | none =>
                            let tres := tableFresh c
                            let key := tableKey f (args.map (subst b))
                            cases hr : runClean prog gt fuel
                                (tableSubConfOf c f (args.map (subst b))
                                  tres key) none with
                            | done result =>
                                by_cases he : result.answers = [] <;>
                                  simp [stepClean, hcur, hcan, hcache, hr,
                                    tres, key, he] at herror
                            | limited result =>
                                simp [stepClean, hcur, hcan, hcache, hr,
                                  tres, key] at herror
                            | exhausted result =>
                                simp [stepClean, hcur, hcan, hcache, hr,
                                  tres, key] at herror
                            | errored result raised =>
                                have hout : StepOutcome.errored result raised =
                                    StepOutcome.errored d err := by
                                  simpa [stepClean, hcur, hcan, hcache, hr,
                                    tres, key] using herror
                                cases hout
                                have hraise0 := ih.runError
                                  (tableSubConfOf c f (args.map (subst b))
                                    tres key) none d err hr
                                exact Raises.table c d f args res rest b tres err
                                  hcur hcan hcache rfl
                                  (by simpa [tableSubConfOf, key] using hraise0)
                | bin op args res =>
                    cases hlocal : localTranslatePredicateGoals? c.world gt op
                        (args.map (subst b)) res rest with
                    | some goals =>
                        simp [stepClean, hcur, hlocal] at herror
                    | none =>
                        cases hc : caughtBinErrorResolved? gt op
                            (args.map (subst b)) with
                        | none =>
                            simp [stepClean, hcur, hlocal, hc] at herror
                        | some raised =>
                            have hcatch : catchDirect? gt b res
                                [Goal.bin op args res] = some (.error raised) :=
                              (caughtBinErrorResolved_some_iff gt b op args res
                                raised).1 hc
                            have hout : StepOutcome.errored c raised =
                                StepOutcome.errored d err := by
                              simpa [stepClean, hcur, hlocal, hc] using herror
                            cases hout
                            exact Raises.bin c op args res rest b err hcur hcatch
                | eq x y => simp [stepClean, hcur] at herror
                | cut => simp [stepClean, hcur] at herror
                | cutAt k => simp [stepClean, hcur] at herror
                | callDyn hd args res => simp [stepClean, hcur] at herror
                | evalg value res => simp [stepClean, hcur] at herror
                | onceg tmpl sub res => simp [stepClean, hcur] at herror
                | amb branches res => simp [stepClean, hcur] at herror
                | spread value res => simp [stepClean, hcur] at herror
                | ite cond thn els res => simp [stepClean, hcur] at herror
                | smatch pattern => simp [stepClean, hcur] at herror
                | wact op args res => simp [stepClean, hcur] at herror

theorem runClean_done_starr (prog : Prog) (gt : GroundingTable)
    (fuel : Nat) (c : Conf) (limit : Option Nat) (d : Conf)
    (h : runClean prog gt fuel c limit = .done d) :
    StepStar prog gt c d ∧ Terminal d :=
  (clean_sound_fuel prog gt fuel).done c limit d h

theorem runClean_error_raises (prog : Prog) (gt : GroundingTable)
    (fuel : Nat) (c : Conf) (limit : Option Nat) (d : Conf) (err : Atom)
    (h : runClean prog gt fuel c limit = .errored d err) :
    Raises prog gt c d err :=
  (clean_sound_fuel prog gt fuel).runError c limit d err h

theorem stepClean_sound (prog : Prog) (gt : GroundingTable)
    (fuel : Nat) (c c' : Conf)
    (hlive : c.cur.isSome ∨ c.alts ≠ [])
    (hprog : stepClean prog gt fuel c = .progressed c') :
    Step prog gt c c' :=
  (clean_sound_fuel prog gt fuel).progressed c c' hlive hprog

theorem stepClean_error_raises (prog : Prog) (gt : GroundingTable)
    (fuel : Nat) (c d : Conf) (err : Atom)
    (h : stepClean prog gt fuel c = .errored d err) :
    Raises prog gt c d err :=
  (clean_sound_fuel prog gt fuel).stepError c d err h

theorem machineMirrorsSpecTotal_proved : machineMirrorsSpecTotal := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro prog gt fuel c c' hlive hprog
    exact stepClean_sound prog gt fuel c c' hlive hprog
  · intro prog gt fuel c limit d hdone
    exact runClean_done_starr prog gt fuel c limit d hdone
  · intro prog gt fuel c d err herror
    exact stepClean_error_raises prog gt fuel c d err herror
  · intro prog gt fuel c limit d err herror
    exact runClean_error_raises prog gt fuel c limit d err herror

end PLeaTTa
