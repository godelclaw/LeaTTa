-- SPDX-License-Identifier: Apache-2.0

/-
Weak-simulation infrastructure for specialization.  The only non-literal
states retained here are dormant resolution branches produced from an open
partial value.  Each such branch carries its already-proved denotational
argument equality and converges literally when activated.
-/
import PLeaTTa.Proofs.Specialize

namespace PLeaTTa

open Metta (Atom Subst)

namespace SpecListRel

theorem mono {α β : Type} {leftRel rightRel : α → β → Prop}
    (lift : ∀ left right, leftRel left right → rightRel left right)
    {left : List α} {right : List β}
    (related : SpecListRel leftRel left right) :
    SpecListRel rightRel left right := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (lift _ _ head) ih

theorem reflOf {α : Type} {rel : α → α → Prop}
    (hrefl : ∀ item, rel item item) (items : List α) :
    SpecListRel rel items items := by
  induction items with
  | nil => exact .nil
  | cons item rest ih => exact .cons (hrefl item) ih

theorem length_eq {α β : Type} {rel : α → β → Prop}
    {left : List α} {right : List β}
    (related : SpecListRel rel left right) : left.length = right.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => simp [ih]

end SpecListRel

/-- Dormant alternatives are either literally identical or one of the exact
    open-partial resolution pairs produced by `resolveAlts_rawArgs_related`. -/
inductive PartialAltRel : Alt → Alt → Prop where
  | same (alt : Alt) : PartialAltRel alt alt
  | pending (leftArgs rightArgs : List Atom) (res : Atom)
      (rest : List Goal) (b : Subst) {left right : Alt}
      (hargs : leftArgs.map (subst b) = rightArgs.map (subst b))
      (related : ResolvedArgsAltRel leftArgs rightArgs res rest b left right) :
      PartialAltRel left right

/-- The active goal is either literally shared or is a just-pulled pending
    open-partial branch. -/
inductive PartialActiveRel :
    Option (List Goal × Subst) → Option (List Goal × Subst) → Prop where
  | same (active : Option (List Goal × Subst)) :
      PartialActiveRel active active
  | pending (leftArgs rightArgs : List Atom) (res : Atom)
      (rest : List Goal) (b : Subst) (leftGoals rightGoals : List Goal)
      (hargs : leftArgs.map (subst b) = rightArgs.map (subst b))
      (related : ResolvedArgsAltRel leftArgs rightArgs res rest b
        (.br leftGoals b) (.br rightGoals b)) :
      PartialActiveRel (some (leftGoals, b)) (some (rightGoals, b))

/-- Configurations related by open-partial simulation have equal observable
    state and position-wise related alternatives.  Only the active goal and
    dormant alternatives may retain the localized raw-argument distinction. -/
structure PartialConfRel (left right : Conf) : Prop where
  cur : PartialActiveRel left.cur right.cur
  alts : SpecListRel PartialAltRel left.alts right.alts
  world : left.world = right.world
  counter : left.counter = right.counter
  qterm : left.qterm = right.qterm
  answers : left.answers = right.answers
  barriers : left.barriers = right.barriers

theorem partialAltRel_refl (alt : Alt) : PartialAltRel alt alt := .same alt

theorem partialAltsRel_refl (alts : List Alt) :
    SpecListRel PartialAltRel alts alts :=
  SpecListRel.reflOf partialAltRel_refl alts

theorem PartialConfRel.refl (c : Conf) : PartialConfRel c c :=
  { cur := .same c.cur
    alts := partialAltsRel_refl c.alts
    world := rfl
    counter := rfl
    qterm := rfl
    answers := rfl
    barriers := rfl }

/-- A raw-argument resolution relation embeds into the global dormant-stack
    relation, retaining its denotational equality witness. -/
theorem resolvedArgsAlts_to_partial
    (leftArgs rightArgs : List Atom) (res : Atom) (rest : List Goal)
    (b : Subst) (hargs : leftArgs.map (subst b) = rightArgs.map (subst b))
    {left right : List Alt}
    (related : SpecListRel
      (ResolvedArgsAltRel leftArgs rightArgs res rest b) left right) :
    SpecListRel PartialAltRel left right :=
  related.mono (fun _ _ head => .pending leftArgs rightArgs res rest b hargs head)

private theorem barrierFold_eq {left right : List Alt}
    (related : SpecListRel PartialAltRel left right) (count : Nat) :
    left.foldl barrierCountStep count =
      right.foldl barrierCountStep count := by
  induction related generalizing count with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | same =>
          simp only [List.foldl_cons]
          exact ih _
      | pending leftArgs rightArgs res rest b hargs branch =>
          cases branch
          simp only [List.foldl_cons, barrierCountStep]
          exact ih count

theorem barrierCount_eq_of_partialAlts {left right : List Alt}
    (related : SpecListRel PartialAltRel left right) :
    barrierCount left = barrierCount right := by
  unfold barrierCount
  exact barrierFold_eq related 0

theorem cutTo_partialAlts (cut : Nat) {left right : List Alt}
    (related : SpecListRel PartialAltRel left right) :
    SpecListRel PartialAltRel (cutTo cut left) (cutTo cut right) := by
  induction related with
  | nil => exact .nil
  | @cons leftHead rightHead leftTail rightTail head tail ih =>
      have hcount : barrierCount (leftHead :: leftTail) =
          barrierCount (rightHead :: rightTail) :=
        barrierCount_eq_of_partialAlts (.cons head tail)
      simp only [cutTo]
      rw [hcount]
      split
      · exact ih
      · exact .cons head tail

/-- Pulling position-wise related stacks either exposes the same branch or
    activates one pending open-partial pair; barriers are skipped in lockstep. -/
theorem pull_with_partialAlts (c : Conf) {left right : List Alt}
    (related : SpecListRel PartialAltRel left right) :
    PartialConfRel
      (pull { c with cur := none, alts := left })
      (pull { c with cur := none, alts := right }) := by
  induction related generalizing c with
  | nil =>
      exact PartialConfRel.refl
        (pull { c with cur := none, alts := [] })
  | @cons leftHead rightHead leftTail rightTail head tail ih =>
      cases head with
      | same =>
          cases leftHead with
          | barrier =>
              let leftHeadConf : Conf :=
                { c with cur := none, alts := Alt.barrier :: leftTail }
              let leftTailConf : Conf :=
                { c with cur := none, alts := leftTail, barriers :=
                    popBarrierCache c.barriers }
              have hleft : pull leftHeadConf = pull leftTailConf := by
                unfold pull
                simp only [leftHeadConf, leftTailConf]
                cases c.barriers <;> rfl
              let rightHeadConf : Conf :=
                { c with cur := none, alts := Alt.barrier :: rightTail }
              let rightTailConf : Conf :=
                { c with cur := none, alts := rightTail, barriers :=
                    popBarrierCache c.barriers }
              have hright : pull rightHeadConf = pull rightTailConf := by
                unfold pull
                simp only [rightHeadConf, rightTailConf]
                cases c.barriers <;> rfl
              change PartialConfRel (pull leftHeadConf) (pull rightHeadConf)
              rw [hleft, hright]
              exact ih
                (c := { c with barriers := popBarrierCache c.barriers })
          | br goals b =>
              rw [pull_branch, pull_branch]
              exact
                { cur := .same (some (goals, b))
                  alts := tail
                  world := rfl
                  counter := rfl
                  qterm := rfl
                  answers := rfl
                  barriers := rfl }
      | pending leftArgs rightArgs res rest b hargs branch =>
          cases branch with
          | branch params result body =>
              rw [pull_branch, pull_branch]
              exact
                { cur := .pending leftArgs rightArgs res rest b _ _ hargs
                    (.branch params result body)
                  alts := tail
                  world := rfl
                  counter := rfl
                  qterm := rfl
                  answers := rfl
                  barriers := rfl }

private def resolvedCallConf (c : Conf) (resolution : List Alt × Nat) : Conf :=
  pull { c with
    cur := none
    counter := resolution.2
    alts := resolution.1 ++ (Alt.barrier :: c.alts)
    barriers := pushBarrierCache c.barriers }

private def activeWithAlts (c : Conf) (alts : List Alt)
    (goals : List Goal) (b : Subst) : Conf :=
  { c with cur := some (goals, b), alts := alts }

/-- A pending sibling alternative heals when pulled even though the remaining
    stacks on the two sides are only related.  Success makes the active
    continuation literally equal modulo those dormant stacks; failure pulls
    the related stacks in lockstep. -/
theorem pendingPartial_branch_steps_related (prog : Prog)
    (gt : Metta.GroundingTable) (c : Conf)
    (leftAlts rightAlts : List Alt)
    (altsRelated : SpecListRel PartialAltRel leftAlts rightAlts)
    (leftArgs rightArgs : List Atom) (res : Atom) (rest : List Goal)
    (b : Subst) (leftGoals rightGoals : List Goal)
    (hargs : leftArgs.map (subst b) = rightArgs.map (subst b))
    (branch : ResolvedArgsAltRel leftArgs rightArgs res rest b
      (.br leftGoals b) (.br rightGoals b)) :
    ∃ leftTarget rightTarget,
      Step prog gt (activeWithAlts c leftAlts leftGoals b) leftTarget ∧
      Step prog gt (activeWithAlts c rightAlts rightGoals b) rightTarget ∧
      PartialConfRel leftTarget rightTarget := by
  cases branch with
  | branch params result body =>
      have hunify := unifyB_callHead_of_args_denote_same b leftArgs rightArgs
        res params result hargs
      cases hleft : unifyB b (Atom.expr (leftArgs ++ [res]))
          (Atom.expr (params ++ [result])) with
      | none =>
          have hright : unifyB b (Atom.expr (rightArgs ++ [res]))
              (Atom.expr (params ++ [result])) = none := by
            rw [← hunify]
            exact hleft
          let leftTarget := pull { c with cur := none, alts := leftAlts }
          let rightTarget := pull { c with cur := none, alts := rightAlts }
          refine ⟨leftTarget, rightTarget, ?_, ?_, ?_⟩
          · simpa [activeWithAlts, leftTarget] using
              (Step.eq_fail (prog := prog) (gt := gt)
                (activeWithAlts c leftAlts _ b) _ _ _ b rfl hleft)
          · simpa [activeWithAlts, rightTarget] using
              (Step.eq_fail (prog := prog) (gt := gt)
                (activeWithAlts c rightAlts _ b) _ _ _ b rfl hright)
          · exact pull_with_partialAlts c altsRelated
      | some nextSubst =>
          have hright : unifyB b (Atom.expr (rightArgs ++ [res]))
              (Atom.expr (params ++ [result])) = some nextSubst := by
            rw [← hunify]
            exact hleft
          let nextGoals := body ++ rest
          let nextBinding := trimFor nextGoals c.qterm nextSubst
          let leftTarget := activeWithAlts c leftAlts nextGoals nextBinding
          let rightTarget := activeWithAlts c rightAlts nextGoals nextBinding
          refine ⟨leftTarget, rightTarget, ?_, ?_, ?_⟩
          · simpa [activeWithAlts, leftTarget, nextGoals, nextBinding] using
              (Step.eq_ok (prog := prog) (gt := gt)
                (activeWithAlts c leftAlts _ b) _ _ nextGoals b nextSubst
                rfl hleft)
          · simpa [activeWithAlts, rightTarget, nextGoals, nextBinding] using
              (Step.eq_ok (prog := prog) (gt := gt)
                (activeWithAlts c rightAlts _ b) _ _ nextGoals b nextSubst
                rfl hright)
          · exact
              { cur := .same (some (nextGoals, nextBinding))
                alts := altsRelated
                world := rfl
                counter := rfl
                qterm := rfl
                answers := rfl
                barriers := rfl }

/-- The complete alternative stacks produced by the two open-partial direct
    calls are related, including the clause barrier and every older exact
    choice point.  Pulling the first branch therefore yields related configs. -/
theorem openPartial_resolution_targets_related (c : Conf) (base : String)
    (bound args : List Atom) (res : Atom) (rest : List Goal) (b : Subst)
    (topological : SubstTopological b) :
    let runtimeArgs := (bound.map (subst b)) ++ args
    let sourceArgs := bound ++ args
    let left := resolveAlts
      (c.world.resolutionCandidates base (bound ++ args).length)
      (runtimeArgs.map (subst b)) runtimeArgs res rest b
      c.qterm (barrierDepth c + 1) c.counter
    let right := resolveAlts
      (c.world.resolutionCandidates base (bound ++ args).length)
      (sourceArgs.map (subst b)) sourceArgs res rest b
      c.qterm (barrierDepth c + 1) c.counter
    PartialConfRel (resolvedCallConf c left) (resolvedCallConf c right) := by
  let runtimeArgs := (bound.map (subst b)) ++ args
  let sourceArgs := bound ++ args
  let left := resolveAlts
    (c.world.resolutionCandidates base (bound ++ args).length)
    (runtimeArgs.map (subst b)) runtimeArgs res rest b
    c.qterm (barrierDepth c + 1) c.counter
  let right := resolveAlts
    (c.world.resolutionCandidates base (bound ++ args).length)
    (sourceArgs.map (subst b)) sourceArgs res rest b
    c.qterm (barrierDepth c + 1) c.counter
  change PartialConfRel (resolvedCallConf c left) (resolvedCallConf c right)
  have hargs : runtimeArgs.map (subst b) = sourceArgs.map (subst b) :=
    partialBoundArgs_denote_same b topological bound args
  have hresolution := resolveAlts_openPartial_related
    (c.world.resolutionCandidates base (bound ++ args).length)
    bound args res rest b c.qterm topological
    (barrierDepth c + 1) c.counter
  have hbranches : SpecListRel PartialAltRel left.1 right.1 :=
    resolvedArgsAlts_to_partial runtimeArgs sourceArgs res rest b hargs
      hresolution.2
  have hsuffix : SpecListRel PartialAltRel
      (Alt.barrier :: c.alts) (Alt.barrier :: c.alts) :=
    .cons (.same .barrier) (partialAltsRel_refl c.alts)
  have hfull := hbranches.append hsuffix
  have hpulled := pull_with_partialAlts
    { c with counter := left.2, barriers := pushBarrierCache c.barriers } hfull
  have hcounter : right.2 = left.2 := hresolution.1.symm
  simpa [resolvedCallConf, hcounter] using hpulled

/-- Actual `call_resolve` steps for the runtime/source partial argument forms
    land in the configuration relation consumed by the weak simulation. -/
theorem openPartial_call_resolution_simulates (prog : Prog)
    (gt : Metta.GroundingTable) (c : Conf) (base : String)
    (bound args : List Atom) (res : Atom) (rest : List Goal) (b : Subst)
    (topological : SubstTopological b)
    (hne : c.world.clauseHeadCandidates base ≠ [])
    (ha : (c.world.resolutionCandidates base (bound ++ args).length).any
      (fun clause => clause.params.length == (bound ++ args).length)) :
    let runtimeArgs := (bound.map (subst b)) ++ args
    let sourceArgs := bound ++ args
    let leftConf : Conf :=
      { c with cur := some (Goal.call base runtimeArgs res :: rest, b) }
    let rightConf : Conf :=
      { c with cur := some (Goal.call base sourceArgs res :: rest, b) }
    let left := resolveAlts
      (c.world.resolutionCandidates base (bound ++ args).length)
      (runtimeArgs.map (subst b)) runtimeArgs res rest b
      c.qterm (barrierDepth c + 1) c.counter
    let right := resolveAlts
      (c.world.resolutionCandidates base (bound ++ args).length)
      (sourceArgs.map (subst b)) sourceArgs res rest b
      c.qterm (barrierDepth c + 1) c.counter
    Step prog gt leftConf (resolvedCallConf c left) ∧
      Step prog gt rightConf (resolvedCallConf c right) ∧
      PartialConfRel (resolvedCallConf c left) (resolvedCallConf c right) := by
  have hsteps := openPartial_call_resolution_steps_related prog gt c base
    bound args res rest b topological hne ha
  exact ⟨hsteps.2.2.1, hsteps.2.2.2,
    openPartial_resolution_targets_related c base bound args res rest b
      topological⟩

/-! ## Constructed specialized-body entry -/

/-- Closed/redundant special case of specialized-body entry.  This lemma is
    retained for callers that genuinely establish pre-guard realization; the
    general open-residual path is `renamed_specialized_body_guards_run_exact`
    below and executes binding guards rather than assuming them away. -/
theorem renamed_specialized_body_guards_run_of_pre_realized (prog : Prog)
    (gt : Metta.GroundingTable) (c : Conf)
    (records : List SpecRecord) (provenance : SpecClauseProvenance)
    (constructed : ProvenanceConstructed records provenance)
    (suffix : String) (barrier : Nat) (continuation : List Goal)
    (runtime : Subst)
    (hcur : c.cur = some
      (provenance.executableClause.body.map
          (renameGoalSuffix suffix barrier) ++
        continuation, runtime))
    (topological : SubstTopological runtime)
    (realized : SubstRealizesBinding runtime
      (renameSpecBindingSuffix suffix provenance.binding)) :
    ∃ isDefined isBin sourceBody targetBody finalSubst,
      sourceBody =
        (specializeCallableHeadGoals isDefined isBin provenance.binding
          provenance.parentClause.body).map
            (renameGoalSuffix suffix barrier) ∧
      ProfileGoalsRel records
        (renameSpecBindingSuffix suffix provenance.binding)
        sourceBody targetBody ∧
      StepStar prog gt c
        { c with cur := some (targetBody ++ continuation, finalSubst) } ∧
      ∃ _ : SubstTopological finalSubst,
        subst finalSubst c.qterm = subst runtime c.qterm := by
  obtain ⟨isDefined, isBin, sourceBody, targetBody, hsource, hbody,
      hrelated⟩ :=
    constructed.renamed_body_shape_suffix records provenance suffix barrier
  have hguardCur : c.cur = some
      (specializationGuards
          (renameSpecBindingSuffix suffix provenance.binding) ++
        (targetBody ++ continuation), runtime) := by
    rw [hbody] at hcur
    simpa [List.append_assoc] using hcur
  obtain ⟨finalSubst, hsteps, hfinalTopological, hqterm⟩ :=
    realized_binding_guards_run prog gt c
      (renameSpecBindingSuffix suffix provenance.binding)
      (targetBody ++ continuation) runtime hguardCur topological realized
  exact ⟨isDefined, isBin, sourceBody, targetBody, finalSubst, hsource,
    hrelated, hsteps, hfinalTopological, hqterm⟩

/-- General specialized-body entry through the real ordered guard trace.
    Construction fixes the recursively profiled suffix; `ExactBindingGuardsRun`
    supplies the concrete successful `unifyB` sequence, exactness witnesses,
    and caller-query invisibility.  No pre-guard `SubstRealizesBinding`
    hypothesis appears: open alpha-copied residuals may be bound by the
    guards themselves. -/
theorem renamed_specialized_body_guards_run_exact (prog : Prog)
    (gt : Metta.GroundingTable) (c : Conf)
    (records : List SpecRecord) (provenance : SpecClauseProvenance)
    (constructed : ProvenanceConstructed records provenance)
    (suffix : String) (barrier : Nat) (continuation targetBody : List Goal)
    (runtime final : Subst)
    (hcur : c.cur = some
      (provenance.executableClause.body.map
          (renameGoalSuffix suffix barrier) ++
        continuation, runtime))
    (hbody :
      provenance.executableClause.body.map
          (renameGoalSuffix suffix barrier) =
        specializationGuards
          (renameSpecBindingSuffix suffix provenance.binding) ++ targetBody)
    (run : ExactBindingGuardsRun c.qterm (targetBody ++ continuation)
      (renameSpecBindingSuffix suffix provenance.binding) runtime final) :
    ∃ isDefined isBin sourceBody,
      sourceBody =
        (specializeCallableHeadGoals isDefined isBin provenance.binding
          provenance.parentClause.body).map
            (renameGoalSuffix suffix barrier) ∧
      ProfileGoalsRel records
        (renameSpecBindingSuffix suffix provenance.binding)
        sourceBody targetBody ∧
      StepStar prog gt c
        { c with cur := some (targetBody ++ continuation, final) } ∧
      Nonempty (SubstTopological final) ∧
        subst final c.qterm = subst runtime c.qterm := by
  obtain ⟨isDefined, isBin, sourceBody, constructedTarget, hsource,
      hconstructedBody, hrelated⟩ :=
    constructed.renamed_body_shape_suffix records provenance suffix barrier
  have htarget : constructedTarget = targetBody := by
    have happend :
        specializationGuards
            (renameSpecBindingSuffix suffix provenance.binding) ++
              constructedTarget =
          specializationGuards
            (renameSpecBindingSuffix suffix provenance.binding) ++
              targetBody := by
      exact hconstructedBody.symm.trans hbody
    exact List.append_cancel_left happend
  subst constructedTarget
  have hguardCur : c.cur = some
      (specializationGuards
          (renameSpecBindingSuffix suffix provenance.binding) ++
        (targetBody ++ continuation), runtime) := by
    rw [hbody] at hcur
    simpa [List.append_assoc] using hcur
  obtain ⟨hsteps, hfinalTopological, hqterm⟩ :=
    exact_binding_guards_run prog gt c c.qterm
      (renameSpecBindingSuffix suffix provenance.binding)
      (targetBody ++ continuation) runtime final rfl hguardCur run
  exact ⟨isDefined, isBin, sourceBody, hsource, hrelated, hsteps,
    hfinalTopological, hqterm⟩

/-- Specialized-body entry from the shared executable guard validator.  This
    is the proof-facing gate used by construction: it replaces a manually
    supplied trace with one reflected from the actual ordered unification and
    trimming computation. -/
theorem renamed_specialized_body_guards_run_checked (prog : Prog)
    (gt : Metta.GroundingTable) (c : Conf)
    (records : List SpecRecord) (provenance : SpecClauseProvenance)
    (constructed : ProvenanceConstructed records provenance)
    (suffix : String) (barrier : Nat) (continuation targetBody : List Goal)
    (runtime final : Subst) (topological : SubstTopological runtime)
    (hcur : c.cur = some
      (provenance.executableClause.body.map
          (renameGoalSuffix suffix barrier) ++ continuation, runtime))
    (hbody :
      provenance.executableClause.body.map
          (renameGoalSuffix suffix barrier) =
        specializationGuards
          (renameSpecBindingSuffix suffix provenance.binding) ++ targetBody)
    (hcheck : exactBindingGuardsRun? c.qterm
      (targetBody ++ continuation)
      (renameSpecBindingSuffix suffix provenance.binding) runtime =
        some final) :
    ∃ isDefined isBin sourceBody,
      sourceBody =
        (specializeCallableHeadGoals isDefined isBin provenance.binding
          provenance.parentClause.body).map
            (renameGoalSuffix suffix barrier) ∧
      ProfileGoalsRel records
        (renameSpecBindingSuffix suffix provenance.binding)
        sourceBody targetBody ∧
      StepStar prog gt c
        { c with cur := some (targetBody ++ continuation, final) } ∧
      Nonempty (SubstTopological final) ∧
        subst final c.qterm = subst runtime c.qterm := by
  exact renamed_specialized_body_guards_run_exact prog gt c records
    provenance constructed suffix barrier continuation targetBody runtime final
    hcur hbody
    (exactBindingGuardsRun?_sound c.qterm (targetBody ++ continuation)
      (renameSpecBindingSuffix suffix provenance.binding) runtime final
      topological hcheck)

end PLeaTTa
