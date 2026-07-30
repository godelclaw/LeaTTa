-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologOrdinaryStepBridge
Purpose: Relate compiler-erased local task administration to exact zero-step
  executable prefixes while retaining cumulative substitution and persistent
  state agreement.
Trusted boundary: none
Main exports:
  NormalizedAlphaGoalsAgree,
  ReadyTaskRelates,
  administrative_prefix_correspondence
-/
import PLeaTTa.Proofs.PrologActivationUnifierBridge
import PLeaTTa.Proofs.PrologStateBridge
import PLeaTTa.Proofs.DemandDrivenCallStep

namespace PLeaTTa.PrologOrdinaryStepBridge

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PrologStateBridge
open PrologGoalAlpha
open PrologMguComposition
open PrologActivationUnifierBridge
open DemandDrivenStep

/-!
The independent goal language retains two administrative forms which the
compiler removes before executable control starts:

* `truth` contributes no executable goal;
* a top-level `conjunction` wrapper is flattened into the surrounding goal
  list.

They are genuine independent `RawStep`s, so an exact state bridge cannot
pretend that they are executable steps.  Conversely, inserting a dummy
executable transition would invent behavior absent from the sealed machine.
This file represents the mismatch as a finite, strictly ranked source-only
prefix paired with an exact zero-step executable prefix.

The relation below is not a new compiler semantics.  It is the existing
`AlphaGoalsAgree`, closed only under those two source administrative forms.
Its task-state layer retains the cumulative residual-MGU valuation produced
by clause activation and the already-proved `SessionRelatesPersistent`
database/world and fresh-frontier relation.
-/

/-- Runtime-alpha goal agreement after erasing source `truth` nodes and
flattening source conjunction wrappers.  Every non-administrative goal still
requires the existing constructor-specific `AlphaGoalAgrees` evidence. -/
inductive NormalizedAlphaGoalsAgree
    (alpha : List (LogicVar × String)) (barrier : Nat) :
    List PeTTaSpec.PrologCore.Goal → List PLeaTTa.Goal → Prop where
  | nil : NormalizedAlphaGoalsAgree alpha barrier [] []
  | truth {references : List PeTTaSpec.PrologCore.Goal}
      {executables : List PLeaTTa.Goal}
      (tail : NormalizedAlphaGoalsAgree alpha barrier references executables) :
      NormalizedAlphaGoalsAgree alpha barrier
        (.truth :: references) executables
  | cons {reference : PeTTaSpec.PrologCore.Goal}
      {executable : PLeaTTa.Goal}
      {references : List PeTTaSpec.PrologCore.Goal}
      {executables : List PLeaTTa.Goal}
      (head : AlphaGoalAgrees alpha barrier reference executable)
      (tail : NormalizedAlphaGoalsAgree alpha barrier references executables) :
      NormalizedAlphaGoalsAgree alpha barrier
        (reference :: references) (executable :: executables)
  | conjunction {referenceBlock referenceTail :
        List PeTTaSpec.PrologCore.Goal}
      {executableBlock executableTail : List PLeaTTa.Goal}
      (block :
        NormalizedAlphaGoalsAgree alpha barrier
          referenceBlock executableBlock)
      (tail :
        NormalizedAlphaGoalsAgree alpha barrier
          referenceTail executableTail) :
      NormalizedAlphaGoalsAgree alpha barrier
        (.conjunction referenceBlock :: referenceTail)
        (executableBlock ++ executableTail)

namespace NormalizedAlphaGoalsAgree

/-- Concatenation preserves the exact flattened executable spine. -/
theorem append
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {leftReference rightReference : List PeTTaSpec.PrologCore.Goal}
    {leftExecutable rightExecutable : List PLeaTTa.Goal}
    (left :
      NormalizedAlphaGoalsAgree alpha barrier
        leftReference leftExecutable)
    (right :
      NormalizedAlphaGoalsAgree alpha barrier
        rightReference rightExecutable) :
    NormalizedAlphaGoalsAgree alpha barrier
      (leftReference ++ rightReference)
      (leftExecutable ++ rightExecutable) := by
  induction left with
  | nil =>
      simpa using right
  | truth tail inductionHypothesis =>
      exact .truth inductionHypothesis
  | cons head tail inductionHypothesis =>
      exact .cons head inductionHypothesis
  | conjunction block tail blockIH tailIH =>
      simpa [List.append_assoc] using
        NormalizedAlphaGoalsAgree.conjunction block tailIH

/-- Exact compiler/runtime alpha agreement embeds without weakening any
non-administrative constructor. -/
theorem ofAlphaGoalsAgree
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement : AlphaGoalsAgree alpha barrier references executables) :
    NormalizedAlphaGoalsAgree alpha barrier references executables := by
  cases agreement with
  | nil =>
      exact .nil
  | cons head tail =>
      exact .cons head (ofAlphaGoalsAgree tail)
  | conjunction block tail =>
      exact .conjunction
        (ofAlphaGoalsAgree block)
        (ofAlphaGoalsAgree tail)

/-- Consuming one source truth node leaves the executable spine unchanged. -/
theorem afterTruth
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      NormalizedAlphaGoalsAgree alpha barrier
        (.truth :: references) executables) :
    NormalizedAlphaGoalsAgree alpha barrier references executables := by
  cases agreement with
  | truth tail =>
      exact tail
  | cons head tail =>
      cases head

/-- Flattening one source conjunction wrapper leaves the executable spine
unchanged. -/
theorem afterConjunction
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {nested rest : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      NormalizedAlphaGoalsAgree alpha barrier
        (.conjunction nested :: rest) executables) :
    NormalizedAlphaGoalsAgree alpha barrier
      (nested ++ rest) executables := by
  cases agreement with
  | conjunction block tail =>
      exact block.append tail
  | cons head tail =>
      cases head

/-- A non-administrative source cut exposes exactly the executable cut at the
barrier carried by the alpha-goal relation.  No other executable constructor
can be selected by administrative normalization. -/
theorem cutHead
    {alpha : List (LogicVar × String)} {barrier : Nat}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      NormalizedAlphaGoalsAgree alpha barrier
        (.cut :: references) executables) :
    ∃ executableTail,
      executables = .cutAt barrier :: executableTail ∧
        NormalizedAlphaGoalsAgree alpha barrier
          references executableTail := by
  cases agreement with
  | cons head tail =>
      cases head with
      | cut =>
          exact ⟨_, rfl, tail⟩

end NormalizedAlphaGoalsAgree

/-- One source-only administrative transition at the active leftmost goal. -/
inductive AdministrativeStep :
    List PeTTaSpec.PrologCore.Goal →
      List PeTTaSpec.PrologCore.Goal → Prop where
  | truth (rest : List PeTTaSpec.PrologCore.Goal) :
      AdministrativeStep (.truth :: rest) rest
  | conjunction (nested rest : List PeTTaSpec.PrologCore.Goal) :
      AdministrativeStep (.conjunction nested :: rest) (nested ++ rest)

/-- Exact transition-counted closure of the source-only administrative
fragment. -/
inductive AdministrativeStepsN :
    Nat → List PeTTaSpec.PrologCore.Goal →
      List PeTTaSpec.PrologCore.Goal → Prop where
  | zero (goals : List PeTTaSpec.PrologCore.Goal) :
      AdministrativeStepsN 0 goals goals
  | succ (count : Nat) (before middle after :
        List PeTTaSpec.PrologCore.Goal)
      (head : AdministrativeStep before middle)
      (tail : AdministrativeStepsN count middle after) :
      AdministrativeStepsN (count + 1) before after

mutual

/-- Number of source administrative nodes exposed by recursively flattening
only conjunction wrappers.  Administrative nodes hidden beneath other
control constructors are not active task steps and are deliberately not
counted until that constructor opens them. -/
def administrativeGoalRank : PeTTaSpec.PrologCore.Goal → Nat
  | .truth => 1
  | .conjunction goals => administrativeRank goals + 1
  | _ => 0

/-- Finite rank for compiler-erased administration in one active task. -/
def administrativeRank : List PeTTaSpec.PrologCore.Goal → Nat
  | [] => 0
  | goal :: goals =>
      administrativeGoalRank goal + administrativeRank goals

end

@[simp] theorem administrativeRank_append
    (left right : List PeTTaSpec.PrologCore.Goal) :
    administrativeRank (left ++ right) =
      administrativeRank left + administrativeRank right := by
  induction left with
  | nil =>
      simp [administrativeRank]
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append, administrativeRank, inductionHypothesis,
        Nat.add_assoc]

/-- Every administrative transition spends exactly one unit of the finite
source rank. -/
theorem AdministrativeStep.rank_exact
    {before after : List PeTTaSpec.PrologCore.Goal}
    (step : AdministrativeStep before after) :
    administrativeRank before = administrativeRank after + 1 := by
  cases step with
  | truth rest =>
      simp [administrativeRank, administrativeGoalRank]
      omega
  | conjunction nested rest =>
      simp [administrativeRank, administrativeGoalRank,
        administrativeRank_append]
      omega

/-- An exact administrative prefix spends exactly its transition count. -/
theorem AdministrativeStepsN.rank_exact
    {count : Nat} {before after : List PeTTaSpec.PrologCore.Goal}
    (steps : AdministrativeStepsN count before after) :
    administrativeRank before =
      count + administrativeRank after := by
  induction steps with
  | zero goals =>
      simp
  | succ count before middle after head tail inductionHypothesis =>
      have first := head.rank_exact
      omega

/-- One administrative goal-list step is the corresponding actual local
`RawStep`, with no observations, cut signal, session change, or binding
change. -/
theorem AdministrativeStep.rawStep
    {before after : List PeTTaSpec.PrologCore.Goal}
    (step : AdministrativeStep before after)
    (scope : CutScopeId) (bindings : Substitution) (session : Session) :
    RawStep session (.task scope before bindings) [] .none session
      (.running (.task scope after bindings)) := by
  cases step with
  | truth _ =>
      exact RawStep.taskTruth scope _ bindings session
  | conjunction _ _ =>
      exact RawStep.taskConjunction scope _ _ bindings session

/-- One administrative goal-list step is also one actual public local-search
transition. -/
theorem AdministrativeStep.transition
    {before after : List PeTTaSpec.PrologCore.Goal}
    (step : AdministrativeStep before after)
    (scope : CutScopeId) (bindings : Substitution) (session : Session) :
    Transition
      (.running session (.task scope before bindings)) []
      (.running session (.task scope after bindings)) := by
  exact .ordinary _ _ _ _ _ (step.rawStep scope bindings session)

/-- The abstract administrative prefix is inhabited by an exact public
source execution with the same count and an empty observation trace. -/
theorem AdministrativeStepsN.sourceSteps
    {count : Nat} {before after : List PeTTaSpec.PrologCore.Goal}
    (steps : AdministrativeStepsN count before after)
    (scope : CutScopeId) (bindings : Substitution) (session : Session) :
    PeTTaSpec.PrologCore.GoalSemantics.StepsN count
      (.running session (.task scope before bindings)) []
      (.running session (.task scope after bindings)) := by
  induction steps with
  | zero goals =>
      exact .zero _
  | succ count before middle after head tail inductionHypothesis =>
      simpa using
        PeTTaSpec.PrologCore.GoalSemantics.StepsN.succ count
          (.running session (.task scope before bindings))
          (.running session (.task scope middle bindings))
          (.running session (.task scope after bindings))
          [] [] (head.transition scope bindings session)
          inductionHypothesis

/-- Actual task payload agreement after compiler-erased administration.  The
independent cumulative binding remains explicit rather than being folded into
the goal syntax. -/
structure TaskPayloadAgrees
    (alpha support : List (LogicVar × String)) (barrier : Nat)
    (canonical : TreeSubstitution) (referenceBase current : Substitution)
    (runtime : Metta.Subst)
    (references : List PeTTaSpec.PrologCore.Goal)
    (executables : List PLeaTTa.Goal) : Prop where
  bindingShape :
    current = TreeSubstitution.reify canonical ++ referenceBase
  control :
    NormalizedAlphaGoalsAgree alpha barrier references executables
  valuation :
    AlphaCumulativeResidualVariantAgreesOn
      alpha support canonical referenceBase runtime

/-- The exact post-clause-activation payload already proved by the MGU bridge
embeds into administrative-normalized task agreement. -/
theorem TaskPayloadAgrees.ofActivated
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {runtime : Metta.Subst}
    {entered : PeTTaSpec.PrologCore.Resolver.EnteredClause}
    {executables : List PLeaTTa.Goal}
    (agreement :
      ActivatedTaskAgrees alpha support barrier canonical referenceBase
        runtime entered executables) :
    TaskPayloadAgrees alpha support barrier canonical referenceBase
      entered.bindings runtime entered.rawBody executables := by
  exact
    ⟨agreement.1,
      NormalizedAlphaGoalsAgree.ofAlphaGoalsAgree agreement.2.1,
      agreement.2.2⟩

/-- Leaf-level state relation for one active independent task and one ready
fine executable state.  The broader Search/OpenConf bridge will add relations
for choices and typed delimiter frames; this leaf pins the actual current
goal/substitution payload and persistent state without constraining those
future frame relations prematurely. -/
def ReadyTaskRelates
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String)) (barrier : Nat)
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (session : Session) (current : Substitution)
    (references : List PeTTaSpec.PrologCore.Goal)
    (state : OpenConf) : Prop :=
  ∃ executableGoals : List PLeaTTa.Goal, ∃ runtime : Metta.Subst,
    SessionRelatesPersistent freshFrontier session state.persistent ∧
      state.control.cur = some (executableGoals, runtime) ∧
      TaskPayloadAgrees alpha support barrier canonical referenceBase current
        runtime references executableGoals

/-- Clause activation plus the persistent state bridge constructs the actual
ready-task relation consumed by ordinary-step simulation. -/
theorem ReadyTaskRelates.ofActivated
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {session : Session} {state : OpenConf}
    {runtime : Metta.Subst}
    {entered : PeTTaSpec.PrologCore.Resolver.EnteredClause}
    {executables : List PLeaTTa.Goal}
    (persistent :
      SessionRelatesPersistent freshFrontier session state.persistent)
    (current : state.control.cur = some (executables, runtime))
    (activated :
      ActivatedTaskAgrees alpha support barrier canonical referenceBase
        runtime entered executables) :
    ReadyTaskRelates freshFrontier alpha support barrier canonical
      referenceBase session entered.bindings entered.rawBody state := by
  exact
    ⟨executables, runtime, persistent, current,
      TaskPayloadAgrees.ofActivated activated⟩

/-- One source administrative step preserves the exact ready executable
state, cumulative valuation, and persistent bridge. -/
theorem ReadyTaskRelates.afterAdministrativeStep
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {session : Session} {current : Substitution}
    {before after : List PeTTaSpec.PrologCore.Goal}
    {state : OpenConf}
    (agreement :
      ReadyTaskRelates freshFrontier alpha support barrier canonical
        referenceBase session current before state)
    (step : AdministrativeStep before after) :
    ReadyTaskRelates freshFrontier alpha support barrier canonical
      referenceBase session current after state := by
  rcases agreement with
    ⟨executables, runtime, persistent, currentControl, payload⟩
  refine
    ⟨executables, runtime, persistent, currentControl,
      ⟨payload.bindingShape, ?_, payload.valuation⟩⟩
  cases step with
  | truth rest =>
      exact payload.control.afterTruth
  | conjunction nested rest =>
      exact payload.control.afterConjunction

/-- A finite source administrative prefix preserves the ready-task relation
without moving the executable state. -/
theorem ReadyTaskRelates.afterAdministrativeSteps
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {session : Session} {current : Substitution}
    {count : Nat}
    {before after : List PeTTaSpec.PrologCore.Goal}
    {state : OpenConf}
    (agreement :
      ReadyTaskRelates freshFrontier alpha support barrier canonical
        referenceBase session current before state)
    (steps : AdministrativeStepsN count before after) :
    ReadyTaskRelates freshFrontier alpha support barrier canonical
      referenceBase session current after state := by
  induction steps with
  | zero goals =>
      exact agreement
  | succ count before middle after head tail inductionHypothesis =>
      exact inductionHypothesis
        (agreement.afterAdministrativeStep head)

/-- Exact bounded-stutter correspondence for compiler-erased task
administration.

The independent side performs exactly `count` real transitions and emits no
observations.  The executable side performs exactly zero transitions, so it
cannot invent an effect, answer, failure, or scheduling decision.  The rank
equation proves that a fixed source task admits no infinite administrative
stutter. -/
theorem administrative_prefix_correspondence
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {session : Session} {scope : CutScopeId} {current : Substitution}
    {count : Nat}
    {before after : List PeTTaSpec.PrologCore.Goal}
    {state : OpenConf}
    (agreement :
      ReadyTaskRelates freshFrontier alpha support barrier canonical
        referenceBase session current before state)
    (steps : AdministrativeStepsN count before after) :
    PeTTaSpec.PrologCore.GoalSemantics.StepsN count
        (.running session (.task scope before current)) []
        (.running session (.task scope after current)) ∧
      DemandDrivenCallStep.StepsN prog gt 0
        (.ready state) (.ready state) ∧
      ReadyTaskRelates freshFrontier alpha support barrier canonical
        referenceBase session current after state ∧
      administrativeRank before =
        count + administrativeRank after := by
  exact
    ⟨steps.sourceSteps scope current session,
      .zero (.ready state),
      agreement.afterAdministrativeSteps steps,
      steps.rank_exact⟩

/-! ## Local cut: one real step on each side -/

/-- Exact executable successor of one tagged cut.  The current goal advances
and the alternative/barrier stacks are pruned by the sealed machine's shared
`cutToTracked`; persistent world and fresh allocation are untouched. -/
def cutSuccessor (state : OpenConf) (barrier : Nat)
    (rest : List PLeaTTa.Goal) (runtime : Metta.Subst) : OpenConf :=
  OpenConf.ofConf
    { state.toConf with
      cur := some (rest, runtime)
      alts := (cutToTracked barrier state.toConf.barriers
        state.toConf.alts).1
      barriers := (cutToTracked barrier state.toConf.barriers
        state.toConf.alts).2 }
    state.frames

@[simp] theorem cutSuccessor_persistent
    (state : OpenConf) (barrier : Nat)
    (rest : List PLeaTTa.Goal) (runtime : Metta.Subst) :
    (cutSuccessor state barrier rest runtime).persistent =
      state.persistent := by
  cases state with
  | mk persistent control frames =>
      cases persistent
      cases control
      rfl

@[simp] theorem cutSuccessor_current
    (state : OpenConf) (barrier : Nat)
    (rest : List PLeaTTa.Goal) (runtime : Metta.Subst) :
    (cutSuccessor state barrier rest runtime).control.cur =
      some (rest, runtime) := by
  rfl

/-- An executable cut head takes exactly one real transition in the
findall/call-fine lane.  It cannot be mistaken for either a nested collector
or a local-call installation head. -/
theorem executable_cut_step
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (state : OpenConf) (barrier : Nat)
    (rest : List PLeaTTa.Goal) (runtime : Metta.Subst)
    (head :
      state.control.cur = some (.cutAt barrier :: rest, runtime)) :
    DemandDrivenCallStep.Step prog gt (.ready state)
      (.ready (cutSuccessor state barrier rest runtime)) := by
  have sealedHead :
      state.toConf.cur = some (.cutAt barrier :: rest, runtime) := by
    simpa [OpenConf.toConf, Control.toConf] using head
  have notFindall : ¬ findallRunHead state.toConf := by
    simp [findallRunHead, sealedHead]
  have notLocalCall :
      ¬ DemandDrivenCallStep.LocalResolveHead state := by
    simp [DemandDrivenCallStep.LocalResolveHead, sealedHead]
  apply DemandDrivenCallStep.Step.ordinary state
    (cutSuccessor state barrier rest runtime) notLocalCall
  apply DemandDrivenStep.Step.ordinary state
    (cutSuccessor state barrier rest runtime).toConf notFindall
  simpa [cutSuccessor] using
    (PLeaTTa.Step.cut_at state.toConf barrier rest runtime sealedHead)

/-- Paired local-cut transition on the actual task states.

The independent transition emits no observation and exposes a typed commit
signal; the executable transition performs the exact `cutToTracked` update at
the barrier selected by `AlphaGoalAgrees.cut`.  The task payload, cumulative
MGU valuation, database/world relation, and fresh frontier survive.  This
leaf theorem intentionally does not yet identify the source choice resources
pruned by commit propagation with executable `Alt`s; that is the separate
wrapper/resource-linearity obligation. -/
theorem cut_step_correspondence
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {session : Session} {scope : CutScopeId} {current : Substitution}
    {references : List PeTTaSpec.PrologCore.Goal}
    {state : OpenConf}
    (agreement :
      ReadyTaskRelates freshFrontier alpha support barrier canonical
        referenceBase session current (.cut :: references) state) :
    ∃ executableTail runtime,
      state.control.cur =
          some (.cutAt barrier :: executableTail, runtime) ∧
        RawStep session (.task scope (.cut :: references) current)
          [] (.commit scope) session
          (.running (.task scope references current)) ∧
        DemandDrivenCallStep.Step prog gt (.ready state)
          (.ready (cutSuccessor state barrier executableTail runtime)) ∧
        (cutSuccessor state barrier executableTail runtime).persistent =
          state.persistent ∧
        ReadyTaskRelates freshFrontier alpha support barrier canonical
          referenceBase session current references
          (cutSuccessor state barrier executableTail runtime) := by
  rcases agreement with
    ⟨executables, runtime, persistent, currentControl, payload⟩
  rcases payload.control.cutHead with
    ⟨executableTail, executableShape, tailControl⟩
  subst executables
  refine
    ⟨executableTail, runtime, currentControl,
      RawStep.taskCut scope references current session,
      executable_cut_step state barrier executableTail runtime currentControl,
      cutSuccessor_persistent state barrier executableTail runtime, ?_⟩
  refine
    ⟨executableTail, runtime, ?_,
      cutSuccessor_current state barrier executableTail runtime,
      ⟨payload.bindingShape, tailControl, payload.valuation⟩⟩
  simpa using persistent

/-! ## Anti-vacuity: exact count and strictness -/

private def threeAdministrativeGoals :
    List PeTTaSpec.PrologCore.Goal :=
  [.truth, .conjunction [.truth]]

/-- The administrative relation really contains a three-transition prefix;
the count is not reflexive closure dressed as a bounded simulation. -/
theorem three_administrative_steps_are_exact :
    AdministrativeStepsN 3 threeAdministrativeGoals [] := by
  apply AdministrativeStepsN.succ 2 threeAdministrativeGoals
    [.conjunction [.truth]] []
  · exact .truth _
  · apply AdministrativeStepsN.succ 1 [.conjunction [.truth]] [.truth] []
    · exact .conjunction [.truth] []
    · apply AdministrativeStepsN.succ 0 [.truth] [] []
      · exact .truth []
      · exact .zero []

/-- A wrong two-step collapse of the same source prefix is refuted by the
strict administrative rank. -/
theorem three_administrative_steps_are_not_two :
    ¬ AdministrativeStepsN 2 threeAdministrativeGoals [] := by
  intro wrong
  have rank := wrong.rank_exact
  norm_num [threeAdministrativeGoals, administrativeRank,
    administrativeGoalRank] at rank

end PLeaTTa.PrologOrdinaryStepBridge
