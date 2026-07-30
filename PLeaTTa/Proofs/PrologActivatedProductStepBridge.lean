-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologActivatedProductStepBridge
Purpose: Carry the post-clause-activation relation through the real source
  product/cut/choice wrappers and the fine executable task lane.
Trusted boundary: none
Main exports:
  ActiveProductRelates,
  RetainedProductResources,
  RepresentativeProductActivation.activeProductRelates,
  ActiveProductRelates.afterAdministrativeStep
-/
import PLeaTTa.Proofs.PrologRepresentativeProductActivationBridge
import PLeaTTa.Proofs.BarrierCache
import PLeaTTa.Proofs.PrologCoreAdequacy

namespace PLeaTTa.PrologActivatedProductStepBridge

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologAlphaFreshFrontierBridge
open PrologOrdinaryStepBridge
open PrologRepresentativeProductActivationBridge
open PrologRepresentativeStepActivationBridge
open PrologStateBridge

/-! ## Active source spelling -/

/-- Post-activation source control with an arbitrary current clause-body
prefix and cumulative substitution.

The retained immutable cursor stays in the right branch at the predicate cut
scope.  The caller tail remains outside that cut boundary in `product`.
Keeping both delimiters explicit is what later lets a clause-local cut prune
later clauses without pruning the caller's alternatives. -/
def activeSourceProduct
    (callerScope : CutScopeId) (opened : OpenedCall)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (current : Substitution)
    (body referenceRest : List PeTTaSpec.PrologCore.Goal) : Search :=
  .product callerScope
    (.cutBoundary opened.scope
      (.choice opened.scope
        (.task opened.scope body current)
        (.clauses opened.scope (finish.advance branch branchTail))))
    referenceRest

@[simp] theorem activeSourceProduct_initial
    (callerScope : CutScopeId) (opened : OpenedCall)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (current : Substitution)
    (referenceRest : List PeTTaSpec.PrologCore.Goal) :
    activeSourceProduct callerScope opened finish branch branchTail current
        branch.body referenceRest =
      activatedSourceProduct callerScope opened finish branch branchTail
        current referenceRest :=
  rfl

/-- A non-answering ordinary body step propagates through the retained clause
choice, the predicate cut boundary, and the caller product without changing
its events or cut signal.

This is a structural reuse lemma: logical payload reasoning remains at the
task leaf, while DFS ownership and delimiter placement are inherited from the
already proved source control semantics. -/
theorem activeSourceProduct_progress
    {callerScope : CutScopeId} {opened : OpenedCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch}
    {before after : Session} {current nextCurrent : Substitution}
    {body nextBody referenceRest : List PeTTaSpec.PrologCore.Goal}
    {events : List Observation}
    (child :
      RawStep before (.task opened.scope body current) events .none after
        (.running (.task opened.scope nextBody nextCurrent)))
    (answerFree : Trace.AnswerFree events) :
    RawStep before
      (activeSourceProduct callerScope opened finish branch branchTail
        current body referenceRest)
      events .none after
      (.running
        (activeSourceProduct callerScope opened finish branch branchTail
          nextCurrent nextBody referenceRest)) := by
  have choiceStep :
      RawStep before
        (.choice opened.scope
          (.task opened.scope body current)
          (.clauses opened.scope (finish.advance branch branchTail)))
        events .none after
        (.running
          (.choice opened.scope
            (.task opened.scope nextBody nextCurrent)
            (.clauses opened.scope
              (finish.advance branch branchTail)))) :=
    .choiceProgress opened.scope _ _ _ events before after child
  have boundaryStep :
      RawStep before
        (.cutBoundary opened.scope
          (.choice opened.scope
            (.task opened.scope body current)
            (.clauses opened.scope (finish.advance branch branchTail))))
        events .none after
        (.running
          (.cutBoundary opened.scope
            (.choice opened.scope
              (.task opened.scope nextBody nextCurrent)
              (.clauses opened.scope
                (finish.advance branch branchTail))))) :=
    .cutBoundaryProgress opened.scope _ _ events before after choiceStep
  exact
    .productProgress callerScope _ _ referenceRest events .none before after
      boundaryStep answerFree

/-! ## Paired active state -/

/-- Relation after one retained clause has entered its body.

The independent side keeps `body` and the caller tail in distinct control
nodes; the executable side flattens them.  `ready` relates that common logical
payload.  The remaining fields retain the exact alternative bank, tracked
barrier cache, cut tag, and suspended fine frames so later cut/backtracking
proofs cannot forget resource ownership. -/
structure ActiveProductRelates
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String)) (barrier : Nat)
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (opened : OpenedCall) (pending : DemandDrivenCallStep.PendingCall)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (altTail : List PLeaTTa.Alt)
    (referenceRest : List PeTTaSpec.PrologCore.Goal)
    (current : Substitution)
    (body : List PeTTaSpec.PrologCore.Goal)
    (state : OpenConf) : Prop where
  ready :
    ReadyTaskRelates freshFrontier alpha support barrier canonical
      referenceBase opened.session current (body ++ referenceRest) state
  retainedAlts :
    state.control.alts =
      altTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts
  retainedAltsZero : PLeaTTa.barrierCount altTail = 0
  retainedBarriers :
    state.control.barriers =
      PLeaTTa.pushBarrierCache pending.outer.barriers
  barrierTag :
    barrier =
      pending.outer.barriers.getD
        (PLeaTTa.barrierCount pending.outer.alts) + 1
  frames : state.frames = pending.frames

/-! ## Control-independent retained resources -/

/-- Exact executable resources owned by one active local-predicate call.

This certificate deliberately contains no goal payload or cut-control
spelling.  Uniform and segmented body relations can therefore share the
barrier/cache proof without identifying the body's predicate barrier with the
caller's older barrier. -/
structure RetainedProductResources
    (barrier : Nat) (pending : DemandDrivenCallStep.PendingCall)
    (altTail : List PLeaTTa.Alt) (state : OpenConf) : Prop where
  retainedAlts :
    state.control.alts =
      altTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts
  retainedAltsZero : PLeaTTa.barrierCount altTail = 0
  retainedBarriers :
    state.control.barriers =
      PLeaTTa.pushBarrierCache pending.outer.barriers
  barrierTag :
    barrier =
      pending.outer.barriers.getD
        (PLeaTTa.barrierCount pending.outer.alts) + 1

/-- Forget the logical payload and frame ownership, retaining only the exact
alternative/barrier resources owned by the active predicate call. -/
def ActiveProductRelates.resources
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {referenceRest body : List PeTTaSpec.PrologCore.Goal}
    {current : Substitution} {state : OpenConf}
    (agreement :
      ActiveProductRelates freshFrontier alpha support barrier canonical
        referenceBase opened pending finish branch branchTail altTail
        referenceRest current body state) :
    RetainedProductResources barrier pending altTail state :=
  ⟨agreement.retainedAlts, agreement.retainedAltsZero,
    agreement.retainedBarriers, agreement.barrierTag⟩

/-- Coherence of an active call's resource certificate recovers coherence of
the suspended outer alternative stack. -/
theorem RetainedProductResources.outerBarrierCacheCoherent
    {barrier : Nat} {pending : DemandDrivenCallStep.PendingCall}
    {altTail : List PLeaTTa.Alt} {state : OpenConf}
    (resources :
      RetainedProductResources barrier pending altTail state)
    (coherent : PLeaTTa.BarrierCacheCoherent state.toConf) :
    match pending.outer.barriers with
    | none => True
    | some depth => depth = PLeaTTa.barrierCount pending.outer.alts := by
  cases cached : pending.outer.barriers with
  | none =>
      trivial
  | some depth =>
      have activeCached :
          state.toConf.barriers = some (depth + 1) := by
        change state.control.barriers = some (depth + 1)
        rw [resources.retainedBarriers, cached]
        rfl
      have activeDepth := coherent.depth_eq activeCached
      have activeAlts :
          state.toConf.alts =
            altTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts := by
        exact resources.retainedAlts
      rw [activeAlts, PLeaTTa.barrierCount_append,
        resources.retainedAltsZero,
        PLeaTTa.barrierCount_cons_barrier] at activeDepth
      omega

/-- A coherent resource certificate identifies the active predicate tag with
the semantic depth immediately above the suspended outer alternatives. -/
theorem RetainedProductResources.barrierTag_eq
    {barrier : Nat} {pending : DemandDrivenCallStep.PendingCall}
    {altTail : List PLeaTTa.Alt} {state : OpenConf}
    (resources :
      RetainedProductResources barrier pending altTail state)
    (coherent : PLeaTTa.BarrierCacheCoherent state.toConf) :
    barrier = PLeaTTa.barrierCount pending.outer.alts + 1 := by
  have outerCoherent := resources.outerBarrierCacheCoherent coherent
  rw [resources.barrierTag]
  cases cached : pending.outer.barriers with
  | none =>
      simp
  | some depth =>
      have depthEq :
          depth = PLeaTTa.barrierCount pending.outer.alts := by
        simpa [cached] using outerCoherent
      simp [depthEq]

/-- A tagged cut at the active predicate barrier removes exactly the retained
clause alternatives and their marker, leaving the caller's alternatives. -/
theorem RetainedProductResources.cutToTracked_alts_eq_outer
    {barrier : Nat} {pending : DemandDrivenCallStep.PendingCall}
    {altTail : List PLeaTTa.Alt} {state : OpenConf}
    (resources :
      RetainedProductResources barrier pending altTail state)
    (coherent : PLeaTTa.BarrierCacheCoherent state.toConf) :
    (PLeaTTa.cutToTracked barrier state.toConf.barriers state.toConf.alts).1 =
      pending.outer.alts := by
  have altsShape :
      state.toConf.alts =
        altTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts :=
    resources.retainedAlts
  rw [PLeaTTa.cutToTracked_fst_of_coherent _ _ _ coherent, altsShape,
    resources.barrierTag_eq coherent]
  exact
    PLeaTTa.PrologCoreAdequacy.cutTo_own_barrier altTail pending.outer.alts

/-! ## Tracked barrier reconstruction -/

/-- Coherence of the active state recovers coherence of the suspended outer
alternative stack.

The proof uses every ownership fact carried by `ActiveProductRelates`: the
retained scan contributes no barriers, the call installs exactly one marker,
and the enabled cache is incremented exactly once. -/
theorem ActiveProductRelates.outerBarrierCacheCoherent
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {referenceRest body : List PeTTaSpec.PrologCore.Goal}
    {current : Substitution} {state : OpenConf}
    (agreement :
      ActiveProductRelates freshFrontier alpha support barrier canonical
        referenceBase opened pending finish branch branchTail altTail
        referenceRest current body state)
    (coherent : PLeaTTa.BarrierCacheCoherent state.toConf) :
    match pending.outer.barriers with
    | none => True
    | some depth => depth = PLeaTTa.barrierCount pending.outer.alts := by
  exact agreement.resources.outerBarrierCacheCoherent coherent

/-- Under the reachable-state cache invariant, the stored call tag is the
semantic depth immediately above the outer alternative stack. -/
theorem ActiveProductRelates.barrierTag_eq
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {referenceRest body : List PeTTaSpec.PrologCore.Goal}
    {current : Substitution} {state : OpenConf}
    (agreement :
      ActiveProductRelates freshFrontier alpha support barrier canonical
        referenceBase opened pending finish branch branchTail altTail
        referenceRest current body state)
    (coherent : PLeaTTa.BarrierCacheCoherent state.toConf) :
    barrier = PLeaTTa.barrierCount pending.outer.alts + 1 := by
  exact agreement.resources.barrierTag_eq coherent

/-- The executable tagged cut removes every retained clause alternative and
the predicate's own barrier, leaving the caller's alternative stack exactly.
No answer-list or stuttering quotient appears in this state equation. -/
theorem ActiveProductRelates.cutToTracked_alts_eq_outer
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {referenceRest body : List PeTTaSpec.PrologCore.Goal}
    {current : Substitution} {state : OpenConf}
    (agreement :
      ActiveProductRelates freshFrontier alpha support barrier canonical
        referenceBase opened pending finish branch branchTail altTail
        referenceRest current body state)
    (coherent : PLeaTTa.BarrierCacheCoherent state.toConf) :
    (PLeaTTa.cutToTracked barrier state.toConf.barriers state.toConf.alts).1 =
      pending.outer.alts := by
  exact agreement.resources.cutToTracked_alts_eq_outer coherent

/-- A stale enabled cache defeats the own-barrier cut even on the smallest
possible stack.  This witnesses that `BarrierCacheCoherent` above is
load-bearing rather than proof decoration. -/
theorem stale_cache_would_defeat_own_barrier_cut :
    (PLeaTTa.cutToTracked 1 (some 0)
      ([PLeaTTa.Alt.barrier] : List PLeaTTa.Alt)).1 ≠ [] := by
  simp [PLeaTTa.cutToTracked, PLeaTTa.cutToCached]

/-! ## Clause-local cut through the real wrapper stack -/

/-- Identity-bearing resource owned by the retained later-clause cursor. -/
def retainedCursorToken
    (opened : OpenedCall) (finish : PreparedCursor)
    (branch : ClauseBranch) (branchTail : List ClauseBranch) : CursorToken :=
  { scope := opened.scope
    cursor := finish.advance branch branchTail }

/-- Source control after the current clause commits: later clauses are gone,
the predicate cut boundary remains around the continuing body, and the
caller's latent tail remains outside it. -/
def cutSourceProduct
    (callerScope : CutScopeId) (opened : OpenedCall)
    (current : Substitution) (body referenceRest :
      List PeTTaSpec.PrologCore.Goal) : Search :=
  .product callerScope
    (.cutBoundary opened.scope
      (.task opened.scope body current))
    referenceRest

/-- One clause-local cut step prunes the retained later-clause cursor,
catches the predicate-local commit, and leaves the caller tail intact.

The singleton pruning observation is exact: it carries the activation scope
and the immutable prepared cursor, rather than merely counting discarded
alternatives. -/
theorem activeSourceProduct_cut
    {session : Session}
    {callerScope : CutScopeId} {opened : OpenedCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch}
    {current : Substitution}
    {bodyRest referenceRest : List PeTTaSpec.PrologCore.Goal} :
    RawStep session
      (activeSourceProduct callerScope opened finish branch branchTail current
        (.cut :: bodyRest) referenceRest)
      [.pruned (retainedCursorToken opened finish branch branchTail)]
      .none session
      (.running
        (cutSourceProduct callerScope opened current bodyRest referenceRest)) := by
  have choiceStep :
      RawStep session
        (.choice opened.scope
          (.task opened.scope (.cut :: bodyRest) current)
          (.clauses opened.scope (finish.advance branch branchTail)))
        [.pruned (retainedCursorToken opened finish branch branchTail)]
        (.commit opened.scope) session
        (.running (.task opened.scope bodyRest current)) := by
    simpa [retainedCursorToken, Search.liveCursors] using
      (RawStep.choiceCommitHere opened.scope
        (.task opened.scope (.cut :: bodyRest) current)
        (.clauses opened.scope (finish.advance branch branchTail))
        (.task opened.scope bodyRest current) []
        session session
        (RawStep.taskCut opened.scope bodyRest current session))
  have boundaryStep :
      RawStep session
        (.cutBoundary opened.scope
          (.choice opened.scope
            (.task opened.scope (.cut :: bodyRest) current)
            (.clauses opened.scope (finish.advance branch branchTail))))
        [.pruned (retainedCursorToken opened finish branch branchTail)]
        .none session
        (.running
          (.cutBoundary opened.scope
            (.task opened.scope bodyRest current))) :=
    RawStep.cutBoundaryCatch opened.scope _ _
      [.pruned (retainedCursorToken opened finish branch branchTail)]
      session session choiceStep
  simpa [activeSourceProduct, cutSourceProduct] using
    (RawStep.productProgress callerScope _ _
      referenceRest
      [.pruned (retainedCursorToken opened finish branch branchTail)]
      .none session session boundaryStep
      (by simp [Trace.AnswerFree]))

/-- Paired state after a clause-local cut has discarded the predicate's
retained alternatives and marker.

The executable side is now exactly at the caller's alternative stack.
Coherence, rather than cache-representation equality, is the correct
postcondition because cached and uncached executions are both valid. -/
structure CommittedProductRelates
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String)) (barrier : Nat)
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (opened : OpenedCall) (pending : DemandDrivenCallStep.PendingCall)
    (referenceRest : List PeTTaSpec.PrologCore.Goal)
    (current : Substitution)
    (body : List PeTTaSpec.PrologCore.Goal)
    (state : OpenConf) : Prop where
  ready :
    ReadyTaskRelates freshFrontier alpha support barrier canonical
      referenceBase opened.session current (body ++ referenceRest) state
  outerAlts : state.control.alts = pending.outer.alts
  cacheCoherent : PLeaTTa.BarrierCacheCoherent state.toConf
  frames : state.frames = pending.frames

/-- The exact representative activation package constructs the active
wrapper relation for its actual fine executable successor. -/
theorem
    PrologRepresentativeProductActivationBridge.RepresentativeProductActivation.activeProductRelates
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {copied : PLeaTTa.Clause}
    {referenceRest : List PeTTaSpec.PrologCore.Goal}
    {executableRest : List PLeaTTa.Goal}
    {qterm : Metta.Atom} {barrier startCounter : Nat}
    {callerScope : CutScopeId}
    {independentResult : Substitution}
    {representative : TreeSubstitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattenedRepresentative : TreeSubstitution}
    {installed : Metta.Subst}
    (activation :
      RepresentativeProductActivation prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        referenceRest executableRest qterm barrier startCounter callerScope
        independentResult representative nextAlpha sourceCanonical
        flattenedRepresentative installed) :
    ActiveProductRelates (AlphaFreshFrontier nextAlpha) nextAlpha support
      barrier (sourceCanonical ++ canonical) referenceBase opened pending
      finish branch branchTail altTail referenceRest independentResult
      branch.body
      (activatedOpenSuccessor pending copied executableRest qterm
        installed) := by
  refine
    ⟨?_, ?_, activation.retainedAltsZero, ?_, activation.barrierTag, rfl⟩
  · exact
      ⟨copied.body ++ executableRest,
        PLeaTTa.trimFor (copied.body ++ executableRest) qterm installed,
        activation.activatedSessionRelates, rfl,
        activation.flattenedPayload⟩
  · change
      (activatedExecutableSuccessor pending copied executableRest qterm
        installed).alts =
        altTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts
    exact activation.retainedAlts
  · change
      (activatedExecutableSuccessor pending copied executableRest qterm
        installed).barriers =
        PLeaTTa.pushBarrierCache pending.outer.barriers
    exact activation.retainedBarriers

/-! ## Compiler-erased administration -/

/-- A task-administrative step commutes with appending the latent caller tail.
This is the exact list fact connecting source `product` control to the
executable's flattened task spine. -/
theorem AdministrativeStep.appendRight
    {before after : List PeTTaSpec.PrologCore.Goal}
    (step : AdministrativeStep before after)
    (tail : List PeTTaSpec.PrologCore.Goal) :
    AdministrativeStep (before ++ tail) (after ++ tail) := by
  cases step with
  | truth =>
      exact .truth _
  | conjunction =>
      simpa [List.append_assoc] using
        (AdministrativeStep.conjunction _ _)

/-- One compiler-erased source administration step moves through the real
wrapper stack.  The executable takes exactly zero fine steps; the paired
payload and every retained resource fact remain unchanged. -/
theorem ActiveProductRelates.afterAdministrativeStep
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {referenceRest beforeBody afterBody :
      List PeTTaSpec.PrologCore.Goal}
    {callerScope : CutScopeId}
    {current : Substitution} {state : OpenConf}
    (agreement :
      ActiveProductRelates freshFrontier alpha support barrier canonical
        referenceBase opened pending finish branch branchTail altTail
        referenceRest current beforeBody state)
    (step : AdministrativeStep beforeBody afterBody) :
    RawStep opened.session
        (activeSourceProduct callerScope opened finish branch branchTail current
          beforeBody referenceRest)
        [] .none opened.session
        (.running
          (activeSourceProduct callerScope opened finish branch branchTail current
            afterBody referenceRest)) ∧
      DemandDrivenCallStep.StepsN prog gt 0
        (.ready state) (.ready state) ∧
      ActiveProductRelates freshFrontier alpha support barrier canonical
        referenceBase opened pending finish branch branchTail altTail
        referenceRest current afterBody state := by
  have child :=
    step.rawStep opened.scope current opened.session
  have sourceStep :=
    activeSourceProduct_progress
      (callerScope := callerScope) (finish := finish) (branch := branch)
      (branchTail := branchTail) (referenceRest := referenceRest)
      child (by simp [Trace.AnswerFree])
  refine ⟨sourceStep, .zero (.ready state), ?_⟩
  exact
    ⟨agreement.ready.afterAdministrativeStep
        (PLeaTTa.PrologActivatedProductStepBridge.AdministrativeStep.appendRight
          step referenceRest),
      agreement.retainedAlts, agreement.retainedAltsZero,
      agreement.retainedBarriers,
      agreement.barrierTag, agreement.frames⟩

/-- An exact finite administrative prefix remains visible as exactly the same
number of wrapped source transitions and exactly zero executable
transitions.  The source event trace is empty, not quotiented; the finite
administrative rank from `AdministrativeStepsN` rules out infinite stutter. -/
theorem ActiveProductRelates.afterAdministrativeSteps
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {referenceRest beforeBody afterBody :
      List PeTTaSpec.PrologCore.Goal}
    {callerScope : CutScopeId}
    {current : Substitution} {state : OpenConf} {count : Nat}
    (agreement :
      ActiveProductRelates freshFrontier alpha support barrier canonical
        referenceBase opened pending finish branch branchTail altTail
        referenceRest current beforeBody state)
    (steps : AdministrativeStepsN count beforeBody afterBody) :
    PeTTaSpec.PrologCore.GoalSemantics.StepsN count
        (.running opened.session
          (activeSourceProduct callerScope opened finish branch branchTail
            current beforeBody referenceRest))
        []
        (.running opened.session
          (activeSourceProduct callerScope opened finish branch branchTail
            current afterBody referenceRest)) ∧
      DemandDrivenCallStep.StepsN prog gt 0
        (.ready state) (.ready state) ∧
      ActiveProductRelates freshFrontier alpha support barrier canonical
        referenceBase opened pending finish branch branchTail altTail
        referenceRest current afterBody state := by
  induction steps with
  | zero goals =>
      exact ⟨.zero _, .zero _, agreement⟩
  | succ count before middle after head tail inductionHypothesis =>
      rcases agreement.afterAdministrativeStep
          (prog := prog) (gt := gt) (callerScope := callerScope) head with
        ⟨firstRaw, _executableZero, middleAgreement⟩
      have first :
          Transition
            (.running opened.session
              (activeSourceProduct callerScope opened finish branch branchTail
                current before referenceRest))
            []
            (.running opened.session
              (activeSourceProduct callerScope opened finish branch branchTail
                current middle referenceRest)) :=
        .ordinary _ [] opened.session opened.session
          (.running
            (activeSourceProduct callerScope opened finish branch branchTail
              current middle referenceRest))
          firstRaw
      rcases inductionHypothesis middleAgreement with
        ⟨remaining, _remainingExecutableZero, finalAgreement⟩
      refine ⟨?_, .zero _, finalAgreement⟩
      simpa using
        PeTTaSpec.PrologCore.GoalSemantics.StepsN.succ count
          (.running opened.session
            (activeSourceProduct callerScope opened finish branch branchTail
              current before referenceRest))
          (.running opened.session
            (activeSourceProduct callerScope opened finish branch branchTail
              current middle referenceRest))
          (.running opened.session
            (activeSourceProduct callerScope opened finish branch branchTail
              current after referenceRest))
          [] [] first remaining

/-! ## Successful primitive unification -/

/-- One successful primitive unification composes through the real active
product state.

The existing leaf bridge supplies the canonical residual MGU, exact
executable equality spelling, trimmed runtime successor, and successor
payload relation on the flattened `bodyTail ++ callerTail`.  This theorem
adds only the source control propagation and preservation of the retained
alternative bank, barrier cache, cut tag, and frame ownership. -/
theorem ActiveProductRelates.afterUnifySuccess
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {referenceRest bodyRest : List PeTTaSpec.PrologCore.Goal}
    {callerScope : CutScopeId}
    {current result : Substitution} {state : OpenConf}
    {left right : Term}
    (agreement :
      ActiveProductRelates freshFrontier alpha support barrier canonical
        referenceBase opened pending finish branch branchTail altTail
        referenceRest current (.unify left right :: bodyRest) state)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote right))
    (supportIncluded :
      ∀ pair, pair ∈ support → pair ∈ alpha)
    (safe : ReadyUnifyContinuationSafe support state)
    (resolved : UnifyResolution current left right result) :
    ∃ (spelling :
          NormalizedAlphaGoalsAgree.ExecutableUnifySpelling)
        (executableLeft executableRight : Metta.Atom)
        (executableTail : List PLeaTTa.Goal) (runtime : Metta.Subst),
      ∃ sourceExtension installed,
        state.control.cur =
            some (spelling.goal executableLeft executableRight ::
              executableTail, runtime) ∧
        RawStep opened.session
          (activeSourceProduct callerScope opened finish branch branchTail
            current (.unify left right :: bodyRest) referenceRest)
          [] .none opened.session
          (.running
            (activeSourceProduct callerScope opened finish branch branchTail
              result bodyRest referenceRest)) ∧
        DemandDrivenCallStep.Step prog gt (.ready state)
          (.ready (unifySuccessor state executableTail installed)) ∧
        ActiveProductRelates freshFrontier alpha support barrier
          (sourceExtension ++ canonical) referenceBase opened pending finish
          branch branchTail altTail referenceRest result bodyRest
          (unifySuccessor state executableTail installed) := by
  have flattenedReady :
      ReadyTaskRelates freshFrontier alpha support barrier canonical
        referenceBase opened.session current
        (.unify left right :: (bodyRest ++ referenceRest)) state := by
    simpa [List.append_assoc] using agreement.ready
  obtain
    ⟨spelling, executableLeft, executableRight, executableTail, runtime,
      sourceExtension, installed, head, _flatSourceStep, executableStep,
      _persistent, nextReady⟩ :=
    PrologOrdinaryStepBridge.unify_step_correspondence
      (prog := prog) (gt := gt) (scope := opened.scope) flattenedReady
      leftSupported rightSupported supportIncluded safe resolved
  have child :
      RawStep opened.session
        (.task opened.scope (.unify left right :: bodyRest) current)
        [] .none opened.session
        (.running (.task opened.scope bodyRest result)) :=
    .taskUnifySuccess opened.scope left right bodyRest current result
      opened.session resolved
  have sourceStep :=
    activeSourceProduct_progress
      (callerScope := callerScope) (finish := finish) (branch := branch)
      (branchTail := branchTail) (referenceRest := referenceRest)
      child (by simp [Trace.AnswerFree])
  refine
    ⟨spelling, executableLeft, executableRight, executableTail, runtime,
      sourceExtension, installed, head, sourceStep, executableStep, ?_⟩
  refine
    ⟨nextReady, ?_, agreement.retainedAltsZero, ?_,
      agreement.barrierTag, ?_⟩
  · change
      state.toConf.alts =
        altTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts
    exact agreement.retainedAlts
  · change
      state.toConf.barriers =
        PLeaTTa.pushBarrierCache pending.outer.barriers
    exact agreement.retainedBarriers
  · simpa [unifySuccessor] using agreement.frames

/-! ## Clause-local cut correspondence -/

/-- One clause-local cut composes through the actual source control wrappers
and the fine executable machine.

The source transition emits the exact retained-cursor prune observation.  The
executable transition removes the retained branch alternatives and their own
barrier, leaving exactly the caller's alternative stack.  The cache
coherence premise is explicit and load-bearing; the stale-cache witness above
shows that the state equation is false without it. -/
theorem ActiveProductRelates.afterCut
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {referenceRest bodyRest : List PeTTaSpec.PrologCore.Goal}
    {callerScope : CutScopeId}
    {current : Substitution} {state : OpenConf}
    (agreement :
      ActiveProductRelates freshFrontier alpha support barrier canonical
        referenceBase opened pending finish branch branchTail altTail
        referenceRest current (.cut :: bodyRest) state)
    (coherent : PLeaTTa.BarrierCacheCoherent state.toConf) :
    ∃ executableTail runtime,
      state.control.cur =
          some (.cutAt barrier :: executableTail, runtime) ∧
        RawStep opened.session
          (activeSourceProduct callerScope opened finish branch branchTail
            current (.cut :: bodyRest) referenceRest)
          [.pruned (retainedCursorToken opened finish branch branchTail)]
          .none opened.session
          (.running
            (cutSourceProduct callerScope opened current bodyRest
              referenceRest)) ∧
        DemandDrivenCallStep.Step prog gt (.ready state)
          (.ready (cutSuccessor state barrier executableTail runtime)) ∧
        CommittedProductRelates freshFrontier alpha support barrier canonical
          referenceBase opened pending referenceRest current bodyRest
          (cutSuccessor state barrier executableTail runtime) := by
  have flattenedReady :
      ReadyTaskRelates freshFrontier alpha support barrier canonical
        referenceBase opened.session current
        (.cut :: (bodyRest ++ referenceRest)) state := by
    simpa [List.append_assoc] using agreement.ready
  obtain
    ⟨executableTail, runtime, head, _leafSourceStep, executableStep,
      _persistent, nextReady⟩ :=
    PrologOrdinaryStepBridge.cut_step_correspondence
      (prog := prog) (gt := gt) (scope := opened.scope) flattenedReady
  refine
    ⟨executableTail, runtime, head, activeSourceProduct_cut,
      executableStep, nextReady, ?_, ?_, ?_⟩
  · change
      (PLeaTTa.cutToTracked barrier state.toConf.barriers
        state.toConf.alts).1 =
        pending.outer.alts
    exact agreement.cutToTracked_alts_eq_outer coherent
  · have nextCoherent :=
      PLeaTTa.BarrierCacheCoherent.cut state.toConf barrier coherent
    unfold PLeaTTa.BarrierCacheCoherent at nextCoherent ⊢
    simpa [cutSuccessor] using nextCoherent
  · simpa [cutSuccessor] using agreement.frames

end PLeaTTa.PrologActivatedProductStepBridge
