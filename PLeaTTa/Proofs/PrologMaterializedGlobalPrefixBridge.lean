-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologMaterializedGlobalPrefixBridge
Purpose: Carry whole-body equality materialization through the exact global
  transition prefix without adding a second phase-state representation.
Trusted boundary: none
Main exports:
  MaterializedPhaseInvariant,
  MaterializedGlobalCertifiedPrefix,
  MaterializedGlobalCertifiedPrefix.activeCut,
  MaterializedGlobalCertifiedPrefix.committedAdministrative,
  MaterializedGlobalCertifiedPrefix.committedBodyAnswer,
  MaterializedGlobalCertifiedPrefix.exists_committedUnify
-/
import PLeaTTa.Proofs.PrologScheduledSuccessPrefixBridge

namespace PLeaTTa.PrologMaterializedGlobalPrefixBridge

open Metta (Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open DemandDrivenStep
open PrologActivatedProductStepBridge
open PrologFailureRebasePrefixBridge
open PrologHeterogeneousPrefixBridge
open PrologOrdinaryStepBridge
open PrologPersistentFreeActivePayloadBridge
open PrologPersistentFreeCommittedPayloadBridge
open PrologPersistentFreeCommittedScheduledPayloadBridge
open PrologPersistentFreeCommittedUnifyTransitionBridge
open PrologScheduledSuccessPrefixBridge

/-!
`ResolverPhaseState` deliberately contains only live source/executable state.
It must not grow a second active/committed constructor merely to remember a
proof about the current residual body.  The predicate below recovers that
proof obligation from the literal state index.  Scheduled,
committed-scheduled, and post-failure states have no executing clause body, so
the obligation is vacuous there; every transition which enters an active body
must establish it anew.
-/

/-- Whole-body equality materialization at precisely the phases where a local
clause body is executing. -/
def MaterializedPhaseInvariant : ResolverPhaseState → Prop
  | .ordinary (.active state) =>
      MaterializedUnifyGoalsAgreeWith state.carrier.index.alpha
        state.representative state.carrier.index.referenceBase
        state.carrier.index.runtime state.carrier.index.bodyBarrier
        state.carrier.index.bodyReferences state.carrier.index.bodyExecutables
  | .ordinary (.committed state) =>
      MaterializedUnifyGoalsAgreeWith state.carrier.index.alpha
        state.representative state.carrier.index.referenceBase
        state.carrier.index.runtime state.carrier.index.bodyBarrier
        state.carrier.index.bodyReferences state.carrier.index.bodyExecutables
  | .ordinary (.scheduled _) => True
  | .ordinary (.committedScheduled _) => True
  | .postFailure _ => True

/-- A proof-relevant global prefix carrying materialization at every literal
phase state.  Its transition edge is exactly `GlobalCertifiedTransition`;
erasing the invariant therefore recovers the established global zipper
without changing any source/fine endpoint or schedule kind. -/
inductive MaterializedGlobalCertifiedPrefix
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable) :
    List GlobalTransitionKind → ResolverPhaseState → ResolverPhaseState →
      Type where
  | nil (state : ResolverPhaseState)
      (materialized : MaterializedPhaseInvariant state) :
      MaterializedGlobalCertifiedPrefix prog gt [] state state
  | cons
      {kind : GlobalTransitionKind}
      {kinds : List GlobalTransitionKind}
      {before middle after : ResolverPhaseState}
      (materialized : MaterializedPhaseInvariant before)
      (head : GlobalCertifiedTransition prog gt kind before middle)
      (tail : MaterializedGlobalCertifiedPrefix prog gt kinds middle after) :
      MaterializedGlobalCertifiedPrefix prog gt (kind :: kinds) before after

namespace MaterializedGlobalCertifiedPrefix

/-- Forget only the invariant proofs; no transition or midpoint is changed. -/
def erase
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List GlobalTransitionKind}
    {before after : ResolverPhaseState} :
    MaterializedGlobalCertifiedPrefix prog gt kinds before after →
      GlobalCertifiedPrefix prog gt kinds before after
  | .nil state _ => .nil state
  | .cons _ head tail => .cons head tail.erase

/-- Materialization at the literal first phase. -/
theorem startMaterialized
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List GlobalTransitionKind}
    {before after : ResolverPhaseState}
    (run : MaterializedGlobalCertifiedPrefix prog gt kinds before after) :
    MaterializedPhaseInvariant before := by
  cases run with
  | nil _ materialized => exact materialized
  | cons materialized _ _ => exact materialized

/-- Materialization at the literal final phase. -/
theorem endMaterialized
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List GlobalTransitionKind}
    {before after : ResolverPhaseState}
    (run : MaterializedGlobalCertifiedPrefix prog gt kinds before after) :
    MaterializedPhaseInvariant after := by
  induction run with
  | nil _ materialized => exact materialized
  | cons _ _ _ ih => exact ih

/-- Concatenation shares the same literal dependent midpoint; the right run's
start proof and the left run's end proof therefore speak about one state. -/
def append
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {leftKinds rightKinds : List GlobalTransitionKind}
    {before middle after : ResolverPhaseState}
    (left : MaterializedGlobalCertifiedPrefix prog gt leftKinds before middle)
    (right : MaterializedGlobalCertifiedPrefix prog gt rightKinds middle after) :
    MaterializedGlobalCertifiedPrefix prog gt (leftKinds ++ rightKinds)
      before after :=
  match left with
  | .nil _ _ => right
  | .cons materialized head tail =>
      .cons materialized head (append tail right)

/-- One certified edge whose two literal endpoints both carry the invariant. -/
def single
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kind : GlobalTransitionKind}
    {before after : ResolverPhaseState}
    (beforeMaterialized : MaterializedPhaseInvariant before)
    (step : GlobalCertifiedTransition prog gt kind before after)
    (afterMaterialized : MaterializedPhaseInvariant after) :
    MaterializedGlobalCertifiedPrefix prog gt [kind] before after :=
  .cons beforeMaterialized step (.nil after afterMaterialized)

theorem sourceSteps
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List GlobalTransitionKind}
    {before after : ResolverPhaseState}
    (run : MaterializedGlobalCertifiedPrefix prog gt kinds before after) :
    StepsN (GlobalTransitionSchedule.sourceCost kinds) before.sourceState
      (GlobalTransitionSchedule.sourceEvents kinds) after.sourceState :=
  run.erase.sourceSteps

theorem fineSteps
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List GlobalTransitionKind}
    {before after : ResolverPhaseState}
    (run : MaterializedGlobalCertifiedPrefix prog gt kinds before after) :
    DemandDrivenCallStep.StepsN prog gt
      (GlobalTransitionSchedule.fineCost kinds) before.fineState
      after.fineState :=
  run.erase.fineSteps

/-- A packet-free local cut preserves the residual whole-body certificate. -/
def activeCut
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (before : MaterializedRepresentativePersistentFreeActivePayloadState)
    (bodyRest : List PeTTaSpec.PrologCore.Goal)
    (bodyExecutableTail : List PLeaTTa.Goal)
    (referenceHead :
      before.carrier.carrier.index.bodyReferences = .cut :: bodyRest)
    (executableHead :
      before.carrier.carrier.index.bodyExecutables =
        .cutAt before.carrier.carrier.index.bodyBarrier :: bodyExecutableTail)
    (coherent :
      PLeaTTa.BarrierCacheCoherent
        before.carrier.carrier.index.openConf.toConf) :
    MaterializedGlobalCertifiedPrefix prog gt
      [ .resolver
          (.forward
            (.cut
              (retainedCursorTokenAt
                before.carrier.carrier.index.predicateScope
                before.carrier.carrier.index.finish
                before.carrier.carrier.index.branch
                before.carrier.carrier.index.branchTail))) ]
      (.ordinary (.active before.carrier))
      (.ordinary
        (.committed
          (RepresentativePersistentFreeActivePayloadState.afterCutMaterialized
            prog gt before bodyRest bodyExecutableTail referenceHead
            executableHead coherent).carrier)) :=
  let after :=
    RepresentativePersistentFreeActivePayloadState.afterCutMaterialized
      prog gt before bodyRest bodyExecutableTail referenceHead executableHead
      coherent
  single before.materializedUnifyGoals
    (.resolver
      (.forward
        (.cut before.carrier bodyRest bodyExecutableTail referenceHead
          executableHead coherent)))
    after.materializedUnifyGoals

/-- Compiler-erased source administration projects the same materialization
certificate to the exact residual body. -/
def committedAdministrative
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (before : MaterializedRepresentativePersistentFreeCommittedPayloadState)
    {count : Nat} {afterBody : List PeTTaSpec.PrologCore.Goal}
    (positive : 0 < count)
    (steps :
      AdministrativeStepsN count
        before.carrier.carrier.index.bodyReferences afterBody) :
    MaterializedGlobalCertifiedPrefix prog gt
      [.committedAdministrative count]
      (.ordinary (.committed before.carrier))
      (.ordinary (.committed (before.afterAdministrative steps).carrier)) :=
  single before.materializedUnifyGoals
    (.committedAdministrative before.carrier positive steps)
    (before.afterAdministrative steps).materializedUnifyGoals

/-- A successful post-cut body exits the materialized executing phases.  The
source schedules its caller in one private step while the fine machine is
already at the same continuation. -/
def committedBodyAnswer
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (before : MaterializedRepresentativePersistentFreeCommittedPayloadState)
    (referenceEmpty : before.carrier.carrier.index.bodyReferences = [])
    (executableEmpty : before.carrier.carrier.index.bodyExecutables = []) :
    MaterializedGlobalCertifiedPrefix prog gt [.committedBodyAnswer]
      (.ordinary (.committed before.carrier))
      (.ordinary
        (.committedScheduled
          (RepresentativePersistentFreeCommittedPayloadState.afterBodyAnswer
            prog gt before.carrier referenceEmpty executableEmpty))) :=
  single before.materializedUnifyGoals
    (.committedBodyAnswer before.carrier referenceEmpty executableEmpty)
    trivial

/-- One selected primitive equality preserves whole-body materialization at
the literal successor.  The producer remains existential because its MGU and
installed runtime are computed data; all elimination stays inside `Prop`. -/
theorem exists_committedUnify
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (before : MaterializedRepresentativePersistentFreeCommittedPayloadState)
    {left right : Term} {result : Substitution}
    {bodyRest : List PeTTaSpec.PrologCore.Goal}
    (referenceHead :
      before.carrier.carrier.index.bodyReferences =
        .unify left right :: bodyRest)
    (continuationLive :
      ReadyUnifyContinuationLive before.carrier.carrier.index.support
        before.carrier.carrier.index.openConf)
    (resolved :
      UnifyResolution before.carrier.carrier.index.current left right result) :
    ∃ bodyExecutableTail : List PLeaTTa.Goal,
      ∃ sourceExtension executableExtension : TreeSubstitution,
      ∃ generated installed : Subst,
      ∃ after : MaterializedRepresentativePersistentFreeCommittedPayloadState,
        ∃ facts :
          RepresentativePersistentFreeCommittedUnifySuccessorFacts prog gt
            before.carrier after.carrier left right result bodyRest
            bodyExecutableTail sourceExtension executableExtension generated
            installed,
          Nonempty
            (MaterializedGlobalCertifiedPrefix prog gt
              [ .committedUnify (CommittedUnifyTransitionLabel.of facts) ]
              (.ordinary (.committed before.carrier))
              (.ordinary (.committed after.carrier))) := by
  obtain
      ⟨bodyExecutableTail, sourceExtension, executableExtension, generated,
        installed, after, facts⟩ :=
    PLeaTTa.PrologPersistentFreeCommittedUnifyTransitionBridge.MaterializedRepresentativePersistentFreeCommittedPayloadState.exists_afterUnifySuccess
      before referenceHead continuationLive resolved
  exact
    ⟨bodyExecutableTail, sourceExtension, executableExtension, generated,
      installed, after, facts,
      ⟨single before.materializedUnifyGoals (.committedUnify facts)
        after.materializedUnifyGoals⟩⟩

end MaterializedGlobalCertifiedPrefix

end PLeaTTa.PrologMaterializedGlobalPrefixBridge
