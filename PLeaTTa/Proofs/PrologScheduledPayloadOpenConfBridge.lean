-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologScheduledPayloadOpenConfBridge
Purpose: Consume the exact selected-head payload transform in the real
  post-answer OpenConf alternative bank and enabled barrier cache
Trusted boundary: none
Main exports:
  ScheduledSelectedHeadTransition.fineAltsExact,
  ScheduledSelectedHeadTransition.fineBarrierCountDroppedExact,
  ScheduledSelectedHeadTransition.fineBarrierCacheExact,
  ScheduledSelectedHeadTransition.fineBarrierCachePayloadExact
-/
import PLeaTTa.Proofs.PrologScheduledPayloadPostHeadBridge
import PLeaTTa.Proofs.PrologRootClosedLocalLiveBridge

namespace PLeaTTa.PrologScheduledPayloadOpenConfBridge

open Metta (Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open DemandDrivenStep
open PrologActivationMacro
open PrologFindallAnswerResourceBridge
open PrologHeterogeneousPrefixBridge
open PrologPersistentFreeScheduledPayloadBridge
open PrologProductResourceContextBridge
open PrologRootClosedAnswerBridge
open PrologScheduledAnswerPropagationBridge
open PrologScheduledHistoryBuildBridge
open PrologScheduledPayloadLandingBridge
open PrologScheduledPayloadPathBridge
open PrologScheduledPayloadPostHeadBridge

namespace ScheduledSelectedHeadTransition

/-! The source-selected dependent zipper and the executable eager pull meet
at the exact residual alternative bank.  The real fine successor is always
`privateAnswerTarget`; no compatible OpenConf is accepted as an input. -/

/-- The real answer-and-pull successor installs exactly the freshened
selected clause head certified by the source offset.

This closes a deliberately important identity seam.  The structural pull
selects opaque `goals` and `binding` fields, while `PulledHeadOffsetAgrees`
names the source clause occurrence and its certified fresh copy.  Their two
equations for the same literal alternative head force the executable current
goal below; no compatible OpenConf or independently chosen clause is
accepted. -/
theorem fineCurrentExact
    {before : RepresentativePersistentFreeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session) :
    (privateAnswerTarget before.carrier.index.openConf
        before.carrier.index.runtime).control.cur =
      some
        (PLeaTTa.Goal.eq
              (.expr
                (selection.selected.resource.args ++
                  [selection.selected.resource.res]))
              (.expr
                (transition.copied.params ++ [transition.copied.result])) ::
            transition.copied.body ++ selection.selected.resource.rest,
          selection.selected.resource.binding) := by
  have selectedPull :
      PLeaTTa.pullAux before.carrier.index.openConf.control.alts =
        some (.branch selection.goals selection.binding, selection.rest) := by
    rw [ready.bankExact]
    rw [← ready.result.historyBuild.cells_map_resource]
    exact selection.pullExact
  have selectedFields :=
    PullOutcomeAgrees.fields_of_pull_some
      (privateAnswerTarget_pullOutcome before.carrier.index.openConf
        before.carrier.index.runtime)
      selectedPull
  have banksEqual :
      resolutionAlt selection.selected.resource.argsv
            selection.selected.resource.args selection.selected.resource.res
            selection.selected.resource.rest
            selection.selected.resource.binding
            selection.selected.resource.qterm
            selection.selected.resource.barrier
            selection.selected.resource.counter transition.clause ::
          selection.localTail =
        .br selection.goals selection.binding :: selection.localTail :=
    transition.offset.priorAlts.symm.trans selection.selectedHead
  have headEqual := (List.cons.inj banksEqual).1
  have selectedHead :
      PLeaTTa.Alt.br
          (PLeaTTa.Goal.eq
                (.expr
                  (selection.selected.resource.args ++
                    [selection.selected.resource.res]))
                (.expr
                  (transition.copied.params ++
                    [transition.copied.result])) ::
              transition.copied.body ++ selection.selected.resource.rest)
          selection.selected.resource.binding =
        PLeaTTa.Alt.br selection.goals selection.binding := by
    simpa [resolutionAlt, transition.offset.copiedExact] using headEqual
  have selectedGoalsExact :
      PLeaTTa.Goal.eq
            (.expr
              (selection.selected.resource.args ++
                [selection.selected.resource.res]))
            (.expr
              (transition.copied.params ++ [transition.copied.result])) ::
          transition.copied.body ++ selection.selected.resource.rest =
        selection.goals := by
    injection selectedHead with goalsExact _bindingExact
  have selectedBindingExact :
      selection.selected.resource.binding = selection.binding := by
    injection selectedHead with _goalsExact bindingExact
  rw [selectedFields.1, ← selectedGoalsExact, ← selectedBindingExact]

/-- The real answer-and-pull successor owns exactly the flattened resources
of the transformed dependent payload. -/
theorem fineAltsExact
    {before : RepresentativePersistentFreeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session) :
    (privateAnswerTarget before.carrier.index.openConf
        before.carrier.index.runtime).control.alts =
      flattenOwnedAlts
        ((payloadCells transition.postPayload).map PayloadCell.resource) [] := by
  have selectedPull :
      PLeaTTa.pullAux before.carrier.index.openConf.control.alts =
        some (.branch selection.goals selection.binding, selection.rest) := by
    rw [ready.bankExact]
    rw [← ready.result.historyBuild.cells_map_resource]
    exact selection.pullExact
  have selectedFields :=
    PullOutcomeAgrees.fields_of_pull_some
      (privateAnswerTarget_pullOutcome before.carrier.index.openConf
        before.carrier.index.runtime)
      selectedPull
  calc
    (privateAnswerTarget before.carrier.index.openConf
        before.carrier.index.runtime).control.alts = selection.rest :=
      selectedFields.2
    _ = flattenOwnedAlts selection.postResources [] :=
      selection.rest_eq_flatten_postResources
    _ =
        flattenOwnedAlts
          ((payloadCells transition.postPayload).map PayloadCell.resource) [] := by
      rw [transition.postResourcesExact]

/-- The selected payload prefix is not merely absent from a proof object:
the real pre/post OpenConf alternative banks differ by exactly one barrier
marker for every dropped earlier cell. -/
theorem fineBarrierCountDroppedExact
    {before : RepresentativePersistentFreeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session) :
    PLeaTTa.barrierCount before.carrier.index.openConf.control.alts =
      PLeaTTa.barrierCount
          (privateAnswerTarget before.carrier.index.openConf
            before.carrier.index.runtime).control.alts +
        selection.earlier.length := by
  have preAltsExact :
      before.carrier.index.openConf.control.alts =
        flattenOwnedAlts
          ((payloadCells before.carrier.payloadContext).map
            PayloadCell.resource) [] := by
    calc
      before.carrier.index.openConf.control.alts =
          flattenOwnedAlts ready.result.history.resources [] :=
        ready.bankExact
      _ =
          flattenOwnedAlts
            (ready.result.historyBuild.cells.map
              ScheduledHistoryCell.resource) [] := by
        rw [ready.result.historyBuild.cells_map_resource]
      _ =
          flattenOwnedAlts
            ((payloadCells before.carrier.payloadContext).map
              PayloadCell.resource) [] := by
        rw [ready.payloadAlignment.cellsExact]
        simp [List.map_map, Function.comp_def, PayloadCell.historyCell]
  calc
    PLeaTTa.barrierCount before.carrier.index.openConf.control.alts =
        PLeaTTa.barrierCount
          (flattenOwnedAlts
            ((payloadCells before.carrier.payloadContext).map
              PayloadCell.resource) []) := by
      rw [preAltsExact]
    _ =
        PLeaTTa.barrierCount
            (flattenOwnedAlts selection.postResources []) +
          selection.earlier.length :=
      transition.barrierMarkersDroppedExact
    _ =
        PLeaTTa.barrierCount
            (privateAnswerTarget before.carrier.index.openConf
              before.carrier.index.runtime).control.alts +
          selection.earlier.length := by
      rw [fineAltsExact transition, transition.postResourcesExact]

/-- If the incoming runtime uses the enabled exact barrier cache, the real
answer-and-pull successor keeps it enabled and sets it to the exact barrier
count of the transformed dependent payload.

This is stronger than `BarrierCacheCoherent`: the uncached `none` lane cannot
inhabit the conclusion. -/
theorem fineBarrierCacheExact
    {before : RepresentativePersistentFreeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session)
    (cache : before.carrier.index.openConf.control.barriers =
      some (PLeaTTa.barrierCount
        before.carrier.index.openConf.control.alts)) :
    (privateAnswerTarget before.carrier.index.openConf
        before.carrier.index.runtime).control.barriers =
      some
        (PLeaTTa.barrierCount
          (privateAnswerTarget before.carrier.index.openConf
            before.carrier.index.runtime).control.alts) := by
  have selectedPull :
      PLeaTTa.pullAux before.carrier.index.openConf.control.alts =
        some (.branch selection.goals selection.binding, selection.rest) := by
    rw [ready.bankExact]
    rw [← ready.result.historyBuild.cells_map_resource]
    exact selection.pullExact
  have tracked :
      PLeaTTa.pullAuxTracked
          before.carrier.index.openConf.control.barriers
          before.carrier.index.openConf.control.alts =
        (some (.branch selection.goals selection.binding, selection.rest),
          some (PLeaTTa.barrierCount selection.rest)) := by
    rw [cache]
    simp only [PLeaTTa.pullAuxTracked]
    rw [PLeaTTa.pullAuxCached_exact, selectedPull]
  have exactCache :
      (privateAnswerTarget before.carrier.index.openConf
          before.carrier.index.runtime).control.barriers =
        some (PLeaTTa.barrierCount selection.rest) := by
    have trackedConf :
        PLeaTTa.pullAuxTracked
            before.carrier.index.openConf.toConf.barriers
            before.carrier.index.openConf.toConf.alts =
          (some (.branch selection.goals selection.binding, selection.rest),
            some (PLeaTTa.barrierCount selection.rest)) := by
      simpa [OpenConf.toConf, Control.toConf] using tracked
    simp only [privateAnswerTarget, answerSuccessor, OpenConf.stepOpen,
      OpenConf.ofConfWith, controlOf, PLeaTTa.pull]
    rw [trackedConf]
  rw [exactCache]
  have postAlts := fineAltsExact transition
  rw [postAlts, transition.postResourcesExact,
    ← selection.rest_eq_flatten_postResources]

/-- The enabled cache equation above names the actual OpenConf field; this
corollary rewrites that field to the exact transformed dependent payload. -/
theorem fineBarrierCachePayloadExact
    {before : RepresentativePersistentFreeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session)
    (cache : before.carrier.index.openConf.control.barriers =
      some (PLeaTTa.barrierCount
        before.carrier.index.openConf.control.alts)) :
    (privateAnswerTarget before.carrier.index.openConf
        before.carrier.index.runtime).control.barriers =
      some
        (PLeaTTa.barrierCount
          (flattenOwnedAlts
            ((payloadCells transition.postPayload).map PayloadCell.resource)
            [])) := by
  rw [fineBarrierCacheExact transition cache, fineAltsExact transition]

end ScheduledSelectedHeadTransition

end PLeaTTa.PrologScheduledPayloadOpenConfBridge
