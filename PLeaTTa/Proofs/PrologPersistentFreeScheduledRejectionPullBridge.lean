-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologPersistentFreeScheduledRejectionPullBridge
Purpose: Classify the eager pull after a scheduled retained-head rejection
  by an occurrence-indexed dependent payload route, without retaining a
  historical persistent packet.
Trusted boundary: none
Main exports:
  PayloadLocalSelection,
  PayloadBankPull,
  classifyPayloadBank,
  ScheduledRejectedFinePullOutcome,
  ScheduledSelectedHeadTransition.classifyRejectedFinePull
-/
import PLeaTTa.Proofs.PrologScheduledPayloadRejectionBridge
import PLeaTTa.Proofs.PrologScheduledPayloadSuccessCarrierBridge

namespace PLeaTTa.PrologPersistentFreeScheduledRejectionPullBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologBodyFailureExhaustedResourceTransitionBridge
open PrologBodyFailureOuterResourceCatchupBridge
open PrologBodyFailureResourceTransitionBridge
open PrologControlSegmentSpineBridge
open PrologHeterogeneousPrefixBridge
open PrologProductResourceContextBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
open PrologRootClosedAnswerBridge
open PrologScheduledHistoryBuildBridge
open PrologScheduledPayloadLandingBridge
open PrologScheduledPayloadPathBridge
open PrologScheduledPayloadPostHeadBridge
open PrologScheduledPayloadRejectionBridge
open PrologScheduledPayloadSuccessCarrierBridge
open PrologSourceProductContextBridge

/-!
# Persistent-free rejection-pull classification

The sealed equality-failure step immediately calls `pull`.  The independent
source lane has only consumed the rejected occurrence, so the fine machine is
one selected branch ahead (or already exhausted).  The classifier below is
Type-valued: its live constructor retains a path through the literal dependent
payload zipper.  It never selects a snapshot by resource equality and never
recovers an `OpenedCall` or `PendingCall` creation packet.
-/

/-- A first-live selection over the erasure of one literal dependent payload.

The selected data are computed by `classifyScheduledCellBank`; the dependent
path below reuses the same ordinal in the exact payload value. -/
structure PayloadLocalSelection
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer) : Type where
  erased :
    ScheduledLocalSelection
      ((payloadCells payload).map PayloadCell.historyCell)

namespace PayloadLocalSelection

/-- Generic selected-cell equation for the structural classifier. -/
private theorem ScheduledLocalSelection.position_cell_exact
    {alpha : List (LogicVar × String)}
    {cells : List (ScheduledHistoryCell alpha)}
    (selection : ScheduledLocalSelection cells) :
    cells.get selection.position = selection.selected := by
  simp [ScheduledLocalSelection.position, selection.cellsExact,
    List.get_eq_getElem]

/-- The erased selection's ordinal lifted into the exact dependent payload. -/
def path
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (selection : PayloadLocalSelection payload) : PayloadPath payload :=
  ⟨⟨selection.erased.position.val, by
      simpa using selection.erased.position.isLt⟩⟩

/-- The structural dependent suffix beginning at the selected occurrence. -/
def route
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (selection : PayloadLocalSelection payload) :
    PayloadRoute payload selection.path :=
  selection.path.route

@[simp] theorem path_position
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (selection : PayloadLocalSelection payload) :
    selection.path.position.val = selection.erased.earlier.length := rfl

/-- The selected dependent cell erases to the exact computed local cell. -/
theorem selected_historyCell_exact
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (selection : PayloadLocalSelection payload) :
    selection.path.cell.historyCell = selection.erased.selected := by
  have exact :=
    ScheduledLocalSelection.position_cell_exact selection.erased
  simpa [path, PayloadPath.cell, List.get_eq_getElem,
    List.getElem_map] using exact

/-- The exact dependent prefix erases to the classifier's empty prefix. -/
theorem earlier_exact
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (selection : PayloadLocalSelection payload) :
    selection.erased.earlier =
      ((payloadCells payload).take selection.path.position.val).map
        PayloadCell.historyCell := by
  have taken :=
    congrArg (List.take selection.erased.earlier.length)
      selection.erased.cellsExact
  simpa [path, ScheduledLocalSelection.position] using taken.symm

/-- The exact dependent suffix after the selected occurrence erases to the
classifier's literal suffix. -/
theorem suffix_exact
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (selection : PayloadLocalSelection payload) :
    selection.erased.suffix =
      ((payloadCells payload).drop (selection.path.position.val + 1)).map
        PayloadCell.historyCell := by
  have dropped :=
    congrArg (List.drop (selection.erased.earlier.length + 1))
      selection.erased.cellsExact
  simpa [path, ScheduledLocalSelection.position] using dropped.symm

/-- Literal split of the dependent cells at the computed occurrence. -/
theorem cells_exact
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (selection : PayloadLocalSelection payload) :
    payloadCells payload =
      (payloadCells payload).take selection.path.position.val ++
        selection.path.cell ::
          (payloadCells payload).drop (selection.path.position.val + 1) := by
  calc
    payloadCells payload =
        (payloadCells payload).take selection.path.position.val ++
          (payloadCells payload).drop selection.path.position.val :=
      (List.take_append_drop selection.path.position.val
        (payloadCells payload)).symm
    _ =
        (payloadCells payload).take selection.path.position.val ++
          selection.path.cell ::
            (payloadCells payload).drop
              (selection.path.position.val + 1) := by
      congr 1
      exact
        (List.cons_get_drop_succ
          (l := payloadCells payload) (n := selection.path.position)).symm

/-- Every dependent cell before the selected path has an empty local bank. -/
theorem earlier_empty
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (selection : PayloadLocalSelection payload) :
    ∀ cell ∈ (payloadCells payload).take selection.path.position.val,
      cell.resource.alts = [] := by
  intro cell member
  have erasedMember : cell.historyCell ∈ selection.erased.earlier := by
    rw [selection.earlier_exact]
    exact List.mem_map.mpr ⟨cell, member, rfl⟩
  simpa [PayloadCell.historyCell] using
    selection.erased.earlierEmpty cell.historyCell erasedMember

/-- The selected dependent resource owns the exact computed branch head. -/
theorem selected_head
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (selection : PayloadLocalSelection payload) :
    selection.path.cell.resource.alts =
      .br selection.erased.goals selection.erased.binding ::
        selection.erased.localTail := by
  have selectedResource := congrArg ScheduledHistoryCell.resource
    selection.selected_historyCell_exact
  have selectedResourceExact :
      selection.path.cell.resource = selection.erased.selected.resource := by
    simpa [PayloadCell.historyCell] using selectedResource
  rw [selectedResourceExact]
  exact selection.erased.selectedHead

/-- Exact tracked pull at the same dependent occurrence, including cache
installation in both the enabled and disabled cache modes. -/
theorem pullAuxTracked_exact
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer}
    (selection : PayloadLocalSelection payload)
    {frames : List Frame} {installed : Option Nat}
    (origins :
      ControlOriginCellsRelate [] frames installed (payloadCells payload)) :
    PLeaTTa.pullAuxTracked installed
        (flattenOwnedAlts
          ((payloadCells payload).map PayloadCell.resource) []) =
      (some
          (.branch selection.erased.goals selection.erased.binding,
            selection.erased.localTail ++ PLeaTTa.Alt.barrier ::
              flattenOwnedAlts
                (((payloadCells payload).drop
                    (selection.path.position.val + 1)).map
                  PayloadCell.resource) []),
        PLeaTTa.pushBarrierCache
          selection.path.cell.snapshot.controlOrigin.outerBarriers) := by
  exact
    ControlOriginCellsRelate.pullAuxTracked_split origins
      selection.cells_exact selection.earlier_empty selection.selected_head

end PayloadLocalSelection

/-- Total Type-valued pull classification of one exact dependent payload. -/
inductive PayloadBankPull
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer) : Type where
  | localLive (selection : PayloadLocalSelection payload) :
      PayloadBankPull payload
  | exhausted
      (allEmpty : ∀ cell ∈ payloadCells payload, cell.resource.alts = [])
      (pullNone :
        PLeaTTa.pullAux
            (flattenOwnedAlts
              ((payloadCells payload).map PayloadCell.resource) []) = none) :
      PayloadBankPull payload

/-- A branch-only scheduled cell bank whose real pull finds nothing has no
hidden nonempty resource. -/
private theorem scheduled_cells_all_empty_of_pull_none
    {alpha : List (LogicVar × String)}
    (cells : List (ScheduledHistoryCell alpha))
    (pullNone :
      PLeaTTa.pullAux
          (flattenOwnedAlts
            (cells.map ScheduledHistoryCell.resource) []) = none) :
    ∀ cell ∈ cells, cell.resource.alts = [] := by
  induction cells with
  | nil => simp
  | cons cell cells inductionHypothesis =>
      cases altsExact : cell.resource.alts with
      | nil =>
          intro item member
          rcases List.mem_cons.mp member with rfl | member
          · exact altsExact
          · apply inductionHypothesis
            · simpa [flattenOwnedAlts, altsExact, PLeaTTa.pullAux] using
                pullNone
            · exact member
      | cons alt tail =>
          rcases cell.ownership.alts_all_branches alt
              (by rw [altsExact]; simp) with ⟨goals, binding, branchExact⟩
          subst alt
          simp [altsExact, PLeaTTa.pullAux] at pullNone

/-- Compute the first live occurrence, or certify total local exhaustion,
directly from the literal payload cell spine. -/
def classifyPayloadBank
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer) :
    PayloadBankPull payload := by
  cases bank : classifyScheduledCellBank
      ((payloadCells payload).map PayloadCell.historyCell) with
  | localLive selection =>
      exact .localLive ⟨selection⟩
  | exhausted pullNone =>
      have allErased :=
        scheduled_cells_all_empty_of_pull_none
          ((payloadCells payload).map PayloadCell.historyCell) pullNone
      exact .exhausted
        (by
          intro cell member
          have erasedMember :
              cell.historyCell ∈
                (payloadCells payload).map PayloadCell.historyCell :=
            List.mem_map.mpr ⟨cell, member, rfl⟩
          simpa [PayloadCell.historyCell] using
            allErased cell.historyCell erasedMember)
        (by
          simpa [List.map_map, Function.comp_def, PayloadCell.historyCell]
            using pullNone)

/-! ## Instantiation at the real scheduled rejection successor -/

namespace ScheduledSelectedHeadTransition

/-- The transformed post-head payload carries the exact current fine control
origins.  No call-opening packet is reconstructed: the head origin comes from
the consumed occurrence and the tail origins are literal suffix facts. -/
theorem postPayload_controlOriginCells
    {before :
      PrologPersistentFreeScheduledPayloadBridge.RepresentativePersistentFreeScheduledPayloadState}
    {ready : PrologRootClosedAnswerBridge.RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session) :
    ControlOriginCellsRelate [] (selectedFineState before).frames
      (selectedFineState before).control.barriers
      (payloadCells transition.postPayload) := by
  have tailOrigins :=
    ControlOriginCellsRelate.ofPayload
      (SourceControlResourcePayloadContextAgrees.tail transition.postPayload)
      (PLeaTTa.PrologScheduledPayloadSuccessCarrierBridge.ScheduledSelectedHeadTransition.postTailControlOrigins
        transition)
  have selectedFacts :=
    PLeaTTa.PrologScheduledPayloadSuccessCarrierBridge.ScheduledSelectedHeadTransition.selectedControlOriginFacts
      transition
  rw [transition.postHeadCellExact]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show
        (PayloadCell.afterSelectedHead transition.selectedPayloadCell
          (afterPulledHead selection.selected.resource selection.localTail)
          (transition.finish.advance transition.branch transition.branchTail)
          ⟨transition.callStart,
            (transition.startPosition + transition.frontier.rejectedCount) + 1,
            transition.tailOwnershipExact⟩
          transition.consumedSnapshot).snapshot.controlOrigin =
            transition.selectedPayloadCell.snapshot.controlOrigin by
          exact transition.controlOriginExact]
    simpa [payloadCells_map_resource] using selectedFacts.1
  · simpa [PayloadCell.afterSelectedHead, transition.controlOriginExact]
      using selectedFacts.2
  · simpa [PayloadCell.afterSelectedHead, transition.controlOriginExact]
      using
        (PLeaTTa.PrologScheduledPayloadSuccessCarrierBridge.ScheduledSelectedHeadTransition.selectedFineBarriersExact
          transition)
  · simpa [PayloadCell.afterSelectedHead, transition.controlOriginExact]
      using tailOrigins

end ScheduledSelectedHeadTransition

/-- Exact fine-machine outcome of the eager pull performed by the rejected
equality step.  The live case carries the dependent occurrence route; the
terminal case accounts for every payload cell. -/
inductive ScheduledRejectedFinePullOutcome
    {before :
      PrologPersistentFreeScheduledPayloadBridge.RepresentativePersistentFreeScheduledPayloadState}
    {ready : PrologRootClosedAnswerBridge.RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session) : Type where
  | localLive
      (next : PayloadLocalSelection transition.postPayload)
      (currentExact :
        (rejectedFineState before).control.cur =
          some (next.erased.goals, next.erased.binding))
      (altsExact :
        (rejectedFineState before).control.alts =
          next.erased.localTail ++ PLeaTTa.Alt.barrier ::
            flattenOwnedAlts
              (((payloadCells transition.postPayload).drop
                  (next.path.position.val + 1)).map
                PayloadCell.resource) [])
      (barriersExact :
        (rejectedFineState before).control.barriers =
          PLeaTTa.pushBarrierCache
            next.path.cell.snapshot.controlOrigin.outerBarriers) :
      ScheduledRejectedFinePullOutcome transition
  | exhausted
      (allEmpty :
        ∀ cell ∈ payloadCells transition.postPayload,
          cell.resource.alts = [])
      (currentExact : (rejectedFineState before).control.cur = none)
      (altsExact : (rejectedFineState before).control.alts = [])
      (terminal : PLeaTTa.Terminal (rejectedFineState before).toConf) :
      ScheduledRejectedFinePullOutcome transition

namespace ScheduledSelectedHeadTransition

/-- Classify the fine successor determined by one selected-head transition.

This is the promised immediate use of the generic classifier: the result is
indexed by `transition.postPayload` and names `rejectedFineState` literally.
No historical session or control packet occurs in the result type.  This is a
fine-lane theorem; relating the source frontier after the rejected occurrence
to a later selected payload occurrence is a separate catch-up obligation. -/
def classifyRejectedFinePull
    {before :
      PrologPersistentFreeScheduledPayloadBridge.RepresentativePersistentFreeScheduledPayloadState}
    {ready : PrologRootClosedAnswerBridge.RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    {transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session} :
    ScheduledRejectedFinePullOutcome transition := by
  have preAlts :
      (selectedFineState before).control.alts =
        flattenOwnedAlts
          ((payloadCells transition.postPayload).map PayloadCell.resource) [] :=
    PLeaTTa.PrologScheduledPayloadOpenConfBridge.ScheduledSelectedHeadTransition.fineAltsExact
      transition
  have origins :=
    PLeaTTa.PrologPersistentFreeScheduledRejectionPullBridge.ScheduledSelectedHeadTransition.postPayload_controlOriginCells
      transition
  cases classified : classifyPayloadBank transition.postPayload with
  | localLive next =>
      have tracked := next.pullAuxTracked_exact origins
      have actualTracked :
          PLeaTTa.pullAuxTracked
              (selectedFineState before).toConf.barriers
              (selectedFineState before).toConf.alts =
            (some
                (.branch next.erased.goals next.erased.binding,
                  next.erased.localTail ++ PLeaTTa.Alt.barrier ::
                    flattenOwnedAlts
                      (((payloadCells transition.postPayload).drop
                          (next.path.position.val + 1)).map
                        PayloadCell.resource) []),
              PLeaTTa.pushBarrierCache
                next.path.cell.snapshot.controlOrigin.outerBarriers) := by
        simpa [OpenConf.toConf, Control.toConf, preAlts] using tracked
      refine .localLive next ?_ ?_ ?_
      all_goals
        unfold rejectedFineState
          PrologOrdinaryStepBridge.unifyFailureSuccessor
        simp only [OpenConf.stepOpen, OpenConf.ofConfWith, controlOf,
          PLeaTTa.pull]
        rw [actualTracked]
  | exhausted allEmpty pullNone =>
      have actualPullNone :
          PLeaTTa.pullAux (selectedFineState before).toConf.alts = none := by
        simpa [OpenConf.toConf, Control.toConf, preAlts] using pullNone
      have exactState :
          (rejectedFineState before).toConf =
            { (selectedFineState before).toConf with
              cur := none
              alts := []
              barriers :=
                (PLeaTTa.pullAuxTracked
                  (selectedFineState before).toConf.barriers
                  (selectedFineState before).toConf.alts).2 } := by
        unfold rejectedFineState
          PrologOrdinaryStepBridge.unifyFailureSuccessor
        rw [OpenConf.stepOpen_toConf]
        unfold PLeaTTa.pull
        generalize trackedEq :
          PLeaTTa.pullAuxTracked
              (selectedFineState before).toConf.barriers
              (selectedFineState before).toConf.alts = tracked
        rcases tracked with ⟨outcome, cache⟩
        have outcomeExact :=
          PLeaTTa.pullAuxTracked_fst
            (selectedFineState before).toConf.barriers
            (selectedFineState before).toConf.alts
        rw [trackedEq, actualPullNone] at outcomeExact
        change outcome = none at outcomeExact
        subst outcome
        rfl
      refine .exhausted allEmpty ?_ ?_ ?_
      · simpa [OpenConf.toConf, Control.toConf] using
          congrArg PLeaTTa.Conf.cur exactState
      · simpa [OpenConf.toConf, Control.toConf] using
          congrArg PLeaTTa.Conf.alts exactState
      · rw [exactState]
        exact ⟨rfl, rfl⟩

end ScheduledSelectedHeadTransition

end PLeaTTa.PrologPersistentFreeScheduledRejectionPullBridge
