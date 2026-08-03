-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologScheduledPayloadSuccessCarrierBridge
Purpose: Package successful post-answer retained-head activation in the
  persistent-free active carrier.
Trusted boundary: none
Main exports:
  ActivationOriginCellsRelate,
  ControlOriginCellsRelate,
  ScheduledSelectedHeadTransition.toPersistentFreeActivePayload
-/
import PLeaTTa.Proofs.PrologScheduledPayloadSuccessBridge
import PLeaTTa.Proofs.PrologPersistentFreeActivePayloadBridge

namespace PLeaTTa.PrologScheduledPayloadSuccessCarrierBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologAlphaFreshFrontierBridge
open PrologBodyFailureResourceTransitionBridge
open PrologControlSegmentSpineBridge
open PrologCurrentSessionPayloadBridge
open PrologHeterogeneousPrefixBridge
open PrologMguComposition
open PrologOrdinaryStepBridge
open PrologPersistentFreeActivePayloadBridge
open PrologProductResourceContextBridge
open PrologProductResourceTransitionBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
open PrologRootClosedAnswerBridge
open PrologScheduledAnswerPropagationBridge
open PrologScheduledPayloadOpenConfBridge
open PrologScheduledPayloadLandingBridge
open PrologScheduledPayloadPathBridge
open PrologScheduledPayloadPostHeadBridge
open PrologScheduledPayloadRejectionBridge
open PrologScheduledPayloadResumeBridge
open PrologScheduledPayloadSuccessBridge
open PrologSourceProductContextBridge
open PrologStateBridge

/-- A private-answer step selecting an ordinary branch records exactly the
cache returned by the real tracked pull.  Catch and softcut resumptions may
install protected alternatives and are intentionally outside this lemma. -/
theorem privateAnswerTarget_branch_barriersExact
    (state : OpenConf) (binding : Subst)
    {goals : List PLeaTTa.Goal} {selectedBinding : Subst}
    {rest : List PLeaTTa.Alt}
    (pulled :
      PLeaTTa.pullAux state.control.alts =
        some (.branch goals selectedBinding, rest)) :
    (privateAnswerTarget state binding).control.barriers =
      (PLeaTTa.pullAuxTracked state.control.barriers
        state.control.alts).2 := by
  simp [privateAnswerTarget, answerSuccessor, OpenConf.stepOpen,
    OpenConf.ofConfWith, controlOf, OpenConf.toConf, Control.toConf,
    PLeaTTa.pull, pulled]

/-! ## Cell-spine characterizations of historical provenance -/

/-- Activation chronology stated over the ordinary occurrence-cell spine.

The generation remains indexed by each cell's frozen cursor.  This spelling
is used only to transport an exact structural suffix; the authoritative
carrier remains the dependent payload zipper. -/
def ActivationOriginCellsRelate
    {alpha support : List (LogicVar × String)}
    (session : Session) :
    List (PayloadCell alpha support) → Prop
  | [] => True
  | cell :: cells =>
      cell.snapshot.activationOrigin.Extends session ∧
        cell.snapshot.activationOrigin.nextCutScope =
          cell.currentScope + 1 ∧
        ActivationOriginCellsRelate
          (alpha := alpha) (support := support) session cells

namespace ActivationOriginCellsRelate

/-- Recursive dependent activation chronology implies the exact ordinary
cell-fold characterization. -/
theorem ofPayload
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {session : Session}
    (payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer)
    (origins : LocalActivationOriginSpineRelates session payload) :
    ActivationOriginCellsRelate session (payloadCells payload) := by
  induction payload with
  | nil => trivial
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      exact ⟨origins.1, origins.2.1, inductionHypothesis origins.2.2⟩

/-- The ordinary occurrence fold reconstructs recursive activation chronology
for the literal dependent payload; no cell or origin is selected by value. -/
theorem toPayload
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {session : Session}
    (payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer)
    (origins : ActivationOriginCellsRelate session (payloadCells payload)) :
    LocalActivationOriginSpineRelates session payload := by
  induction payload with
  | nil currentBarrier scope =>
      exact
        LocalActivationOriginSpineRelates.nil session currentBarrier scope
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      exact ⟨origins.1, origins.2.1, inductionHypothesis origins.2.2⟩

/-- Dropping an exact ordinal prefix drops the same chronology prefix. -/
theorem drop
    {alpha support : List (LogicVar × String)}
    {session : Session} {cells : List (PayloadCell alpha support)}
    (origins : ActivationOriginCellsRelate session cells) (count : Nat) :
    ActivationOriginCellsRelate session (cells.drop count) := by
  induction count generalizing cells with
  | zero => simpa using origins
  | succ count inductionHypothesis =>
      cases cells with
      | nil => trivial
      | cons cell cells =>
          exact inductionHypothesis origins.2.2

end ActivationOriginCellsRelate

/-! ## Allocation chronology over the same ordinary occurrence spine -/

/-- Every cursor/resource endpoint in an ordinary payload-cell suffix lies
below the supplied source and executable allocation floors. -/
def PayloadCellEndpointsBelow
    {alpha support : List (LogicVar × String)}
    (referenceFloor executableFloor : Nat) :
    List (PayloadCell alpha support) → Prop
  | [] => True
  | cell :: cells =>
      cell.cursor.reservedUntil ≤ referenceFloor ∧
        cell.resource.finalCounter ≤ executableFloor ∧
        PayloadCellEndpointsBelow
          (alpha := alpha) (support := support)
          referenceFloor executableFloor cells

namespace PayloadCellEndpointsBelow

/-- Dependent endpoint domination erases to the exact ordinary cell spine. -/
theorem ofPayload
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {referenceFloor executableFloor : Nat}
    (payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer)
    (below : endpointsBelow payload referenceFloor executableFloor) :
    PayloadCellEndpointsBelow referenceFloor executableFloor
      (payloadCells payload) := by
  induction payload with
  | nil => trivial
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      exact ⟨below.1, below.2.1, inductionHypothesis below.2.2⟩

/-- The ordinary cell fold reconstructs dependent endpoint domination for
the literal payload. -/
theorem toPayload
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {referenceFloor executableFloor : Nat}
    (payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer)
    (below :
      PayloadCellEndpointsBelow referenceFloor executableFloor
        (payloadCells payload)) :
    endpointsBelow payload referenceFloor executableFloor := by
  induction payload with
  | nil => trivial
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      exact ⟨below.1, below.2.1, inductionHypothesis below.2.2⟩

/-- Raising either floor preserves domination of the complete cell suffix. -/
theorem mono
    {alpha support : List (LogicVar × String)}
    {referenceBefore executableBefore referenceAfter executableAfter : Nat}
    {cells : List (PayloadCell alpha support)}
    (below :
      PayloadCellEndpointsBelow referenceBefore executableBefore cells)
    (referenceMono : referenceBefore ≤ referenceAfter)
    (executableMono : executableBefore ≤ executableAfter) :
    PayloadCellEndpointsBelow referenceAfter executableAfter cells := by
  induction cells with
  | nil => trivial
  | cons cell cells inductionHypothesis =>
      exact
        ⟨Nat.le_trans below.1 referenceMono,
          Nat.le_trans below.2.1 executableMono,
          inductionHypothesis below.2.2⟩

/-- Dropping an ordinal prefix preserves all remaining endpoint bounds. -/
theorem drop
    {alpha support : List (LogicVar × String)}
    {referenceFloor executableFloor : Nat}
    {cells : List (PayloadCell alpha support)}
    (below : PayloadCellEndpointsBelow referenceFloor executableFloor cells)
    (count : Nat) :
    PayloadCellEndpointsBelow referenceFloor executableFloor
      (cells.drop count) := by
  induction count generalizing cells with
  | zero => simpa using below
  | succ count inductionHypothesis =>
      cases cells with
      | nil => trivial
      | cons cell cells => exact inductionHypothesis below.2.2

end PayloadCellEndpointsBelow

/-- Recursive historical allocation order over ordinary payload cells.

For every occurrence, its complete older suffix lies below that occurrence's
source reservation start and executable allocation seed. -/
def ActivationOrderedCellsRelate
    {alpha support : List (LogicVar × String)} :
    List (PayloadCell alpha support) → Prop
  | [] => True
  | cell :: cells =>
      PayloadCellEndpointsBelow cell.cursor.reservationStart
          cell.resource.counter cells ∧
        ActivationOrderedCellsRelate
          (alpha := alpha) (support := support) cells

namespace ActivationOrderedCellsRelate

/-- Recursive dependent allocation chronology erases exactly to the cell
spine. -/
theorem ofPayload
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer)
    (ordered : ActivationOrdered payload) :
    ActivationOrderedCellsRelate (payloadCells payload) := by
  induction payload with
  | nil => trivial
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      exact
        ⟨PayloadCellEndpointsBelow.ofPayload outerAgrees ordered.1,
          inductionHypothesis ordered.2⟩

/-- The ordinary cell chronology reconstructs `ActivationOrdered` for the
literal dependent payload. -/
theorem toPayload
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer)
    (ordered : ActivationOrderedCellsRelate (payloadCells payload)) :
    ActivationOrdered payload := by
  induction payload with
  | nil => trivial
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      exact
        ⟨PayloadCellEndpointsBelow.toPayload outerAgrees ordered.1,
          inductionHypothesis ordered.2⟩

/-- Dropping a prefix preserves recursive allocation order at every retained
suffix depth. -/
theorem drop
    {alpha support : List (LogicVar × String)}
    {cells : List (PayloadCell alpha support)}
    (ordered : ActivationOrderedCellsRelate cells) (count : Nat) :
    ActivationOrderedCellsRelate (cells.drop count) := by
  induction count generalizing cells with
  | zero => simpa using ordered
  | succ count inductionHypothesis =>
      cases cells with
      | nil => trivial
      | cons cell cells => exact inductionHypothesis ordered.2

end ActivationOrderedCellsRelate

/-- Exact historical backtrack-control provenance over an ordinary cell
spine.  The installed cache is threaded explicitly; the base cache at the
empty suffix is intentionally unconstrained, matching the dependent relation.
-/
def ControlOriginCellsRelate
    {alpha support : List (LogicVar × String)}
    (baseAlts : List PLeaTTa.Alt) (frames : List Frame) :
    Option Nat → List (PayloadCell alpha support) → Prop
  | _installed, [] => True
  | installed, cell :: cells =>
      cell.snapshot.controlOrigin.outerAlts =
          flattenOwnedAlts (cells.map PayloadCell.resource) baseAlts ∧
        cell.snapshot.controlOrigin.frames = frames ∧
        installed =
          PLeaTTa.pushBarrierCache
            cell.snapshot.controlOrigin.outerBarriers ∧
        ControlOriginCellsRelate
          (alpha := alpha) (support := support) baseAlts frames
          cell.snapshot.controlOrigin.outerBarriers cells

namespace ControlOriginCellsRelate

/-- The dependent control-origin relation implies its exact cell-fold
characterization. -/
theorem ofPayload
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt} {frames : List Frame}
    {installed : Option Nat}
    (payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer)
    (origins :
      LocalControlOriginSpineRelates baseAlts frames installed payload) :
    ControlOriginCellsRelate baseAlts frames installed
      (payloadCells payload) := by
  induction payload generalizing installed with
  | nil => simp [payloadCells, ControlOriginCellsRelate]
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      have outerAlts :
          snapshot.controlOrigin.outerAlts =
            flattenOwnedAlts resources baseAlts := by
        simpa [headCell] using
          LocalControlOriginSpineRelates.headOuterAlts_eq
            (.cons currentBarrier currentScope nextScope outerScope segment
              segments resource resources cursor context segmentAgrees
              resourceRest resourceQuery resourceBarrier resourceOwnership
              snapshot outerAgrees)
            origins
      have outerFrames : snapshot.controlOrigin.frames = frames := by
        simpa [headCell] using
          LocalControlOriginSpineRelates.headFrames_eq
            (.cons currentBarrier currentScope nextScope outerScope segment
              segments resource resources cursor context segmentAgrees
              resourceRest resourceQuery resourceBarrier resourceOwnership
              snapshot outerAgrees)
            origins
      have installedExact :
          installed =
            PLeaTTa.pushBarrierCache
              snapshot.controlOrigin.outerBarriers := by
        simpa [headCell] using
          LocalControlOriginSpineRelates.installedBarriers_eq_push_headOuter
            (.cons currentBarrier currentScope nextScope outerScope segment
              segments resource resources cursor context segmentAgrees
              resourceRest resourceQuery resourceBarrier resourceOwnership
              snapshot outerAgrees)
            origins
      have tailOrigins :=
        LocalControlOriginSpineRelates.tail origins
      refine ⟨?_, outerFrames, installedExact, inductionHypothesis tailOrigins⟩
      simpa [payloadCells_map_resource] using outerAlts

/-- The cell fold reconstructs the dependent control-origin relation for the
literal payload. -/
theorem toPayload
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt} {frames : List Frame}
    {installed : Option Nat}
    (payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer)
    (origins :
      ControlOriginCellsRelate baseAlts frames installed
        (payloadCells payload)) :
    LocalControlOriginSpineRelates baseAlts frames installed payload := by
  induction payload generalizing installed with
  | nil currentBarrier scope =>
      exact LocalControlOriginSpineRelates.nil currentBarrier scope baseAlts
        frames installed
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      have tailOrigins := inductionHypothesis origins.2.2.2
      have rebuilt :
          LocalControlOriginSpineRelates baseAlts frames
            (PLeaTTa.pushBarrierCache
              snapshot.controlOrigin.outerBarriers)
            (SourceControlResourcePayloadContextAgrees.cons currentBarrier
              currentScope nextScope outerScope segment segments resource
              resources cursor context segmentAgrees resourceRest
              resourceQuery resourceBarrier resourceOwnership snapshot
              outerAgrees) :=
        LocalControlOriginSpineRelates.cons
          (currentBarrier := currentBarrier)
          (currentScope := currentScope)
          (nextScope := nextScope)
          (outerScope := outerScope)
          (segment := segment)
          (segments := segments)
          (resource := resource)
          (resources := resources)
          (cursor := cursor)
          (context := context)
          (segmentAgrees := segmentAgrees)
          (resourceRest := resourceRest)
          (resourceQuery := resourceQuery)
          (resourceBarrier := resourceBarrier)
          (resourceOwnership := resourceOwnership)
          (snapshot := snapshot)
          (outerAgrees := outerAgrees)
          (outerInstalled := snapshot.controlOrigin.outerBarriers)
          tailOrigins
          (by simpa [payloadCells_map_resource] using origins.1)
          rfl origins.2.1
      rw [origins.2.2.1]
      exact rebuilt

/-- Dropping an ordinal prefix exposes the cache immediately outside the
remaining head together with its exact control-origin suffix. -/
theorem drop
    {alpha support : List (LogicVar × String)}
    {baseAlts : List PLeaTTa.Alt} {frames : List Frame}
    {installed : Option Nat} {cells : List (PayloadCell alpha support)}
    (origins : ControlOriginCellsRelate baseAlts frames installed cells)
    (count : Nat) :
    ∃ nextInstalled,
      ControlOriginCellsRelate baseAlts frames nextInstalled
        (cells.drop count) := by
  induction count generalizing installed cells with
  | zero => exact ⟨installed, by simpa using origins⟩
  | succ count inductionHypothesis =>
      cases cells with
      | nil => exact ⟨installed, trivial⟩
      | cons cell cells =>
          exact inductionHypothesis origins.2.2.2

/-- Pulling through a structurally empty prefix installs exactly the cache
recorded at the selected payload occurrence.

This statement covers both cache modes.  It does not infer an enabled cache
from a barrier count: `none` remains `none`, while an enabled cache is popped
once for each crossed local marker.  The selected branch itself leaves its
own marker live, so the result is the pushed cache immediately outside that
exact occurrence. -/
theorem pullAuxTracked_split
    {alpha support : List (LogicVar × String)}
    {base : List PLeaTTa.Alt} {frames : List Frame}
    {installed : Option Nat}
    {cells earlier later : List (PayloadCell alpha support)}
    {selected : PayloadCell alpha support}
    {goals : List PLeaTTa.Goal} {binding : Subst}
    {localTail : List PLeaTTa.Alt}
    (origins : ControlOriginCellsRelate base frames installed cells)
    (split : cells = earlier ++ selected :: later)
    (earlierEmpty : forall cell, cell ∈ earlier -> cell.resource.alts = [])
    (selectedHead :
      selected.resource.alts = .br goals binding :: localTail) :
    PLeaTTa.pullAuxTracked installed
        (flattenOwnedAlts (cells.map PayloadCell.resource) base) =
      (some
          (.branch goals binding,
            localTail ++ PLeaTTa.Alt.barrier ::
              flattenOwnedAlts (later.map PayloadCell.resource) base),
        PLeaTTa.pushBarrierCache
          selected.snapshot.controlOrigin.outerBarriers) := by
  induction earlier generalizing cells installed with
  | nil =>
      subst cells
      rw [origins.2.2.1]
      simp only [List.nil_append, List.map_cons, flattenOwnedAlts_cons,
        selectedHead, List.cons_append, PLeaTTa.pullAuxTracked]
      cases selected.snapshot.controlOrigin.outerBarriers <;> rfl
  | cons first earlier inductionHypothesis =>
      subst cells
      have firstEmpty : first.resource.alts = [] :=
        earlierEmpty first (by simp)
      have tailEmpty :
          forall cell, cell ∈ earlier -> cell.resource.alts = [] := by
        intro cell member
        exact earlierEmpty cell (by simp [member])
      rw [origins.2.2.1]
      have popped :
          PLeaTTa.pullAuxTracked
              (PLeaTTa.pushBarrierCache
                first.snapshot.controlOrigin.outerBarriers)
              (PLeaTTa.Alt.barrier ::
                flattenOwnedAlts
                  ((earlier ++ selected :: later).map PayloadCell.resource)
                  base) =
            PLeaTTa.pullAuxTracked
              first.snapshot.controlOrigin.outerBarriers
              (flattenOwnedAlts
                ((earlier ++ selected :: later).map PayloadCell.resource)
                base) := by
        cases first.snapshot.controlOrigin.outerBarriers <;> rfl
      change
        PLeaTTa.pullAuxTracked
            (PLeaTTa.pushBarrierCache
              first.snapshot.controlOrigin.outerBarriers)
            (first.resource.alts ++ PLeaTTa.Alt.barrier ::
              flattenOwnedAlts
                ((earlier ++ selected :: later).map PayloadCell.resource)
                base) = _
      rw [firstEmpty, List.nil_append, popped]
      exact
        inductionHypothesis origins.2.2.2 rfl tailEmpty

end ControlOriginCellsRelate

/-! ## Root closure and control-spine recovery -/

namespace SourceControlResourcePayloadContextAgrees

/-- Forget retained resources and snapshots while retaining the exact ordered
caller-control spine. -/
theorem controlSpine
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer) :
    ControlSpineAgrees alpha segments := by
  induction payload with
  | nil => exact .nil
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      exact .cons segmentAgrees inductionHypothesis

end SourceControlResourcePayloadContextAgrees

namespace RootClosedAnswerReady

/-- Root-closed answer readiness forces the older executable alternative base
to be literally empty; it is not merely hidden behind an equal flattened
bank. -/
theorem baseAlts_eq_nil
    {before : RepresentativeScheduledPayloadState}
    (ready : RootClosedAnswerReady before) :
    before.carrier.index.baseAlts = [] := by
  have historyResources :
      ready.result.history.resources =
        before.carrier.index.active :: before.carrier.index.resources := by
    simpa [currentAnswerHistory_resources] using ready.result.resourcesExact
  have flattenedExact :
      flattenOwnedAlts
          (before.carrier.index.active :: before.carrier.index.resources)
          before.carrier.index.baseAlts =
        flattenOwnedAlts
          (before.carrier.index.active :: before.carrier.index.resources)
          [] := by
    calc
      flattenOwnedAlts
          (before.carrier.index.active :: before.carrier.index.resources)
          before.carrier.index.baseAlts =
          before.carrier.index.openConf.control.alts :=
        before.carrier.agreement.core.resourceStack.actualAlts.symm
      _ = flattenOwnedAlts ready.result.history.resources [] :=
        ready.bankExact
      _ = flattenOwnedAlts
          (before.carrier.index.active :: before.carrier.index.resources)
          [] := by rw [historyResources]
  have appended :
      flattenOwnedAlts
            (before.carrier.index.active :: before.carrier.index.resources)
            [] ++ before.carrier.index.baseAlts =
        flattenOwnedAlts
          (before.carrier.index.active :: before.carrier.index.resources)
          [] := by
    exact
      (flattenOwnedAlts_base
          (before.carrier.index.active :: before.carrier.index.resources)
          before.carrier.index.baseAlts).symm.trans flattenedExact
  have dropped :=
    congrArg
      (List.drop
        (flattenOwnedAlts
          (before.carrier.index.active :: before.carrier.index.resources)
          []).length)
      appended
  simpa using dropped

end RootClosedAnswerReady

/-! ## Exact scheduled suffix invariants -/

namespace ScheduledSelectedHeadTransition

/-- The selected occurrence followed by the transformed literal tail is the
exact positional suffix of the original payload spine. -/
theorem selectedCellSpineExact
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session) :
    (payloadCells before.carrier.payloadContext).drop
        selection.path.position.val =
      transition.selectedPayloadCell ::
        payloadCells
          (SourceControlResourcePayloadContextAgrees.tail
            transition.postPayload) := by
  calc
    (payloadCells before.carrier.payloadContext).drop
        selection.path.position.val =
        (ready.payloadAlignment.payloadPath selection.path).cell ::
          (payloadCells before.carrier.payloadContext).drop
            (selection.path.position.val + 1) := by
      simp [PayloadPath.cell]
    _ = transition.selectedPayloadCell ::
          payloadCells
            (SourceControlResourcePayloadContextAgrees.tail
              transition.postPayload) := by
      exact
        congrArg₂ List.cons transition.selectedPayloadCellExact.symm
          transition.postLaterCellsExact.symm

/-- The exact selected historical activation is dominated by the current
session and names the selected predicate's typed cut high-water. -/
theorem selectedActivationOriginFacts
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session) :
    transition.selectedPayloadCell.snapshot.activationOrigin.Extends
        before.carrier.index.session ∧
      transition.selectedPayloadCell.snapshot.activationOrigin.nextCutScope =
        transition.selectedPayloadCell.currentScope + 1 := by
  have cells :=
    ActivationOriginCellsRelate.drop
      (ActivationOriginCellsRelate.ofPayload before.carrier.payloadContext
        before.carrier.agreement.activationOrigins)
      selection.path.position.val
  rw [selectedCellSpineExact transition] at cells
  exact ⟨cells.1, cells.2.1⟩

/-- Rejected-prefix cursor motion preserves the selected occurrence's compact
control origin exactly. -/
theorem selectedSnapshotAtFinish_controlOrigin
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session) :
    transition.selectedSnapshotAtFinish.controlOrigin =
      transition.selectedPayloadCell.snapshot.controlOrigin := by
  simp [ScheduledSelectedHeadTransition.selectedSnapshotAtFinish,
    RetainedCallPayloadSnapshot.afterRejectedPulls,
    RetainedCallPayloadSnapshot.transportCursor,
    ScheduledSelectedHeadTransition.selectedSnapshot]

/-- Rejected-prefix transport reindexes only the phantom call generation;
the selected activation remains dominated by the current session and retains
the exact typed cut high-water. -/
theorem selectedSnapshotAtFinish_activationFacts
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session) :
    transition.selectedSnapshotAtFinish.activationOrigin.Extends
        before.carrier.index.session ∧
      transition.selectedSnapshotAtFinish.activationOrigin.nextCutScope =
        transition.selectedPayloadCell.currentScope + 1 := by
  have selectedFacts := selectedActivationOriginFacts transition
  have selectedSnapshotExtends :
      transition.selectedSnapshot.activationOrigin.Extends
        before.carrier.index.session :=
    RetainedCallPayloadSnapshot.activationExtends_transportResourceCursor
      transition.selectedResourceExact transition.selectedCursorExact
      transition.selectedPayloadCell.snapshot selectedFacts.1
  have transported :=
    RetainedCallPayloadSnapshot.activationExtends_transportCursor
      (RetainedCallPayloadSnapshot.RejectedPullsN.preserves_callContext
        transition.frontier.rejectedPulls)
      (RetainedCallPayloadSnapshot.RejectedPullsN.reservationStart_le
        transition.frontier.rejectedPulls
        transition.selectedCursorWellFormed)
      (PLeaTTa.PrologSupportedCallFrontierBridge.RejectedPullsN.preserves_reservedUntil
        transition.frontier.rejectedPulls)
      transition.selectedSnapshot selectedSnapshotExtends
  constructor
  · simpa [ScheduledSelectedHeadTransition.selectedSnapshotAtFinish,
      RetainedCallPayloadSnapshot.afterRejectedPulls] using transported
  · simpa [ScheduledSelectedHeadTransition.selectedSnapshotAtFinish,
      RetainedCallPayloadSnapshot.afterRejectedPulls,
      ScheduledSelectedHeadTransition.selectedSnapshot] using selectedFacts.2

/-- The selected occurrence records the exact later alternative bank and
the unchanged fine-lane frame stack. -/
theorem selectedControlOriginFacts
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session) :
    transition.selectedPayloadCell.snapshot.controlOrigin.outerAlts =
        flattenOwnedAlts transition.postLaterResources [] ∧
      transition.selectedPayloadCell.snapshot.controlOrigin.frames =
        (selectedFineState before).frames := by
  have allCells :=
    ControlOriginCellsRelate.ofPayload before.carrier.payloadContext
      before.carrier.agreement.controlOrigins
  rw [
    PLeaTTa.PrologScheduledPayloadSuccessCarrierBridge.RootClosedAnswerReady.baseAlts_eq_nil
      ready] at allCells
  obtain ⟨selectedInstalled, selectedCells⟩ :=
    ControlOriginCellsRelate.drop allCells selection.path.position.val
  rw [selectedCellSpineExact transition] at selectedCells
  constructor
  · simpa [payloadCells_map_resource] using selectedCells.1
  · simpa [selectedFineState] using selectedCells.2.1

/-- The real answer pull installs the cache recorded by the exact selected
payload occurrence, in both enabled and disabled cache modes.

The proof follows the positional payload prefix.  Every earlier occurrence
is structurally empty, so its marker is crossed once; the selected branch is
then pulled without crossing its own marker. -/
theorem selectedFineBarriersExact
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session) :
    (selectedFineState before).control.barriers =
      PLeaTTa.pushBarrierCache
        transition.selectedPayloadCell.snapshot.controlOrigin.outerBarriers := by
  have origins :=
    ControlOriginCellsRelate.ofPayload before.carrier.payloadContext
      before.carrier.agreement.controlOrigins
  rw [
    PLeaTTa.PrologScheduledPayloadSuccessCarrierBridge.RootClosedAnswerReady.baseAlts_eq_nil
      ready] at origins
  have split :
      payloadCells before.carrier.payloadContext =
        (payloadCells before.carrier.payloadContext).take
            selection.path.position.val ++
          transition.selectedPayloadCell ::
            (payloadCells before.carrier.payloadContext).drop
              (selection.path.position.val + 1) := by
    calc
      payloadCells before.carrier.payloadContext =
          (payloadCells before.carrier.payloadContext).take
              selection.path.position.val ++
            (payloadCells before.carrier.payloadContext).drop
              selection.path.position.val :=
        (List.take_append_drop selection.path.position.val
          (payloadCells before.carrier.payloadContext)).symm
      _ =
          (payloadCells before.carrier.payloadContext).take
              selection.path.position.val ++
            (ready.payloadAlignment.payloadPath selection.path).cell ::
              (payloadCells before.carrier.payloadContext).drop
                (selection.path.position.val + 1) := by
        congr 1
        simp [PayloadPath.cell]
      _ =
          (payloadCells before.carrier.payloadContext).take
              selection.path.position.val ++
            transition.selectedPayloadCell ::
              (payloadCells before.carrier.payloadContext).drop
                (selection.path.position.val + 1) := by
        rw [transition.selectedPayloadCellExact]
  have earlierEmpty :
      forall cell,
        cell ∈
            (payloadCells before.carrier.payloadContext).take
              selection.path.position.val ->
          cell.resource.alts = [] := by
    intro cell member
    have historyMember : cell.historyCell ∈ selection.earlier := by
      rw [transition.route.earlierExact]
      exact List.mem_map.mpr ⟨cell, member, rfl⟩
    simpa [PayloadCell.historyCell] using
      selection.earlierEmpty cell.historyCell historyMember
  have selectedHead :
      transition.selectedPayloadCell.resource.alts =
        .br selection.goals selection.binding :: selection.localTail := by
    rw [transition.selectedResourceExact]
    exact selection.selectedHead
  have tracked :=
    ControlOriginCellsRelate.pullAuxTracked_split origins split earlierEmpty
      selectedHead
  have trackedCache := congrArg Prod.snd tracked
  have actualAlts :
      before.carrier.index.openConf.control.alts =
        flattenOwnedAlts
          ((payloadCells before.carrier.payloadContext).map
            PayloadCell.resource) [] := by
    calc
      before.carrier.index.openConf.control.alts =
          flattenOwnedAlts
            (before.carrier.index.active :: before.carrier.index.resources)
            before.carrier.index.baseAlts :=
        before.carrier.agreement.core.resourceStack.actualAlts
      _ =
          flattenOwnedAlts
            (before.carrier.index.active :: before.carrier.index.resources)
            [] := by
        rw [
          PLeaTTa.PrologScheduledPayloadSuccessCarrierBridge.RootClosedAnswerReady.baseAlts_eq_nil
            ready]
      _ =
          flattenOwnedAlts
            ((payloadCells before.carrier.payloadContext).map
              PayloadCell.resource) [] := by
        rw [payloadCells_map_resource before.carrier.payloadContext]
  have selectedPull :
      PLeaTTa.pullAux before.carrier.index.openConf.control.alts =
        some (.branch selection.goals selection.binding, selection.rest) := by
    rw [ready.bankExact]
    rw [← ready.result.historyBuild.cells_map_resource]
    exact selection.pullExact
  calc
    (selectedFineState before).control.barriers =
        (PLeaTTa.pullAuxTracked
          before.carrier.index.openConf.control.barriers
          before.carrier.index.openConf.control.alts).2 := by
      simpa [selectedFineState] using
        privateAnswerTarget_branch_barriersExact
          before.carrier.index.openConf before.carrier.index.runtime
          selectedPull
    _ = PLeaTTa.pushBarrierCache
          transition.selectedPayloadCell.snapshot.controlOrigin.outerBarriers := by
      rw [actualAlts]
      exact trackedCache

/-- The selected answer-and-pull state still dominates every later retained
payload endpoint at the current source/executable high-waters. -/
theorem postTailEndpointsCurrent
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session) :
    endpointsBelow
      (SourceControlResourcePayloadContextAgrees.tail transition.postPayload)
      before.carrier.index.session.resolver.nextFresh
      (selectedFineState before).persistent.counter := by
  have allCells :=
    PayloadCellEndpointsBelow.ofPayload before.carrier.payloadContext
      before.carrier.agreement.endpointsCurrent
  have laterCells :=
    PayloadCellEndpointsBelow.drop allCells
      (selection.path.position.val + 1)
  rw [← transition.postLaterCellsExact] at laterCells
  have tailBelow :=
    PayloadCellEndpointsBelow.toPayload
      (SourceControlResourcePayloadContextAgrees.tail transition.postPayload)
      laterCells
  rw [selectedFineState, privateAnswerTarget_persistent]
  exact tailBelow

/-- Prefix elimination preserves the complete recursive allocation chronology
of every cell later than the selected occurrence. -/
theorem postTailActivationOrdered
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session) :
    ActivationOrdered
      (SourceControlResourcePayloadContextAgrees.tail
        transition.postPayload) := by
  have allCells :=
    ActivationOrderedCellsRelate.ofPayload before.carrier.payloadContext
      before.carrier.agreement.activationOrdered
  have laterCells :=
    ActivationOrderedCellsRelate.drop allCells
      (selection.path.position.val + 1)
  rw [← transition.postLaterCellsExact] at laterCells
  exact
    ActivationOrderedCellsRelate.toPayload
      (SourceControlResourcePayloadContextAgrees.tail transition.postPayload)
      laterCells

/-- The complete older suffix lies below the selected clause's actual source
fresh interval and executable resolution seed.  This is the exact premise
needed to alpha-extend that suffix after successful head unification. -/
theorem postTailEndpointsAtActivation
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session) :
    endpointsBelow
      (SourceControlResourcePayloadContextAgrees.tail transition.postPayload)
      transition.branch.firstFresh selection.selected.resource.counter := by
  have allCells :=
    ActivationOrderedCellsRelate.ofPayload before.carrier.payloadContext
      before.carrier.agreement.activationOrdered
  have selectedCells :=
    ActivationOrderedCellsRelate.drop allCells selection.path.position.val
  have selectedSpine :
      (payloadCells before.carrier.payloadContext).drop
          selection.path.position.val =
        transition.selectedPayloadCell ::
          (payloadCells before.carrier.payloadContext).drop
            (selection.path.position.val + 1) := by
    calc
      (payloadCells before.carrier.payloadContext).drop
          selection.path.position.val =
          (ready.payloadAlignment.payloadPath selection.path).cell ::
            (payloadCells before.carrier.payloadContext).drop
              (selection.path.position.val + 1) := by
        simp [PayloadPath.cell]
      _ = transition.selectedPayloadCell ::
            (payloadCells before.carrier.payloadContext).drop
              (selection.path.position.val + 1) := by
        rw [transition.selectedPayloadCellExact]
  rw [selectedSpine] at selectedCells
  have laterAtSelected := selectedCells.1
  rw [← transition.postLaterCellsExact] at laterAtSelected
  have branchMember : transition.branch ∈ transition.finish.remaining := by
    rw [transition.offset.cursorRemaining]
    simp
  have selectedStartBelowBranch :
      transition.selectedPayloadCell.cursor.reservationStart ≤
        transition.branch.firstFresh := by
    calc
      transition.selectedPayloadCell.cursor.reservationStart =
          selection.selected.cursor.reservationStart := by
        rw [transition.selectedCursorExact]
      _ ≤ transition.finish.reservationStart :=
        RetainedCallPayloadSnapshot.RejectedPullsN.reservationStart_le
          transition.frontier.rejectedPulls transition.selectedCursorWellFormed
      _ ≤ transition.branch.firstFresh :=
        transition.offset.cursorWellFormed.1.start_le_member_first branchMember
  have laterAtActivation :=
    PayloadCellEndpointsBelow.mono laterAtSelected selectedStartBelowBranch
      (by rw [transition.selectedResourceExact])
  exact
    PayloadCellEndpointsBelow.toPayload
      (SourceControlResourcePayloadContextAgrees.tail transition.postPayload)
      laterAtActivation

/-- Prefix elimination preserves current-session domination of each exact
later historical activation. -/
theorem postTailActivationOrigins
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session) :
    LocalActivationOriginSpineRelates before.carrier.index.session
      (SourceControlResourcePayloadContextAgrees.tail
        transition.postPayload) := by
  have allCells :=
    ActivationOriginCellsRelate.ofPayload before.carrier.payloadContext
      before.carrier.agreement.activationOrigins
  have laterCells :=
    ActivationOriginCellsRelate.drop allCells
      (selection.path.position.val + 1)
  rw [← transition.postLaterCellsExact] at laterCells
  exact
    ActivationOriginCellsRelate.toPayload
      (SourceControlResourcePayloadContextAgrees.tail transition.postPayload)
      laterCells

/-- The selected cell's exact historical outer cache is the installed cache
for the literal later suffix.  Root closure discharges the older base rather
than hiding it behind flattened-bank equality. -/
theorem postTailControlOrigins
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session) :
    LocalControlOriginSpineRelates [] (selectedFineState before).frames
      transition.selectedPayloadCell.snapshot.controlOrigin.outerBarriers
      (SourceControlResourcePayloadContextAgrees.tail
        transition.postPayload) := by
  have allCells :=
    ControlOriginCellsRelate.ofPayload before.carrier.payloadContext
      before.carrier.agreement.controlOrigins
  rw [
    PLeaTTa.PrologScheduledPayloadSuccessCarrierBridge.RootClosedAnswerReady.baseAlts_eq_nil
      ready] at allCells
  obtain ⟨selectedInstalled, selectedCells⟩ :=
    ControlOriginCellsRelate.drop allCells selection.path.position.val
  have selectedSpine :
      (payloadCells before.carrier.payloadContext).drop
          selection.path.position.val =
        transition.selectedPayloadCell ::
          (payloadCells before.carrier.payloadContext).drop
            (selection.path.position.val + 1) := by
    calc
      (payloadCells before.carrier.payloadContext).drop
          selection.path.position.val =
          (ready.payloadAlignment.payloadPath selection.path).cell ::
            (payloadCells before.carrier.payloadContext).drop
              (selection.path.position.val + 1) := by
        simp [PayloadPath.cell]
      _ = transition.selectedPayloadCell ::
            (payloadCells before.carrier.payloadContext).drop
              (selection.path.position.val + 1) := by
        rw [transition.selectedPayloadCellExact]
  rw [selectedSpine] at selectedCells
  have laterCells := selectedCells.2.2.2
  rw [← transition.postLaterCellsExact] at laterCells
  have tailOrigins :=
    ControlOriginCellsRelate.toPayload
      (SourceControlResourcePayloadContextAgrees.tail transition.postPayload)
      laterCells
  simpa [selectedFineState, privateAnswerTarget] using tailOrigins

/-! ## Successful selected-head carrier reconstruction -/

/-- A paired successful selected-head transition reconstructs the exact
persistent-free active payload relation at its real source and fine
successors.

The result does not retain an `OpenedCall`, `PendingCall`, historical
`Session`, or historical `OpenConf`.  The only historical data are the
occurrence-indexed compact origins already owned by the payload snapshots.
The current session and every live executable component come from the actual
post-step state. -/
theorem toPersistentFreeActivePayload
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    {transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session}
    {partition : RootPayloadPartition before}
    {independentResult : Substitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattened : TreeSubstitution}
    {installed : Subst}
    (relation :
      ScheduledSuccessfulHeadRelates prog gt before ready selection scope
        transition partition independentResult nextAlpha sourceCanonical
        flattened installed) :
    ∃ nextPayloadContext :
        ActiveProductPayloadContextAt nextAlpha before.carrier.index.support
          before.carrier.index.qterm
          transition.selectedPayloadCell.currentScope transition.finish
          transition.branch transition.branchTail
          selection.selected.resource.barrier
          transition.selectedPayloadCell.segment.barrier
          transition.selectedPayloadCell.segment.references
          transition.selectedPayloadCell.segment.executables
          transition.selectedPayloadCell.outerSegments
          (afterPulledHead selection.selected.resource selection.localTail)
          transition.postLaterResources
          transition.selectedPayloadCell.nextScope
          transition.selectedPayloadCell.outerScope
          transition.postLaterContext,
      PersistentFreeActiveProductPayloadResourceRelatesAt
        (AlphaFreshFrontier nextAlpha) nextAlpha
        before.carrier.index.support
        (sourceCanonical ++ transition.selectedSnapshotAtFinish.canonical)
        transition.selectedSnapshotAtFinish.referenceBase
        transition.selectedPayloadCell.currentScope
        before.carrier.index.session transition.finish transition.branch
        transition.branchTail selection.localTail
        selection.selected.resource.barrier
        transition.selectedPayloadCell.segment.barrier
        transition.branch.body transition.copied.body
        transition.selectedPayloadCell.segment.references
        transition.selectedPayloadCell.segment.executables
        transition.selectedPayloadCell.outerSegments independentResult
        (PLeaTTa.trimFor
          (transition.copied.body ++ selection.selected.resource.rest)
          (selectedFineState before).control.qterm installed)
        before.carrier.index.qterm
        (afterPulledHead selection.selected.resource selection.localTail)
        transition.postLaterResources
        transition.selectedPayloadCell.nextScope
        transition.selectedPayloadCell.outerScope
        transition.postLaterContext []
        (successfulSourceFrontier transition independentResult)
        (successfulFineState transition installed) nextPayloadContext ∧
      RetainedCallPayloadSnapshot.RestorationDataAgrees
        (headCell nextPayloadContext).snapshot
        transition.selectedSnapshotAtFinish ∧
      AlphaCumulativeResidualVariantAgreesOnWith nextAlpha
        before.carrier.index.support
        (sourceCanonical ++ transition.selectedSnapshotAtFinish.canonical)
        transition.selectedSnapshotAtFinish.referenceBase
        (PLeaTTa.trimFor
          (transition.copied.body ++ selection.selected.resource.rest)
          (selectedFineState before).control.qterm installed)
        (flattened ++
          transition.selectedSnapshotAtFinish.residualRepresentative) := by
  have currentQuery :
      (selectedFineState before).control.qterm =
        selection.selected.resource.qterm := by
    calc
      (selectedFineState before).control.qterm =
          before.carrier.index.openConf.control.qterm := by
        simp [selectedFineState]
      _ = before.carrier.index.qterm :=
        before.carrier.agreement.core.control.ready.2.2.1
      _ = selection.selected.resource.qterm :=
        transition.selectedResourceQueryExact.symm
  let oldTail :=
    SourceControlResourcePayloadContextAgrees.tail transition.postPayload
  let nextTail :=
    SourceControlResourcePayloadContextAgrees.extendAbove
      relation.extensionAbove oldTail (postTailEndpointsAtActivation transition)
  have nextTailAtExtension :
      endpointsBelow nextTail transition.branch.firstFresh
        selection.selected.resource.counter := by
    simpa [nextTail, oldTail] using
      SourceControlResourcePayloadContextAgrees.extendAbove_endpointsBelow
        relation.extensionAbove oldTail
        (postTailEndpointsAtActivation transition)
  have nextTailCurrent :
      endpointsBelow nextTail
        before.carrier.index.session.resolver.nextFresh
        (selectedFineState before).persistent.counter := by
    simpa [nextTail, oldTail] using
      SourceControlResourcePayloadContextAgrees.extendAbove_endpointsBelow_at
        relation.extensionAbove oldTail
        (postTailEndpointsAtActivation transition)
        (postTailEndpointsCurrent transition)
  have nextTailOrdered : ActivationOrdered nextTail := by
    simpa [nextTail, oldTail] using
      ActivationOrdered.extendAbove relation.extensionAbove oldTail
        (postTailEndpointsAtActivation transition)
        (postTailActivationOrdered transition)
  have nextTailActivationOrigins :
      LocalActivationOriginSpineRelates before.carrier.index.session
        nextTail := by
    simpa [nextTail, oldTail] using
      (postTailActivationOrigins transition).extendAbove relation.extensionAbove
        oldTail (postTailEndpointsAtActivation transition)
  have nextTailControlOrigins :
      LocalControlOriginSpineRelates [] (selectedFineState before).frames
        transition.selectedPayloadCell.snapshot.controlOrigin.outerBarriers
        nextTail := by
    simpa [nextTail, oldTail] using
      (postTailControlOrigins transition).extendAbove relation.extensionAbove
        oldTail (postTailEndpointsAtActivation transition) []
        (selectedFineState before).frames
        transition.selectedPayloadCell.snapshot.controlOrigin.outerBarriers
  rcases relation.nextSnapshot with
    ⟨nextSnapshot, nextSnapshotRestoration, nextSnapshotControlOrigin,
      nextSnapshotActivationOrigin⟩
  have callerAgrees :
      transition.selectedPayloadCell.segment.Agrees nextAlpha :=
    (SourceControlResourcePayloadContextAgrees.controlSpine
      transition.postPayload).head.mono relation.alphaIncluded
  have activeOwnership :
      (afterPulledHead selection.selected.resource selection.localTail).HasIndexedOwnershipAt
        nextAlpha
        (transition.finish.advance transition.branch transition.branchTail) :=
    ⟨transition.callStart,
      (transition.startPosition + transition.frontier.rejectedCount) + 1,
      transition.tailOwnershipExact.mono relation.alphaIncluded⟩
  let nextPayloadContext :
      ActiveProductPayloadContextAt nextAlpha before.carrier.index.support
        before.carrier.index.qterm
        transition.selectedPayloadCell.currentScope transition.finish
        transition.branch transition.branchTail
        selection.selected.resource.barrier
        transition.selectedPayloadCell.segment.barrier
        transition.selectedPayloadCell.segment.references
        transition.selectedPayloadCell.segment.executables
        transition.selectedPayloadCell.outerSegments
        (afterPulledHead selection.selected.resource selection.localTail)
        transition.postLaterResources
        transition.selectedPayloadCell.nextScope
        transition.selectedPayloadCell.outerScope
        transition.postLaterContext :=
    .cons selection.selected.resource.barrier
      transition.selectedPayloadCell.currentScope
      transition.selectedPayloadCell.nextScope
      transition.selectedPayloadCell.outerScope
      transition.selectedPayloadCell.segment
      transition.selectedPayloadCell.outerSegments
      (afterPulledHead selection.selected.resource selection.localTail)
      transition.postLaterResources
      (transition.finish.advance transition.branch transition.branchTail)
      transition.postLaterContext callerAgrees
      (by
        simpa [afterPulledHead] using
          transition.selectedSnapshotAtFinish.resourceRest)
      (by
        simpa [afterPulledHead] using
          transition.selectedResourceQueryExact)
      (by simp [afterPulledHead])
      activeOwnership nextSnapshot nextTail
  have endpointBounds :=
    transition.selectedEndpointBounds
      before.carrier.agreement.endpointsCurrent
  have headCursorCurrent :
      (transition.finish.advance transition.branch
          transition.branchTail).reservedUntil ≤
        before.carrier.index.session.resolver.nextFresh := by
    simpa [PreparedCursor.advance] using endpointBounds.1
  have headResourceCurrent :
      (afterPulledHead selection.selected.resource
          selection.localTail).finalCounter ≤
        (selectedFineState before).persistent.counter := by
    simpa [afterPulledHead, selectedFineState] using endpointBounds.2
  have nextEndpointsCurrent :
      endpointsBelow nextPayloadContext
        before.carrier.index.session.resolver.nextFresh
        (successfulFineState transition installed).persistent.counter := by
    simp only [nextPayloadContext, endpointsBelow]
    rw [relation.finePersistent]
    exact ⟨headCursorCurrent, headResourceCurrent, nextTailCurrent⟩
  have branchMember : transition.branch ∈ transition.finish.remaining := by
    rw [transition.offset.cursorRemaining]
    simp
  have branchFirstBelowAdvanced :
      transition.branch.firstFresh ≤
        (transition.finish.advance transition.branch
          transition.branchTail).reservationStart := by
    simpa [PreparedCursor.advance] using
      transition.offset.cursorWellFormed.1.member_first_le_next branchMember
  have nextTailAtActivation :
      endpointsBelow nextTail
        (transition.finish.advance transition.branch
          transition.branchTail).reservationStart
        (afterPulledHead selection.selected.resource
          selection.localTail).counter :=
    endpointsBelow_mono nextTail nextTailAtExtension
      branchFirstBelowAdvanced (by simp [afterPulledHead])
  have nextActivationOrdered : ActivationOrdered nextPayloadContext := by
    exact ⟨nextTailAtActivation, nextTailOrdered⟩
  have selectedActivationFacts :=
    selectedSnapshotAtFinish_activationFacts transition
  have nextActivationOrigins :
      LocalActivationOriginSpineRelates before.carrier.index.session
        nextPayloadContext := by
    exact
      ⟨by
          rw [nextSnapshotActivationOrigin]
          exact selectedActivationFacts.1,
        by
          rw [nextSnapshotActivationOrigin]
          exact selectedActivationFacts.2,
        nextTailActivationOrigins⟩
  have selectedControlFacts := selectedControlOriginFacts transition
  have nextOriginOld :
      nextSnapshot.controlOrigin =
        transition.selectedPayloadCell.snapshot.controlOrigin :=
    nextSnapshotControlOrigin.trans
      (selectedSnapshotAtFinish_controlOrigin transition)
  have nextHeadOrigin :
      (SourceControlResourcePayloadContextAgrees.headCell
        nextPayloadContext).snapshot.controlOrigin =
        nextSnapshot.controlOrigin := by
    rfl
  have rebuiltControlOrigins :
      LocalControlOriginSpineRelates [] (selectedFineState before).frames
        (PLeaTTa.pushBarrierCache
          transition.selectedPayloadCell.snapshot.controlOrigin.outerBarriers)
        nextPayloadContext :=
    LocalControlOriginSpineRelates.prepend nextPayloadContext
      nextTailControlOrigins
      (by
        rw [nextHeadOrigin, nextOriginOld]
        exact selectedControlFacts.1)
      (by rw [nextHeadOrigin, nextOriginOld])
      (by
        rw [nextHeadOrigin, nextOriginOld]
        exact selectedControlFacts.2)
  have nextControlOrigins :
      LocalControlOriginSpineRelates []
        (successfulFineState transition installed).frames
        (successfulFineState transition installed).control.barriers
        nextPayloadContext := by
    rw [relation.fineFrames, relation.fineBarriers,
      selectedFineBarriersExact transition]
    exact rebuiltControlOrigins
  have bodyPayload :
      TaskPayloadAgrees nextAlpha before.carrier.index.support
        selection.selected.resource.barrier
        (sourceCanonical ++ transition.selectedSnapshotAtFinish.canonical)
        transition.selectedSnapshotAtFinish.referenceBase independentResult
        (PLeaTTa.trimFor
          (transition.copied.body ++ selection.selected.resource.rest)
          (selectedFineState before).control.qterm installed)
        transition.branch.body transition.copied.body := by
    simpa [currentQuery] using relation.successorTask
  have spinePayload :
      TaskSpinePayloadAgrees nextAlpha before.carrier.index.support
        (sourceCanonical ++ transition.selectedSnapshotAtFinish.canonical)
        transition.selectedSnapshotAtFinish.referenceBase independentResult
        (PLeaTTa.trimFor
          (transition.copied.body ++ selection.selected.resource.rest)
          (selectedFineState before).control.qterm installed)
        ({ barrier := selection.selected.resource.barrier
           references := transition.branch.body
           executables := transition.copied.body } ::
         transition.selectedPayloadCell.segment ::
         transition.selectedPayloadCell.outerSegments) :=
    TaskSpinePayloadAgrees.activateLocalCall
      transition.selectedSnapshotAtFinish.payload bodyPayload
      (fun pair member =>
        relation.alphaIncluded pair
          (transition.selectedSnapshotAtFinish.alphaIncluded pair member))
  have targetPersistent :
      SessionRelatesPersistent (AlphaFreshFrontier nextAlpha)
        before.carrier.index.session
        (successfulFineState transition installed).persistent := by
    refine ⟨?_, ?_⟩
    · rw [relation.finePersistent]
      simpa [selectedFineState] using
        before.carrier.agreement.core.control.ready.1.database
    · rw [relation.finePersistent]
      exact relation.freshFrontier
  have targetCurrent :
      (successfulFineState transition installed).control.cur =
        some
          (flattenExecutables
            ({ barrier := selection.selected.resource.barrier
               references := transition.branch.body
               executables := transition.copied.body } ::
             transition.selectedPayloadCell.segment ::
             transition.selectedPayloadCell.outerSegments),
           PLeaTTa.trimFor
            (transition.copied.body ++ selection.selected.resource.rest)
            (selectedFineState before).control.qterm installed) := by
    simp [successfulFineState, flattenExecutables_cons,
      transition.selectedSnapshotAtFinish.resourceRest]
  have targetQuery :
      (successfulFineState transition installed).control.qterm =
        before.carrier.index.qterm := by
    calc
      (successfulFineState transition installed).control.qterm =
          (selectedFineState before).control.qterm := by
        rfl
      _ = selection.selected.resource.qterm := currentQuery
      _ = before.carrier.index.qterm :=
        transition.selectedResourceQueryExact
  have targetReady :
      SpinedReadyTaskRelates (AlphaFreshFrontier nextAlpha) nextAlpha
        before.carrier.index.support
        (sourceCanonical ++ transition.selectedSnapshotAtFinish.canonical)
        transition.selectedSnapshotAtFinish.referenceBase
        before.carrier.index.session independentResult
        (PLeaTTa.trimFor
          (transition.copied.body ++ selection.selected.resource.rest)
          (selectedFineState before).control.qterm installed)
        before.carrier.index.qterm
        ({ barrier := selection.selected.resource.barrier
           references := transition.branch.body
           executables := transition.copied.body } ::
         transition.selectedPayloadCell.segment ::
         transition.selectedPayloadCell.outerSegments)
        (successfulFineState transition installed) :=
    ⟨targetPersistent, targetCurrent, targetQuery, spinePayload⟩
  have targetActualAlts :
      (successfulFineState transition installed).control.alts =
        flattenOwnedAlts
          (afterPulledHead selection.selected.resource selection.localTail ::
            transition.postLaterResources) [] := by
    calc
      (successfulFineState transition installed).control.alts =
          (selectedFineState before).control.alts := relation.fineAlts
      _ = flattenOwnedAlts
            ((payloadCells transition.postPayload).map
              PayloadCell.resource) [] := by
        simpa [selectedFineState] using
          PLeaTTa.PrologScheduledPayloadOpenConfBridge.ScheduledSelectedHeadTransition.fineAltsExact
            transition
      _ = flattenOwnedAlts
            (afterPulledHead selection.selected.resource selection.localTail ::
              transition.postLaterResources) [] := by
        rw [payloadCells_map_resource transition.postPayload]
  have targetAgreement :
      PersistentFreeActiveProductPayloadResourceRelatesAt
        (AlphaFreshFrontier nextAlpha) nextAlpha
        before.carrier.index.support
        (sourceCanonical ++ transition.selectedSnapshotAtFinish.canonical)
        transition.selectedSnapshotAtFinish.referenceBase
        transition.selectedPayloadCell.currentScope
        before.carrier.index.session transition.finish transition.branch
        transition.branchTail selection.localTail
        selection.selected.resource.barrier
        transition.selectedPayloadCell.segment.barrier
        transition.branch.body transition.copied.body
        transition.selectedPayloadCell.segment.references
        transition.selectedPayloadCell.segment.executables
        transition.selectedPayloadCell.outerSegments independentResult
        (PLeaTTa.trimFor
          (transition.copied.body ++ selection.selected.resource.rest)
          (selectedFineState before).control.qterm installed)
        before.carrier.index.qterm
        (afterPulledHead selection.selected.resource selection.localTail)
        transition.postLaterResources
        transition.selectedPayloadCell.nextScope
        transition.selectedPayloadCell.outerScope
        transition.postLaterContext []
        (successfulSourceFrontier transition independentResult)
        (successfulFineState transition installed) nextPayloadContext :=
    { ready := targetReady
      activeAlts := by simp [afterPulledHead]
      actualAlts := targetActualAlts
      sourceShape := rfl
      endpointsCurrent := nextEndpointsCurrent
      activationOrdered := nextActivationOrdered
      activationOrigins := nextActivationOrigins
      controlOrigins := nextControlOrigins }
  refine ⟨nextPayloadContext, targetAgreement, ?_, ?_⟩
  · exact nextSnapshotRestoration
  · simpa [currentQuery] using relation.successorCumulative

/-! ## Type-valued scheduled-success successor -/

/-- The exact active successor of one successful scheduled-head transition.

This package lives in `Type`.  In particular, the dependent payload value is
data carried by the transition rather than a proposition which a later layer
would have to reopen with choice.  The older existence theorem remains the
constructive producer: it can establish `Nonempty` for this package, while an
actual global transition stores the package itself. -/
structure ScheduledSuccessfulHeadSuccessor
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (before : RepresentativeScheduledPayloadState)
    (ready : RootClosedAnswerReady before)
    (selection : ScheduledLocalSelection ready.result.historyBuild.cells)
    (scope : CutScopeId)
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session)
    (partition : RootPayloadPartition before)
    (independentResult : Substitution)
    (nextAlpha : List (LogicVar × String))
    (sourceCanonical flattened : TreeSubstitution)
    (installed : Subst)
    (relation :
      ScheduledSuccessfulHeadRelates prog gt before ready selection scope
        transition partition independentResult nextAlpha sourceCanonical
        flattened installed) where
  payloadContext :
    ActiveProductPayloadContextAt nextAlpha before.carrier.index.support
      before.carrier.index.qterm
      transition.selectedPayloadCell.currentScope transition.finish
      transition.branch transition.branchTail
      selection.selected.resource.barrier
      transition.selectedPayloadCell.segment.barrier
      transition.selectedPayloadCell.segment.references
      transition.selectedPayloadCell.segment.executables
      transition.selectedPayloadCell.outerSegments
      (afterPulledHead selection.selected.resource selection.localTail)
      transition.postLaterResources
      transition.selectedPayloadCell.nextScope
      transition.selectedPayloadCell.outerScope
      transition.postLaterContext
  agreement :
    PersistentFreeActiveProductPayloadResourceRelatesAt
      (AlphaFreshFrontier nextAlpha) nextAlpha
      before.carrier.index.support
      (sourceCanonical ++ transition.selectedSnapshotAtFinish.canonical)
      transition.selectedSnapshotAtFinish.referenceBase
      transition.selectedPayloadCell.currentScope
      before.carrier.index.session transition.finish transition.branch
      transition.branchTail selection.localTail
      selection.selected.resource.barrier
      transition.selectedPayloadCell.segment.barrier
      transition.branch.body transition.copied.body
      transition.selectedPayloadCell.segment.references
      transition.selectedPayloadCell.segment.executables
      transition.selectedPayloadCell.outerSegments independentResult
      (PLeaTTa.trimFor
        (transition.copied.body ++ selection.selected.resource.rest)
        (selectedFineState before).control.qterm installed)
      before.carrier.index.qterm
      (afterPulledHead selection.selected.resource selection.localTail)
      transition.postLaterResources
      transition.selectedPayloadCell.nextScope
      transition.selectedPayloadCell.outerScope
      transition.postLaterContext []
      (successfulSourceFrontier transition independentResult)
      (successfulFineState transition installed) payloadContext
  restoration :
    RetainedCallPayloadSnapshot.RestorationDataAgrees
      (headCell payloadContext).snapshot
      transition.selectedSnapshotAtFinish
  cumulative :
    AlphaCumulativeResidualVariantAgreesOnWith nextAlpha
      before.carrier.index.support
      (sourceCanonical ++ transition.selectedSnapshotAtFinish.canonical)
      transition.selectedSnapshotAtFinish.referenceBase
      (PLeaTTa.trimFor
        (transition.copied.body ++ selection.selected.resource.rest)
        (selectedFineState before).control.qterm installed)
      (flattened ++
        transition.selectedSnapshotAtFinish.residualRepresentative)

namespace ScheduledSuccessfulHeadSuccessor

/-- Reify the successor package as the single global persistent-free active
carrier.  Every index is the literal endpoint already certified by
`agreement`; no historical creation packet is reconstructed. -/
def carrier
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    {transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session}
    {partition : RootPayloadPartition before}
    {independentResult : Substitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattened : TreeSubstitution}
    {installed : Subst}
    {relation :
      ScheduledSuccessfulHeadRelates prog gt before ready selection scope
        transition partition independentResult nextAlpha sourceCanonical
        flattened installed}
    (successor :
      ScheduledSuccessfulHeadSuccessor prog gt before ready selection scope
        transition partition independentResult nextAlpha sourceCanonical
        flattened installed relation) :
    PersistentFreeActivePayloadState :=
  { index :=
      { freshFrontier := AlphaFreshFrontier nextAlpha
        alpha := nextAlpha
        support := before.carrier.index.support
        canonical :=
          sourceCanonical ++ transition.selectedSnapshotAtFinish.canonical
        referenceBase := transition.selectedSnapshotAtFinish.referenceBase
        predicateScope := transition.selectedPayloadCell.currentScope
        session := before.carrier.index.session
        finish := transition.finish
        branch := transition.branch
        branchTail := transition.branchTail
        altTail := selection.localTail
        bodyBarrier := selection.selected.resource.barrier
        callerBarrier := transition.selectedPayloadCell.segment.barrier
        bodyReferences := transition.branch.body
        bodyExecutables := transition.copied.body
        callerReferences := transition.selectedPayloadCell.segment.references
        callerExecutables := transition.selectedPayloadCell.segment.executables
        outer := transition.selectedPayloadCell.outerSegments
        current := independentResult
        runtime :=
          PLeaTTa.trimFor
            (transition.copied.body ++ selection.selected.resource.rest)
            (selectedFineState before).control.qterm installed
        qterm := before.carrier.index.qterm
        active :=
          afterPulledHead selection.selected.resource selection.localTail
        resources := transition.postLaterResources
        callerScope := transition.selectedPayloadCell.nextScope
        outerScope := transition.selectedPayloadCell.outerScope
        context := transition.postLaterContext
        baseAlts := []
        source := successfulSourceFrontier transition independentResult
        openConf := successfulFineState transition installed }
    payloadContext := successor.payloadContext
    agreement := successor.agreement }

/-- The representative-bearing phase endpoint stored by the global zipper. -/
def after
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    {transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session}
    {partition : RootPayloadPartition before}
    {independentResult : Substitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattened : TreeSubstitution}
    {installed : Subst}
    {relation :
      ScheduledSuccessfulHeadRelates prog gt before ready selection scope
        transition partition independentResult nextAlpha sourceCanonical
        flattened installed}
    (successor :
      ScheduledSuccessfulHeadSuccessor prog gt before ready selection scope
        transition partition independentResult nextAlpha sourceCanonical
        flattened installed relation) :
    RepresentativePersistentFreeActivePayloadState :=
  { carrier := successor.carrier
    representative :=
      flattened ++ transition.selectedSnapshotAtFinish.residualRepresentative
    cumulative := successor.cumulative }

@[simp] theorem after_sourceState
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    {transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session}
    {partition : RootPayloadPartition before}
    {independentResult : Substitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattened : TreeSubstitution}
    {installed : Subst}
    {relation :
      ScheduledSuccessfulHeadRelates prog gt before ready selection scope
        transition partition independentResult nextAlpha sourceCanonical
        flattened installed}
    (successor :
      ScheduledSuccessfulHeadSuccessor prog gt before ready selection scope
        transition partition independentResult nextAlpha sourceCanonical
        flattened installed relation) :
    successor.after.carrier.sourceState =
      .running before.carrier.index.session
        (successfulSourceFrontier transition independentResult) := rfl

@[simp] theorem after_fineState
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    {transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session}
    {partition : RootPayloadPartition before}
    {independentResult : Substitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattened : TreeSubstitution}
    {installed : Subst}
    {relation :
      ScheduledSuccessfulHeadRelates prog gt before ready selection scope
        transition partition independentResult nextAlpha sourceCanonical
        flattened installed}
    (successor :
      ScheduledSuccessfulHeadSuccessor prog gt before ready selection scope
        transition partition independentResult nextAlpha sourceCanonical
        flattened installed relation) :
    successor.after.carrier.fineState =
      .ready (successfulFineState transition installed) := rfl

@[simp] theorem after_session
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    {transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session}
    {partition : RootPayloadPartition before}
    {independentResult : Substitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattened : TreeSubstitution}
    {installed : Subst}
    {relation :
      ScheduledSuccessfulHeadRelates prog gt before ready selection scope
        transition partition independentResult nextAlpha sourceCanonical
        flattened installed}
    (successor :
      ScheduledSuccessfulHeadSuccessor prog gt before ready selection scope
        transition partition independentResult nextAlpha sourceCanonical
        flattened installed relation) :
    successor.after.carrier.index.session = before.carrier.index.session := rfl

@[simp] theorem after_openConf
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    {transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session}
    {partition : RootPayloadPartition before}
    {independentResult : Substitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattened : TreeSubstitution}
    {installed : Subst}
    {relation :
      ScheduledSuccessfulHeadRelates prog gt before ready selection scope
        transition partition independentResult nextAlpha sourceCanonical
        flattened installed}
    (successor :
      ScheduledSuccessfulHeadSuccessor prog gt before ready selection scope
        transition partition independentResult nextAlpha sourceCanonical
        flattened installed relation) :
    successor.after.carrier.index.openConf =
      successfulFineState transition installed := rfl

@[simp] theorem after_representative
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    {transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session}
    {partition : RootPayloadPartition before}
    {independentResult : Substitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattened : TreeSubstitution}
    {installed : Subst}
    {relation :
      ScheduledSuccessfulHeadRelates prog gt before ready selection scope
        transition partition independentResult nextAlpha sourceCanonical
        flattened installed}
    (successor :
      ScheduledSuccessfulHeadSuccessor prog gt before ready selection scope
        transition partition independentResult nextAlpha sourceCanonical
        flattened installed relation) :
    successor.after.representative =
      flattened ++
        transition.selectedSnapshotAtFinish.residualRepresentative := rfl

/-- The existing constructive proof inhabits the new Type-valued package.
`Nonempty` is only the producer theorem's proposition; it is never stored as
phase data. -/
theorem nonempty
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    {transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session}
    {partition : RootPayloadPartition before}
    {independentResult : Substitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattened : TreeSubstitution}
    {installed : Subst}
    (relation :
      ScheduledSuccessfulHeadRelates prog gt before ready selection scope
        transition partition independentResult nextAlpha sourceCanonical
        flattened installed) :
    Nonempty
      (ScheduledSuccessfulHeadSuccessor prog gt before ready selection scope
        transition partition independentResult nextAlpha sourceCanonical
        flattened installed relation) := by
  rcases ScheduledSelectedHeadTransition.toPersistentFreeActivePayload relation with
    ⟨payloadContext, agreement, restoration, cumulative⟩
  exact ⟨⟨payloadContext, agreement, restoration, cumulative⟩⟩

end ScheduledSuccessfulHeadSuccessor

end ScheduledSelectedHeadTransition

end PLeaTTa.PrologScheduledPayloadSuccessCarrierBridge
