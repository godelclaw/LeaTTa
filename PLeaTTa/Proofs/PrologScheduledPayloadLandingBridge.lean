-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologScheduledPayloadLandingBridge
Purpose: Classify one rooted local scheduled pull while selecting the exact
  immutable payload occurrence by position
Trusted boundary: none
Main exports:
  ScheduledLocalSelection,
  ScheduledCellBankPull,
  ScheduledPayloadPullOutcome,
  ScheduledPayloadAlignment.classifyPull
-/
import PLeaTTa.Proofs.PrologRootClosedAnswerBridge
import PLeaTTa.Proofs.PrologBodyFailureExhaustedResourceTransitionBridge

namespace PLeaTTa.PrologScheduledPayloadLandingBridge

open Metta (Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PrologAnswerPullClassificationBridge
open PrologAnswerResourceBridge
open PrologBodyFailureExhaustedResourceTransitionBridge
open PrologBodyFailureResourceTransitionBridge
open PrologProductResourceContextBridge
open PrologRootClosedAnswerBridge
open PrologScheduledAnswerPropagationBridge
open PrologScheduledHistoryBuildBridge
open PrologScheduledPayloadPathBridge

/-!
# Type-valued local pull selection

The older generic pull classifier returns a proposition.  That is sufficient
for trace facts, but it cannot choose the Type-valued immutable snapshot
needed by a post-answer phase.  This module computes the first branch directly
from the exact local-history occurrence cells.  The source landing remains a
proof field; no source proposition is eliminated to generate data.
-/

/-- Structural decomposition selected by one eager pull over an ordered list
of locally owned history cells.

The cells before `selected` are explicitly empty, the selected resource owns
the displayed branch at its literal head, and `rest` is the exact executable
bank obtained by consuming that head while preserving the selected marker and
every later cell.  This proof-relevant decomposition is the post-answer
zipper transform; the ordinal path below is only a derived view. -/
structure ScheduledLocalSelection
    {alpha : List (LogicVar × String)}
    (cells : List (ScheduledHistoryCell alpha)) : Type where
  earlier : List (ScheduledHistoryCell alpha)
  selected : ScheduledHistoryCell alpha
  suffix : List (ScheduledHistoryCell alpha)
  goals : List PLeaTTa.Goal
  binding : Subst
  localTail : List PLeaTTa.Alt
  rest : List PLeaTTa.Alt
  cellsExact : cells = earlier ++ selected :: suffix
  earlierEmpty : ∀ cell ∈ earlier, cell.resource.alts = []
  selectedHead : selected.resource.alts = .br goals binding :: localTail
  restExact :
    rest =
      localTail ++ PLeaTTa.Alt.barrier ::
        flattenOwnedAlts (suffix.map ScheduledHistoryCell.resource) []
  pullExact :
    PLeaTTa.pullAux
        (flattenOwnedAlts (cells.map ScheduledHistoryCell.resource) []) =
      some (.branch goals binding, rest)

namespace ScheduledLocalSelection

/-- Executable resource zipper after the eager pull: every earlier empty
descriptor is dropped, the selected descriptor consumes exactly one head,
and every later descriptor is preserved literally. -/
def postResources
    {alpha : List (LogicVar × String)}
    {cells : List (ScheduledHistoryCell alpha)}
    (selection : ScheduledLocalSelection cells) :
    List RetainedAlternativeSegment :=
  afterPulledHead selection.selected.resource selection.localTail ::
    selection.suffix.map ScheduledHistoryCell.resource

/-- Flattening the post-resource zipper is exactly the residual bank returned
by the real eager pull. -/
theorem rest_eq_flatten_postResources
    {alpha : List (LogicVar × String)}
    {cells : List (ScheduledHistoryCell alpha)}
    (selection : ScheduledLocalSelection cells) :
    selection.rest = flattenOwnedAlts selection.postResources [] := by
  simp [postResources, flattenOwnedAlts, afterPulledHead,
    selection.restExact]

/-- The selected ordinal is derived from the structural prefix, so the
coordinate cannot drift from the drop-prefix equation. -/
def position
    {alpha : List (LogicVar × String)}
    {cells : List (ScheduledHistoryCell alpha)}
    (selection : ScheduledLocalSelection cells) : Fin cells.length :=
  ⟨selection.earlier.length, by
    have lengths := congrArg List.length selection.cellsExact
    simp at lengths
    omega⟩

@[simp] theorem position_val
    {alpha : List (LogicVar × String)}
    {cells : List (ScheduledHistoryCell alpha)}
    (selection : ScheduledLocalSelection cells) :
    selection.position.val = selection.earlier.length := rfl

/-- The corresponding coordinate in one exact scheduled-history build. -/
def path
    {alpha : List (LogicVar × String)}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    {build : ScheduledHistoryBuild history}
    (selection : ScheduledLocalSelection build.cells) :
    ScheduledHistoryBuild.Path build :=
  ⟨selection.position⟩

/-- The derived coordinate names the structural selected cell exactly. -/
theorem path_cell_exact
    {alpha : List (LogicVar × String)}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    {build : ScheduledHistoryBuild history}
    (selection : ScheduledLocalSelection build.cells) :
    selection.path.cell = selection.selected := by
  simpa [path, ScheduledHistoryBuild.Path.cell, position,
    selection.cellsExact, List.get_eq_getElem]

/-- An enabled barrier cache must drop exactly one marker per crossed empty
cell.  The selected marker remains behind the selected resource's local
tail; dropping it too would violate this equation. -/
theorem barrierCount_drop_exact
    {alpha : List (LogicVar × String)}
    {cells : List (ScheduledHistoryCell alpha)}
    (selection : ScheduledLocalSelection cells) :
    PLeaTTa.barrierCount
        (flattenOwnedAlts (cells.map ScheduledHistoryCell.resource) []) =
      PLeaTTa.barrierCount selection.rest + selection.earlier.length := by
  have cellsResources :
      cells.map ScheduledHistoryCell.resource =
        selection.earlier.map ScheduledHistoryCell.resource ++
          selection.selected.resource ::
            selection.suffix.map ScheduledHistoryCell.resource := by
    simpa using
      congrArg (List.map ScheduledHistoryCell.resource)
        selection.cellsExact
  have earlierEmpty :
      ∀ resource ∈
          selection.earlier.map ScheduledHistoryCell.resource,
        resource.alts = [] := by
    intro resource member
    rcases List.mem_map.mp member with ⟨cell, cellMember, rfl⟩
    exact selection.earlierEmpty cell cellMember
  rw [cellsResources]
  simpa [selection.restExact] using
    (flattenOwnedAlts_first_nonempty_barrierCount
      (selection.earlier.map ScheduledHistoryCell.resource)
      selection.selected.resource
      (selection.suffix.map ScheduledHistoryCell.resource) []
      selection.goals selection.binding selection.localTail earlierEmpty
      selection.selectedHead)

end ScheduledLocalSelection

/-- Exact eager-pull result for an ordered list of locally owned history
cells.  The live constructor exposes the complete structural selection. -/
inductive ScheduledCellBankPull
    {alpha : List (LogicVar × String)}
    (cells : List (ScheduledHistoryCell alpha)) : Type where
  | localLive
      (selection : ScheduledLocalSelection cells) :
      ScheduledCellBankPull cells
  | exhausted
      (pullNone :
        PLeaTTa.pullAux
            (flattenOwnedAlts
              (cells.map ScheduledHistoryCell.resource) []) = none) :
      ScheduledCellBankPull cells

/-- A non-branch at the head of an owned local alternative bank is
impossible.  The existential branch spelling is eliminated only into
`False`; no branch payload is chosen from a proposition. -/
private theorem owned_nonbranch_head_impossible
    {alpha : List (LogicVar × String)}
    (cell : ScheduledHistoryCell alpha)
    {alt : PLeaTTa.Alt} {tail : List PLeaTTa.Alt}
    (altsExact : cell.resource.alts = alt :: tail)
    (notBranch : ∀ goals binding, alt ≠ .br goals binding) : False := by
  rcases cell.ownership.alts_all_branches alt (by rw [altsExact]; simp) with
    ⟨goals, binding, exactBranch⟩
  exact notBranch goals binding exactBranch

/-- Compute the first local branch by source-occurrence order.

Every retained bank is certified branch-only.  Non-branch executable
constructors are inspected as data and discharged through `False`; no
existential ownership witness is eliminated to choose the branch payload. -/
def classifyScheduledCellBank
    {alpha : List (LogicVar × String)} :
    (cells : List (ScheduledHistoryCell alpha)) →
      ScheduledCellBankPull cells
  | [] => .exhausted rfl
  | cell :: cells => by
      cases altsExact : cell.resource.alts with
      | nil =>
          cases classifyScheduledCellBank cells with
          | localLive selection =>
              exact .localLive
                { earlier := cell :: selection.earlier
                  selected := selection.selected
                  suffix := selection.suffix
                  goals := selection.goals
                  binding := selection.binding
                  localTail := selection.localTail
                  rest := selection.rest
                  cellsExact := by
                    simpa using
                      congrArg (List.cons cell) selection.cellsExact
                  earlierEmpty := by
                    intro item member
                    rcases List.mem_cons.mp member with rfl | member
                    · exact altsExact
                    · exact selection.earlierEmpty item member
                  selectedHead := selection.selectedHead
                  restExact := selection.restExact
                  pullExact := by
                    simpa [flattenOwnedAlts, altsExact, PLeaTTa.pullAux] using
                      selection.pullExact }
          | exhausted pullNone =>
              exact .exhausted (by
                simpa [flattenOwnedAlts, altsExact, PLeaTTa.pullAux] using
                  pullNone)
      | cons alt resourceTail =>
          cases alt with
          | br goals binding =>
              exact .localLive
                { earlier := []
                  selected := cell
                  suffix := cells
                  goals := goals
                  binding := binding
                  localTail := resourceTail
                  rest :=
                    resourceTail ++
                      PLeaTTa.Alt.barrier ::
                        flattenOwnedAlts
                          (cells.map ScheduledHistoryCell.resource) []
                  cellsExact := rfl
                  earlierEmpty := by simp
                  selectedHead := altsExact
                  restExact := rfl
                  pullExact := by simp [altsExact, PLeaTTa.pullAux] }
          | barrier =>
              exact False.elim
                (owned_nonbranch_head_impossible cell altsExact
                  (by intros; simp))
          | catchActive frame =>
              exact False.elim
                (owned_nonbranch_head_impossible cell altsExact
                  (by intros; simp))
          | catchDormant frame protectedAlts =>
              exact False.elim
                (owned_nonbranch_head_impossible cell altsExact
                  (by intros; simp))
          | softcutActive frame seenSuccess =>
              exact False.elim
                (owned_nonbranch_head_impossible cell altsExact
                  (by intros; simp))
          | softcutDormant frame protectedAlts =>
              exact False.elim
                (owned_nonbranch_head_impossible cell altsExact
                  (by intros; simp))

/-! ## Source landing proof at the computed data -/

/-- A computed live local bank has the source landing at exactly the same
goals, binding, and residual alternative suffix.  Classification of the
Prop-valued source zipper is used only to prove this proposition; it chooses
no Type-valued payload coordinate. -/
private theorem sourceLanding_of_pull
    {alpha : List (LogicVar × String)}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    {goals : List PLeaTTa.Goal} {binding : Subst}
    {rest : List PLeaTTa.Alt}
    (pullExact :
      PLeaTTa.pullAux (flattenOwnedAlts history.resources []) =
        some (.branch goals binding, rest)) :
    OriginPrefixLanding alpha history.resourceAgreement goals binding rest := by
  rcases AnswerOriginResourceAgrees.classifyPrefix history.resourceAgreement
      with selected | falls
  · rcases selected with ⟨selectedGoals, selectedBinding, selectedRest,
      landing⟩
    have landingPull :
        PLeaTTa.pullAux (flattenOwnedAlts history.resources []) =
          some (.branch selectedGoals selectedBinding, selectedRest) := by
      simpa [ScheduledAnswerHistory.resources] using landing.pullAux_exact
    rw [pullExact] at landingPull
    cases landingPull
    exact landing
  · have none :
        PLeaTTa.pullAux (flattenOwnedAlts history.resources []) = none := by
      simpa [ScheduledAnswerHistory.resources, PLeaTTa.pullAux] using
        falls.pullAux_eq
    rw [pullExact] at none
    contradiction

/-- A computed empty local bank forces source fall-through to the literal
empty endpoint. -/
private theorem sourceFallsThrough_of_pull_none
    {alpha : List (LogicVar × String)}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    (pullNone :
      PLeaTTa.pullAux (flattenOwnedAlts history.resources []) = none) :
    OriginPrefixFallsThrough alpha history.resourceAgreement := by
  rcases AnswerOriginResourceAgrees.classifyPrefix history.resourceAgreement
      with selected | falls
  · rcases selected with ⟨goals, binding, rest, landing⟩
    have some :
        PLeaTTa.pullAux (flattenOwnedAlts history.resources []) =
          some (.branch goals binding, rest) := by
      simpa [ScheduledAnswerHistory.resources] using landing.pullAux_exact
    rw [pullNone] at some
    contradiction
  · exact falls

/-! ## Exact payload-selected outcome -/

/-- One closed local-history pull classified together with the exact
payload/history alignment.  The local constructor stores a history path; its
immutable payload path is the positional image under `alignment`. -/
inductive ScheduledPayloadPullOutcome
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat}
    {segments : List PrologControlSegmentSpineBridge.ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : PrologSourceProductContextBridge.ActiveProductContext}
    {payload :
      PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
        alpha support qterm currentBarrier segments resources inner context
        outer}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    {build : ScheduledHistoryBuild history}
    (alignment : ScheduledPayloadAlignment payload build) : Type where
  | localLive
      (selection : ScheduledLocalSelection build.cells)
      (landing :
        OriginPrefixLanding alpha history.resourceAgreement selection.goals
          selection.binding selection.rest) :
      ScheduledPayloadPullOutcome alignment
  | terminal
      (falls : OriginPrefixFallsThrough alpha history.resourceAgreement) :
      ScheduledPayloadPullOutcome alignment

namespace ScheduledPayloadAlignment

/-- Exact structural coupling of one eager history selection to the dependent
payload suffix at the same occurrence.

The earlier and later history cells are the erasures of the literal payload
prefix and suffix.  The selected payload cell erases to the selected history
cell.  Thus consumers may pattern-match `route.suffix` to recover its exact
dependent `outerAgrees` without searching for a resource-equal occurrence. -/
structure SelectionRoute
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat}
    {segments : List PrologControlSegmentSpineBridge.ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : PrologSourceProductContextBridge.ActiveProductContext}
    {payload :
      PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
        alpha support qterm currentBarrier segments resources inner context
        outer}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    {build : ScheduledHistoryBuild history}
    (alignment : ScheduledPayloadAlignment payload build)
    (selection : ScheduledLocalSelection build.cells) : Type where
  route :
    PayloadRoute payload (alignment.payloadPath selection.path)
  earlierExact :
    selection.earlier =
      ((payloadCells payload).take selection.path.position.val).map
        PayloadCell.historyCell
  selectedExact :
    (alignment.payloadPath selection.path).cell.historyCell =
      selection.selected
  suffixExact :
    selection.suffix =
      ((payloadCells payload).drop (selection.path.position.val + 1)).map
        PayloadCell.historyCell

/-- Build the structural route from the two exact list equations already
carried by the selection and alignment. -/
def selectionRoute
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat}
    {segments : List PrologControlSegmentSpineBridge.ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : PrologSourceProductContextBridge.ActiveProductContext}
    {payload :
      PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
        alpha support qterm currentBarrier segments resources inner context
        outer}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    {build : ScheduledHistoryBuild history}
    (alignment : ScheduledPayloadAlignment payload build)
    (selection : ScheduledLocalSelection build.cells) :
    SelectionRoute alignment selection := by
  let historyPath := selection.path
  let payloadPath := alignment.payloadPath historyPath
  have historyTakeRaw :=
    congrArg (List.take historyPath.position.val) selection.cellsExact
  have historyTake :
      build.cells.take historyPath.position.val = selection.earlier := by
    simpa [historyPath, ScheduledLocalSelection.path,
      ScheduledLocalSelection.position] using historyTakeRaw
  have alignmentTakeRaw :=
    congrArg (List.take historyPath.position.val) alignment.cellsExact
  have alignmentTake :
      build.cells.take historyPath.position.val =
        ((payloadCells payload).take historyPath.position.val).map
          PayloadCell.historyCell := by
    simpa using alignmentTakeRaw
  have historyDropRaw :=
    congrArg (List.drop (historyPath.position.val + 1)) selection.cellsExact
  have historyDrop :
      build.cells.drop (historyPath.position.val + 1) =
        selection.suffix := by
    simpa [historyPath, ScheduledLocalSelection.path,
      ScheduledLocalSelection.position] using historyDropRaw
  have alignmentDropRaw :=
    congrArg (List.drop (historyPath.position.val + 1)) alignment.cellsExact
  have alignmentDrop :
      build.cells.drop (historyPath.position.val + 1) =
        ((payloadCells payload).drop (historyPath.position.val + 1)).map
          PayloadCell.historyCell := by
    simpa using alignmentDropRaw
  exact
    { route := payloadPath.route
      earlierExact := historyTake.symm.trans alignmentTake
      selectedExact :=
        (alignment.selected_history_cell_exact historyPath).trans
          selection.path_cell_exact
      suffixExact := historyDrop.symm.trans alignmentDrop }

/-- The structural selection splits the executable resource spine at exactly
the same occurrence as the dependent payload route. -/
theorem selection_resources_exact
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat}
    {segments : List PrologControlSegmentSpineBridge.ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : PrologSourceProductContextBridge.ActiveProductContext}
    {payload :
      PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
        alpha support qterm currentBarrier segments resources inner context
        outer}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    {build : ScheduledHistoryBuild history}
    (alignment : ScheduledPayloadAlignment payload build)
    (selection : ScheduledLocalSelection build.cells) :
    resources =
      selection.earlier.map
          (fun cell : ScheduledHistoryCell alpha => cell.resource) ++
        selection.selected.resource ::
          selection.suffix.map
            (fun cell : ScheduledHistoryCell alpha => cell.resource) := by
  calc
    resources = (payloadCells payload).map PayloadCell.resource :=
      (payloadCells_map_resource payload).symm
    _ = build.cells.map ScheduledHistoryCell.resource := by
      rw [alignment.cellsExact]
      simp
    _ =
        selection.earlier.map ScheduledHistoryCell.resource ++
          selection.selected.resource ::
            selection.suffix.map ScheduledHistoryCell.resource := by
      simpa using
        congrArg (List.map ScheduledHistoryCell.resource)
          selection.cellsExact

/-- A list has a unique first element which violates an empty-prefix
predicate.  This is the generic maximal-prefix fact coupling the independent
payload classifier to the executable classifier without comparing resource
values after the fact. -/
private theorem first_live_resource_decomposition_unique
    (leftPrefix : List RetainedAlternativeSegment)
    (leftFirst : RetainedAlternativeSegment)
    (leftSuffix : List RetainedAlternativeSegment)
    (rightPrefix : List RetainedAlternativeSegment)
    (rightFirst : RetainedAlternativeSegment)
    (rightSuffix : List RetainedAlternativeSegment)
    (same :
      leftPrefix ++ leftFirst :: leftSuffix =
        rightPrefix ++ rightFirst :: rightSuffix)
    (leftEmpty : ∀ resource ∈ leftPrefix, resource.alts = [])
    (rightEmpty : ∀ resource ∈ rightPrefix, resource.alts = [])
    (leftLive : leftFirst.alts ≠ [])
    (rightLive : rightFirst.alts ≠ []) :
    leftPrefix = rightPrefix ∧ leftFirst = rightFirst ∧
      leftSuffix = rightSuffix := by
  induction leftPrefix generalizing rightPrefix with
  | nil =>
      cases rightPrefix with
      | nil =>
          simpa using List.cons.inj same
      | cons rightHead rightPrefix =>
          have headEq : leftFirst = rightHead := by
            simpa using congrArg List.head? same
          exact False.elim
            (leftLive ((congrArg RetainedAlternativeSegment.alts headEq).trans
              (rightEmpty rightHead (by simp))))
  | cons leftHead leftPrefix inductionHypothesis =>
      cases rightPrefix with
      | nil =>
          have headEq : leftHead = rightFirst := by
            simpa using congrArg List.head? same
          exact False.elim
            (rightLive
              ((congrArg RetainedAlternativeSegment.alts headEq).symm.trans
                (leftEmpty leftHead (by simp))))
      | cons rightHead rightPrefix =>
          have consEq :
              leftHead ::
                  (leftPrefix ++ leftFirst :: leftSuffix) =
                rightHead ::
                  (rightPrefix ++ rightFirst :: rightSuffix) := by
            simpa using same
          have headEq := (List.cons.inj consEq).1
          have tailEq := (List.cons.inj consEq).2
          have leftTailEmpty :
              ∀ resource ∈ leftPrefix, resource.alts = [] := by
            intro resource member
            exact leftEmpty resource (by simp [member])
          have rightTailEmpty :
              ∀ resource ∈ rightPrefix, resource.alts = [] := by
            intro resource member
            exact rightEmpty resource (by simp [member])
          obtain ⟨prefixEq, firstEq, suffixEq⟩ :=
            inductionHypothesis rightPrefix tailEq leftTailEmpty
              rightTailEmpty
          exact ⟨by simp [headEq, prefixEq], firstEq, suffixEq⟩

/-- The generic owned-resource classifier selects exactly the structural
history/payload coordinate already computed by `ScheduledLocalSelection`.

This theorem additionally supplies ranked source-exhaustion work for every
earlier empty cell.  The live partition is therefore ready for the existing
source rejected-prefix and immutable-snapshot activation machinery. -/
theorem selection_partition
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat}
    {segments : List PrologControlSegmentSpineBridge.ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : PrologSourceProductContextBridge.ActiveProductContext}
    {payload :
      PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
        alpha support qterm currentBarrier segments resources inner context
        outer}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    {build : ScheduledHistoryBuild history}
    (alignment : ScheduledPayloadAlignment payload build)
    (selection : ScheduledLocalSelection build.cells) :
    ∃ partition :
        OuterResourceCatchupPartition alpha segments resources context,
      partition.crossedResources =
          selection.earlier.map ScheduledHistoryCell.resource ∧
        partition.first = selection.selected.resource ∧
        partition.survivingResources =
          selection.suffix.map ScheduledHistoryCell.resource ∧
        partition.tail = selection.localTail := by
  have resourcesExact :=
    PLeaTTa.PrologScheduledPayloadLandingBridge.ScheduledPayloadAlignment.selection_resources_exact
      alignment selection
  have earlierEmpty :
      ∀ resource ∈
          selection.earlier.map ScheduledHistoryCell.resource,
        resource.alts = [] := by
    intro resource member
    rcases List.mem_map.mp member with ⟨cell, cellMember, rfl⟩
    exact selection.earlierEmpty cell cellMember
  have selectedLive : selection.selected.resource.alts ≠ [] := by
    rw [selection.selectedHead]
    simp
  cases
      PrologBodyFailureExhaustedResourceTransitionBridge.SourceControlResourceContextAgrees.classifyLocal
        payload.alignment with
  | firstLive partition =>
      have partitionEmpty := partition.crossedWork.all_empty
      have partitionLive : partition.first.alts ≠ [] := by
        rw [partition.firstHead]
        simp
      have same :
          selection.earlier.map ScheduledHistoryCell.resource ++
              selection.selected.resource ::
                selection.suffix.map ScheduledHistoryCell.resource =
            partition.crossedResources ++
              partition.first :: partition.survivingResources :=
        resourcesExact.symm.trans partition.resourcesEq
      obtain ⟨crossedEq, firstEq, survivingEq⟩ :=
        first_live_resource_decomposition_unique
          (selection.earlier.map ScheduledHistoryCell.resource)
          selection.selected.resource
          (selection.suffix.map ScheduledHistoryCell.resource)
          partition.crossedResources partition.first
          partition.survivingResources same earlierEmpty partitionEmpty
          selectedLive partitionLive
      have tailEq : partition.tail = selection.localTail := by
        have heads :
            PLeaTTa.Alt.br partition.goals partition.binding ::
                partition.tail =
              PLeaTTa.Alt.br selection.goals selection.binding ::
                selection.localTail := by
          calc
            _ = partition.first.alts := partition.firstHead.symm
            _ = selection.selected.resource.alts := by rw [firstEq]
            _ = _ := selection.selectedHead
        exact (List.cons.inj heads).2
      exact
        ⟨partition, crossedEq.symm, firstEq.symm, survivingEq.symm,
          tailEq⟩
  | allEmpty partition =>
      have selectedMember : selection.selected.resource ∈ resources := by
        rw [resourcesExact]
        simp
      have selectedEmpty :=
        partition.crossedWork.all_empty selection.selected.resource
          selectedMember
      exact False.elim (selectedLive selectedEmpty)

/-- Total Type-valued classification of one exact local scheduled history. -/
def classifyPull
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat}
    {segments : List PrologControlSegmentSpineBridge.ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : PrologSourceProductContextBridge.ActiveProductContext}
    {payload :
      PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
        alpha support qterm currentBarrier segments resources inner context
        outer}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    {build : ScheduledHistoryBuild history}
    (alignment : ScheduledPayloadAlignment payload build) :
    ScheduledPayloadPullOutcome alignment := by
  cases bankPull : classifyScheduledCellBank build.cells with
  | localLive selection =>
      have historyPull :
          PLeaTTa.pullAux (flattenOwnedAlts history.resources []) =
            some
              (PLeaTTa.PullTarget.branch selection.goals selection.binding,
                selection.rest) := by
        rw [← build.cells_map_resource]
        exact selection.pullExact
      exact .localLive selection
        (sourceLanding_of_pull historyPull)
  | exhausted pullNone =>
      have historyPull :
          PLeaTTa.pullAux (flattenOwnedAlts history.resources []) = none := by
        rw [← build.cells_map_resource]
        exact pullNone
      exact .terminal (sourceFallsThrough_of_pull_none historyPull)

end ScheduledPayloadAlignment

namespace ScheduledPayloadPullOutcome

/-- The exact immutable payload coordinate selected by a local-live outcome;
terminal exhaustion selects no payload cell. -/
def selectedPayloadPath?
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat}
    {segments : List PrologControlSegmentSpineBridge.ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {context : PrologSourceProductContextBridge.ActiveProductContext}
    {payload :
      PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
        alpha support qterm currentBarrier segments resources inner context
        outer}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    {build : ScheduledHistoryBuild history}
    {alignment : ScheduledPayloadAlignment payload build}
    (outcome : ScheduledPayloadPullOutcome alignment) :
    Option (PayloadPath payload) :=
  match outcome with
  | .localLive selection _ =>
      some (alignment.payloadPath selection.path)
  | .terminal _ => none

end ScheduledPayloadPullOutcome

end PLeaTTa.PrologScheduledPayloadLandingBridge
