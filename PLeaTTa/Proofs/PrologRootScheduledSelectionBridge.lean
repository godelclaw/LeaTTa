-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologRootScheduledSelectionBridge
Purpose: Factor literal-root activation through the first root-closed
  scheduled local selection, before success or rejection is decided.
Trusted boundary: none
Main exports:
  RootClosedSingletonSelectedPrefix,
  RepresentativeRootCallSuccessorFacts.toScheduledSelected
-/
import PLeaTTa.Proofs.PrologScheduledSuccessPrefixBridge
import PLeaTTa.Proofs.PrologRootCallReadyBridge

namespace PLeaTTa.PrologRootScheduledSelectionBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologHeterogeneousPrefixBridge
open PrologCurrentSessionPayloadTransitionBridge
open PrologNestedCallReadyBridge
open PrologOrdinaryStepBridge
open PrologPersistentFreeActivePayloadBridge
open PrologPersistentFreeScheduledPayloadBridge
open PrologProductResourceContextBridge
open PrologRootCallReadyBridge
open PrologRootClosedAnswerBridge
open PrologRetainedPayloadSnapshotBridge
open PrologScheduledHistoryBuildBridge
open PrologScheduledPayloadLandingBridge
open PrologScheduledPayloadPathBridge
open PrologScheduledPayloadPostHeadBridge
open PrologScheduledPayloadResumeBridge
open PrologScheduledSuccessPrefixBridge

/-- Type-valued root prefix ending at the first local scheduled selection.

The carrier deliberately stops before deciding whether the selected source
head succeeds or fails.  Both continuations therefore share the same exact
root activation, body administration, answer scheduling, occurrence cell,
and selected transition.  Source and fine costs are indices of the real
runs, not caller-provided equalities. -/
structure RootClosedSingletonSelectedPrefix
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (sourceStart : PeTTaSpec.PrologCore.GoalSemantics.State)
    (fineStart : DemandDrivenCallStep.FineConf)
    (sourceEvents : List Observation)
    (sourceCost fineCost : Nat)
    (retainedCursor : PreparedCursor)
    (retainedSupport : List (LogicVar × String))
    (retainedQuery : Atom) : Type where
  before : RepresentativePersistentFreeScheduledPayloadState
  ready : RootClosedAnswerReady before
  selection : ScheduledLocalSelection ready.result.historyBuild.cells
  scope : CutScopeId
  transition :
    ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
      before.carrier.index.session
  sourceSteps :
    StepsN sourceCost sourceStart sourceEvents before.carrier.sourceState
  fineSteps :
    DemandDrivenCallStep.StepsN prog gt fineCost fineStart
      before.carrier.fineState
  selectedResourceExact :
    selection.selected.resource = before.carrier.index.active
  selectedCursorExact :
    selection.selected.cursor = retainedCursor
  retainedCursorExact :
    retainedCursor =
      before.carrier.index.finish.advance before.carrier.index.branch
        before.carrier.index.branchTail
  supportExact : before.carrier.index.support = retainedSupport
  selectedQueryExact : selection.selected.resource.qterm = retainedQuery
  localTailEmpty : selection.localTail = []
  freshFrontierExact :
    before.carrier.index.freshFrontier =
      PrologAlphaFreshFrontierBridge.AlphaFreshFrontier
        before.carrier.index.alpha
  below :
    PLeaTTa.ConfBelowResolutionCounter before.carrier.index.openConf.toConf

namespace RepresentativeRootCallSuccessorFacts

/-- A literal root activation with one retained executable alternative
reaches the first local scheduled transition after the selected body's
certified administrative prefix and answer.

The theorem is intentionally root-closed.  Older resources, outer source
segments, caller references, and base alternatives remain fixed to the
emptiness facts produced by `activate_literal_root`; supporting non-root
positions is a separate resource-zipper obligation. -/
theorem toScheduledSelected
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {session : Session} {rootFine : OpenConf} {rootScope : CutScopeId}
    {predicate : String} {referencePayload : List Term}
    {referenceBindings : Substitution}
    {args : List Atom} {res : Atom} {binding : Subst}
    {branches : List PLeaTTa.Alt} {finalCounter callerBarrier : Nat}
    {rejects : Nat} {skippedBranches : List ClauseBranch}
    {skippedClauses : List PLeaTTa.Clause}
    {finish : PreparedCursor} {firstBranch : ClauseBranch}
    {firstClause : PLeaTTa.Clause} {branchTail : List ClauseBranch}
    {clauseTail : List PLeaTTa.Clause} {altTail : List PLeaTTa.Alt}
    {firstCopied : PLeaTTa.Clause}
    {firstIndependentResult : Substitution}
    {firstRepresentative : TreeSubstitution}
    {firstNextAlpha : List (LogicVar × String)}
    {firstSourceCanonical firstFlattened : TreeSubstitution}
    {firstInstalled : Subst}
    {active : RepresentativeActivePayloadState}
    (facts :
      RepresentativeRootCallSuccessorFacts prog gt alpha support canonical
        referenceBase session rootFine rootScope predicate referencePayload
        referenceBindings args res binding branches finalCounter callerBarrier
        rejects skippedBranches skippedClauses finish firstBranch firstClause
        branchTail clauseTail altTail firstCopied firstIndependentResult
        firstRepresentative firstNextAlpha firstSourceCanonical firstFlattened
        firstInstalled active)
    {administrativeCount : Nat}
    (administration :
      AdministrativeStepsN administrativeCount
        active.carrier.index.bodyReferences [])
    (executableBodyEmpty : active.carrier.index.bodyExecutables = [])
    {retainedGoals : List PLeaTTa.Goal} {retainedBinding : Subst}
    (retainedSingleton :
      altTail = [.br retainedGoals retainedBinding]) :
    Nonempty
      (RootClosedSingletonSelectedPrefix prog gt
        (.running session
          (.task rootScope [.call predicate referencePayload]
            referenceBindings))
        (.ready rootFine)
        [.opened (requestFor predicate referencePayload referenceBindings)]
        ((rejects + 2) + (administrativeCount + 1)) 3
        (finish.advance firstBranch branchTail) support
        rootFine.control.qterm) := by
  let normalized :=
    RepresentativeActivePayloadState.afterAdministrative prog gt active
      administration
  have normalizedReferencesEmpty :
      normalized.carrier.index.bodyReferences = [] := by
    rfl
  have normalizedExecutablesEmpty :
      normalized.carrier.index.bodyExecutables = [] := by
    change active.carrier.index.bodyExecutables = []
    exact executableBodyEmpty
  let before :=
    RepresentativeActivePayloadState.afterBodyAnswer prog gt normalized
      normalizedReferencesEmpty normalizedExecutablesEmpty
  have callerEmpty : before.carrier.index.callerReferences = [] := by
    simpa [before, normalized] using facts.callerReferencesEmpty
  have outerEmpty : before.carrier.index.outer = [] := by
    simpa [before, normalized] using facts.outerEmpty
  have baseEmpty : before.carrier.index.baseAlts = [] := by
    simpa [before, normalized] using facts.baseAltsEmpty
  have resourcesEmpty : before.carrier.index.resources = [] := by
    simpa [before, normalized] using facts.resourcesEmpty
  have allOuterEmpty :
      ∀ segment, segment ∈ before.carrier.index.outer →
        segment.references = [] := by
    rw [outerEmpty]
    simp
  let ready :=
    PrologRootClosedAnswerBridge.RepresentativePersistentFreeScheduledPayloadState.rootClosedAnswerReady
      before
      callerEmpty allOuterEmpty baseEmpty
  have activeAltsShape :
      before.carrier.index.active.alts =
        [.br retainedGoals retainedBinding] := by
    calc
      before.carrier.index.active.alts = active.carrier.index.active.alts := by
        simp [before, normalized]
      _ = altTail := facts.activeAltsExact
      _ = [.br retainedGoals retainedBinding] := retainedSingleton
  have historyResources :
      ready.result.history.resources = [before.carrier.index.active] := by
    rw [ready.result.resourcesExact, currentAnswerHistory_resources,
      resourcesEmpty]
    rfl
  have cellsLength : ready.result.historyBuild.cells.length = 1 := by
    have mapped := congrArg List.length
      ready.result.historyBuild.cells_map_resource
    rw [historyResources] at mapped
    simpa using mapped
  obtain ⟨only, cellsExact⟩ := List.length_eq_one_iff.mp cellsLength
  have onlyResource : only.resource = before.carrier.index.active := by
    have mapped := ready.result.historyBuild.cells_map_resource
    rw [cellsExact, historyResources] at mapped
    exact (List.cons.inj mapped).1
  have tailCellsEmpty :
      payloadCells
          (ActiveProductPayloadContextAt.outerPayload
            before.carrier.payloadContext) = [] := by
    have mapped := payloadCells_map_resource
      (ActiveProductPayloadContextAt.outerPayload before.carrier.payloadContext)
    have mappedEmpty := mapped.trans resourcesEmpty
    apply List.eq_nil_of_length_eq_zero
    have lengths := congrArg List.length mappedEmpty
    simpa using lengths
  have initialCellsExact :
      ready.result.historyBuild.cells =
        (currentAnswerHistoryBuild before).cells := by
    rw [ready.result.historyCellsExact, tailCellsEmpty]
    simp
  have onlyCursor :
      only.cursor =
        before.carrier.index.finish.advance before.carrier.index.branch
          before.carrier.index.branchTail := by
    have mapped := congrArg (List.map ScheduledHistoryCell.cursor)
      initialCellsExact
    rw [cellsExact] at mapped
    simpa [currentAnswerHistoryBuild, ScheduledHistoryBuild.cells] using
      (List.cons.inj mapped).1
  have sourceRun :
      StepsN ((rejects + 2) + (administrativeCount + 1))
        (.running session
          (.task rootScope [.call predicate referencePayload]
            referenceBindings))
        [.opened (requestFor predicate referencePayload referenceBindings)]
        before.carrier.sourceState := by
    have activeToBefore :
        CertifiedPrefix prog gt
          [.administrative administrativeCount, .bodyAnswer]
          (.active
            (PLeaTTa.PrologPersistentFreeActivePayloadBridge.RepresentativePersistentFreeActivePayloadState.ofLegacy
              active))
          (.scheduled before) :=
      .cons (.administrative active administration)
        (.cons
          (.bodyAnswer normalized normalizedReferencesEmpty
            normalizedExecutablesEmpty)
          (.nil (.scheduled before)))
    have combined := facts.sourceSteps.trans activeToBefore.sourceSteps
    simpa [
      PLeaTTa.PrologHeterogeneousPrefixBridge.TransitionSchedule.sourceCost,
      PLeaTTa.PrologHeterogeneousPrefixBridge.TransitionSchedule.sourceEvents,
      PLeaTTa.PrologHeterogeneousPrefixBridge.TransitionKind.sourceCost,
      PLeaTTa.PrologHeterogeneousPrefixBridge.TransitionKind.sourceEvents,
      ProductPhaseState.sourceState,
      PLeaTTa.PrologPersistentFreeActivePayloadBridge.RepresentativePersistentFreeActivePayloadState.ofLegacy]
      using combined
  have fineRun :
      DemandDrivenCallStep.StepsN prog gt 3 (.ready rootFine)
        before.carrier.fineState := by
    have activeToBefore :
        CertifiedPrefix prog gt
          [.administrative administrativeCount, .bodyAnswer]
          (.active
            (PLeaTTa.PrologPersistentFreeActivePayloadBridge.RepresentativePersistentFreeActivePayloadState.ofLegacy
              active))
          (.scheduled before) :=
      .cons (.administrative active administration)
        (.cons
          (.bodyAnswer normalized normalizedReferencesEmpty
            normalizedExecutablesEmpty)
          (.nil (.scheduled before)))
    have combined := facts.fineSteps.trans activeToBefore.fineSteps
    simpa [
      PLeaTTa.PrologHeterogeneousPrefixBridge.TransitionSchedule.fineCost,
      PLeaTTa.PrologHeterogeneousPrefixBridge.TransitionKind.fineCost,
      ProductPhaseState.fineState,
      PLeaTTa.PrologPersistentFreeActivePayloadBridge.RepresentativePersistentFreeActivePayloadState.ofLegacy]
      using combined
  cases classified :
      ScheduledPayloadAlignment.classifyPull ready.payloadAlignment with
  | terminal falls =>
      have impossible := falls.pullAux_eq
      change
        PLeaTTa.pullAux
            (flattenOwnedAlts ready.result.history.resources []) =
          PLeaTTa.pullAux [] at impossible
      rw [historyResources] at impossible
      simp only [flattenOwnedAlts_cons, flattenOwnedAlts_nil] at impossible
      rw [activeAltsShape] at impossible
      change PLeaTTa.pullAux
          [.br retainedGoals retainedBinding, .barrier] =
        PLeaTTa.pullAux [] at impossible
      simp [PLeaTTa.pullAux] at impossible
  | localLive selection landing =>
      have decomposition :
          [only] =
            selection.earlier ++ selection.selected :: selection.suffix :=
        cellsExact.symm.trans selection.cellsExact
      have lengths := congrArg List.length decomposition
      simp only [List.length_cons, List.length_nil, List.length_append] at lengths
      have earlierLength : selection.earlier.length = 0 := by omega
      have suffixLength : selection.suffix.length = 0 := by omega
      have earlierExact : selection.earlier = [] :=
        List.length_eq_zero_iff.mp earlierLength
      have suffixExact : selection.suffix = [] :=
        List.length_eq_zero_iff.mp suffixLength
      have selectedExact : selection.selected = only := by
        rw [earlierExact, suffixExact] at decomposition
        simpa using (List.cons.inj decomposition).1.symm
      have selectedResourceExact :
          selection.selected.resource = before.carrier.index.active := by
        rw [selectedExact, onlyResource]
      have selectedCursorExact :
          selection.selected.cursor =
            before.carrier.index.finish.advance before.carrier.index.branch
              before.carrier.index.branchTail := by
        rw [selectedExact, onlyCursor]
      have rootRetainedCursorExact :
          before.carrier.index.finish.advance before.carrier.index.branch
              before.carrier.index.branchTail =
            finish.advance firstBranch branchTail := by
        change
          active.carrier.index.finish.advance active.carrier.index.branch
              active.carrier.index.branchTail =
            finish.advance firstBranch branchTail
        exact facts.retainedCursorExact
      have supportExact : before.carrier.index.support = support := by
        change active.carrier.index.support = support
        exact facts.carrierSupport
      have selectedQueryExact :
          selection.selected.resource.qterm = rootFine.control.qterm := by
        rw [selectedResourceExact]
        change active.carrier.index.active.qterm = rootFine.control.qterm
        have exactQuery :=
          congrArg RetainedAlternativeSegment.qterm facts.activeResourceExact
        simpa [retainedTailResource] using exactQuery
      have localTailEmpty : selection.localTail = [] := by
        have selectedHead := selection.selectedHead
        rw [selectedResourceExact, activeAltsShape] at selectedHead
        exact (List.cons.inj selectedHead).2.symm
      obtain ⟨transition⟩ :=
        ScheduledPayloadAlignment.selectAndAdvanceHead
          ready.payloadAlignment selection before.carrier.index.session
      have freshFrontierExact :
          before.carrier.index.freshFrontier =
            PrologAlphaFreshFrontierBridge.AlphaFreshFrontier
              before.carrier.index.alpha := by
        change active.carrier.index.freshFrontier =
          PrologAlphaFreshFrontierBridge.AlphaFreshFrontier
            active.carrier.index.alpha
        exact facts.freshFrontierExact
      have below :
          PLeaTTa.ConfBelowResolutionCounter
            before.carrier.index.openConf.toConf := by
        simpa [before, normalized] using facts.below
      exact
        ⟨⟨before, ready, selection,
          (ready.payloadAlignment.payloadPath selection.path).cell.currentScope,
          transition, sourceRun, fineRun, selectedResourceExact,
          selectedCursorExact.trans rootRetainedCursorExact,
          rootRetainedCursorExact.symm, supportExact, selectedQueryExact,
          localTailEmpty, freshFrontierExact, below⟩⟩

end RepresentativeRootCallSuccessorFacts

end PLeaTTa.PrologRootScheduledSelectionBridge
