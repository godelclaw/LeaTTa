-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologScheduledPayloadResumeBridge
Purpose: Specialize exact scheduled-answer propagation to the live
  representative payload carrier without restoring frozen substitutions
Trusted boundary: none
Main exports:
  RepresentativePrivateScheduledResume,
  RepresentativePrivateScheduledResume.sourceStepsN,
  RepresentativeScheduledPayloadState.privateScheduledResume
-/
import PLeaTTa.Proofs.PrologHeterogeneousPrefixBridge
import PLeaTTa.Proofs.PrologScheduledAnswerPropagationBridge

namespace PLeaTTa.PrologScheduledPayloadResumeBridge

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologCurrentSessionPayloadTransitionBridge
open PrologHeterogeneousPrefixBridge
open PrologNestedCallChainBridge
open PrologNestedCallReadyBridge
open PrologProductResourceContextBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
open PrologScheduledAnswerPropagationBridge
open PrologSourceProductContextBridge

/-! ## Representative extraction -/

/-- Every active payload carrier exposes one coherent cumulative residual
representative as Type-valued data.

The carrier's own head payload supplies the existential witness.  Selecting
it once here prevents later scheduled-answer proofs from independently
choosing different residual orientations. -/
theorem
    _root_.PLeaTTa.PrologNestedCallChainBridge.ActivePayloadState.existsRepresentative
    (state : ActivePayloadState) :
    ∃ representative : RepresentativeActivePayloadState,
      representative.carrier = state := by
  have payload := state.agreement.core.control.ready.2.2.2.headPayload
  obtain ⟨representative, cumulative⟩ := payload.valuation.existsWith
  exact
    ⟨{ carrier := state
       representative := representative
       cumulative := cumulative },
      rfl⟩

/-! ## The live current-cell history -/

/-- The currently scheduled predicate supplies the first answer-history cell
from its own retained resource and advanced cursor.

The immutable payload snapshot is deliberately absent from this definition.
Snapshots restore pre-head substitutions only after failure/backtracking;
successful answer propagation must carry the live `current`, runtime state,
and representative forward unchanged. -/
def currentAnswerHistory
    (state : RepresentativeScheduledPayloadState) :
    ScheduledAnswerHistory state.carrier.index.alpha
      (ScheduledAnswerHistory.oneLevelSource
        state.carrier.index.callerScope state.carrier.index.predicateScope
        state.carrier.index.current
        (state.carrier.index.finish.advance state.carrier.index.branch
          state.carrier.index.branchTail))
      (ScheduledAnswerHistory.oneLevelNext
        state.carrier.index.callerScope state.carrier.index.predicateScope
        (state.carrier.index.finish.advance state.carrier.index.branch
          state.carrier.index.branchTail)) :=
  ScheduledAnswerHistory.oneLevel
    state.carrier.index.callerScope state.carrier.index.predicateScope
    state.carrier.index.current
    (state.carrier.index.finish.advance state.carrier.index.branch
      state.carrier.index.branchTail)
    state.carrier.index.active
    (_root_.PLeaTTa.PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.activeOwnership
      state.carrier.payloadContext)

@[simp] theorem currentAnswerHistory_resources
    (state : RepresentativeScheduledPayloadState) :
    (currentAnswerHistory state).resources = [state.carrier.index.active] :=
  ScheduledAnswerHistory.oneLevel_resources _ _ _ _ _ _

/-- Private scheduling changes only control ownership; the answer packet
retains the live cumulative source substitution selected by the current
clause body. -/
@[simp] theorem currentAnswerHistory_bindings
    (state : RepresentativeScheduledPayloadState) :
    (currentAnswerHistory state).bindings = state.carrier.index.current := rfl

/-! ## One exact live private resume -/

/-- One live scheduled answer crossing the next older payload cell.

All list decompositions are literal equalities against `before`; `outerCell`
couples the older control segment, source frame, cursor, resource ownership,
and immutable snapshot in one object.  Only its structural ownership is used
on this successful path.  No snapshot field can generate the target
substitution, persistent state, representative, or answer payload. -/
structure RepresentativePrivateScheduledResume
    (before : RepresentativeScheduledPayloadState) where
  outerSegment : PrologControlSegmentSpineBridge.ControlSegment
  remainingSegments : List PrologControlSegmentSpineBridge.ControlSegment
  outerResource : RetainedAlternativeSegment
  remainingResources : List RetainedAlternativeSegment
  outerFrame : ActiveProductFrame
  remainingContext : ActiveProductContext
  segmentsExact :
    before.carrier.index.outer = outerSegment :: remainingSegments
  resourcesExact :
    before.carrier.index.resources = outerResource :: remainingResources
  contextExact :
    before.carrier.index.context = outerFrame :: remainingContext
  outerCell :
    HeadCell before.carrier.index.alpha before.carrier.index.support
      outerSegment remainingSegments outerResource
      before.carrier.index.callerScope outerFrame
  sourceExact :
    before.carrier.index.source =
      ActiveProductContext.plug remainingContext
        (privateResumeSource (currentAnswerHistory before)
          outerFrame.callerScope before.carrier.index.callerScope
          outerCell.cursor outerSegment.references)

namespace RepresentativePrivateScheduledResume

/-- The structurally certified one-frame resume.  Its ownership comes from
the same `outerCell` that fixes the source frame and retained cursor. -/
def resume
    {before : RepresentativeScheduledPayloadState}
    (facts : RepresentativePrivateScheduledResume before) :
    PrivateScheduledResume before.carrier.index.alpha
      (currentAnswerHistory before) facts.outerFrame.callerScope
      before.carrier.index.callerScope facts.outerCell.cursor
      facts.outerSegment.references facts.outerResource :=
  PrivateScheduledResume.ofHistory (currentAnswerHistory before)
    facts.outerFrame.callerScope before.carrier.index.callerScope
    facts.outerCell.cursor facts.outerSegment.references facts.outerResource
    facts.outerCell.ownership

/-- Literal source successor after this one private propagation layer. -/
def targetSource
    {before : RepresentativeScheduledPayloadState}
    (facts : RepresentativePrivateScheduledResume before) : Search :=
  ActiveProductContext.plug facts.remainingContext
    (privateResumeTarget (currentAnswerHistory before)
      facts.outerFrame.callerScope before.carrier.index.callerScope
      facts.outerCell.cursor facts.outerSegment.references)

/-- The target source session is the live current session, not a snapshot. -/
def targetSourceState
    {before : RepresentativeScheduledPayloadState}
    (facts : RepresentativePrivateScheduledResume before) : State :=
  .running before.carrier.index.session facts.targetSource

/-- Literal current source session carried by the historical target. -/
def targetSession
    {before : RepresentativeScheduledPayloadState}
    (_facts : RepresentativePrivateScheduledResume before) : Session :=
  before.carrier.index.session

/-- Literal current fine configuration carried by the historical target. -/
def targetOpenConf
    {before : RepresentativeScheduledPayloadState}
    (_facts : RepresentativePrivateScheduledResume before) : OpenConf :=
  before.carrier.index.openConf

/-- The fine machine already exposes the caller continuation; source-only
scheduling therefore leaves its literal open configuration unchanged. -/
def targetFineState
    {before : RepresentativeScheduledPayloadState}
    (_facts : RepresentativePrivateScheduledResume before) :
    DemandDrivenCallStep.FineConf :=
  before.carrier.fineState

/-- Successful propagation carries the live cumulative representative
forward; it never restores `outerCell.snapshot.residualRepresentative`. -/
def targetRepresentative
    {before : RepresentativeScheduledPayloadState}
    (_facts : RepresentativePrivateScheduledResume before) :
    TreeSubstitution :=
  before.representative

/-- No payload cell is retired or duplicated by private scheduling. -/
def targetCellIdentities
    {before : RepresentativeScheduledPayloadState}
    (_facts : RepresentativePrivateScheduledResume before) :
    List PrologNestedCallChainBridge.PayloadCellIdentity :=
  before.carrier.cellIdentities

/-- One private live resume is exactly one silent source transition and keeps
the current persistent session definitionally unchanged. -/
theorem sourceStep
    {before : RepresentativeScheduledPayloadState}
    (facts : RepresentativePrivateScheduledResume before) :
    RawStep before.carrier.index.session before.carrier.index.source [] .none
      before.carrier.index.session (.running facts.targetSource) := by
  rw [facts.sourceExact]
  exact
    ActiveProductContext.liftProgress facts.remainingContext
      (facts.resume.sourceStep before.carrier.index.session)
      (by simp [Trace.AnswerFree])

/-- Exact step-indexed form of `sourceStep`. -/
theorem sourceStepsN
    {before : RepresentativeScheduledPayloadState}
    (facts : RepresentativePrivateScheduledResume before) :
    StepsN 1 before.carrier.sourceState [] facts.targetSourceState := by
  exact .succ 0 _ _ _ [] [] (.ordinary _ [] _ _ _ facts.sourceStep) (.zero _)

/-- The fine side takes exactly zero steps across this source-only resume. -/
theorem fineStepsN
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeScheduledPayloadState}
    (facts : RepresentativePrivateScheduledResume before) :
    DemandDrivenCallStep.StepsN prog gt 0 before.carrier.fineState
      facts.targetFineState :=
  .zero _

@[simp] theorem targetRepresentative_exact
    {before : RepresentativeScheduledPayloadState}
    (facts : RepresentativePrivateScheduledResume before) :
    facts.targetRepresentative = before.representative := rfl

@[simp] theorem targetSession_exact
    {before : RepresentativeScheduledPayloadState}
    (facts : RepresentativePrivateScheduledResume before) :
    facts.targetSession = before.carrier.index.session := rfl

@[simp] theorem targetOpenConf_exact
    {before : RepresentativeScheduledPayloadState}
    (facts : RepresentativePrivateScheduledResume before) :
    facts.targetOpenConf = before.carrier.index.openConf := rfl

@[simp] theorem targetCellIdentities_exact
    {before : RepresentativeScheduledPayloadState}
    (facts : RepresentativePrivateScheduledResume before) :
    facts.targetCellIdentities = before.carrier.cellIdentities := rfl

/-- The new historical right region contains exactly the current resource
followed by the older resource certified by this payload cell. -/
theorem resumedResources_exact
    {before : RepresentativeScheduledPayloadState}
    (facts : RepresentativePrivateScheduledResume before) :
    (currentAnswerHistory before).resources ++ [facts.outerResource] =
      [before.carrier.index.active, facts.outerResource] := by
  simp

/-- The complete live resource bank is unchanged: the historical prefix is
exactly the current active resource plus the first older resource, followed
by the untouched older tail. -/
theorem resumedResourceBank_exact
    {before : RepresentativeScheduledPayloadState}
    (facts : RepresentativePrivateScheduledResume before) :
    ((currentAnswerHistory before).resources ++ [facts.outerResource]) ++
        facts.remainingResources =
      before.carrier.index.active :: before.carrier.index.resources := by
  rw [currentAnswerHistory_resources, facts.resourcesExact]
  rfl

/-- Exactly two resource markers inhabit the new scheduled right region;
the count is derived from its actual ownership certificate. -/
theorem resumedBarrierCount_exact
    {before : RepresentativeScheduledPayloadState}
    (facts : RepresentativePrivateScheduledResume before) :
    PLeaTTa.barrierCount
        (flattenOwnedAlts
          ((currentAnswerHistory before).resources ++
            [facts.outerResource]) []) =
      2 := by
  have count :=
    PrologAnswerResourceBridge.AnswerOriginResourceAgrees.scheduled_barrierCount_exact
      facts.resume.rightRegion
  simpa using count

/-- A successful resume cannot silently restore the older immutable snapshot.
The target representative is the live one even when the two values are
observably different. -/
theorem targetRepresentative_ne_snapshot_of_ne
    {before : RepresentativeScheduledPayloadState}
    (facts : RepresentativePrivateScheduledResume before)
    (different :
      before.representative ≠
        facts.outerCell.snapshot.residualRepresentative) :
    facts.targetRepresentative ≠
      facts.outerCell.snapshot.residualRepresentative := by
  simpa using different

end RepresentativePrivateScheduledResume

/-! ## Live producer -/

/-- An empty current caller continuation and one older live predicate frame
produce the exact private scheduled-resume certificate.

The producer eliminates `before`'s own payload tail.  Thus the outer cursor,
resource ownership, frame, control segment, and snapshot all come from the
same dependent zipper constructor.  The snapshot itself is retained only as
identity evidence and is never read to construct the successful target.
[SPEC metta.pl:251-256; ISO:SLD leftmost depth-first selection] -/
theorem
    _root_.PLeaTTa.PrologHeterogeneousPrefixBridge.RepresentativeScheduledPayloadState.privateScheduledResume
    (before : RepresentativeScheduledPayloadState)
    (referenceEmpty : before.carrier.index.callerReferences = [])
    (outerNonempty : before.carrier.index.context ≠ []) :
    Nonempty (RepresentativePrivateScheduledResume before) := by
  let payloadTail :=
    ActiveProductPayloadContext.outerPayload before.carrier.payloadContext
  have lengths :=
    SourceControlResourcePayloadContextAgrees.lengths_eq payloadTail
  have segmentsNonempty : before.carrier.index.outer ≠ [] := by
    intro empty
    apply outerNonempty
    apply List.eq_nil_of_length_eq_zero
    rw [lengths.1, empty]
    rfl
  have resourcesNonempty : before.carrier.index.resources ≠ [] := by
    intro empty
    have segmentsLengthZero : before.carrier.index.outer.length = 0 := by
      rw [lengths.2, empty]
      rfl
    exact segmentsNonempty (List.eq_nil_of_length_eq_zero segmentsLengthZero)
  cases segmentsExact : before.carrier.index.outer with
  | nil => exact (segmentsNonempty segmentsExact).elim
  | cons outerSegment remainingSegments =>
      cases resourcesExact : before.carrier.index.resources with
      | nil => exact (resourcesNonempty resourcesExact).elim
      | cons outerResource remainingResources =>
          cases contextExact : before.carrier.index.context with
          | nil => exact (outerNonempty contextExact).elim
          | cons outerFrame remainingContext =>
              have shaped :
                  SourceControlResourcePayloadContextAgrees
                    before.carrier.index.alpha before.carrier.index.support
                    before.carrier.index.qterm
                    before.carrier.index.callerBarrier
                    (outerSegment :: remainingSegments)
                    (outerResource :: remainingResources)
                    before.carrier.index.callerScope
                    (outerFrame :: remainingContext)
                    before.carrier.index.outerScope := by
                simpa only [segmentsExact, resourcesExact, contextExact] using
                  payloadTail
              let cell :=
                SourceControlResourcePayloadContextAgrees.headCell shaped
              refine ⟨{
                outerSegment := outerSegment
                remainingSegments := remainingSegments
                outerResource := outerResource
                remainingResources := remainingResources
                outerFrame := outerFrame
                remainingContext := remainingContext
                segmentsExact := segmentsExact
                resourcesExact := resourcesExact
                contextExact := contextExact
                outerCell := cell
                sourceExact := ?_ }⟩
              rw [before.carrier.agreement.core.sourceShape, referenceEmpty,
                contextExact]
              simp only [ActiveProductContext.plug_cons]
              simp only [ActiveProductFrame.wrap, privateResumeSource,
                enclosingHead]
              rw [cell.predicateScopeExact, cell.retainedShape,
                cell.callerRestExact]
              rfl

/-- Absorb the complete maximal empty-caller prefix of a live scheduled
payload state.

The source cost is computed from the literal outer control spine.  The fine
machine takes zero steps because all of these source product frames have
already been flattened into its one retained alternative bank.  No
intermediate historical state is admitted into the global phase vocabulary.
[SPEC metta.pl:251-256; ISO:SLD leftmost depth-first selection] -/
theorem
    _root_.PLeaTTa.PrologHeterogeneousPrefixBridge.RepresentativeScheduledPayloadState.absorbPrivatePrefix
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (before : RepresentativeScheduledPayloadState)
    (referenceEmpty : before.carrier.index.callerReferences = []) :
    ∃ target : Search,
      StepsN (privateResumeCost before.carrier.index.outer)
        before.carrier.sourceState []
        (.running before.carrier.index.session target) ∧
      DemandDrivenCallStep.StepsN prog gt 0 before.carrier.fineState
        before.carrier.fineState := by
  let payloadTail :=
    ActiveProductPayloadContext.outerPayload before.carrier.payloadContext
  let alignment :=
    SourceControlResourcePayloadContextAgrees.alignment payloadTail
  let target :=
    absorbContextTarget before.carrier.index.context
      (currentAnswerHistory before).bindings
      (ScheduledAnswerHistory.oneLevelSource
        before.carrier.index.callerScope before.carrier.index.predicateScope
        before.carrier.index.current
        (before.carrier.index.finish.advance before.carrier.index.branch
          before.carrier.index.branchTail))
      (ScheduledAnswerHistory.oneLevelNext
        before.carrier.index.callerScope before.carrier.index.predicateScope
        (before.carrier.index.finish.advance before.carrier.index.branch
          before.carrier.index.branchTail))
  have sourceSteps :=
    absorbAlignedContext alignment (currentAnswerHistory before) rfl
      before.carrier.index.session
  have sourceExact :
      before.carrier.index.source =
        ActiveProductContext.plug before.carrier.index.context
          (ScheduledAnswerHistory.oneLevelSource
            before.carrier.index.callerScope before.carrier.index.predicateScope
            before.carrier.index.current
            (before.carrier.index.finish.advance before.carrier.index.branch
              before.carrier.index.branchTail)) := by
    rw [before.carrier.agreement.core.sourceShape, referenceEmpty]
    rfl
  refine ⟨target, ?_, .zero _⟩
  change
    StepsN (privateResumeCost before.carrier.index.outer)
      (.running before.carrier.index.session before.carrier.index.source) []
      (.running before.carrier.index.session target)
  rw [sourceExact]
  exact sourceSteps

/-- If every older caller tail is empty, the live source performs exactly one
silent step per outer payload frame and the fine machine remains literal. -/
theorem
    _root_.PLeaTTa.PrologHeterogeneousPrefixBridge.RepresentativeScheduledPayloadState.absorbAllEmptyFrames
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (before : RepresentativeScheduledPayloadState)
    (referenceEmpty : before.carrier.index.callerReferences = [])
    (allEmpty :
      ∀ segment ∈ before.carrier.index.outer, segment.references = []) :
    ∃ target : Search,
      StepsN before.carrier.index.outer.length before.carrier.sourceState []
        (.running before.carrier.index.session target) ∧
      DemandDrivenCallStep.StepsN prog gt 0 before.carrier.fineState
        before.carrier.fineState := by
  obtain ⟨target, sourceSteps, fineSteps⟩ :=
    before.absorbPrivatePrefix (prog := prog) (gt := gt) referenceEmpty
  refine ⟨target, ?_, fineSteps⟩
  simpa [privateResumeCost_eq_length_of_all_empty
    before.carrier.index.outer allEmpty] using sourceSteps

end PLeaTTa.PrologScheduledPayloadResumeBridge
