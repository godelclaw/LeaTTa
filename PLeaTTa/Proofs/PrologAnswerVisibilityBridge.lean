-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologAnswerVisibilityBridge
Purpose: Classify one answer as public or collector-private from the exact
  source-collection/executable-frame occurrence correspondence
Trusted boundary: none
Main exports: AnswerVisibility, AnswerVisibility.classify,
  RepresentativeScheduledPayloadState.sourceCellsEmpty,
  RootClosedAnswerReady.withPublicAnswerOfOccurrences
-/
import PLeaTTa.Proofs.PrologScheduledAnswerValueBridge
import PLeaTTa.Proofs.PrologFindallFrameZipperBridge

namespace PLeaTTa.PrologAnswerVisibilityBridge

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open CompilerAdequacy
open DemandDrivenStep
open PrologFindallCopyBridge
open PrologFindallFrameZipperBridge
open PrologHeterogeneousPrefixBridge
open PrologMguBridge
open PrologOrdinaryStepBridge
open PrologProductSchedulingBridge
open PrologRecursiveCallPayloadBridge
open PrologRootClosedAnswerBridge
open PrologRootClosedLocalLiveBridge
open PrologScheduledAnswerValueBridge
open PrologSourceProductContextBridge
open PrologStateBridge

/-- Exhaustive visibility shape of one source search whose active collector
occurrences agree positionally with an executable frame stack.

The root constructor records that both exact lists are empty.  The private
constructor records the innermost source cell and executable findall frame,
plus their remaining positional agreement.  It deliberately carries no
template-value or accumulator agreement; that is the substantive private
collection theorem still to be composed. -/
inductive AnswerVisibility (search : Search) (frames : List Frame) : Prop where
  | rootPublic
      (sourceCellsEmpty : activeCollectionCells search = some [])
      (framesEmpty : frames = [])
  | collectorPrivate
      (cell : SourceCollectionCell) (cells : List SourceCollectionCell)
      (frame : FindallFrame) (remaining : List Frame)
      (sourceCells : activeCollectionCells search = some (cell :: cells))
      (framesExact : frames = .findall frame :: remaining)
      (headAgrees : cell.AgreesFrame (.findall frame))
      (tailAgrees :
        List.Forall₂ SourceCollectionCell.AgreesFrame cells remaining)

namespace AnswerVisibility

/-- Positional occurrence agreement determines exactly one public/private
visibility shape.  A malformed source collector is rejected by
`CollectionOccurrenceAgrees`; a root-source/findall-frame mismatch has no
constructor because `List.Forall₂` cannot align lists of different lengths. -/
theorem classify
    {search : Search} {frames : List Frame}
    (occurrences : CollectionOccurrenceAgrees search frames) :
    AnswerVisibility search frames := by
  cases sourceCells : activeCollectionCells search with
  | none =>
      simp [CollectionOccurrenceAgrees, sourceCells] at occurrences
  | some cells =>
      cases cells with
      | nil =>
          cases framesExact : frames with
          | nil =>
              exact .rootPublic sourceCells rfl
          | cons executableFrame remaining =>
              have aligned :
                  List.Forall₂ SourceCollectionCell.AgreesFrame []
                    (executableFrame :: remaining) := by
                simpa only [CollectionOccurrenceAgrees, sourceCells,
                  framesExact] using occurrences
              cases aligned
      | cons cell cells =>
          cases framesExact : frames with
          | nil =>
              have aligned :
                  List.Forall₂ SourceCollectionCell.AgreesFrame
                    (cell :: cells) [] := by
                simpa only [CollectionOccurrenceAgrees, sourceCells,
                  framesExact] using occurrences
              cases aligned
          | cons executableFrame remaining =>
              have aligned :
                  List.Forall₂ SourceCollectionCell.AgreesFrame
                    (cell :: cells) (executableFrame :: remaining) := by
                simpa only [CollectionOccurrenceAgrees, sourceCells,
                  framesExact] using occurrences
              cases aligned with
              | cons headAgrees tailAgrees =>
                  cases executableFrame with
                  | findall frame =>
                      exact
                        .collectorPrivate cell cells frame remaining
                          sourceCells rfl headAgrees tailAgrees

/-- An aligned source root forces an empty executable frame stack.  This is
the load-bearing bridge from source visibility to executable ownership for
an arbitrary search.  When a particular search is already known
unconditionally to have no source cells, its occurrence-alignment premise is
equivalent to an empty executable frame stack; this lemma does not by itself
discharge that premise. -/
theorem framesEmpty_of_sourceCellsEmpty
    {search : Search} {frames : List Frame}
    (occurrences : CollectionOccurrenceAgrees search frames)
    (sourceCellsEmpty : activeCollectionCells search = some []) :
    frames = [] := by
  have lengthExact := occurrences.length_eq sourceCellsEmpty
  exact List.eq_nil_of_length_eq_zero lengthExact.symm

/-- Source-root occurrence alignment derives ownership of the current public
answer accumulator. -/
theorem publicOwner_of_sourceCellsEmpty
    {search : Search} {frames : List Frame}
    (occurrences : CollectionOccurrenceAgrees search frames)
    (sourceCellsEmpty : activeCollectionCells search = some []) :
    PublicAnswerOwner frames := by
  rw [framesEmpty_of_sourceCellsEmpty occurrences sourceCellsEmpty]
  exact publicAnswerOwner_nil

end AnswerVisibility

/-! ## Scheduled product states are source-root focuses -/

/-- Predicate product/cut/choice frames preserve the active collector-cell
extractor exactly.  They cannot introduce a findall boundary. -/
@[simp] theorem activeProductFrame_wrap_cells
    (frame : ActiveProductFrame) (focus : Search) :
    activeCollectionCells (frame.wrap focus) = activeCollectionCells focus := by
  simp [ActiveProductFrame.wrap, activeCollectionCells]

/-- An arbitrary stack of already-entered predicate product regions neither
adds nor removes an active collection occurrence. -/
theorem activeProductContext_plug_cells
    (context : ActiveProductContext) (focus : Search) :
    activeCollectionCells (ActiveProductContext.plug context focus) =
      activeCollectionCells focus := by
  induction context generalizing focus with
  | nil => rfl
  | cons frame outer inductionHypothesis =>
      rw [ActiveProductContext.plug_cons, inductionHypothesis,
        activeProductFrame_wrap_cells]

/-- The scheduled predicate-product focus itself contains no collection
boundary.  Collection context, when present, belongs to the separate active
control zipper rather than this product carrier. -/
@[simp] theorem scheduledSourceProduct_cells
    (callerScope : CutScopeId) (opened : OpenedCall)
    (finish : PeTTaSpec.PrologCore.Resolver.PreparedCursor)
    (branch : PeTTaSpec.PrologCore.Resolver.ClauseBranch)
    (branchTail : List PeTTaSpec.PrologCore.Resolver.ClauseBranch)
    (current : Substitution)
    (referenceRest : List PeTTaSpec.PrologCore.Goal) :
    activeCollectionCells
        (scheduledSourceProduct callerScope opened finish branch branchTail
          current referenceRest) = some [] := by
  simp [scheduledSourceProduct, scheduledSourceProductAt,
    activeCollectionCells]

namespace RepresentativeScheduledPayloadState

/-- Every scheduled product carrier is a source-root focus with respect to
collection visibility.  This follows from its literal source-shape equation;
it is not inferred from the executable frame stack. -/
theorem sourceCellsEmpty (state : RepresentativeScheduledPayloadState) :
    activeCollectionCells state.carrier.index.source = some [] := by
  rw [state.carrier.agreement.core.sourceShape,
    activeProductContext_plug_cells]
  exact
    scheduledSourceProduct_cells state.carrier.index.callerScope
      state.carrier.index.opened state.carrier.index.finish
      state.carrier.index.branch state.carrier.index.branchTail
      state.carrier.index.current state.carrier.index.callerReferences

end RepresentativeScheduledPayloadState

namespace RootClosedAnswerReady

/-- Re-express the exact rooted public answer relation through positional
source/fine occurrence agreement.  The scheduled source shape is
unconditionally root-visible, so at this focused carrier the occurrence
premise is equivalent to an empty executable frame stack; contextual zipper
production of that premise remains separate work. -/
theorem withPublicAnswerOfOccurrences
    {sourceQuery : Term}
    {prog : Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeScheduledPayloadState}
    (ready : RootClosedAnswerReady before)
    (queryAgreement :
      AlphaTermAgrees before.carrier.index.alpha sourceQuery
        before.carrier.index.openConf.control.qterm)
    (querySupported :
      AlphaTermsSupported before.carrier.index.alpha
        before.carrier.index.support [sourceQuery])
    (occurrences :
      CollectionOccurrenceAgrees before.carrier.index.source
        before.carrier.index.openConf.frames) :
    RootClosedPublicAnswerRelates sourceQuery prog gt before ready :=
  PLeaTTa.PrologScheduledAnswerValueBridge.RootClosedAnswerReady.withPublicAnswer
    ready queryAgreement querySupported
      (AnswerVisibility.publicOwner_of_sourceCellsEmpty occurrences
        (PLeaTTa.PrologAnswerVisibilityBridge.RepresentativeScheduledPayloadState.sourceCellsEmpty
          before))

end RootClosedAnswerReady

namespace RootClosedLocalLiveAnswerRelates

/-- Re-express public value/observation content for a rooted local-live answer
through source/fine occurrence alignment.  At this scheduled product focus
the occurrence premise carries exactly the same rootness content as an empty
frame equation; the theorem does not yet derive it from an enclosing control
context. -/
theorem withPublicAnswerOfOccurrences
    {sourceQuery : Term}
    {prog : Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Metta.Subst}
    {selectedTail : List PLeaTTa.Alt}
    {count : Nat} {target : Search}
    (control :
      RootClosedLocalLiveAnswerRelates prog gt before ready selectedGoals
        selectedBinding selectedTail count target)
    (queryAgreement :
      AlphaTermAgrees before.carrier.index.alpha sourceQuery
        before.carrier.index.openConf.control.qterm)
    (querySupported :
      AlphaTermsSupported before.carrier.index.alpha
        before.carrier.index.support [sourceQuery])
    (occurrences :
      CollectionOccurrenceAgrees before.carrier.index.source
        before.carrier.index.openConf.frames) :
    RootClosedLocalLivePublicAnswerRelates sourceQuery prog gt before ready
      selectedGoals selectedBinding selectedTail count target := by
  have framesEmpty :=
    AnswerVisibility.framesEmpty_of_sourceCellsEmpty occurrences
      (PLeaTTa.PrologAnswerVisibilityBridge.RepresentativeScheduledPayloadState.sourceCellsEmpty
        before)
  exact
    PLeaTTa.PrologScheduledAnswerValueBridge.RootClosedLocalLiveAnswerRelates.withPublicAnswer
      control queryAgreement querySupported framesEmpty

end RootClosedLocalLiveAnswerRelates

end PLeaTTa.PrologAnswerVisibilityBridge
