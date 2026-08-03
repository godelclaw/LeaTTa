-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologRootClosedAnswerBridge
Purpose: Eliminate the unreachable older-base pull branch for rooted local
  scheduled answers
Trusted boundary: none
Main exports: AllEmptyHistoryResult,
  RepresentativePersistentFreeScheduledPayloadState.rootClosedAnswerReady,
  RootClosedAnswerReady.classifyPull
-/
import PLeaTTa.Proofs.PrologScheduledPayloadResumeBridge
import PLeaTTa.Proofs.PrologAnswerPullClassificationBridge
import PLeaTTa.Proofs.PrologScheduledHistoryBuildBridge
import PLeaTTa.Proofs.PrologScheduledPayloadPathBridge

namespace PLeaTTa.PrologRootClosedAnswerBridge

open Metta (Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologAnswerPullClassificationBridge
open PrologAnswerResourceBridge
open PrologControlSegmentSpineBridge
open PrologCurrentSessionPayloadTransitionBridge
open PrologHeterogeneousPrefixBridge
open PrologProductResourceContextBridge
open PrologPersistentFreeScheduledPayloadBridge
open PrologRetainedPayloadSnapshotBridge
open PrologScheduledAnswerPropagationBridge
open PrologScheduledHistoryBuildBridge
open PrologScheduledPayloadPathBridge
open PrologScheduledPayloadResumeBridge
open PrologSourceProductContextBridge

/-! ## A Type-valued all-empty history fold -/

/-- Result of absorbing a complete all-empty outer payload zipper.

The target source is a type index fixed by `absorbContextTarget`.  The final
history is data produced from the Type-valued payload zipper, and its resource
equation says that every outer resource was appended once in executable
order. -/
structure AllEmptyHistoryResult
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {outerResources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments outerResources inner context outer)
    {source next : Search}
    (initial : ScheduledAnswerHistory alpha source next)
    (initialBuild : ScheduledHistoryBuild initial)
    (expectedSource : Search) : Type where
  targetSource : Search
  targetSourceExact : targetSource = expectedSource
  targetNext : Search
  history : ScheduledAnswerHistory alpha targetSource targetNext
  historyBuild : ScheduledHistoryBuild history
  historyCellsExact :
    historyBuild.cells =
      initialBuild.cells ++
        (payloadCells payload).map PayloadCell.historyCell
  historyContextExact :
    historyBuild.activeContext =
      initialBuild.activeContext ++ context
  bindingsExact : history.bindings = initial.bindings
  resourcesExact :
    history.resources = initial.resources ++ outerResources

/-- Compute the complete scheduled history after crossing an all-empty
payload zipper.

The recursion is over `SourceControlResourcePayloadContextAgrees`, which is
Type-valued.  The Prop-valued alignment proof is never eliminated to choose a
`Search`; equality evidence only rewrites each already-present caller tail to
the required empty list. -/
noncomputable def absorbAllEmptyHistory
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat}
    {segments : List PrologControlSegmentSpineBridge.ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer)
    {source next : Search}
    (history : ScheduledAnswerHistory alpha source next)
    (historyBuild : ScheduledHistoryBuild history)
    (scopeExact : history.leafScope = inner)
    (allEmpty :
      forall segment, segment ∈ segments -> segment.references = []) :
    AllEmptyHistoryResult payload history historyBuild
      (absorbContextTarget context history.bindings source next) := by
  induction payload generalizing source next with
  | nil currentBarrier scope =>
      exact
        { targetSource := source
          targetSourceExact := rfl
          targetNext := next
          history := history
          historyBuild := historyBuild
          historyCellsExact := by simp [payloadCells]
          historyContextExact := by simp
          bindingsExact := rfl
          resourcesExact := by simp only [List.append_nil] }
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerPayload
      inductionHypothesis =>
      have empty : segment.references = [] :=
        allEmpty segment (by simp)
      have tailEmpty :
          forall candidate, candidate ∈ segments ->
            candidate.references = [] := by
        intro candidate member
        exact allEmpty candidate (by simp [member])
      let resume :
          PrivateScheduledResume alpha history nextScope currentScope cursor
            segment.references resource :=
        PrivateScheduledResume.ofHistory history nextScope currentScope cursor
          segment.references resource resourceOwnership
      rw [empty] at resume
      let nextHistory := resume.nextHistory
      let nextBuild : ScheduledHistoryBuild nextHistory :=
        .resumed historyBuild nextScope currentScope cursor resource resume
      let tailResult :=
        inductionHypothesis nextHistory nextBuild rfl tailEmpty
      refine
        { targetSource := tailResult.targetSource
          targetSourceExact := ?_
          targetNext := tailResult.targetNext
          history := tailResult.history
          historyBuild := tailResult.historyBuild
          historyCellsExact := ?_
          historyContextExact := ?_
          bindingsExact := ?_
          resourcesExact := ?_ }
      · simpa [absorbContextTarget, empty, nextHistory,
          PrivateScheduledResume.nextHistory, privateResumeTarget,
          enclosingHeadNext] using tailResult.targetSourceExact
      · simpa [nextBuild, ScheduledHistoryBuild.cells, payloadCells,
          PayloadCell.historyCell, List.append_assoc] using
          tailResult.historyCellsExact
      · simpa [nextBuild, ScheduledHistoryBuild.activeContext, empty,
          List.append_assoc] using tailResult.historyContextExact
      · simpa [nextHistory, PrivateScheduledResume.nextHistory] using
          tailResult.bindingsExact
      · simpa [ScheduledAnswerHistory.resources, nextHistory,
          PrivateScheduledResume.nextHistory, List.append_assoc] using
          tailResult.resourcesExact

/-! ## Closed scheduled pull outcomes -/

/-- The only two pull outcomes available to a complete scheduled history.
There is no constructor for an older unowned base: the history's endpoint is
literally `[]`. -/
inductive ClosedScheduledPullOutcome
    {alpha : List (LogicVar × String)} {source next : Search}
    (history : ScheduledAnswerHistory alpha source next) :
    List Observation -> Prop where
  | localLive (goals : List PLeaTTa.Goal) (binding : Subst)
      (rest : List PLeaTTa.Alt)
      (landing :
        OriginPrefixLanding alpha history.resourceAgreement goals binding
          rest) :
      ClosedScheduledPullOutcome history []
  | terminal
      (falls : OriginPrefixFallsThrough alpha history.resourceAgreement) :
      ClosedScheduledPullOutcome history [.completed]

/-- Structural classification of a complete scheduled history.  The generic
three-way classifier is not used: its older-base branch is unrepresentable at
the literal empty endpoint. -/
theorem
    _root_.PLeaTTa.PrologScheduledAnswerPropagationBridge.ScheduledAnswerHistory.classifyClosedPull
    {alpha : List (LogicVar × String)} {source next : Search}
    (history : ScheduledAnswerHistory alpha source next) :
    exists events, ClosedScheduledPullOutcome history events := by
  rcases AnswerOriginResourceAgrees.classifyPrefix history.resourceAgreement
      with ⟨goals, binding, rest, landing⟩ | falls
  · exact ⟨[], .localLive goals binding rest landing⟩
  · exact ⟨[.completed], .terminal falls⟩

namespace ClosedScheduledPullOutcome

/-- A closed source classification determines the executable pull result at
the complete owned bank. -/
theorem toPullOutcomeAgrees
    {alpha : List (LogicVar × String)} {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    {events : List Observation}
    (outcome : ClosedScheduledPullOutcome history events) :
    (exists goals binding rest,
        events = [] /\
          PrologFindallAnswerResourceBridge.PullOutcomeAgrees
            (flattenOwnedAlts history.resources [])
            (some (goals, binding)) rest) \/
      (events = [.completed] /\
        PrologFindallAnswerResourceBridge.PullOutcomeAgrees
          (flattenOwnedAlts history.resources []) none []) := by
  cases outcome with
  | localLive goals binding rest landing =>
      exact .inl
        ⟨goals, binding, rest, rfl,
          .selected goals binding rest landing.pullAux_exact⟩
  | terminal falls =>
      have pullNone :
          PLeaTTa.pullAux (flattenOwnedAlts history.resources []) = none := by
        simpa [ScheduledAnswerHistory.resources, PLeaTTa.pullAux] using
          falls.pullAux_eq
      exact .inr ⟨rfl, .exhausted pullNone⟩

end ClosedScheduledPullOutcome

/-! ## Live rooted producer -/

/-- Literal source endpoint after every empty caller frame has privately
absorbed the current scheduled answer. -/
def fullyAbsorbedSource
    (before : RepresentativePersistentFreeScheduledPayloadState) : Search :=
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

/-- Type-valued local construction provenance for the current one-level
history.  The cursor ownership is extracted from the same dependent payload
zipper carried by `before`. -/
def currentAnswerHistoryBuild
    (before : RepresentativePersistentFreeScheduledPayloadState) :
    ScheduledHistoryBuild (currentAnswerHistory before) :=
  .oneLevel before.carrier.index.callerScope
    before.carrier.index.predicateScope before.carrier.index.current
    (before.carrier.index.finish.advance before.carrier.index.branch
      before.carrier.index.branchTail)
    before.carrier.index.active
    (ActiveProductPayloadContextAt.activeOwnership
      before.carrier.payloadContext)

/-- A live scheduled carrier whose complete private caller spine has been
absorbed and whose locally owned resource bank is the entire executable bank.
-/
structure RootClosedAnswerReady
    (before : RepresentativePersistentFreeScheduledPayloadState) : Type where
  result :
    AllEmptyHistoryResult
      (ActiveProductPayloadContextAt.outerPayload before.carrier.payloadContext)
      (currentAnswerHistory before) (currentAnswerHistoryBuild before)
      (fullyAbsorbedSource before)
  sourceSteps :
    StepsN before.carrier.index.outer.length before.carrier.sourceState []
      (.running before.carrier.index.session (fullyAbsorbedSource before))
  bankExact :
    before.carrier.index.openConf.control.alts =
      flattenOwnedAlts result.history.resources []
  /-- Root closure includes the active caller continuation, not only the
  older payload tail.  Retaining this constructor premise keeps the exact
  source frame recoverable after the private answer history is built. -/
  callerReferencesEmpty : before.carrier.index.callerReferences = []
  fineHead :
    before.carrier.index.openConf.toConf.cur =
      some ([], before.carrier.index.runtime)

namespace RepresentativePersistentFreeScheduledPayloadState

/-- Construct the exact closed answer frontier from a rooted live scheduled
carrier.  Root closure and all-empty caller tails are inherited from the
actual phase state; the final history and bank cannot be supplied separately.
-/
noncomputable def rootClosedAnswerReady
    (before : RepresentativePersistentFreeScheduledPayloadState)
    (referenceEmpty : before.carrier.index.callerReferences = [])
    (allEmpty :
      forall segment, segment ∈ before.carrier.index.outer ->
        segment.references = [])
    (rootClosed : before.carrier.index.baseAlts = []) :
    RootClosedAnswerReady before := by
  let payloadTail :=
    ActiveProductPayloadContextAt.outerPayload before.carrier.payloadContext
  let result :=
    absorbAllEmptyHistory payloadTail (currentAnswerHistory before)
      (currentAnswerHistoryBuild before)
      rfl allEmpty
  have sourceRun :=
    absorbAlignedContext payloadTail.alignment (currentAnswerHistory before)
      rfl before.carrier.index.session
  have sourceExact :
      before.carrier.index.source =
        ActiveProductContext.plug before.carrier.index.context
          (ScheduledAnswerHistory.oneLevelSource
            before.carrier.index.callerScope before.carrier.index.predicateScope
            before.carrier.index.current
            (before.carrier.index.finish.advance before.carrier.index.branch
              before.carrier.index.branchTail)) := by
    rw [before.carrier.agreement.sourceShape, referenceEmpty]
    rfl
  have exactSourceSteps :
      StepsN before.carrier.index.outer.length before.carrier.sourceState []
        (.running before.carrier.index.session
          (fullyAbsorbedSource before)) := by
    change
      StepsN before.carrier.index.outer.length
        (.running before.carrier.index.session before.carrier.index.source) []
        (.running before.carrier.index.session
          (fullyAbsorbedSource before))
    rw [sourceExact]
    simpa [fullyAbsorbedSource,
      privateResumeCost_eq_length_of_all_empty
        before.carrier.index.outer allEmpty] using sourceRun
  have bankExact :
      before.carrier.index.openConf.control.alts =
        flattenOwnedAlts result.history.resources [] := by
    rw [before.carrier.agreement.actualAlts, rootClosed]
    rw [result.resourcesExact, currentAnswerHistory_resources]
    rfl
  have scheduledReady := before.carrier.agreement.ready
  rcases scheduledReady with
    ⟨_persistent, currentControl, _queryTerm, payload⟩
  have callerExecutablesEmpty :
      before.carrier.index.callerExecutables = [] :=
    PrologOrdinaryStepBridge.NormalizedAlphaGoalsAgree.executables_eq_nil_of_references_eq_nil
      payload.control.head referenceEmpty
  have outerExecutablesEmpty :
      flattenExecutables before.carrier.index.outer = [] :=
    payload.control.tail.flattenExecutables_eq_nil_of_all_references_eq_nil
      allEmpty
  have fineHead :
      before.carrier.index.openConf.toConf.cur =
        some ([], before.carrier.index.runtime) := by
    simpa [OpenConf.toConf, Control.toConf, callerExecutablesEmpty,
      outerExecutablesEmpty] using currentControl
  exact
    { result := result
      sourceSteps := exactSourceSteps
      bankExact := bankExact
      callerReferencesEmpty := referenceEmpty
      fineHead := fineHead }

end RepresentativePersistentFreeScheduledPayloadState

namespace RootClosedAnswerReady

/-- The completed local history and the full immutable payload zipper carry
the same occurrence cells in the same order.  This strengthens the older
resource-list equation with exact cursors, so duplicate-but-equal executable
banks cannot select the wrong snapshot. -/
theorem historyCells_eq_payloadCells
    {before : RepresentativePersistentFreeScheduledPayloadState}
    (ready : RootClosedAnswerReady before) :
    ready.result.historyBuild.cells =
      (payloadCells before.carrier.payloadContext).map
        PayloadCell.historyCell := by
  rw [ready.result.historyCellsExact]
  cases before.carrier.payloadContext
  rfl

/-- The completed history also reconstructs every typed source frame,
including the active predicate cell which is absent from the older-only
`index.context`.  Thus payload occurrence identity and cut/product context
identity are coupled by the same Type-valued construction tree. -/
theorem historyContext_eq_fullContext
    {before : RepresentativePersistentFreeScheduledPayloadState}
    (ready : RootClosedAnswerReady before) :
    ready.result.historyBuild.activeContext =
      { callerScope := before.carrier.index.callerScope
        predicateScope := before.carrier.index.predicateScope
        retained :=
          .clauses before.carrier.index.predicateScope
            (before.carrier.index.finish.advance before.carrier.index.branch
              before.carrier.index.branchTail)
        callerRest := before.carrier.index.callerReferences } ::
        before.carrier.index.context := by
  rw [ready.result.historyContextExact]
  cases before.carrier.payloadContext
  simp [currentAnswerHistoryBuild, ScheduledHistoryBuild.activeContext,
    ready.callerReferencesEmpty]

/-- Package the exact positional bridge used by later answer-landing
classification. -/
def payloadAlignment
    {before : RepresentativePersistentFreeScheduledPayloadState}
    (ready : RootClosedAnswerReady before) :
    ScheduledPayloadAlignment before.carrier.payloadContext
      ready.result.historyBuild :=
  ⟨ready.historyCells_eq_payloadCells⟩

/-- Classify the actual eager executable pull at a rooted local answer.  The
result is local-live or terminal; an unowned older-base branch is absent by
construction. -/
theorem classifyPull
    {before : RepresentativePersistentFreeScheduledPayloadState}
    (ready : RootClosedAnswerReady before) :
    exists events,
      ClosedScheduledPullOutcome ready.result.history events /\
        ((exists goals binding rest,
            events = [] /\
              PrologFindallAnswerResourceBridge.PullOutcomeAgrees
                before.carrier.index.openConf.control.alts
                (some (goals, binding)) rest) \/
          (events = [.completed] /\
            PrologFindallAnswerResourceBridge.PullOutcomeAgrees
              before.carrier.index.openConf.control.alts none [])) := by
  obtain ⟨events, outcome⟩ := ready.result.history.classifyClosedPull
  refine ⟨events, outcome, ?_⟩
  rcases outcome.toPullOutcomeAgrees with selected | exhausted
  · left
    rcases selected with ⟨goals, binding, rest, eventsExact, pull⟩
    exact
      ⟨goals, binding, rest, eventsExact, by
        simpa only [ready.bankExact] using pull⟩
  · right
    rcases exhausted with ⟨eventsExact, pull⟩
    exact
      ⟨eventsExact, by simpa only [ready.bankExact] using pull⟩

end RootClosedAnswerReady

end PLeaTTa.PrologRootClosedAnswerBridge
