-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologRootClosedAnswerBridge
Purpose: Eliminate the unreachable older-base pull branch for rooted local
  scheduled answers
Trusted boundary: none
Main exports: AllEmptyHistoryResult,
  RepresentativeScheduledPayloadState.rootClosedAnswerReady,
  RootClosedAnswerReady.classifyPull
-/
import PLeaTTa.Proofs.PrologScheduledPayloadResumeBridge
import PLeaTTa.Proofs.PrologAnswerPullClassificationBridge

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
open PrologRetainedPayloadSnapshotBridge
open PrologScheduledAnswerPropagationBridge
open PrologScheduledPayloadResumeBridge
open PrologSourceProductContextBridge

/-! ## A Type-valued all-empty history fold -/

/-- Result of absorbing a complete all-empty outer payload zipper.

The target source is a type index fixed by `absorbContextTarget`.  The final
history is data produced from the Type-valued payload zipper, and its resource
equation says that every outer resource was appended once in executable
order. -/
structure AllEmptyHistoryResult
    {alpha : List (LogicVar × String)} {source next : Search}
    (initial : ScheduledAnswerHistory alpha source next)
    (outerResources : List RetainedAlternativeSegment)
    (expectedSource : Search) : Type where
  targetSource : Search
  targetSourceExact : targetSource = expectedSource
  targetNext : Search
  history : ScheduledAnswerHistory alpha targetSource targetNext
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
    (scopeExact : history.leafScope = inner)
    (allEmpty :
      forall segment, segment ∈ segments -> segment.references = []) :
    AllEmptyHistoryResult history resources
      (absorbContextTarget context history.bindings source next) := by
  induction payload generalizing source next with
  | nil currentBarrier scope =>
      exact
        { targetSource := source
          targetSourceExact := rfl
          targetNext := next
          history := history
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
      let tailResult :=
        inductionHypothesis nextHistory rfl tailEmpty
      refine
        { targetSource := tailResult.targetSource
          targetSourceExact := ?_
          targetNext := tailResult.targetNext
          history := tailResult.history
          bindingsExact := ?_
          resourcesExact := ?_ }
      · simpa [absorbContextTarget, empty, nextHistory,
          PrivateScheduledResume.nextHistory, privateResumeTarget,
          enclosingHeadNext] using tailResult.targetSourceExact
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
    (before : RepresentativeScheduledPayloadState) : Search :=
  absorbContextTarget before.carrier.index.context
    (currentAnswerHistory before).bindings
    (ScheduledAnswerHistory.oneLevelSource
      before.carrier.index.callerScope before.carrier.index.opened.scope
      before.carrier.index.current
      (before.carrier.index.finish.advance before.carrier.index.branch
        before.carrier.index.branchTail))
    (ScheduledAnswerHistory.oneLevelNext
      before.carrier.index.callerScope before.carrier.index.opened.scope
      (before.carrier.index.finish.advance before.carrier.index.branch
        before.carrier.index.branchTail))

/-- A live scheduled carrier whose complete private caller spine has been
absorbed and whose locally owned resource bank is the entire executable bank.
-/
structure RootClosedAnswerReady
    (before : RepresentativeScheduledPayloadState) : Type where
  result :
    AllEmptyHistoryResult (currentAnswerHistory before)
      before.carrier.index.resources
      (fullyAbsorbedSource before)
  sourceSteps :
    StepsN before.carrier.index.outer.length before.carrier.sourceState []
      (.running before.carrier.index.session (fullyAbsorbedSource before))
  bankExact :
    before.carrier.index.openConf.control.alts =
      flattenOwnedAlts result.history.resources []
  fineHead :
    before.carrier.index.openConf.toConf.cur =
      some ([], before.carrier.index.runtime)

namespace RepresentativeScheduledPayloadState

/-- Construct the exact closed answer frontier from a rooted live scheduled
carrier.  Root closure and all-empty caller tails are inherited from the
actual phase state; the final history and bank cannot be supplied separately.
-/
noncomputable def rootClosedAnswerReady
    (before : RepresentativeScheduledPayloadState)
    (referenceEmpty : before.carrier.index.callerReferences = [])
    (allEmpty :
      forall segment, segment ∈ before.carrier.index.outer ->
        segment.references = [])
    (rootClosed : before.carrier.index.baseAlts = []) :
    RootClosedAnswerReady before := by
  let payloadTail :=
    ActiveProductPayloadContext.outerPayload before.carrier.payloadContext
  let result :=
    absorbAllEmptyHistory payloadTail (currentAnswerHistory before) rfl allEmpty
  have sourceRun :=
    absorbAlignedContext payloadTail.alignment (currentAnswerHistory before)
      rfl before.carrier.index.session
  have sourceExact :
      before.carrier.index.source =
        ActiveProductContext.plug before.carrier.index.context
          (ScheduledAnswerHistory.oneLevelSource
            before.carrier.index.callerScope before.carrier.index.opened.scope
            before.carrier.index.current
            (before.carrier.index.finish.advance before.carrier.index.branch
              before.carrier.index.branchTail)) := by
    rw [before.carrier.agreement.core.sourceShape, referenceEmpty]
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
    rw [before.carrier.agreement.core.resourceStack.actualAlts, rootClosed]
    rw [result.resourcesExact, currentAnswerHistory_resources]
    rfl
  have scheduledReady := before.carrier.agreement.core.control.ready
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
      fineHead := fineHead }

end RepresentativeScheduledPayloadState

namespace RootClosedAnswerReady

/-- Classify the actual eager executable pull at a rooted local answer.  The
result is local-live or terminal; an unowned older-base branch is absent by
construction. -/
theorem classifyPull
    {before : RepresentativeScheduledPayloadState}
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
