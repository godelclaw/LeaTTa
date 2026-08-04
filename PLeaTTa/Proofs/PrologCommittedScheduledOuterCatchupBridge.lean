-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologCommittedScheduledOuterCatchupBridge
Purpose: Propagate one post-cut answer through empty callers, then expose the
  surviving outer resource spine without weakening ordinary answer ownership.
Trusted boundary: none
Main exports:
  liftCommittedAnswerThroughEmptyContext,
  committedLiftedSuccessor_descends
-/
import PLeaTTa.Proofs.PrologAnswerOriginBridge
import PLeaTTa.Proofs.PrologBodyFailureOuterResourceCatchupBridge
import PLeaTTa.Proofs.PrologCommittedScheduledTerminalBridge
import PLeaTTa.Proofs.PrologFindallAnswerResourceBridge

namespace PLeaTTa.PrologCommittedScheduledOuterCatchupBridge

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open DemandDrivenStep
open PrologAnswerOriginBridge
open PrologBodyFailureExhaustedResourceTransitionBridge
open PrologBodyFailureOuterResourceCatchupBridge
open PrologCommittedScheduledTerminalBridge
open PrologFindallAnswerResourceBridge
open PrologPersistentFreeCommittedScheduledPayloadBridge
open PrologProductResourceContextBridge
open PrologRetainedPayloadSnapshotBridge
open PrologSourceProductContextBridge

/-! ## Source-only answer propagation

The ordinary scheduled-answer relation intentionally requires a nonempty
retained-resource history.  A post-cut answer has no innermost retained
resource: the cut consumed that occurrence and its cursor.  The definitions
below therefore retain only the exact `AnswerOrigin` while the answer crosses
empty callers.  Resource accounting resumes after the committed successor
has exposed the unchanged outer context.
-/

/-- Source and successor after repeatedly scheduling one answer through an
inner-to-outer context.

The function is purely structural.  A theorem below requires every caller
tail to be empty before treating the first component as another answer
origin. -/
def liftCommittedAnswerPair :
    ActiveProductContext -> Substitution -> Search -> Search -> Search × Search
  | [], _, source, next => (source, next)
  | frame :: outer, bindings, _, next =>
      let right := frame.wrap next
      let scheduled :=
        .choice frame.callerScope
          (.task frame.callerScope frame.callerRest bindings) right
      let after := .choice frame.callerScope .done right
      liftCommittedAnswerPair outer bindings scheduled after

/-- The successor component is independent of the discarded pre-answer
source.  Naming it separately makes the post-answer descent theorem state
only the control fact it proves. -/
def liftCommittedSuccessor : ActiveProductContext -> Search -> Search
  | [], next => next
  | frame :: outer, next =>
      liftCommittedSuccessor outer
        (.choice frame.callerScope .done (frame.wrap next))

@[simp] theorem liftCommittedAnswerPair_snd
    (context : ActiveProductContext) (bindings : Substitution)
    (source next : Search) :
    (liftCommittedAnswerPair context bindings source next).2 =
      liftCommittedSuccessor context next := by
  induction context generalizing source next with
  | nil => rfl
  | cons frame outer inductionHypothesis =>
      simpa [liftCommittedAnswerPair, liftCommittedSuccessor] using
        inductionHypothesis
          (.choice frame.callerScope
            (.task frame.callerScope frame.callerRest bindings)
            (frame.wrap next))
          (.choice frame.callerScope .done (frame.wrap next))

/-- One exact post-cut answer origin at the innermost caller.

Its inactive right branch is the exhausted committed predicate, not an
ordinary retained-resource region. -/
def committedAnswerOrigin
    (callerScope predicateScope : CutScopeId) (bindings : Substitution) :
    AnswerOrigin callerScope bindings
      (committedScheduledSourceProductAt callerScope predicateScope bindings [])
      (committedScheduledAfterAnswerAt callerScope predicateScope) :=
  .choice callerScope
    (.product callerScope (.cutBoundary predicateScope .done) []) .task

/-- An exact answer origin crosses one empty caller per source step.

Only source control is transported here.  No retained resource or executable
alternative is synthesized for the exhausted committed predicate. -/
theorem liftCommittedAnswerThroughEmptyContext
    {leafScope : CutScopeId} {bindings : Substitution}
    {source next : Search}
    (context : ActiveProductContext)
    (allEmpty : forall frame, frame ∈ context -> frame.callerRest = [])
    (origin : AnswerOrigin leafScope bindings source next)
    (session : Session) :
    StepsN context.length
      (.running session (ActiveProductContext.plug context source)) []
      (.running session
        (liftCommittedAnswerPair context bindings source next).1) ∧
      exists outerLeaf,
        AnswerOrigin outerLeaf bindings
          (liftCommittedAnswerPair context bindings source next).1
          (liftCommittedAnswerPair context bindings source next).2 := by
  induction context generalizing leafScope source next with
  | nil =>
      exact ⟨.zero _, leafScope, origin⟩
  | cons frame outer inductionHypothesis =>
      have headEmpty : frame.callerRest = [] :=
        allEmpty frame (by simp)
      have tailEmpty :
          forall candidate, candidate ∈ outer -> candidate.callerRest = [] := by
        intro candidate member
        exact allEmpty candidate (by simp [member])
      let right : Search := frame.wrap next
      let scheduled : Search :=
        .choice frame.callerScope
          (.task frame.callerScope [] bindings) right
      let after : Search := .choice frame.callerScope .done right
      have childAnswer :
          RawStep session source [.answer bindings] .none session
            (.running next) :=
        origin.toRawStep session
      have privateRaw :
          RawStep session (frame.wrap source) [] .none session
            (.running scheduled) := by
        dsimp [ActiveProductFrame.wrap, scheduled, right]
        rw [headEmpty]
        apply RawStep.productAnswer
        apply RawStep.cutBoundaryProgress
        apply RawStep.choiceProgress
        exact childAnswer
      have liftedRaw :
          RawStep session
            (ActiveProductContext.plug outer (frame.wrap source)) [] .none
            session
            (.running (ActiveProductContext.plug outer scheduled)) :=
        ActiveProductContext.liftProgress outer privateRaw
          (by simp [Trace.AnswerFree])
      have first :
          StepsN 1
            (.running session
              (ActiveProductContext.plug outer (frame.wrap source))) []
            (.running session
              (ActiveProductContext.plug outer scheduled)) := by
        exact .succ 0 _ _ _ [] [] (.ordinary _ [] _ _ _ liftedRaw) (.zero _)
      have nextOrigin :
          AnswerOrigin frame.callerScope bindings scheduled after := by
        exact .choice frame.callerScope right .task
      obtain ⟨tailSteps, outerLeaf, finalOrigin⟩ :=
        inductionHypothesis tailEmpty nextOrigin
      have composed := StepsN.trans first tailSteps
      refine ⟨?_, outerLeaf, ?_⟩
      · simpa [liftCommittedAnswerPair, scheduled, after, right,
          headEmpty, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          composed
      · simpa [liftCommittedAnswerPair, scheduled, after, right,
          headEmpty] using finalOrigin

/-! ## Exact post-answer descent -/

/-- Descending the lifted successor takes one real leftmost-DFS step per
outer frame, followed by the supplied innermost successor step.

No transition is quotiented away: this is the divergence-sensitive bridge
from the public answer successor to the explicit committed exhaustion focus. -/
theorem liftCommittedSuccessor_descends
    (context : ActiveProductContext) (session : Session)
    {next focus : Search}
    (innermost :
      RawStep session next [] .none session (.running focus)) :
    StepsN (context.length + 1)
      (.running session (liftCommittedSuccessor context next)) []
      (.running session (ActiveProductContext.plug context focus)) := by
  induction context generalizing next focus with
  | nil =>
      exact .succ 0 _ _ _ [] [] (.ordinary _ [] _ _ _ innermost) (.zero _)
  | cons frame outer inductionHypothesis =>
      let scheduledNext : Search :=
        .choice frame.callerScope .done (frame.wrap next)
      have switchRaw :
          RawStep session scheduledNext [] .none session
            (.running (frame.wrap next)) := by
        exact
          .choiceComplete frame.callerScope .done (frame.wrap next) session
            session (.done session)
      have descent := inductionHypothesis switchRaw
      have finalRaw :
          RawStep session
            (ActiveProductContext.plug (frame :: outer) next) [] .none session
            (.running
              (ActiveProductContext.plug (frame :: outer) focus)) :=
        ActiveProductContext.liftProgress (frame :: outer) innermost
          (by simp [Trace.AnswerFree])
      have final :
          StepsN 1
            (.running session
              (ActiveProductContext.plug (frame :: outer) next)) []
            (.running session
              (ActiveProductContext.plug (frame :: outer) focus)) := by
        exact .succ 0 _ _ _ [] [] (.ordinary _ [] _ _ _ finalRaw) (.zero _)
      have composed := StepsN.trans descent final
      simpa [liftCommittedSuccessor, scheduledNext, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using composed

/-- The innermost committed answer successor switches silently to the exact
exhausted predicate product. -/
theorem committedAfterAnswer_switches
    (session : Session) (callerScope predicateScope : CutScopeId) :
    RawStep session
      (committedScheduledAfterAnswerAt callerScope predicateScope) [] .none
      session
      (.running
        (.product callerScope (.cutBoundary predicateScope .done) [])) := by
  exact
    .choiceComplete callerScope .done
      (.product callerScope (.cutBoundary predicateScope .done) []) session
      session (.done session)

/-- The fully lifted public-answer successor reaches the explicit exhausted
post-cut focus in exactly `context.length + 1` source steps. -/
theorem committedLiftedSuccessor_descends
    (context : ActiveProductContext) (session : Session)
    (callerScope predicateScope : CutScopeId) :
    StepsN (context.length + 1)
      (.running session
        (liftCommittedSuccessor context
          (committedScheduledAfterAnswerAt callerScope predicateScope))) []
      (.running session
        (ActiveProductContext.plug context
          (.product callerScope (.cutBoundary predicateScope .done) []))) :=
  liftCommittedSuccessor_descends context session
    (committedAfterAnswer_switches session callerScope predicateScope)

/-- A committed answer crosses every empty caller privately, then the
outermost empty task emits the one public source answer.

The endpoint is the structural successor built by the same recursion; no
compatible successor may be supplied by a caller. -/
theorem committedSource_reachesLiftedSuccessor
    (context : ActiveProductContext)
    (allEmpty : forall frame, frame ∈ context -> frame.callerRest = [])
    (session : Session) (callerScope predicateScope : CutScopeId)
    (bindings : Substitution) :
    StepsN (context.length + 1)
      (.running session
        (ActiveProductContext.plug context
          (committedScheduledSourceProductAt callerScope predicateScope
            bindings [])))
      [.answer bindings]
      (.running session
        (liftCommittedSuccessor context
          (committedScheduledAfterAnswerAt callerScope predicateScope))) := by
  obtain ⟨privateSteps, outerLeaf, finalOrigin⟩ :=
    liftCommittedAnswerThroughEmptyContext context allEmpty
      (committedAnswerOrigin callerScope predicateScope bindings) session
  have publicRaw :
      RawStep session
        (liftCommittedAnswerPair context bindings
          (committedScheduledSourceProductAt callerScope predicateScope
            bindings [])
          (committedScheduledAfterAnswerAt callerScope predicateScope)).1
        [.answer bindings] .none session
        (.running
          (liftCommittedAnswerPair context bindings
            (committedScheduledSourceProductAt callerScope predicateScope
              bindings [])
            (committedScheduledAfterAnswerAt callerScope predicateScope)).2) :=
    finalOrigin.toRawStep session
  have publicStep :
      StepsN 1
        (.running session
          (liftCommittedAnswerPair context bindings
            (committedScheduledSourceProductAt callerScope predicateScope
              bindings [])
            (committedScheduledAfterAnswerAt callerScope predicateScope)).1)
        [.answer bindings]
        (.running session
          (liftCommittedAnswerPair context bindings
            (committedScheduledSourceProductAt callerScope predicateScope
              bindings [])
            (committedScheduledAfterAnswerAt callerScope predicateScope)).2) :=
    .succ 0 _ _ _ [.answer bindings] []
      (.ordinary _ [.answer bindings] _ _ _ publicRaw) (.zero _)
  have composed := StepsN.trans privateSteps publicStep
  simpa [liftCommittedAnswerPair_snd] using composed

/-- The explicit committed focus is a genuine one-step completion producer.
The completion remains available for the existing ranked outer-resource
catch-up theorem to consume. -/
theorem committedExhaustedFocus_completes
    (session : Session) (callerScope predicateScope : CutScopeId) :
    RawStep session
      (.product callerScope (.cutBoundary predicateScope .done) [])
      [.completed] .none session (.terminal .completed) := by
  exact
    .productComplete callerScope (.cutBoundary predicateScope .done) []
      [.completed] session session
      (.cutBoundaryComplete predicateScope .done session session
        (.done session))
      (by simp [Trace.AnswerFree])

/-! ## Reuse of ranked outer-resource catch-up -/

/-- After the committed successor has descended to its exhausted focus, the
existing ranked catch-up exposes the first live outer resource.

The count is deliberately additive: the first summand is descent through the
recorded answer-successor spine; the second is the already-certified rejected
pull and frame-promotion work. -/
theorem committedLiftedSuccessor_catchupFirstLive
    {alpha : List (LogicVar × String)}
    {segments : List PrologControlSegmentSpineBridge.ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {context : ActiveProductContext}
    (partition :
      OuterResourceCatchupPartition alpha segments resources context)
    (session : Session) (callerScope predicateScope : CutScopeId) :
    StepsN
      ((context.length + 1) +
        (partition.rejectionSteps + partition.crossedFrames.length + 1))
      (.running session
        (liftCommittedSuccessor context
          (committedScheduledAfterAnswerAt callerScope predicateScope))) []
      (.running session (firstLiveSourceFrontier partition)) := by
  have descent :=
    committedLiftedSuccessor_descends context session callerScope
      predicateScope
  have focusCompleted :=
    committedExhaustedFocus_completes session callerScope predicateScope
  have catchup :=
    CrossedEmptyResourceFramesAgrees.sourceCatchupToFrame
      partition.crossedWork session
      (.product callerScope (.cutBoundary predicateScope .done) [])
      focusCompleted partition.firstFrame partition.survivingContext
      partition.firstCursor partition.firstRetainedShape
  have catchupFromContext :
      StepsN
        (partition.rejectionSteps + partition.crossedFrames.length + 1)
        (.running session
          (ActiveProductContext.plug context
            (.product callerScope (.cutBoundary predicateScope .done) []))) []
        (.running session (firstLiveSourceFrontier partition)) := by
    have startEq :
        State.running session
            (ActiveProductContext.plug context
              (.product callerScope (.cutBoundary predicateScope .done) [])) =
          State.running session
            (ActiveProductContext.plug
              (partition.crossedFrames ++
                partition.firstFrame :: partition.survivingContext)
              (.product callerScope
                (.cutBoundary predicateScope .done) [])) :=
      congrArg
        (fun frames =>
          State.running session
            (ActiveProductContext.plug frames
              (.product callerScope
                (.cutBoundary predicateScope .done) [])))
        partition.contextEq
    rw [startEq]
    simpa [firstLiveSourceFrontier] using catchup
  exact StepsN.trans descent catchupFromContext

/-- If every outer resource and the older base are exhausted, the same
sequential composition reaches the genuine public completion terminal.

The completion observation is emitted only by the final ranked catch-up; all
descent and rejection steps remain present and silent. -/
theorem committedLiftedSuccessor_catchupTerminal
    {alpha : List (LogicVar × String)}
    {segments : List PrologControlSegmentSpineBridge.ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {context : ActiveProductContext}
    {base : List PLeaTTa.Alt}
    (partition :
      TerminalOuterResourceCatchupPartition alpha segments resources context
        base)
    (session : Session) (callerScope predicateScope : CutScopeId) :
    StepsN
      ((context.length + 1) +
        (partition.rejectionSteps + context.length + 1))
      (.running session
        (liftCommittedSuccessor context
          (committedScheduledAfterAnswerAt callerScope predicateScope)))
      [.completed] (.terminal session .completed) := by
  have descent :=
    committedLiftedSuccessor_descends context session callerScope
      predicateScope
  have focusCompleted :=
    committedExhaustedFocus_completes session callerScope predicateScope
  have catchup :=
    CrossedEmptyResourceFramesAgrees.sourceCatchupTerminal
      partition.crossedWork session
      (.product callerScope (.cutBoundary predicateScope .done) [])
      focusCompleted
  exact StepsN.trans descent catchup

/-- Complete exact source prefix for a post-cut answer whose eager pull finds
the first live outer resource.

The answer is emitted once, before every silent descent, rejection, and frame
promotion step. -/
theorem committedSource_catchupFirstLive
    {alpha : List (LogicVar × String)}
    {segments : List PrologControlSegmentSpineBridge.ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {context : ActiveProductContext}
    (partition :
      OuterResourceCatchupPartition alpha segments resources context)
    (allEmpty : forall frame, frame ∈ context -> frame.callerRest = [])
    (session : Session) (callerScope predicateScope : CutScopeId)
    (bindings : Substitution) :
    StepsN
      ((context.length + 1) +
        ((context.length + 1) +
          (partition.rejectionSteps + partition.crossedFrames.length + 1)))
      (.running session
        (ActiveProductContext.plug context
          (committedScheduledSourceProductAt callerScope predicateScope
            bindings [])))
      [.answer bindings]
      (.running session (firstLiveSourceFrontier partition)) := by
  exact
    StepsN.trans
      (committedSource_reachesLiftedSuccessor context allEmpty session
        callerScope predicateScope bindings)
      (committedLiftedSuccessor_catchupFirstLive partition session callerScope
        predicateScope)

/-- Complete exact source trace for a post-cut answer whose complete owned
outer bank and older base are exhausted.

The trace preserves the public order `[answer, completed]`; all intervening
administrative work remains represented in the exact step count. -/
theorem committedSource_catchupTerminal
    {alpha : List (LogicVar × String)}
    {segments : List PrologControlSegmentSpineBridge.ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {context : ActiveProductContext}
    {base : List PLeaTTa.Alt}
    (partition :
      TerminalOuterResourceCatchupPartition alpha segments resources context
        base)
    (allEmpty : forall frame, frame ∈ context -> frame.callerRest = [])
    (session : Session) (callerScope predicateScope : CutScopeId)
    (bindings : Substitution) :
    StepsN
      ((context.length + 1) +
        ((context.length + 1) +
          (partition.rejectionSteps + context.length + 1)))
      (.running session
        (ActiveProductContext.plug context
          (committedScheduledSourceProductAt callerScope predicateScope
            bindings [])))
      [.answer bindings, .completed]
      (.terminal session .completed) := by
  exact
    StepsN.trans
      (committedSource_reachesLiftedSuccessor context allEmpty session
        callerScope predicateScope bindings)
      (committedLiftedSuccessor_catchupTerminal partition session callerScope
        predicateScope)

/-! ## Payload-derived root readiness -/

/-- An all-empty control spine makes every corresponding source frame's
caller continuation empty.

The result is derived by induction over the Type-valued payload zipper, so a
caller frame cannot be paired with an unrelated control segment. -/
theorem payloadContext_allCallerRestsEmpty
    {alpha support : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat}
    {segments : List PrologControlSegmentSpineBridge.ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (payload :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer)
    (allEmpty :
      forall segment, segment ∈ segments -> segment.references = []) :
    forall frame, frame ∈ context -> frame.callerRest = [] := by
  induction payload with
  | nil currentBarrier scope =>
      simp
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      intro frame member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact allEmpty segment (by simp)
      · apply inductionHypothesis
        · intro candidate candidateMember
          exact allEmpty candidate (by simp [candidateMember])
        · exact member

/-- Root closure facts for a live post-cut scheduled carrier.

Unlike the earlier root-only terminal interface, this form retains the full
outer payload/resource zipper.  It closes only the arbitrary older base and
fine frame stack; the owned local bank is classified constructively below. -/
structure RootClosedCommittedAnswerReady
    (before : RepresentativePersistentFreeCommittedScheduledPayloadState) :
    Type where
  callerReferencesEmpty : before.carrier.index.callerReferences = []
  allOuterReferencesEmpty :
    forall segment, segment ∈ before.carrier.index.outer ->
      segment.references = []
  baseAltsEmpty : before.carrier.index.baseAlts = []
  rootFrames : before.carrier.index.openConf.frames = []
  contextCallersEmpty :
    forall frame, frame ∈ before.carrier.index.context ->
      frame.callerRest = []
  alignment :
    SourceControlResourceContextAgrees before.carrier.index.alpha
      before.carrier.index.qterm before.carrier.index.callerBarrier
      before.carrier.index.outer before.carrier.index.resources
      before.carrier.index.callerScope before.carrier.index.context
      before.carrier.index.outerScope
  bankExact :
    before.carrier.index.openConf.control.alts =
      flattenOwnedAlts before.carrier.index.resources []
  fineHead :
    before.carrier.index.openConf.toConf.cur =
      some ([], before.carrier.index.runtime)

namespace RepresentativePersistentFreeCommittedScheduledPayloadState

/-- Derive the exact rooted interface from the live packet-free committed
carrier. -/
def rootClosedAnswerReady
    (before : RepresentativePersistentFreeCommittedScheduledPayloadState)
    (referenceEmpty : before.carrier.index.callerReferences = [])
    (allEmpty :
      forall segment, segment ∈ before.carrier.index.outer ->
        segment.references = [])
    (rootClosed : before.carrier.index.baseAlts = [])
    (rootFrames : before.carrier.index.openConf.frames = []) :
    RootClosedCommittedAnswerReady before := by
  have contextCallersEmpty :=
    payloadContext_allCallerRestsEmpty before.carrier.payloadContext allEmpty
  have alignment := before.carrier.payloadContext.alignment
  have bankExact :
      before.carrier.index.openConf.control.alts =
        flattenOwnedAlts before.carrier.index.resources [] := by
    rw [before.carrier.agreement.actualAlts, rootClosed]
  have scheduledReady := before.carrier.agreement.ready
  rcases scheduledReady with
    ⟨_persistent, currentControl, _queryTerm, payload⟩
  have callerExecutablesEmpty :
      before.carrier.index.callerExecutables = [] :=
    PrologOrdinaryStepBridge.NormalizedAlphaGoalsAgree.executables_eq_nil_of_references_eq_nil
      payload.control.head referenceEmpty
  have outerExecutablesEmpty :
      PrologControlSegmentSpineBridge.flattenExecutables
          before.carrier.index.outer = [] :=
    payload.control.tail.flattenExecutables_eq_nil_of_all_references_eq_nil
      allEmpty
  have fineHead :
      before.carrier.index.openConf.toConf.cur =
        some ([], before.carrier.index.runtime) := by
    simpa [OpenConf.toConf, Control.toConf, callerExecutablesEmpty,
      outerExecutablesEmpty] using currentControl
  exact
    { callerReferencesEmpty := referenceEmpty
      allOuterReferencesEmpty := allEmpty
      baseAltsEmpty := rootClosed
      rootFrames := rootFrames
      contextCallersEmpty := contextCallersEmpty
      alignment := alignment
      bankExact := bankExact
      fineHead := fineHead }

end RepresentativePersistentFreeCommittedScheduledPayloadState

/-- Exhaustive owned-bank outcome after a rooted committed answer.

An arbitrary older base is absent by construction, leaving exactly the first
live local resource or genuine terminal exhaustion. -/
inductive RootClosedCommittedPullOutcome
    {before : RepresentativePersistentFreeCommittedScheduledPayloadState}
    (ready : RootClosedCommittedAnswerReady before) : Prop where
  | firstLive
      (partition :
        OuterResourceCatchupPartition before.carrier.index.alpha
          before.carrier.index.outer before.carrier.index.resources
          before.carrier.index.context)
  | terminal
      (partition :
        TerminalOuterResourceCatchupPartition before.carrier.index.alpha
          before.carrier.index.outer before.carrier.index.resources
          before.carrier.index.context [])

namespace RootClosedCommittedAnswerReady

/-- Common fine-machine half of either rooted pull outcome.

The top-level frame premise makes the answer publicly observable.  The real
answer successor still performs the executable pull; later outcome-specific
relations identify its exact selected branch or terminal fields. -/
structure FineAnswerRelates
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    {before : RepresentativePersistentFreeCommittedScheduledPayloadState}
    (ready : RootClosedCommittedAnswerReady before) : Prop where
  fineStep :
    DemandDrivenCallStep.Step prog gt before.carrier.fineState
      (.ready
        (privateAnswerTarget before.carrier.index.openConf
          before.carrier.index.runtime))
  fineRun :
    DemandDrivenCallStep.StepsN prog gt 1 before.carrier.fineState
      (.ready
        (privateAnswerTarget before.carrier.index.openConf
          before.carrier.index.runtime))
  publicAnswerExact :
    publicAnswers
        (privateAnswerTarget before.carrier.index.openConf
          before.carrier.index.runtime) =
      publicAnswers before.carrier.index.openConf ++
        [PLeaTTa.subst before.carrier.index.runtime
          before.carrier.index.openConf.control.qterm]
  persistentExact :
    (privateAnswerTarget before.carrier.index.openConf
      before.carrier.index.runtime).persistent =
        before.carrier.index.openConf.persistent
  scopesExact :
    (privateAnswerTarget before.carrier.index.openConf
      before.carrier.index.runtime).scopes =
        before.carrier.index.openConf.scopes
  framesExact :
    (privateAnswerTarget before.carrier.index.openConf
      before.carrier.index.runtime).frames = []

/-- The actual rooted answer is one call-fine step and appends exactly one
public query value before its eager pull outcome is inspected. -/
theorem fineAnswer
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativePersistentFreeCommittedScheduledPayloadState}
    (ready : RootClosedCommittedAnswerReady before) :
    FineAnswerRelates prog gt ready := by
  have publicOwner : PublicAnswerOwner before.carrier.index.openConf.frames := by
    rw [ready.rootFrames]
    exact publicAnswerOwner_nil
  have openStepAndAnswer :=
    answer_is_one_public_step prog gt before.carrier.index.openConf
      before.carrier.index.runtime publicOwner ready.fineHead
  have notLocalCall :
      ¬ DemandDrivenCallStep.LocalResolveHead
        before.carrier.index.openConf := by
    intro hLocal
    rcases hLocal with
      ⟨f, args, res, rest, binding, head, _nonempty, _arity⟩
    rw [ready.fineHead] at head
    simp at head
  have fineStep :
      DemandDrivenCallStep.Step prog gt before.carrier.fineState
        (.ready
          (privateAnswerTarget before.carrier.index.openConf
            before.carrier.index.runtime)) :=
    .ordinary _ _ notLocalCall openStepAndAnswer.1
  have fineRun :
      DemandDrivenCallStep.StepsN prog gt 1 before.carrier.fineState
        (.ready
          (privateAnswerTarget before.carrier.index.openConf
            before.carrier.index.runtime)) := by
    simpa using
      DemandDrivenCallStep.StepsN.succ 0 before.carrier.fineState
        (.ready
          (privateAnswerTarget before.carrier.index.openConf
            before.carrier.index.runtime))
        (.ready
          (privateAnswerTarget before.carrier.index.openConf
            before.carrier.index.runtime))
        fineStep (.zero _)
  exact
    { fineStep := fineStep
      fineRun := fineRun
      publicAnswerExact := openStepAndAnswer.2
      persistentExact := by simp
      scopesExact := by simp
      framesExact := by simpa using ready.rootFrames }

/-- Classify the exact owned resource bank without constructing a scheduled
history for the consumed post-cut occurrence. -/
theorem classifyPull
    {before : RepresentativePersistentFreeCommittedScheduledPayloadState}
    (ready : RootClosedCommittedAnswerReady before) :
    RootClosedCommittedPullOutcome ready := by
  cases
      PLeaTTa.PrologBodyFailureExhaustedResourceTransitionBridge.SourceControlResourceContextAgrees.classifyCatchup
        ready.alignment ([] : List PLeaTTa.Alt) with
  | firstLive partition => exact .firstLive partition
  | terminal partition => exact .terminal partition
  | baseLive partition =>
      have impossible := partition.baseLive
      simp [PLeaTTa.pullAux] at impossible
  | baseCatchResume partition =>
      have impossible := partition.baseResume
      simp [PLeaTTa.pullAux] at impossible
  | baseSoftcutElse partition =>
      have impossible := partition.baseElse
      simp [PLeaTTa.pullAux] at impossible
  | baseSoftcutDone partition =>
      have impossible := partition.baseDone
      simp [PLeaTTa.pullAux] at impossible
  | baseSoftcutResume partition =>
      have impossible := partition.baseResume
      simp [PLeaTTa.pullAux] at impossible

/-- Root closure fixes the exact source start consumed by both classified
outcomes. -/
theorem sourceExact
    {before : RepresentativePersistentFreeCommittedScheduledPayloadState}
    (ready : RootClosedCommittedAnswerReady before) :
    before.carrier.index.source =
      ActiveProductContext.plug before.carrier.index.context
        (committedScheduledSourceProductAt
          before.carrier.index.callerScope
          before.carrier.index.predicateScope
          before.carrier.index.current []) := by
  rw [before.carrier.agreement.sourceShape, ready.callerReferencesEmpty]

/-- Exact source/fine correspondence when the rooted committed answer's
eager pull selects the first live owned outer clause branch. -/
structure FirstLiveRelates
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    {before : RepresentativePersistentFreeCommittedScheduledPayloadState}
    (ready : RootClosedCommittedAnswerReady before)
    (partition :
      OuterResourceCatchupPartition before.carrier.index.alpha
        before.carrier.index.outer before.carrier.index.resources
        before.carrier.index.context) : Prop where
  sourceRun :
    StepsN
      ((before.carrier.index.context.length + 1) +
        ((before.carrier.index.context.length + 1) +
          (partition.rejectionSteps +
            partition.crossedFrames.length + 1)))
      before.carrier.sourceState [.answer before.carrier.index.current]
      (.running before.carrier.index.session
        (firstLiveSourceFrontier partition))
  fine : FineAnswerRelates prog gt ready
  fineSelected :
    (privateAnswerTarget before.carrier.index.openConf
        before.carrier.index.runtime).control.cur =
        some (partition.goals, partition.binding) ∧
      (privateAnswerTarget before.carrier.index.openConf
        before.carrier.index.runtime).control.alts =
        partition.tail ++ PLeaTTa.Alt.barrier ::
          flattenOwnedAlts partition.survivingResources []

/-- Exact source/fine correspondence when the complete rooted committed
resource bank is exhausted. -/
structure TerminalRelates
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    {before : RepresentativePersistentFreeCommittedScheduledPayloadState}
    (ready : RootClosedCommittedAnswerReady before)
    (partition :
      TerminalOuterResourceCatchupPartition before.carrier.index.alpha
        before.carrier.index.outer before.carrier.index.resources
        before.carrier.index.context []) : Prop where
  sourceRun :
    StepsN
      ((before.carrier.index.context.length + 1) +
        ((before.carrier.index.context.length + 1) +
          (partition.rejectionSteps +
            before.carrier.index.context.length + 1)))
      before.carrier.sourceState
      [.answer before.carrier.index.current, .completed]
      (.terminal before.carrier.index.session .completed)
  fine : FineAnswerRelates prog gt ready
  fineFields :
    (privateAnswerTarget before.carrier.index.openConf
        before.carrier.index.runtime).control.cur = none ∧
      (privateAnswerTarget before.carrier.index.openConf
        before.carrier.index.runtime).control.alts = []
  fineTerminal :
    DemandDrivenStep.Terminal
      (privateAnswerTarget before.carrier.index.openConf
        before.carrier.index.runtime)

/-- Exhaustion of the real pull fixes both post-pull control fields.

This is the terminal sibling of `PullOutcomeAgrees.fields_of_pull_some`; it
eliminates dormant delimiter and selected-branch outcomes against the literal
`pullAux = none` equation. -/
private theorem fields_of_pull_none
    {beforeAlts : List PLeaTTa.Alt}
    {cur : Option (List PLeaTTa.Goal × Metta.Subst)}
    {afterAlts : List PLeaTTa.Alt}
    (outcome : PullOutcomeAgrees beforeAlts cur afterAlts)
    (exhausted : PLeaTTa.pullAux beforeAlts = none) :
    cur = none ∧ afterAlts = [] := by
  cases outcome with
  | exhausted _ => exact ⟨rfl, rfl⟩
  | selected goals binding rest selected =>
      rw [exhausted] at selected
      contradiction
  | catchResumed frame protectedAlts rest resumed =>
      rw [exhausted] at resumed
      contradiction
  | softcutElse frame rest selected =>
      rw [exhausted] at selected
      contradiction
  | softcutDone frame rest selected =>
      rw [exhausted] at selected
      contradiction
  | softcutResumed frame protectedAlts rest resumed =>
      rw [exhausted] at resumed
      contradiction

/-- Compose the first-live classifier branch into exact source and fine
execution. -/
theorem relateFirstLive
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativePersistentFreeCommittedScheduledPayloadState}
    (ready : RootClosedCommittedAnswerReady before)
    (partition :
      OuterResourceCatchupPartition before.carrier.index.alpha
        before.carrier.index.outer before.carrier.index.resources
        before.carrier.index.context) :
    FirstLiveRelates prog gt ready partition := by
  have sourceRunRaw :=
    committedSource_catchupFirstLive partition ready.contextCallersEmpty
      before.carrier.index.session before.carrier.index.callerScope
      before.carrier.index.predicateScope before.carrier.index.current
  have sourceRun :
      StepsN
        ((before.carrier.index.context.length + 1) +
          ((before.carrier.index.context.length + 1) +
            (partition.rejectionSteps +
              partition.crossedFrames.length + 1)))
        before.carrier.sourceState [.answer before.carrier.index.current]
        (.running before.carrier.index.session
          (firstLiveSourceFrontier partition)) := by
    simpa [PersistentFreeCommittedScheduledPayloadState.sourceState,
      ready.sourceExact] using sourceRunRaw
  have prefixEmpty :
      forall resource, resource ∈ partition.crossedResources ->
        resource.alts = [] :=
    partition.crossedWork.all_empty
  have selectedPull :
      PLeaTTa.pullAux before.carrier.index.openConf.control.alts =
        some
          (.branch partition.goals partition.binding,
            partition.tail ++ PLeaTTa.Alt.barrier ::
              flattenOwnedAlts partition.survivingResources []) := by
    calc
      PLeaTTa.pullAux before.carrier.index.openConf.control.alts =
          PLeaTTa.pullAux
            (flattenOwnedAlts before.carrier.index.resources []) :=
        congrArg PLeaTTa.pullAux ready.bankExact
      _ = PLeaTTa.pullAux
            (flattenOwnedAlts
              (partition.crossedResources ++
                partition.first :: partition.survivingResources) []) :=
        congrArg (fun resources =>
          PLeaTTa.pullAux (flattenOwnedAlts resources []))
          partition.resourcesEq
      _ = some
            (.branch partition.goals partition.binding,
              partition.tail ++ PLeaTTa.Alt.barrier ::
                flattenOwnedAlts partition.survivingResources []) :=
        pullAux_flattenOwnedAlts_first_nonempty
          partition.crossedResources partition.first
          partition.survivingResources [] partition.goals partition.binding
          partition.tail prefixEmpty partition.firstHead
  have fineSelected :=
    PullOutcomeAgrees.fields_of_pull_some
      (privateAnswerTarget_pullOutcome before.carrier.index.openConf
        before.carrier.index.runtime)
      selectedPull
  exact
    { sourceRun := sourceRun
      fine := ready.fineAnswer
      fineSelected := fineSelected }

/-- Compose the terminal classifier branch into exact source and fine
execution. -/
theorem relateTerminal
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativePersistentFreeCommittedScheduledPayloadState}
    (ready : RootClosedCommittedAnswerReady before)
    (partition :
      TerminalOuterResourceCatchupPartition before.carrier.index.alpha
        before.carrier.index.outer before.carrier.index.resources
        before.carrier.index.context []) :
    TerminalRelates prog gt ready partition := by
  have sourceRunRaw :=
    committedSource_catchupTerminal partition ready.contextCallersEmpty
      before.carrier.index.session before.carrier.index.callerScope
      before.carrier.index.predicateScope before.carrier.index.current
  have sourceRun :
      StepsN
        ((before.carrier.index.context.length + 1) +
          ((before.carrier.index.context.length + 1) +
            (partition.rejectionSteps +
              before.carrier.index.context.length + 1)))
        before.carrier.sourceState
        [.answer before.carrier.index.current, .completed]
        (.terminal before.carrier.index.session .completed) := by
    simpa [PersistentFreeCommittedScheduledPayloadState.sourceState,
      ready.sourceExact] using sourceRunRaw
  have allEmpty :
      forall resource, resource ∈ before.carrier.index.resources ->
        resource.alts = [] :=
    partition.crossedWork.all_empty
  have pullNone :
      PLeaTTa.pullAux before.carrier.index.openConf.control.alts = none := by
    calc
      PLeaTTa.pullAux before.carrier.index.openConf.control.alts =
          PLeaTTa.pullAux
            (flattenOwnedAlts before.carrier.index.resources []) :=
        congrArg PLeaTTa.pullAux ready.bankExact
      _ = PLeaTTa.pullAux ([] : List PLeaTTa.Alt) :=
        pullAux_flattenOwnedAlts_all_empty
          before.carrier.index.resources [] allEmpty
      _ = none := partition.baseTerminal
  have outcome :=
    privateAnswerTarget_pullOutcome before.carrier.index.openConf
      before.carrier.index.runtime
  have fineFields :
      (privateAnswerTarget before.carrier.index.openConf
          before.carrier.index.runtime).control.cur = none ∧
        (privateAnswerTarget before.carrier.index.openConf
          before.carrier.index.runtime).control.alts = [] := by
    exact fields_of_pull_none outcome pullNone
  have fineTerminal :
      DemandDrivenStep.Terminal
        (privateAnswerTarget before.carrier.index.openConf
          before.carrier.index.runtime) := by
    refine ⟨fineFields, ?_⟩
    exact (ready.fineAnswer (prog := prog) (gt := gt)).framesExact
  exact
    { sourceRun := sourceRun
      fine := ready.fineAnswer
      fineFields := fineFields
      fineTerminal := fineTerminal }

/-- Exhaustive exact correspondence for one rooted post-cut scheduled
answer.  The result names the actual constructive partition and immediately
composes it into source and fine execution. -/
inductive ClassifiedRelates
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    {before : RepresentativePersistentFreeCommittedScheduledPayloadState}
    (ready : RootClosedCommittedAnswerReady before) : Prop where
  | firstLive
      (partition :
        OuterResourceCatchupPartition before.carrier.index.alpha
          before.carrier.index.outer before.carrier.index.resources
          before.carrier.index.context)
      (relation : FirstLiveRelates prog gt ready partition)
  | terminal
      (partition :
        TerminalOuterResourceCatchupPartition before.carrier.index.alpha
          before.carrier.index.outer before.carrier.index.resources
          before.carrier.index.context [])
      (relation : TerminalRelates prog gt ready partition)

/-- Classify and execute the actual rooted owned bank in one theorem.

There is no user-selected branch, source endpoint, transition count, or fine
successor: all are fixed by the live carrier and the constructive classifier. -/
theorem classifyAndRelate
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativePersistentFreeCommittedScheduledPayloadState}
    (ready : RootClosedCommittedAnswerReady before) :
    ClassifiedRelates prog gt ready := by
  cases ready.classifyPull with
  | firstLive partition =>
      exact .firstLive partition (ready.relateFirstLive partition)
  | terminal partition =>
      exact .terminal partition (ready.relateTerminal partition)

end RootClosedCommittedAnswerReady

end PLeaTTa.PrologCommittedScheduledOuterCatchupBridge
