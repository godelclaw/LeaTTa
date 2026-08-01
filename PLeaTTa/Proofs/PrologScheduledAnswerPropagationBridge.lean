-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologScheduledAnswerPropagationBridge
Purpose: Propagate one exact local answer through an enclosing predicate
  product while retaining every live alternative as a scheduled history.
Trusted boundary: none
Main exports:
  ScheduledAnswerHistory,
  PrivateScheduledResume,
  PrivateScheduledResume.nextHistory
-/
import PLeaTTa.Proofs.PrologAnswerResourceBridge

namespace PLeaTTa.PrologScheduledAnswerPropagationBridge

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open PrologAnswerOriginBridge
open PrologAnswerResourceBridge
open PrologControlSegmentSpineBridge
open PrologProductResourceContextBridge
open PrologSourceProductContextBridge

/-! ## Resource-history algebra -/

/-- Flattening an appended resource spine is literal nesting of the two
flattenings.  This is the ordered resource analogue of list append; no marker
is removed or inserted by the equation itself. -/
theorem flattenOwnedAlts_append
    (left right : List RetainedAlternativeSegment)
    (base : List PLeaTTa.Alt) :
    flattenOwnedAlts (left ++ right) base =
      flattenOwnedAlts left (flattenOwnedAlts right base) := by
  induction left with
  | nil => rfl
  | cons resource resources inductionHypothesis =>
      simp only [List.cons_append, flattenOwnedAlts_cons,
        inductionHypothesis]

/-- An older alternative base is appended after every resource-owned slice
and marker.  Stating this separately prevents list append from being confused
with resource-spine append in later history composition. -/
theorem flattenOwnedAlts_base
    (resources : List RetainedAlternativeSegment)
    (base : List PLeaTTa.Alt) :
    flattenOwnedAlts resources base =
      flattenOwnedAlts resources [] ++ base := by
  induction resources with
  | nil => rfl
  | cons resource resources inductionHypothesis =>
      simp only [flattenOwnedAlts_cons, inductionHypothesis,
        List.cons_append, List.append_assoc]

/-- Extend both endpoints of an answer-origin history by the same untouched
resource and alternative suffix.

The suffix is threaded through the recursively selected left path.  Every
inactive right region and cut marker already owned by the origin remains in
its original position; the extension cannot reorder or consume it. -/
def answerOriginResource_appendSuffix
    {alpha : List (LogicVar × String)}
    {leafScope : CutScopeId} {bindings : Substitution}
    {source next : Search}
    {origin : AnswerOrigin leafScope bindings source next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (agreement :
      AnswerOriginResourceAgrees alpha origin beforeResources afterResources
        beforeAlts afterAlts)
    (resourceSuffix : List RetainedAlternativeSegment)
    (altSuffix : List PLeaTTa.Alt) :
    AnswerOriginResourceAgrees alpha origin
      (beforeResources ++ resourceSuffix)
      (afterResources ++ resourceSuffix)
      (beforeAlts ++ altSuffix) (afterAlts ++ altSuffix) :=
  match agreement with
  | .task leafScope bindings resources alts =>
      .task leafScope bindings (resources ++ resourceSuffix)
        (alts ++ altSuffix)
  | .choice scope right inside insideAgreement regionAgreement =>
      .choice scope right inside
        (by
          simpa only [List.append_assoc] using
            answerOriginResource_appendSuffix insideAgreement resourceSuffix
              altSuffix)
        regionAgreement
  | .cutBoundary scope inside insideAgreement =>
      .cutBoundary scope inside
        (by
          simpa only [List.cons_append] using
            answerOriginResource_appendSuffix insideAgreement resourceSuffix
              altSuffix)

/-! ## Exact answer packets -/

/-- One local answer path together with the complete nonempty resource slice
accounted for by its inactive right regions.

The generic trace provider cannot create this packet: `origin` identifies an
actual empty source task, while `resourceAgreement` accounts for every source
right region and executable alternative in lockstep.  "Empty" below means the
origin traversal has accounted for the whole local slice; the alternatives
remain live inside the scheduled right product.  Source and successor are
type indices, so a shape-compatible origin from another state cannot cross
into this packet.

`resourcesRev` grows by cons in outer-to-inner chronological order.  The one
explicit reverse at the semantic boundary recovers the executable's required
inner-to-outer resource order without repeated snoc reassociation. -/
structure ScheduledAnswerHistory (alpha : List (LogicVar × String))
    (source next : Search) where
  leafScope : CutScopeId
  bindings : Substitution
  resourcesRev : List RetainedAlternativeSegment
  resourcesRevNonempty : resourcesRev ≠ []
  origin : AnswerOrigin leafScope bindings source next
  resourceAgreement :
    AnswerOriginResourceAgrees alpha origin resourcesRev.reverse []
      (flattenOwnedAlts resourcesRev.reverse []) []

namespace ScheduledAnswerHistory

/-- Literal executable order of the history's retained resources. -/
def resources
    {alpha : List (LogicVar × String)} {source next : Search}
    (history : ScheduledAnswerHistory alpha source next) :
    List RetainedAlternativeSegment :=
  history.resourcesRev.reverse

theorem resourcesNonempty
    {alpha : List (LogicVar × String)} {source next : Search}
    (history : ScheduledAnswerHistory alpha source next) :
    history.resources ≠ [] := by
  simpa [resources] using history.resourcesRevNonempty

/-- The answer packet reconstructs the exact singleton-answer source step at
the current persistent session.  Session equality is definitional. -/
theorem sourceStep
    {alpha : List (LogicVar × String)} {source next : Search}
    (history : ScheduledAnswerHistory alpha source next) (session : Session) :
    RawStep session source [.answer history.bindings] .none session
      (.running next) :=
  history.origin.toRawStep session

/-- Freeze the packet as the right branch of one private product scheduling
successor.  The entire ordered resource slice survives inside the branch. -/
def rightRegion
    {alpha : List (LogicVar × String)} {source next : Search}
    (history : ScheduledAnswerHistory alpha source next)
    (callerScope : CutScopeId)
    (callerTail : List PeTTaSpec.PrologCore.Goal) :
    RightAlternativeRegionAgrees alpha
      (.product callerScope next callerTail)
      history.resources (flattenOwnedAlts history.resources []) :=
  .scheduled callerScope callerTail history.origin history.resources
    history.resourcesNonempty history.resourceAgreement

/-- Literal one-level scheduled source with an empty caller continuation. -/
def oneLevelSource
    (callerScope predicateScope : CutScopeId) (bindings : Substitution)
    (cursor : PreparedCursor) : Search :=
  .choice callerScope (.task callerScope [] bindings)
    (.product callerScope
      (.cutBoundary predicateScope
        (.choice predicateScope .done (.clauses predicateScope cursor))) [])

/-- Exact successor of the one-level answer leaf. -/
def oneLevelNext
    (callerScope predicateScope : CutScopeId)
    (cursor : PreparedCursor) : Search :=
  .choice callerScope .done
    (.product callerScope
      (.cutBoundary predicateScope
        (.choice predicateScope .done (.clauses predicateScope cursor))) [])

/-- The first scheduled history created by one successful local predicate.

The empty caller task is the answer leaf.  Its inactive right product owns
the selected predicate's retained cursor, alternatives, and exactly one cut
marker. -/
def oneLevel
    {alpha : List (LogicVar × String)}
    (callerScope predicateScope : CutScopeId) (bindings : Substitution)
    (cursor : PreparedCursor) (resource : RetainedAlternativeSegment)
    (ownership : resource.HasIndexedOwnershipAt alpha cursor) :
    ScheduledAnswerHistory alpha
      (oneLevelSource callerScope predicateScope bindings cursor)
      (oneLevelNext callerScope predicateScope cursor) :=
  let right : Search :=
    .product callerScope
      (.cutBoundary predicateScope
        (.choice predicateScope .done (.clauses predicateScope cursor))) []
  let source : Search :=
    .choice callerScope (.task callerScope [] bindings) right
  let next : Search := .choice callerScope .done right
  let origin : AnswerOrigin callerScope bindings source next :=
    .choice callerScope right .task
  let region :
      RightAlternativeRegionAgrees alpha right [resource]
        (flattenOwnedAlts [resource] []) := by
    simpa only [flattenOwnedAlts_cons, flattenOwnedAlts_nil,
      List.append_nil] using
      AnswerOriginResourceAgrees.one_level_scheduled_region_exact callerScope
        predicateScope bindings cursor [] resource ownership
  let resourceAgreement :
      AnswerOriginResourceAgrees alpha origin [resource] []
        (flattenOwnedAlts [resource] []) [] := by
    apply AnswerOriginResourceAgrees.choice
      (inside := AnswerOrigin.task)
      (regionResources := [resource])
      (regionAlts := flattenOwnedAlts [resource] [])
    · simpa only [List.append_nil] using
        (AnswerOriginResourceAgrees.task callerScope bindings [resource]
          (flattenOwnedAlts [resource] []))
    · exact region
  { leafScope := callerScope
    bindings := bindings
    resourcesRev := [resource]
    resourcesRevNonempty := by simp
    origin := origin
    resourceAgreement := resourceAgreement }

@[simp] theorem oneLevel_resources
    {alpha : List (LogicVar × String)}
    (callerScope predicateScope : CutScopeId) (bindings : Substitution)
    (cursor : PreparedCursor) (resource : RetainedAlternativeSegment)
    (ownership : resource.HasIndexedOwnershipAt alpha cursor) :
    (oneLevel callerScope predicateScope bindings cursor resource
      ownership).resources = [resource] := rfl

end ScheduledAnswerHistory

/-! ## One enclosing predicate frame -/

/-- Source head in which an older predicate activation is waiting for the
answer represented by `history`. -/
def enclosingHead
    {alpha : List (LogicVar × String)} {source next : Search}
    (_history : ScheduledAnswerHistory alpha source next)
    (predicateScope : CutScopeId) (cursor : PreparedCursor) : Search :=
  .cutBoundary predicateScope
    (.choice predicateScope source (.clauses predicateScope cursor))

/-- Exact head successor after replacing only the answer-producing leaf by
its recorded successor. -/
def enclosingHeadNext
    {alpha : List (LogicVar × String)} {source next : Search}
    (_history : ScheduledAnswerHistory alpha source next)
    (predicateScope : CutScopeId) (cursor : PreparedCursor) : Search :=
  .cutBoundary predicateScope
    (.choice predicateScope next (.clauses predicateScope cursor))

/-- Source state before an enclosing product privately consumes the answer. -/
def privateResumeSource
    {alpha : List (LogicVar × String)} {source next : Search}
    (history : ScheduledAnswerHistory alpha source next)
    (callerScope predicateScope : CutScopeId) (cursor : PreparedCursor)
    (callerTail : List PeTTaSpec.PrologCore.Goal) : Search :=
  .product callerScope (enclosingHead history predicateScope cursor) callerTail

/-- Source successor after the product schedules the caller continuation on
the left and retains the complete answer history on the right. -/
def privateResumeTarget
    {alpha : List (LogicVar × String)} {source next : Search}
    (history : ScheduledAnswerHistory alpha source next)
    (callerScope predicateScope : CutScopeId) (cursor : PreparedCursor)
    (callerTail : List PeTTaSpec.PrologCore.Goal) : Search :=
  .choice callerScope
    (.task callerScope callerTail history.bindings)
    (.product callerScope
      (enclosingHeadNext history predicateScope cursor) callerTail)

/-- Exact origin of the answer while it crosses the older predicate's
choice and cut boundary.  The surrounding product is deliberately absent:
products consume answers rather than propagate them. -/
def enclosingOrigin
    {alpha : List (LogicVar × String)} {source next : Search}
    (history : ScheduledAnswerHistory alpha source next)
    (predicateScope : CutScopeId) (cursor : PreparedCursor) :
    AnswerOrigin history.leafScope history.bindings
      (enclosingHead history predicateScope cursor)
      (enclosingHeadNext history predicateScope cursor) :=
  .cutBoundary predicateScope
    (.choice predicateScope (.clauses predicateScope cursor) history.origin)

/-- One exact private scheduling transition plus the larger historical right
region it creates.

No payload cell or executable resource is retired.  `history.resources` is
extended by the one older resource in leaf-to-root order, and the resulting
right branch owns that complete slice. -/
structure PrivateScheduledResume
    (alpha : List (LogicVar × String))
    {source next : Search}
    (history : ScheduledAnswerHistory alpha source next)
    (callerScope predicateScope : CutScopeId)
    (cursor : PreparedCursor)
    (callerTail : List PeTTaSpec.PrologCore.Goal)
    (outerResource : RetainedAlternativeSegment) where
  outerOwnership : outerResource.HasIndexedOwnershipAt alpha cursor
  sourceStep :
    ∀ session,
      RawStep session
        (privateResumeSource history callerScope predicateScope cursor
          callerTail)
        [] .none session
        (.running
          (privateResumeTarget history callerScope predicateScope cursor
            callerTail))
  headHistory :
    AnswerOriginResourceAgrees alpha
      (enclosingOrigin history predicateScope cursor)
      (history.resources ++ [outerResource]) []
      (flattenOwnedAlts (history.resources ++ [outerResource]) []) []
  rightRegion :
    RightAlternativeRegionAgrees alpha
      (.product callerScope
        (enclosingHeadNext history predicateScope cursor) callerTail)
      (history.resources ++ [outerResource])
      (flattenOwnedAlts (history.resources ++ [outerResource]) [])

namespace PrivateScheduledResume

/-- Construct one private scheduling layer from the literal older cursor
ownership.  The marker inserted for `outerResource` is consumed exactly once
by the enclosing cut boundary when building the history; it remains present
exactly once in the frozen right-region alternative slice. -/
def ofHistory
    {alpha : List (LogicVar × String)} {source next : Search}
    (history : ScheduledAnswerHistory alpha source next)
    (callerScope predicateScope : CutScopeId)
    (cursor : PreparedCursor)
    (callerTail : List PeTTaSpec.PrologCore.Goal)
    (outerResource : RetainedAlternativeSegment)
    (outerOwnership : outerResource.HasIndexedOwnershipAt alpha cursor) :
    PrivateScheduledResume alpha history callerScope predicateScope cursor
      callerTail outerResource := by
  rcases outerOwnership with ⟨callStart, position, ownership⟩
  let extended :=
    answerOriginResource_appendSuffix history.resourceAgreement [outerResource]
      (outerResource.alts ++ [PLeaTTa.Alt.barrier])
  have throughChoice :
      AnswerOriginResourceAgrees alpha
        (AnswerOrigin.choice predicateScope (.clauses predicateScope cursor)
          history.origin)
        (history.resources ++ [outerResource]) []
        (flattenOwnedAlts history.resources [] ++
          (outerResource.alts ++ [PLeaTTa.Alt.barrier]))
        [PLeaTTa.Alt.barrier] := by
    apply AnswerOriginResourceAgrees.choice
      (inside := history.origin)
      (regionResources := [outerResource])
      (regionAlts := outerResource.alts)
    · simpa only [ScheduledAnswerHistory.resources, List.nil_append,
        List.singleton_append] using extended
    · exact .clauses predicateScope callStart cursor position outerResource
        ownership
  have throughBoundary :
      AnswerOriginResourceAgrees alpha
        (enclosingOrigin history predicateScope cursor)
        (history.resources ++ [outerResource]) []
        (flattenOwnedAlts history.resources [] ++
          (outerResource.alts ++ [PLeaTTa.Alt.barrier])) [] := by
    exact .cutBoundary predicateScope _ throughChoice
  have exactHistory :
      AnswerOriginResourceAgrees alpha
        (enclosingOrigin history predicateScope cursor)
        (history.resources ++ [outerResource]) []
        (flattenOwnedAlts (history.resources ++ [outerResource]) []) [] := by
    have altsExact :
        flattenOwnedAlts (history.resources ++ [outerResource]) [] =
          flattenOwnedAlts history.resources [] ++
            (outerResource.alts ++ [PLeaTTa.Alt.barrier]) := by
      rw [flattenOwnedAlts_append, flattenOwnedAlts_cons,
        flattenOwnedAlts_nil, flattenOwnedAlts_base]
    rw [altsExact]
    exact throughBoundary
  refine
    { outerOwnership := ⟨callStart, position, ownership⟩
      sourceStep := ?_
      headHistory := exactHistory
      rightRegion := ?_ }
  · intro session
    apply RawStep.productAnswer
    exact (enclosingOrigin history predicateScope cursor).toRawStep session
  · exact
      .scheduled callerScope callerTail
        (enclosingOrigin history predicateScope cursor)
        (history.resources ++ [outerResource]) (by simp) exactHistory

/-- The private scheduling transition is exactly one source step with no
public observation and no persistent-session change. -/
theorem sourceStepsN
    {alpha : List (LogicVar × String)} {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    {callerScope predicateScope : CutScopeId}
    {cursor : PreparedCursor}
    {callerTail : List PeTTaSpec.PrologCore.Goal}
    {outerResource : RetainedAlternativeSegment}
    (resume :
      PrivateScheduledResume alpha history callerScope predicateScope cursor
        callerTail outerResource)
    (session : Session) :
    StepsN 1
      (.running session
        (privateResumeSource history callerScope predicateScope cursor
          callerTail))
      []
      (.running session
        (privateResumeTarget history callerScope predicateScope cursor
          callerTail)) := by
  have transition :
      Transition
        (.running session
          (privateResumeSource history callerScope predicateScope cursor
            callerTail))
        []
        (.running session
          (privateResumeTarget history callerScope predicateScope cursor
            callerTail)) :=
    .ordinary _ [] session session _ (resume.sourceStep session)
  exact .succ 0 _ _ _ [] [] transition (.zero _)

/-- Absorbing one older frame grows the scheduled historical resource prefix
by exactly one.  This refutes both accidental retirement and duplication. -/
theorem resourceCount_exact
    {alpha : List (LogicVar × String)} {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    {callerScope predicateScope : CutScopeId}
    {cursor : PreparedCursor}
    {callerTail : List PeTTaSpec.PrologCore.Goal}
    {outerResource : RetainedAlternativeSegment}
    (_resume :
      PrivateScheduledResume alpha history callerScope predicateScope cursor
        callerTail outerResource) :
    (history.resources ++ [outerResource]).length =
      history.resources.length + 1 := by
  simp

/-- If the newly scheduled caller continuation is empty, its answer path is
again a complete scheduled-history packet.  Thus private propagation repeats
one frame at a time without a recursive macro or a stuttering quotient. -/
def nextHistory
    {alpha : List (LogicVar × String)} {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    {callerScope predicateScope : CutScopeId}
    {cursor : PreparedCursor}
    {outerResource : RetainedAlternativeSegment}
    (resume :
      PrivateScheduledResume alpha history callerScope predicateScope cursor
        [] outerResource) :
    ScheduledAnswerHistory alpha
      (privateResumeTarget history callerScope predicateScope cursor [])
      (.choice callerScope .done
        (.product callerScope
          (enclosingHeadNext history predicateScope cursor) [])) :=
  let origin :
      AnswerOrigin callerScope history.bindings
        (privateResumeTarget history callerScope predicateScope cursor [])
        (.choice callerScope .done
          (.product callerScope
            (enclosingHeadNext history predicateScope cursor) [])) :=
    .choice callerScope
      (.product callerScope
        (enclosingHeadNext history predicateScope cursor) [])
      .task
  let agreement :
      AnswerOriginResourceAgrees alpha origin
        (history.resources ++ [outerResource]) []
        (flattenOwnedAlts (history.resources ++ [outerResource]) []) [] :=
    by
      apply AnswerOriginResourceAgrees.choice
        (inside := AnswerOrigin.task)
        (regionResources := history.resources ++ [outerResource])
        (regionAlts :=
          flattenOwnedAlts (history.resources ++ [outerResource]) [])
      · exact
          (by
            simpa only [List.append_nil] using
              (AnswerOriginResourceAgrees.task callerScope history.bindings
                (history.resources ++ [outerResource])
                (flattenOwnedAlts
                  (history.resources ++ [outerResource]) [])))
      · exact resume.rightRegion
  { leafScope := callerScope
    bindings := history.bindings
    resourcesRev := outerResource :: history.resourcesRev
    resourcesRevNonempty := by simp
    origin := origin
    resourceAgreement := by
      simpa [ScheduledAnswerHistory.resources] using agreement }

end PrivateScheduledResume

/-! ## Exact multi-frame private absorption -/

/-- Number of consecutive source frames privately crossed before a public
caller continuation becomes runnable.  Every available frame is crossed at
least once; recursion continues exactly while the crossed caller tail is
empty. -/
def privateResumeCost : List ControlSegment → Nat
  | [] => 0
  | segment :: segments =>
      if segment.references = [] then 1 + privateResumeCost segments else 1

/-- If every caller continuation in the remaining spine is empty, private
answer propagation crosses exactly one source frame per payload cell. -/
theorem privateResumeCost_eq_length_of_all_empty
    (segments : List ControlSegment)
    (allEmpty : ∀ segment ∈ segments, segment.references = []) :
    privateResumeCost segments = segments.length := by
  induction segments with
  | nil => rfl
  | cons segment segments inductionHypothesis =>
      have headEmpty := allEmpty segment (by simp)
      have tailEmpty :
          ∀ candidate ∈ segments, candidate.references = [] := by
        intro candidate member
        exact allEmpty candidate (by simp [member])
      simp [privateResumeCost, headEmpty,
        inductionHypothesis tailEmpty]
      omega

/-- Literal endpoint obtained by crossing private frames until a public
caller continuation is installed.

This function consumes only Type-valued frame data plus the literal answer
history payload.  It cannot inspect the Prop-valued alignment proof used by
the adequacy theorem.  The first nonempty caller tail is installed by its own
crossed frame and stops recursion; an all-empty frame list is exhausted. -/
def absorbContextTarget :
    (context : ActiveProductContext) →
    (bindings : Substitution) → (source next : Search) → Search
  | [], _, source, _ => source
  | frame :: context, bindings, _, next =>
      let right : Search :=
        .product frame.callerScope
          (.cutBoundary frame.predicateScope
            (.choice frame.predicateScope next frame.retained))
          frame.callerRest
      let scheduled : Search :=
        .choice frame.callerScope
          (.task frame.callerScope frame.callerRest bindings) right
      if frame.callerRest = [] then
        absorbContextTarget context bindings scheduled
          (.choice frame.callerScope .done right)
      else
        ActiveProductContext.plug context scheduled

/-- An exact aligned payload/resource context absorbs a local answer through
its maximal empty-caller prefix.

Each recursive case constructs `PrivateScheduledResume.nextHistory`; no
historical intermediate is exposed as a phase state.  The source takes one
real silent step per crossed frame, while the persistent session is carried
literally.  The generic trace provider supplies neither answer content nor
scheduling: both remain determined by the source history and the certified
leftmost product rules. -/
theorem absorbAlignedContext
    {alpha : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (alignment :
      SourceControlResourceContextAgrees alpha qterm currentBarrier segments
        resources inner context outer)
    {source next : Search}
    (history : ScheduledAnswerHistory alpha source next)
    (_scopeExact : history.leafScope = inner)
    (session : Session) :
    StepsN (privateResumeCost segments)
      (.running session (ActiveProductContext.plug context source)) []
      (.running session
        (absorbContextTarget context history.bindings source next)) := by
  induction alignment generalizing source next with
  | nil currentBarrier scope =>
      exact .zero _
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership outerAgrees
      inductionHypothesis =>
      let resume :
          PrivateScheduledResume alpha history nextScope currentScope cursor
            segment.references resource :=
        PrivateScheduledResume.ofHistory history nextScope currentScope cursor
          segment.references resource resourceOwnership
      have firstRaw :
          RawStep session
            (ActiveProductContext.plug
              ({ callerScope := nextScope
                 predicateScope := currentScope
                 retained := .clauses currentScope cursor
                 callerRest := segment.references } :: context)
              source)
            [] .none session
            (.running
              (ActiveProductContext.plug context
                (privateResumeTarget history nextScope currentScope cursor
                  segment.references))) := by
        have lifted :=
          ActiveProductContext.liftProgress context
            (resume.sourceStep session) (by simp [Trace.AnswerFree])
        simpa [ActiveProductContext.plug, ActiveProductFrame.wrap,
          privateResumeSource, enclosingHead] using lifted
      have firstSteps :
          StepsN 1
            (.running session
              (ActiveProductContext.plug
                ({ callerScope := nextScope
                   predicateScope := currentScope
                   retained := .clauses currentScope cursor
                   callerRest := segment.references } :: context)
                source))
            []
            (.running session
              (ActiveProductContext.plug context
                (privateResumeTarget history nextScope currentScope cursor
                  segment.references))) := by
        exact .succ 0 _ _ _ [] [] (.ordinary _ [] _ _ _ firstRaw) (.zero _)
      by_cases empty : segment.references = []
      · let emptyResume :
            PrivateScheduledResume alpha history nextScope currentScope cursor
              [] resource := by
          simpa only [empty] using resume
        let nextHistory := emptyResume.nextHistory
        have tailSteps := inductionHypothesis nextHistory rfl
        have firstStepsEmpty :
            StepsN 1
              (.running session
                (ActiveProductContext.plug
                  ({ callerScope := nextScope
                     predicateScope := currentScope
                     retained := .clauses currentScope cursor
                     callerRest := segment.references } :: context)
                  source))
              []
              (.running session
                (ActiveProductContext.plug context
                  (privateResumeTarget history nextScope currentScope cursor
                    []))) := by
          simpa only [empty] using firstSteps
        have composed := StepsN.trans firstStepsEmpty tailSteps
        simpa [privateResumeCost, absorbContextTarget, empty, emptyResume,
          nextHistory, PrivateScheduledResume.nextHistory,
          privateResumeTarget, enclosingHeadNext] using composed
      · simpa [privateResumeCost, absorbContextTarget, empty,
          privateResumeTarget, enclosingHeadNext] using firstSteps

/-! ## Non-vacuity -/

/-- One real two-frame source/resource zipper inhabits the private scheduling
step introduced above.  The step is exactly one silent source transition,
the new scheduled region owns both resources, and its bank contains exactly
two predicate markers. -/
theorem two_level_private_resume_is_inhabited :
    ∃ session : Session,
      ∃ historySource historyNext : Search,
        ∃ history : ScheduledAnswerHistory
            ([] : List (LogicVar × String)) historySource historyNext,
          ∃ outerCursor : PreparedCursor,
            ∃ outerResource : RetainedAlternativeSegment,
              ∃ _resume :
                  PrivateScheduledResume [] history 3 2 outerCursor []
                    outerResource,
                StepsN 1
                  (.running session
                    (privateResumeSource history 3 2 outerCursor []))
                  []
                  (.running session
                    (privateResumeTarget history 3 2 outerCursor [])) ∧
                (history.resources ++ [outerResource]).length = 2 ∧
                PLeaTTa.barrierCount
                    (flattenOwnedAlts
                      (history.resources ++ [outerResource]) []) = 2 := by
  let segment : ControlSegment :=
    { barrier := 0
      references := []
      executables := [] }
  have segmentAgrees : segment.Agrees [] :=
    PrologOrdinaryStepBridge.NormalizedAlphaGoalsAgree.nil
  obtain
      ⟨innerCursor, outerCursor, innerResource, outerResource, alignment⟩ :=
    two_resource_frames_are_inhabited (.sym "scheduled-answer-query")
      1 2 3 0 segment segment segmentAgrees segmentAgrees
  cases alignment with
  | cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ innerOwnership outerAlignment =>
      cases outerAlignment with
      | cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ outerOwnership tail =>
          let history :=
            ScheduledAnswerHistory.oneLevel 2 1 [] innerCursor innerResource
              innerOwnership
          let resume :
              PrivateScheduledResume [] history 3 2 outerCursor []
                outerResource :=
            PrivateScheduledResume.ofHistory history 3 2 outerCursor []
              outerResource outerOwnership
          let session : Session := default
          refine ⟨session, _, _, history, outerCursor, outerResource, resume,
            ?_, ?_, ?_⟩
          · exact resume.sourceStepsN session
          · simp [history]
          · have count :=
              PLeaTTa.PrologAnswerResourceBridge.AnswerOriginResourceAgrees.scheduled_barrierCount_exact
                resume.rightRegion
            simpa [history] using count

/-- Two consecutive empty caller frames genuinely require two silent source
steps while retaining three cursor scopes: the answer-producing predicate
plus both older predicates.

The current resource comes from a separately indexed query bank, so it is
provably distinct from either outer resource.  This is the anti-vacuity guard
for the unbounded-source/zero-fine-cost scheduling kind: the `n = 2` case is
not a relabelled one-frame transition. -/
theorem two_frame_absorption_is_inhabited :
    ∃ currentCursor firstCursor secondCursor : PreparedCursor,
      ∃ currentResource firstResource secondResource :
          RetainedAlternativeSegment,
        ∃ session : Session, ∃ target : Search,
          let start :=
            ActiveProductContext.plug
              [{ callerScope := 2
                 predicateScope := 1
                 retained := .clauses 1 firstCursor
                 callerRest := [] },
               { callerScope := 3
                 predicateScope := 2
                 retained := .clauses 2 secondCursor
                 callerRest := [] }]
              (ScheduledAnswerHistory.oneLevelSource 1 0 [] currentCursor)
          StepsN 2 (.running session start) [] (.running session target) ∧
            start.liveCursorScopes = [0, 1, 2] ∧
            currentResource ≠ firstResource ∧
            currentResource ≠ secondResource := by
  let emptySegment : ControlSegment :=
    { barrier := 0
      references := []
      executables := [] }
  have emptyAgrees : emptySegment.Agrees [] :=
    PrologOrdinaryStepBridge.NormalizedAlphaGoalsAgree.nil
  obtain
      ⟨currentCursor, _currentSpareCursor, currentResource,
        _currentSpareResource, currentAlignment⟩ :=
    two_resource_frames_are_inhabited (.sym "current-answer-query")
      4 5 6 0 emptySegment emptySegment emptyAgrees emptyAgrees
  obtain
      ⟨firstCursor, secondCursor, firstResource, secondResource,
        outerAlignment⟩ :=
    two_resource_frames_are_inhabited (.sym "outer-answer-query")
      1 2 3 0 emptySegment emptySegment emptyAgrees emptyAgrees
  have currentOwnership :
      currentResource.HasIndexedOwnershipAt [] currentCursor :=
    SourceControlResourceContextAgrees.headOwnership currentAlignment
  have currentQuery :
      currentResource.qterm = .sym "current-answer-query" :=
    SourceControlResourceContextAgrees.headQuery currentAlignment
  have firstQuery :
      firstResource.qterm = .sym "outer-answer-query" :=
    SourceControlResourceContextAgrees.headQuery outerAlignment
  have secondQuery :
      secondResource.qterm = .sym "outer-answer-query" :=
    SourceControlResourceContextAgrees.headQuery outerAlignment.tail
  let history :=
    ScheduledAnswerHistory.oneLevel 1 0 [] currentCursor currentResource
      currentOwnership
  let session : Session := default
  let target :=
    absorbContextTarget
      [{ callerScope := 2
         predicateScope := 1
         retained := .clauses 1 firstCursor
         callerRest := [] },
       { callerScope := 3
         predicateScope := 2
         retained := .clauses 2 secondCursor
         callerRest := [] }]
      history.bindings
      (ScheduledAnswerHistory.oneLevelSource 1 0 [] currentCursor)
      (ScheduledAnswerHistory.oneLevelNext 1 0 currentCursor)
  have steps := absorbAlignedContext outerAlignment history rfl session
  have currentNeFirst : currentResource ≠ firstResource := by
    intro same
    have querySame := congrArg RetainedAlternativeSegment.qterm same
    rw [currentQuery, firstQuery] at querySame
    simp at querySame
  have currentNeSecond : currentResource ≠ secondResource := by
    intro same
    have querySame := congrArg RetainedAlternativeSegment.qterm same
    rw [currentQuery, secondQuery] at querySame
    simp at querySame
  refine
    ⟨currentCursor, firstCursor, secondCursor, currentResource, firstResource,
      secondResource, session, target, ?_, rfl, currentNeFirst,
      currentNeSecond⟩
  simpa [history, target, emptySegment, privateResumeCost] using steps

end PLeaTTa.PrologScheduledAnswerPropagationBridge
