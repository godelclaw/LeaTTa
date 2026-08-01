-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologRetainedPayloadCatchupBridge
Purpose: Carry retained pre-head payload snapshots through exact outer
  resource catch-up to the first live local predicate.
Trusted boundary: none
Main exports:
  FirstLivePayloadSuffix,
  OuterResourceCatchupPartition.payloadAlignedSuffix,
  FirstLivePayloadSuffix.snapshotAtFinish,
  FirstLivePayloadSuffix.snapshotAfterPulledHead
-/
import PLeaTTa.Proofs.PrologRetainedPayloadSnapshotBridge
import PLeaTTa.Proofs.PrologBodyFailureOuterResourceCatchupBridge

namespace PLeaTTa.PrologRetainedPayloadCatchupBridge

open Metta (Atom)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.Resolver
open PrologBodyFailureResourceTransitionBridge
open PrologBodyFailureExhaustedResourceTransitionBridge
open PrologControlSegmentSpineBridge
open PrologPrefilterScanBridge
open PrologProductResourceContextBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
open PrologSourceProductContextBridge
open PrologSupportedCursorAlternativeBridge

/-!
The eager executable may cross several empty retained predicate resources
before installing the first live alternative.  The independent source catches
up later.  The earlier typed zipper proved that source frames, control
segments, and executable resources stay aligned; this module proves that the
new immutable payload cell is dropped at exactly the same rate.
-/

/-- Exact payload-bearing suffix exposed by a first-live outer-resource
partition.

The head snapshot is indexed by `partition.firstCursor` itself, not merely by
some cursor whose frame spelling happens to be propositionally compatible. -/
structure FirstLivePayloadSuffix
    {alpha support : List (LogicVar × String)}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {context : ActiveProductContext}
    (partition :
      OuterResourceCatchupPartition alpha segments resources context)
    (qterm : Atom) (outer : CutScopeId) where
  suffixBarrier : Nat
  suffix :
    SourceControlResourcePayloadContextAgrees alpha support qterm
      suffixBarrier
      (partition.firstSegment :: partition.survivingSegments)
      (partition.first :: partition.survivingResources)
      partition.firstFrame.predicateScope
      (partition.firstFrame :: partition.survivingContext) outer
  activationOrdered : ActivationOrdered suffix
  snapshot :
    RetainedCallPayloadSnapshot alpha support partition.first
      partition.firstCursor partition.firstSegment
      partition.survivingSegments

/-- Exact resource ownership includes the prepared-cursor invariant needed to
transport generated-name bounds across later rejected pulls. -/
theorem OuterResourceCatchupPartition.firstCursorWellFormed
    {alpha : List (LogicVar × String)}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {context : ActiveProductContext}
    (partition :
      OuterResourceCatchupPartition alpha segments resources context) :
    partition.firstCursor.WellFormed := by
  rcases partition.firstOwnership with
    ⟨_callStart, _position, ownership⟩
  rcases ownership.scan with
    ⟨_candidates, wellFormed, _query, _substitutedArgs, _supported,
      _arities, _scan⟩
  exact wellFormed

namespace FirstLivePayloadSuffix

/-- Transport the first live resource's immutable payload across its exact
source-only rejected prefix.

The finite support is unchanged because neither the call payload nor its
runtime spelling changes; only the cursor's frozen suffix and reservation
start move. -/
def snapshotAtFinish
    {alpha support : List (LogicVar × String)}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {context : ActiveProductContext}
    {partition :
      OuterResourceCatchupPartition alpha segments resources context}
    {qterm : Atom} {outer : CutScopeId}
    (suffix :
      FirstLivePayloadSuffix (support := support) partition qterm outer)
    {count : Nat} {finish : PreparedCursor}
    (pulls : RejectedPullsN count partition.firstCursor finish) :
    RetainedCallPayloadSnapshot alpha support partition.first finish
      partition.firstSegment partition.survivingSegments :=
  RetainedCallPayloadSnapshot.transportCursor
    (RetainedCallPayloadSnapshot.RejectedPullsN.preserves_callContext pulls)
    (RetainedCallPayloadSnapshot.RejectedPullsN.reservationStart_le pulls
      (_root_.PLeaTTa.PrologRetainedPayloadCatchupBridge.OuterResourceCatchupPartition.firstCursorWellFormed
        partition))
    (_root_.PLeaTTa.PrologSupportedCallFrontierBridge.RejectedPullsN.preserves_reservedUntil
      pulls)
    suffix.snapshot

/-- After selecting the retained head, move the same immutable payload to the
advanced tail cursor and the executable resource with exactly one alternative
consumed.

This is the complete cursor/resource transport needed by entry-free
reactivation.  It stores no call-entry machine state and performs no MGU.
-/
def snapshotAfterPulledHead
    {alpha support : List (LogicVar × String)}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {context : ActiveProductContext}
    {partition :
      OuterResourceCatchupPartition alpha segments resources context}
    {qterm : Atom} {outer : CutScopeId}
    (suffix :
      FirstLivePayloadSuffix (support := support) partition qterm outer)
    {count : Nat} {finish : PreparedCursor}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    {branchTail : List ClauseBranch} {copied : PLeaTTa.Clause}
    {remainingAlts : List PLeaTTa.Alt}
    (pulls : RejectedPullsN count partition.firstCursor finish)
    (offset :
      PulledHeadOffsetAgrees alpha finish branch clause branchTail copied
        partition.first remainingAlts) :
    RetainedCallPayloadSnapshot alpha support
      (afterPulledHead partition.first remainingAlts)
      (finish.advance branch branchTail)
      partition.firstSegment partition.survivingSegments := by
  exact
    RetainedCallPayloadSnapshot.afterRejectedPullsAndPulledHead
      suffix.snapshot
      (_root_.PLeaTTa.PrologRetainedPayloadCatchupBridge.OuterResourceCatchupPartition.firstCursorWellFormed
        partition)
      pulls offset

end FirstLivePayloadSuffix

/-- Drop the exact crossed prefix from the payload-bearing zipper and expose
the first live resource's original pre-head payload.

The first cursor equality is derived twice: positionally from the payload
zipper and structurally from `partition.firstRetainedShape`.  Thus the
partition cannot be paired with a payload belonging to another retained
occurrence. -/
def OuterResourceCatchupPartition.payloadAlignedSuffix
    {alpha support : List (LogicVar × String)}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {context : ActiveProductContext}
    (partition :
      OuterResourceCatchupPartition alpha segments resources context)
    {qterm : Atom} {currentBarrier : Nat}
    {inner outer : CutScopeId}
    (alignment :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer) :
    ActivationOrdered alignment →
    FirstLivePayloadSuffix (support := support) partition qterm outer := by
  intro ordered
  let count := partition.crossedResources.length
  have crossedFrameLength :
      partition.crossedFrames.length = count := by
    dsimp [count]
    exact partition.crossedWork.length_eq.symm
  have crossedSegmentLength :
      partition.crossedSegments.length = count := by
    dsimp [count]
    exact partition.crossedSegmentDepth
  have within : count ≤ segments.length := by
    rw [partition.segmentsEq]
    simp [count, crossedSegmentLength]
  obtain ⟨suffixBarrier, suffixInner, orderedSuffix⟩ :=
    ActivationOrdered.dropAlignedPrefix alignment ordered count within
  have segmentsDrop :
      segments.drop count =
        partition.firstSegment :: partition.survivingSegments := by
    calc
      segments.drop count =
          (partition.crossedSegments ++
            partition.firstSegment :: partition.survivingSegments).drop
              count :=
        congrArg (List.drop count) partition.segmentsEq
      _ = partition.firstSegment :: partition.survivingSegments := by
        rw [← crossedSegmentLength]
        simp
  have resourcesDrop :
      resources.drop count =
        partition.first :: partition.survivingResources := by
    calc
      resources.drop count =
          (partition.crossedResources ++
            partition.first :: partition.survivingResources).drop count :=
        congrArg (List.drop count) partition.resourcesEq
      _ = partition.first :: partition.survivingResources := by
        simp [count]
  have contextDrop :
      context.drop count =
        partition.firstFrame :: partition.survivingContext := by
    calc
      context.drop count =
          (partition.crossedFrames ++
            partition.firstFrame :: partition.survivingContext).drop count :=
        congrArg (List.drop count) partition.contextEq
      _ = partition.firstFrame :: partition.survivingContext := by
        rw [← crossedFrameLength]
        simp
  rw [segmentsDrop, resourcesDrop, contextDrop] at orderedSuffix
  let suffix := orderedSuffix.1
  have headShape :=
    PLeaTTa.PrologSpinedSourceActivationBridge.SourceControlContextAgrees.head_shape
      suffix.alignment.control
  have scopeEq :
      partition.firstFrame.predicateScope = suffixInner :=
    headShape.1
  subst suffixInner
  let suffixExact := orderedSuffix.1
  have suffixExactOrdered : ActivationOrdered suffixExact :=
    orderedSuffix.2
  let cell := suffixExact.headCell
  have cursorEq : cell.cursor = partition.firstCursor := by
    have shapeEq :
        Search.clauses partition.firstFrame.predicateScope cell.cursor =
          Search.clauses partition.firstFrame.predicateScope
            partition.firstCursor :=
      cell.retainedShape.symm.trans partition.firstRetainedShape
    injection shapeEq
  have snapshot :
      RetainedCallPayloadSnapshot alpha support partition.first
        partition.firstCursor partition.firstSegment
        partition.survivingSegments := by
    simpa [cursorEq] using cell.snapshot
  exact ⟨suffixBarrier, suffixExact, suffixExactOrdered, snapshot⟩

end PLeaTTa.PrologRetainedPayloadCatchupBridge
