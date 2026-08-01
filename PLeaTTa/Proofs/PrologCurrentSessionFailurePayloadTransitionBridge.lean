-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologCurrentSessionFailurePayloadTransitionBridge
Purpose: Preserve exact current-session payload ownership through primitive
  unification failure and its source-only rejected-prefix catch-up.
Trusted boundary: none
Main exports:
  PostFailurePayloadOffsetContext,
  ActiveProductPayloadContext.afterRejectedPullsAndPulledHead,
  SpinedPostFailureFrontierPayloadResourceRelatesAt,
  SpinedActiveProductPayloadResourceRelatesAt.afterUnifyFailureRetained
-/
import PLeaTTa.Proofs.PrologCurrentSessionPayloadTransitionBridge
import PLeaTTa.Proofs.PrologBodyFailureResourceTransitionBridge
import PLeaTTa.Proofs.PrologRetainedPayloadActivationBridge

namespace PLeaTTa.PrologCurrentSessionFailurePayloadTransitionBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PLeaTTa.PrologBooleanAliasSafety
open PrologActivationMacro
open PrologAlphaFreshFrontierBridge
open PrologBodyFailureBacktrackingBridge
open PrologBodyFailureResourceTransitionBridge
open PrologCallPayloadBridge
open PrologControlSegmentSpineBridge
open PrologCurrentSessionPayloadBridge
open PrologCurrentSessionPayloadTransitionBridge
open PrologOrdinaryStepBridge
open PrologPrefilterScanBridge
open PrologProductResourceContextBridge
open PrologProductResourceTransitionBridge
open PrologRecursiveCallPayloadBridge
open PrologRepresentativeCallFrontierBridge
open PrologRepresentativeProductActivationBridge
open PrologRetainedCursorOwnershipBridge
open PrologRetainedPayloadActivationBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
open PrologSourceProductContextBridge
open PrologStateBridge
open PrologSupportedCursorAlternativeBridge

/-!
After primitive equality failure, the independent source has paid its
conservative rejected prefix and is stopped at an unadvanced retained cursor.
The executable has already pulled that cursor's head into `cur`, so its
retained resource and immutable payload snapshot belong to the one-head
advanced cursor.

The ordinary payload zipper cannot express this phase: it would claim that
the source and executable own the same cursor.  The definitions below make the
one-head offset a dependent index while retaining every outer payload cell
literally.
-/

/-- Exact payload zipper in the executable-ahead post-failure phase.

The first source cursor used by the operational frontier is `cursor`; the
payload-bearing retained resource instead owns
`cursor.advance branch branchTail`.  Every outer segment, resource, frame, and
payload cell is unchanged. -/
abbrev PostFailurePayloadOffsetContext
    (alpha support : List (LogicVar × String)) (qterm : Atom)
    (opened : OpenedCall)
    (cursor : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch)
    (bodyBarrier callerBarrier : Nat)
    (callerReferences : List PeTTaSpec.PrologCore.Goal)
    (callerExecutables : List PLeaTTa.Goal)
    (outer : List ControlSegment)
    (resource : RetainedAlternativeSegment)
    (remainingAlts : List PLeaTTa.Alt)
    (resources : List RetainedAlternativeSegment)
    (callerScope outerScope : CutScopeId)
    (context : ActiveProductContext) :=
  SourceControlResourcePayloadContextAgrees alpha support qterm bodyBarrier
    ({ barrier := callerBarrier
       references := callerReferences
       executables := callerExecutables } ::
     outer)
    (afterPulledHead resource remainingAlts :: resources)
    opened.scope
    ({ callerScope := callerScope
       predicateScope := opened.scope
       retained :=
         .clauses opened.scope (cursor.advance branch branchTail)
       callerRest := callerReferences } ::
     context)
    outerScope

namespace PostFailurePayloadOffsetContext

/-- Extract the offset zipper's literal consumed head snapshot.

Unlike the generic `headCell`, this specialized eliminator fixes the cursor
to the one-head advance in its return type.  Subsequent activation therefore
cannot existentially choose a merely shape-compatible cursor. -/
def headSnapshot
    {alpha support : List (LogicVar × String)}
    {qterm : Atom}
    {opened : OpenedCall}
    {cursor : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch}
    {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {remainingAlts : List PLeaTTa.Alt}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    (payloadContext :
      PostFailurePayloadOffsetContext alpha support qterm opened cursor branch
        branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer resource remainingAlts resources callerScope
        outerScope context) :
    RetainedCallPayloadSnapshot alpha support
      (afterPulledHead resource remainingAlts)
      (cursor.advance branch branchTail)
      { barrier := callerBarrier
        references := callerReferences
        executables := callerExecutables }
      outer := by
  cases payloadContext with
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource retainedResources retainedCursor retainedContext segmentAgrees
      resourceRest resourceQuery resourceBarrier resourceOwnership snapshot
      outerAgrees =>
      exact snapshot

end PostFailurePayloadOffsetContext

namespace PulledHeadOffsetAgrees

/-- A retained head really places the payload cursor one source transition
ahead of the operational source cursor. -/
theorem sourceCursor_ne_advanced
    {alpha : List (LogicVar × String)}
    {cursor : PreparedCursor}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    {branchTail : List ClauseBranch} {copied : PLeaTTa.Clause}
    {resource : RetainedAlternativeSegment}
    {remainingAlts : List PLeaTTa.Alt}
    (agreement :
      PulledHeadOffsetAgrees alpha cursor branch clause branchTail copied
        resource remainingAlts) :
    cursor ≠ cursor.advance branch branchTail := by
  intro equal
  have remainingEqual :=
    congrArg (fun item : PreparedCursor => item.remaining) equal
  rw [agreement.cursorRemaining] at remainingEqual
  simp [PreparedCursor.advance] at remainingEqual

end PulledHeadOffsetAgrees

namespace RetainedAlternativeSegment

/-- Exact retained ownership exposes the prepared-cursor invariant without
eliminating its existential proof into payload data. -/
theorem owns_wellFormed
    {alpha : List (LogicVar × String)}
    {cursor : PreparedCursor}
    {resource : RetainedAlternativeSegment}
    (ownership : resource.HasIndexedOwnershipAt alpha cursor) :
    cursor.WellFormed := by
  rcases ownership with ⟨_callStart, _position, exactOwnership⟩
  rcases exactOwnership.scan with
    ⟨_candidates, wellFormed, _query, _substitutedArgs, _supported, _arities,
      _scan⟩
  exact wellFormed

end RetainedAlternativeSegment

namespace ActiveProductPayloadContext

/-- Transform exactly the active payload cell across failure catch-up.

The counted rejected prefix transports the frozen snapshot to the current
source cursor.  The pulled-head offset then advances that cursor once and
consumes one executable alternative.  The outer payload zipper is reused
verbatim. -/
def afterRejectedPullsAndPulledHead
    {alpha support : List (LogicVar × String)}
    {qterm : Atom}
    {opened : OpenedCall}
    {finish : PreparedCursor} {selected : ClauseBranch}
    {selectedTail : List ClauseBranch}
    {next : PreparedCursor}
    {nextBranch : ClauseBranch} {nextClause : PLeaTTa.Clause}
    {nextBranchTail : List ClauseBranch}
    {nextCopied : PLeaTTa.Clause}
    {nextAltTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    (payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish selected
        selectedTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context)
    {count : Nat}
    (pulls :
      RejectedPullsN count (finish.advance selected selectedTail) next)
    (offset :
      PulledHeadOffsetAgrees alpha next nextBranch nextClause nextBranchTail
        nextCopied active nextAltTail) :
    PostFailurePayloadOffsetContext alpha support qterm opened next nextBranch
      nextBranchTail bodyBarrier callerBarrier callerReferences
      callerExecutables outer active nextAltTail resources callerScope
      outerScope context := by
  cases payloadContext with
  | cons currentBarrier currentScope nextScope finalScope segment segments
      resource retainedResources before retainedContext segmentAgrees
      resourceRest resourceQuery resourceBarrier resourceOwnership snapshot
      outerAgrees =>
      have beforeWellFormed :
          (finish.advance selected selectedTail).WellFormed :=
        RetainedAlternativeSegment.owns_wellFormed resourceOwnership
      let nextSnapshot :=
        RetainedCallPayloadSnapshot.afterRejectedPullsAndPulledHead snapshot
          beforeWellFormed pulls offset
      exact
        .cons bodyBarrier opened.scope callerScope outerScope
          { barrier := callerBarrier
            references := callerReferences
            executables := callerExecutables }
          outer (afterPulledHead active nextAltTail) resources
          (next.advance nextBranch nextBranchTail) context
          segmentAgrees
          (by simpa [afterPulledHead] using resourceRest)
          (by simpa [afterPulledHead] using resourceQuery)
          (by simpa [afterPulledHead] using resourceBarrier)
          offset.tailOwnership nextSnapshot outerAgrees

/-- Failure catch-up retains the exact stronger chronology needed to
reactivate the eagerly pulled head.

The result is indexed by the transformed zipper's literal head snapshot.
Thus no proof token from another cursor, resource, or payload can be paired
with this post-failure state. -/
def activationChronology_afterRejectedPullsAndPulledHead
    {alpha support : List (LogicVar × String)}
    {qterm : Atom}
    {opened : OpenedCall}
    {finish : PreparedCursor} {selected : ClauseBranch}
    {selectedTail : List ClauseBranch}
    {next : PreparedCursor}
    {nextBranch : ClauseBranch} {nextClause : PLeaTTa.Clause}
    {nextBranchTail : List ClauseBranch}
    {nextCopied : PLeaTTa.Clause}
    {nextAltTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    (payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish selected
        selectedTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context)
    {count : Nat}
    (pulls :
      RejectedPullsN count (finish.advance selected selectedTail) next)
    (offset :
      PulledHeadOffsetAgrees alpha next nextBranch nextClause nextBranchTail
        nextCopied active nextAltTail) :
    SelectedHeadActivationChronology
      (PostFailurePayloadOffsetContext.headSnapshot
        (afterRejectedPullsAndPulledHead payloadContext pulls offset)) := by
  cases payloadContext with
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource retainedResources before retainedContext segmentAgrees
      resourceRest resourceQuery resourceBarrier resourceOwnership snapshot
      outerAgrees =>
      exact
        SelectedHeadActivationChronology.ofRejectedPullsAndBeforePull snapshot
          (RetainedAlternativeSegment.owns_wellFormed resourceOwnership)
          pulls offset

/-- The transformed head and every unchanged outer payload cell remain below
the same persistent allocator endpoints.

Rejected pulls and the final head advance preserve `reservedUntil`; consuming
the executable head preserves `finalCounter`. -/
theorem endpointsBelow_afterRejectedPullsAndPulledHead
    {alpha support : List (LogicVar × String)}
    {qterm : Atom}
    {opened : OpenedCall}
    {finish : PreparedCursor} {selected : ClauseBranch}
    {selectedTail : List ClauseBranch}
    {next : PreparedCursor}
    {nextBranch : ClauseBranch} {nextClause : PLeaTTa.Clause}
    {nextBranchTail : List ClauseBranch}
    {nextCopied : PLeaTTa.Clause}
    {nextAltTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    (payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish selected
        selectedTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context)
    {count : Nat}
    (pulls :
      RejectedPullsN count (finish.advance selected selectedTail) next)
    (offset :
      PulledHeadOffsetAgrees alpha next nextBranch nextClause nextBranchTail
        nextCopied active nextAltTail)
    {referenceFloor executableFloor : Nat}
    (below :
      endpointsBelow payloadContext referenceFloor executableFloor) :
    endpointsBelow
      (afterRejectedPullsAndPulledHead payloadContext pulls offset)
      referenceFloor executableFloor := by
  cases payloadContext with
  | cons currentBarrier currentScope nextScope finalScope segment segments
      resource retainedResources before retainedContext segmentAgrees
      resourceRest resourceQuery resourceBarrier resourceOwnership snapshot
      outerAgrees =>
      change
        (finish.advance selected selectedTail).reservedUntil ≤
            referenceFloor ∧
          active.finalCounter ≤ executableFloor ∧
          endpointsBelow outerAgrees referenceFloor executableFloor at below
      change
        (next.advance nextBranch nextBranchTail).reservedUntil ≤
            referenceFloor ∧
          (afterPulledHead active nextAltTail).finalCounter ≤ executableFloor ∧
          endpointsBelow outerAgrees referenceFloor executableFloor
      have reservedUntil :
          (next.advance nextBranch nextBranchTail).reservedUntil =
            (finish.advance selected selectedTail).reservedUntil := by
        exact
          (_root_.PLeaTTa.PrologSupportedCallFrontierBridge.RejectedPullsN.preserves_reservedUntil
            pulls).trans rfl
      exact
        ⟨by rw [reservedUntil]; exact below.1,
          by simpa [afterPulledHead] using below.2.1,
          below.2.2⟩

/-- Failure catch-up rewrites only the active payload cell; the complete
outer payload zipper is the identical Type-valued object. -/
theorem outerPayload_afterRejectedPullsAndPulledHead
    {alpha support : List (LogicVar × String)}
    {qterm : Atom}
    {opened : OpenedCall}
    {finish : PreparedCursor} {selected : ClauseBranch}
    {selectedTail : List ClauseBranch}
    {next : PreparedCursor}
    {nextBranch : ClauseBranch} {nextClause : PLeaTTa.Clause}
    {nextBranchTail : List ClauseBranch}
    {nextCopied : PLeaTTa.Clause}
    {nextAltTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    (payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish selected
        selectedTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context)
    {count : Nat}
    (pulls :
      RejectedPullsN count (finish.advance selected selectedTail) next)
    (offset :
      PulledHeadOffsetAgrees alpha next nextBranch nextClause nextBranchTail
        nextCopied active nextAltTail) :
    ActiveProductPayloadContext.outerPayload
        (afterRejectedPullsAndPulledHead payloadContext pulls offset) =
      ActiveProductPayloadContext.outerPayload payloadContext := by
  cases payloadContext
  rfl

/-- Failure catch-up changes only the active payload cell.  The generic
linear tail eliminator therefore returns the identical outer zipper before
and after the one-head offset is installed. -/
theorem tail_afterRejectedPullsAndPulledHead
    {alpha support : List (LogicVar × String)}
    {qterm : Atom}
    {opened : OpenedCall}
    {finish : PreparedCursor} {selected : ClauseBranch}
    {selectedTail : List ClauseBranch}
    {next : PreparedCursor}
    {nextBranch : ClauseBranch} {nextClause : PLeaTTa.Clause}
    {nextBranchTail : List ClauseBranch}
    {nextCopied : PLeaTTa.Clause}
    {nextAltTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    (payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish selected
        selectedTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context)
    {count : Nat}
    (pulls :
      RejectedPullsN count (finish.advance selected selectedTail) next)
    (offset :
      PulledHeadOffsetAgrees alpha next nextBranch nextClause nextBranchTail
        nextCopied active nextAltTail) :
    SourceControlResourcePayloadContextAgrees.tail
        (afterRejectedPullsAndPulledHead payloadContext pulls offset) =
      SourceControlResourcePayloadContextAgrees.tail payloadContext := by
  cases payloadContext
  rfl

/-- Rejected pulls and eager head consumption preserve recursive allocation
chronology.

The transformed head cursor starts no earlier than the original active
cursor, while `afterPulledHead` preserves the resource allocation seed.
Every older cell and its recursive chronology are the literal original
tail. -/
theorem activationOrdered_afterRejectedPullsAndPulledHead
    {alpha support : List (LogicVar × String)}
    {qterm : Atom}
    {opened : OpenedCall}
    {finish : PreparedCursor} {selected : ClauseBranch}
    {selectedTail : List ClauseBranch}
    {next : PreparedCursor}
    {nextBranch : ClauseBranch} {nextClause : PLeaTTa.Clause}
    {nextBranchTail : List ClauseBranch}
    {nextCopied : PLeaTTa.Clause}
    {nextAltTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    (payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish selected
        selectedTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context)
    {count : Nat}
    (pulls :
      RejectedPullsN count (finish.advance selected selectedTail) next)
    (offset :
      PulledHeadOffsetAgrees alpha next nextBranch nextClause nextBranchTail
        nextCopied active nextAltTail)
    (ordered : ActivationOrdered payloadContext) :
    ActivationOrdered
      (afterRejectedPullsAndPulledHead payloadContext pulls offset) := by
  cases payloadContext with
  | cons currentBarrier currentScope nextScope finalScope segment segments
      resource retainedResources before retainedContext segmentAgrees
      resourceRest resourceQuery resourceBarrier resourceOwnership snapshot
      outerAgrees =>
      have beforeWellFormed :
          (finish.advance selected selectedTail).WellFormed :=
        RetainedAlternativeSegment.owns_wellFormed resourceOwnership
      have prefixStartMono :
          (finish.advance selected selectedTail).reservationStart ≤
            next.reservationStart :=
        RetainedCallPayloadSnapshot.RejectedPullsN.reservationStart_le pulls
          beforeWellFormed
      have nextBranchMember : nextBranch ∈ next.remaining := by
        rw [offset.cursorRemaining]
        simp
      have nextStartBelowAdvanced :
          next.reservationStart ≤
            (next.advance nextBranch nextBranchTail).reservationStart := by
        simpa [PreparedCursor.advance] using
          Nat.le_trans
            (offset.cursorWellFormed.1.start_le_member_first nextBranchMember)
            (offset.cursorWellFormed.1.member_first_le_next nextBranchMember)
      have headOrdered :
          endpointsBelow outerAgrees
            (next.advance nextBranch nextBranchTail).reservationStart
            (afterPulledHead active nextAltTail).counter := by
        simpa [afterPulledHead] using
          endpointsBelow_mono outerAgrees ordered.1
            (Nat.le_trans prefixStartMono nextStartBelowAdvanced)
            (Nat.le_succ _)
      exact ⟨headOrdered, ordered.2⟩

/-- The offset phase neither drops nor duplicates a payload-bearing retained
resource. -/
theorem cellCount_afterRejectedPullsAndPulledHead
    {alpha support : List (LogicVar × String)}
    {qterm : Atom}
    {opened : OpenedCall}
    {finish : PreparedCursor} {selected : ClauseBranch}
    {selectedTail : List ClauseBranch}
    {next : PreparedCursor}
    {nextBranch : ClauseBranch} {nextClause : PLeaTTa.Clause}
    {nextBranchTail : List ClauseBranch}
    {nextCopied : PLeaTTa.Clause}
    {nextAltTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    (payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish selected
        selectedTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context)
    {count : Nat}
    (pulls :
      RejectedPullsN count (finish.advance selected selectedTail) next)
    (offset :
      PulledHeadOffsetAgrees alpha next nextBranch nextClause nextBranchTail
        nextCopied active nextAltTail) :
    ActiveProductPayloadContext.cellCount
        (afterRejectedPullsAndPulledHead payloadContext pulls offset) =
      ActiveProductPayloadContext.cellCount payloadContext := by
  cases payloadContext
  rfl

/-- The transformed dependent zipper exposes the exact one-head-advanced
cursor at its first payload cell. -/
theorem headCursor_afterRejectedPullsAndPulledHead
    {alpha support : List (LogicVar × String)}
    {qterm : Atom}
    {opened : OpenedCall}
    {finish : PreparedCursor} {selected : ClauseBranch}
    {selectedTail : List ClauseBranch}
    {next : PreparedCursor}
    {nextBranch : ClauseBranch} {nextClause : PLeaTTa.Clause}
    {nextBranchTail : List ClauseBranch}
    {nextCopied : PLeaTTa.Clause}
    {nextAltTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    (payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish selected
        selectedTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context)
    {count : Nat}
    (pulls :
      RejectedPullsN count (finish.advance selected selectedTail) next)
    (offset :
      PulledHeadOffsetAgrees alpha next nextBranch nextClause nextBranchTail
        nextCopied active nextAltTail) :
    (SourceControlResourcePayloadContextAgrees.headCell
        (afterRejectedPullsAndPulledHead payloadContext pulls offset)).cursor =
      next.advance nextBranch nextBranchTail := by
  cases payloadContext
  rfl

/-- Failure catch-up changes cursor and executable ownership metadata but
preserves the immutable logical representative stored in the retained head
payload. -/
theorem headSnapshotRepresentative_afterRejectedPullsAndPulledHead
    {alpha support : List (LogicVar × String)}
    {qterm : Atom}
    {opened : OpenedCall}
    {finish : PreparedCursor} {selected : ClauseBranch}
    {selectedTail : List ClauseBranch}
    {next : PreparedCursor}
    {nextBranch : ClauseBranch} {nextClause : PLeaTTa.Clause}
    {nextBranchTail : List ClauseBranch}
    {nextCopied : PLeaTTa.Clause}
    {nextAltTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    (payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish selected
        selectedTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context)
    {count : Nat}
    (pulls :
      RejectedPullsN count (finish.advance selected selectedTail) next)
    (offset :
      PulledHeadOffsetAgrees alpha next nextBranch nextClause nextBranchTail
        nextCopied active nextAltTail) :
    (PostFailurePayloadOffsetContext.headSnapshot
      (afterRejectedPullsAndPulledHead payloadContext pulls offset)).residualRepresentative =
      (SourceControlResourcePayloadContextAgrees.headCell payloadContext).snapshot.residualRepresentative := by
  cases payloadContext
  rfl

/-- Consequently the operational source cursor cannot be confused with the
payload cursor already owned by the eager executable head. -/
theorem sourceCursor_ne_payloadHead
    {alpha support : List (LogicVar × String)}
    {qterm : Atom}
    {opened : OpenedCall}
    {finish : PreparedCursor} {selected : ClauseBranch}
    {selectedTail : List ClauseBranch}
    {next : PreparedCursor}
    {nextBranch : ClauseBranch} {nextClause : PLeaTTa.Clause}
    {nextBranchTail : List ClauseBranch}
    {nextCopied : PLeaTTa.Clause}
    {nextAltTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    (payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish selected
        selectedTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context)
    {count : Nat}
    (pulls :
      RejectedPullsN count (finish.advance selected selectedTail) next)
    (offset :
      PulledHeadOffsetAgrees alpha next nextBranch nextClause nextBranchTail
        nextCopied active nextAltTail) :
    next ≠
      (SourceControlResourcePayloadContextAgrees.headCell
        (afterRejectedPullsAndPulledHead payloadContext pulls offset)).cursor := by
  rw [headCursor_afterRejectedPullsAndPulledHead payloadContext pulls offset]
  exact
    PLeaTTa.PrologCurrentSessionFailurePayloadTransitionBridge.PulledHeadOffsetAgrees.sourceCursor_ne_advanced
      offset

end ActiveProductPayloadContext

/-- Fully composed current-session post-failure relation with its exact
one-head-offset payload zipper.

The resource/control relation keeps the operational source cursor unadvanced;
the dependent payload index keeps the immutable snapshot on the advanced
tail cursor. -/
structure SpinedPostFailureFrontierPayloadResourceRelatesAt
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (opened : OpenedCall) (session : Session)
    (pending : DemandDrivenCallStep.PendingCall)
    (bodyBarrier callerBarrier : Nat)
    (callerReferences : List PeTTaSpec.PrologCore.Goal)
    (callerExecutables : List PLeaTTa.Goal)
    (outer : List ControlSegment)
    (qterm : Atom)
    (cursor : PreparedCursor)
    (branch : ClauseBranch) (clause : PLeaTTa.Clause)
    (branchTail : List ClauseBranch)
    (copied : PLeaTTa.Clause)
    (resource : RetainedAlternativeSegment)
    (remainingAlts : List PLeaTTa.Alt)
    (resources : List RetainedAlternativeSegment)
    (callerScope outerScope : CutScopeId)
    (context : ActiveProductContext)
    (baseAlts : List PLeaTTa.Alt)
    (source : Search) (state : OpenConf)
    (payloadContext :
      PostFailurePayloadOffsetContext alpha support qterm opened cursor branch
        branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer resource remainingAlts resources callerScope
        outerScope context) : Prop where
  core :
    SpinedPostFailureFrontierResourceRelatesAt freshFrontier alpha opened
      session pending bodyBarrier callerBarrier callerReferences
      callerExecutables outer qterm cursor branch clause branchTail copied
      resource remainingAlts resources callerScope outerScope context baseAlts
      source state
  endpointsCurrent :
    endpointsBelow payloadContext session.resolver.nextFresh
      state.persistent.counter
  activationOrdered : ActivationOrdered payloadContext
  activationChronology :
    SelectedHeadActivationChronology
      (PostFailurePayloadOffsetContext.headSnapshot payloadContext)
  /-- The retained bank was allocated against the pending call's exact
  executable high-water.  Failure and eager head consumption do not change
  that upper endpoint. -/
  resourceFinalCounter :
    resource.finalCounter = pending.persistent.counter
  /-- Every older payload predates the exact source/executable allocation
  seeds of the retained head waiting to be reactivated. -/
  outerActivationEndpoints :
    endpointsBelow
      (SourceControlResourcePayloadContextAgrees.tail payloadContext)
      branch.firstFresh resource.counter

namespace SpinedActiveProductPayloadResourceRelatesAt

/-- Primitive equality failure preserves the complete current-session payload
bank through the exact rejected-prefix catch-up.

The `RejectedPullsN` witness returned by the resource theorem is consumed
directly by the payload transformation; no second existential scan may choose
a different endpoint. -/
theorem afterUnifyFailureRetained
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {session : Session}
    {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {selected : ClauseBranch}
    {selectedTail : List ClauseBranch}
    {altTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {bodyRest callerReferences : List PeTTaSpec.PrologCore.Goal}
    {bodyExecutables callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {current : Substitution} {runtime : Subst} {qterm : Atom}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {source : Search} {state : OpenConf}
    {payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish selected
        selectedTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context}
    {left right : Term}
    (agreement :
      SpinedActiveProductPayloadResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened session pending finish selected
        selectedTail altTail bodyBarrier callerBarrier
        (.unify left right :: bodyRest) bodyExecutables callerReferences
        callerExecutables outer current runtime qterm active resources
        callerScope outerScope context baseAlts source state payloadContext)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote right))
    (currentSafe : Substitution.BooleanAliasSafe current)
    (leftAliasSafe : TermBooleanAliasSafe left)
    (rightAliasSafe : TermBooleanAliasSafe right)
    (clash : ¬ ∃ result, UnifyResolution current left right result)
    (nonempty : active.alts ≠ []) :
    ∃ (count : Nat)
        (skippedBranches : List ClauseBranch)
        (skippedClauses candidates : List PLeaTTa.Clause)
        (next : PreparedCursor)
        (nextBranch : ClauseBranch) (nextClause : PLeaTTa.Clause)
        (nextBranchTail : List ClauseBranch)
        (nextClauseTail : List PLeaTTa.Clause)
        (nextAltTail : List PLeaTTa.Alt)
        (nextCopied : PLeaTTa.Clause)
        (pulls :
          RejectedPullsN count (finish.advance selected selectedTail) next)
        (offset :
          PulledHeadOffsetAgrees alpha next nextBranch nextClause
            nextBranchTail nextCopied active nextAltTail),
      selectedTail = skippedBranches ++ (nextBranch :: nextBranchTail) ∧
      candidates = skippedClauses ++ (nextClause :: nextClauseTail) ∧
      skippedBranches.length = count ∧
      skippedClauses.length = count ∧
      (∀ clause ∈ skippedClauses,
        resolutionClauseRetained active.argsv
          (PLeaTTa.subst active.binding active.res) clause = false) ∧
      PeTTaSpec.PrologCore.GoalSemantics.StepsN (count + 1)
        (.running session source)
        []
        (.running session
          (ActiveProductContext.plug context
            (sourceProductFrontier callerScope opened next
              callerReferences))) ∧
      DemandDrivenCallStep.Step prog gt (.ready state)
        (.ready (unifyFailureSuccessor state)) ∧
      SpinedPostFailureFrontierPayloadResourceRelatesAt freshFrontier alpha
        support opened session pending bodyBarrier callerBarrier
        callerReferences callerExecutables outer qterm next nextBranch
        nextClause nextBranchTail nextCopied active nextAltTail resources
        callerScope outerScope context baseAlts
        (ActiveProductContext.plug context
          (sourceProductFrontier callerScope opened next callerReferences))
        (unifyFailureSuccessor state)
        (ActiveProductPayloadContext.afterRejectedPullsAndPulledHead
          payloadContext pulls offset) := by
  rcases
      PLeaTTa.PrologBodyFailureResourceTransitionBridge.SpinedActiveProductResourceRelatesAt.afterUnifyFailureRetained
        agreement.core leftSupported rightSupported currentSafe leftAliasSafe
          rightAliasSafe clash nonempty with
    ⟨count, skippedBranches, skippedClauses, candidates, next, nextBranch,
      nextClause, nextBranchTail, nextClauseTail, nextAltTail, nextCopied,
      selectedTailEq, candidatesEq, branchCount, clauseCount, skippedRejected,
      pulls, sourceSteps, executableStep, post⟩
  have endpointsBefore :
      endpointsBelow
        (ActiveProductPayloadContext.afterRejectedPullsAndPulledHead
          payloadContext pulls post.resourceStack.offset)
        session.resolver.nextFresh state.persistent.counter := by
    exact
      ActiveProductPayloadContext.endpointsBelow_afterRejectedPullsAndPulledHead
        payloadContext pulls post.resourceStack.offset
        agreement.endpointsCurrent
  have endpointsAfter :
      endpointsBelow
        (ActiveProductPayloadContext.afterRejectedPullsAndPulledHead
          payloadContext pulls post.resourceStack.offset)
        session.resolver.nextFresh
        (unifyFailureSuccessor state).persistent.counter := by
    simpa [unifyFailureSuccessor_persistent] using endpointsBefore
  have beforeWellFormed :
      (finish.advance selected selectedTail).WellFormed :=
    RetainedAlternativeSegment.owns_wellFormed
      agreement.core.resourceStack.activeOwnership
  have prefixStartMono :
      (finish.advance selected selectedTail).reservationStart ≤
        next.reservationStart :=
    RetainedCallPayloadSnapshot.RejectedPullsN.reservationStart_le pulls
      beforeWellFormed
  have nextBranchMember : nextBranch ∈ next.remaining := by
    rw [post.resourceStack.offset.cursorRemaining]
    simp
  have nextStartBelowBranch :
      next.reservationStart ≤ nextBranch.firstFresh :=
    post.resourceStack.offset.cursorWellFormed.1.start_le_member_first
      nextBranchMember
  have oldOuterAtNextBranch :
      endpointsBelow
        (SourceControlResourcePayloadContextAgrees.tail payloadContext)
        nextBranch.firstFresh active.counter :=
    endpointsBelow_mono
      (SourceControlResourcePayloadContextAgrees.tail payloadContext)
      agreement.outerActivationEndpoints
      (Nat.le_trans prefixStartMono nextStartBelowBranch)
      (Nat.le_refl _)
  have outerActivationEndpoints :
      endpointsBelow
        (SourceControlResourcePayloadContextAgrees.tail
          (ActiveProductPayloadContext.afterRejectedPullsAndPulledHead
            payloadContext pulls post.resourceStack.offset))
        nextBranch.firstFresh active.counter := by
    rw [
      ActiveProductPayloadContext.tail_afterRejectedPullsAndPulledHead
        payloadContext pulls post.resourceStack.offset]
    exact oldOuterAtNextBranch
  have activationOrdered :
      ActivationOrdered
        (ActiveProductPayloadContext.afterRejectedPullsAndPulledHead
          payloadContext pulls post.resourceStack.offset) :=
    ActiveProductPayloadContext.activationOrdered_afterRejectedPullsAndPulledHead
      payloadContext pulls post.resourceStack.offset
      agreement.activationOrdered
  exact
    ⟨count, skippedBranches, skippedClauses, candidates, next, nextBranch,
      nextClause, nextBranchTail, nextClauseTail, nextAltTail, nextCopied,
      pulls, post.resourceStack.offset, selectedTailEq, candidatesEq,
      branchCount, clauseCount, skippedRejected, sourceSteps, executableStep,
      ⟨post, endpointsAfter,
        activationOrdered,
        ActiveProductPayloadContext.activationChronology_afterRejectedPullsAndPulledHead
          payloadContext pulls post.resourceStack.offset,
        agreement.core.resourceStack.activeFinalCounter,
        outerActivationEndpoints⟩⟩

end SpinedActiveProductPayloadResourceRelatesAt

end PLeaTTa.PrologCurrentSessionFailurePayloadTransitionBridge
