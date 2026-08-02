-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologCurrentSessionExhaustedPayloadCatchupBridge
Purpose: Preserve the exact retained payload zipper through active-resource
  exhaustion and ranked outer-resource catch-up.
Trusted boundary: none
Main exports:
  ExhaustedProductPayloadContext,
  ActiveProductPayloadContext.afterRejectedPullsExhausted,
  SpinedExhaustedPayloadResourceRelatesAt,
  SpinedActiveProductPayloadResourceRelatesAt.afterUnifyFailureExhausted,
  SpinedExhaustedPayloadResourceRelatesAt.catchupFirstLive,
  SpinedExhaustedPayloadResourceRelatesAt.catchupTerminal,
  SpinedExhaustedPayloadResourceRelatesAt.catchupClassified
-/
import PLeaTTa.Proofs.PrologCurrentSessionFailurePayloadTransitionBridge
import PLeaTTa.Proofs.PrologRetainedPayloadCatchupBridge

namespace PLeaTTa.PrologCurrentSessionExhaustedPayloadCatchupBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologActivationMacro
open PrologAlphaFreshFrontierBridge
open PrologBooleanAliasSafety
open PrologBodyFailureExhaustedResourceTransitionBridge
open PrologBodyFailureOuterResourceCatchupBridge
open PrologBodyFailureResourceTransitionBridge
open PrologControlSegmentSpineBridge
open PrologCurrentSessionFailurePayloadTransitionBridge
open PrologCurrentSessionPayloadBridge
open PrologCurrentSessionPayloadTransitionBridge
open PrologOrdinaryStepBridge
open PrologPrefilterScanBridge
open PrologProductResourceContextBridge
open PrologProductResourceTransitionBridge
open PrologRepresentativeProductActivationBridge
open PrologRetainedPayloadCatchupBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
open PrologSourceProductContextBridge
open PrologStateBridge
open PrologSupportedCallFrontierBridge

/-!
Primitive failure may exhaust the active retained predicate completely.  The
eager executable then crosses its marker and may also cross several empty
outer predicate resources before the independent source catches up.

The resource-only bridge already accounts for those transitions.  This
module couples the same counted rejection proof to the immutable payload
zipper.  No payload scan is repeated: the active snapshot is transported by
the exact `RejectedPullsN` returned by the resource transition, and outer
payload cells are dropped by the exact ranked partition used by catch-up.
-/

/-- Exact payload zipper while the operational source still owns the empty
active predicate cursor and the eager executable has already crossed that
predicate marker. -/
abbrev ExhaustedProductPayloadContext
    (alpha support : List (LogicVar × String)) (qterm : Atom)
    (opened : OpenedCall) (cursor : PreparedCursor)
    (bodyBarrier callerBarrier : Nat)
    (callerReferences : List PeTTaSpec.PrologCore.Goal)
    (callerExecutables : List PLeaTTa.Goal)
    (outer : List ControlSegment)
    (active : RetainedAlternativeSegment)
    (resources : List RetainedAlternativeSegment)
    (callerScope outerScope : CutScopeId)
    (context : ActiveProductContext) :=
  SourceControlResourcePayloadContextAgrees alpha support qterm bodyBarrier
    ({ barrier := callerBarrier
       references := callerReferences
       executables := callerExecutables } ::
     outer)
    (active :: resources) opened.scope
    ({ callerScope := callerScope
       predicateScope := opened.scope
       retained := .clauses opened.scope cursor
       callerRest := callerReferences } ::
     context)
    outerScope

namespace ActiveProductPayloadContext

/-- Transport only the active payload cell through the exact maximal rejected
suffix which proves that the active local predicate is exhausted.

The returned zipper keeps every outer payload cell literally.  The
`ExhaustedCursorOffsetAgrees` certificate supplies ownership at the exact
result cursor; the counted pulls transport the immutable logical payload to
that same cursor. -/
def afterRejectedPullsExhausted
    {alpha support : List (LogicVar × String)}
    {qterm : Atom}
    {opened : OpenedCall}
    {finish : PreparedCursor} {selected : ClauseBranch}
    {selectedTail : List ClauseBranch}
    {next : PreparedCursor}
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
    (exhausted : ExhaustedCursorOffsetAgrees alpha next active) :
    ExhaustedProductPayloadContext alpha support qterm opened next bodyBarrier
      callerBarrier callerReferences callerExecutables outer active resources
      callerScope outerScope context := by
  cases payloadContext with
  | cons currentBarrier currentScope nextScope finalScope segment segments
      resource retainedResources before retainedContext segmentAgrees
      resourceRest resourceQuery resourceBarrier resourceOwnership snapshot
      outerAgrees =>
      have beforeWellFormed :
          (finish.advance selected selectedTail).WellFormed :=
        PLeaTTa.PrologCurrentSessionFailurePayloadTransitionBridge.RetainedAlternativeSegment.owns_wellFormed
          resourceOwnership
      let nextSnapshot :=
        RetainedCallPayloadSnapshot.afterRejectedPulls snapshot
          beforeWellFormed pulls
      exact
        .cons bodyBarrier opened.scope callerScope outerScope
          { barrier := callerBarrier
            references := callerReferences
            executables := callerExecutables }
          outer active resources next context segmentAgrees resourceRest
          resourceQuery resourceBarrier exhausted.ownership nextSnapshot
          outerAgrees

/-- Rejected pulls preserve every current allocator domination bound.

`reservedUntil` is frozen by the counted rejection derivation, while the
resource descriptor and all outer cells are unchanged. -/
theorem endpointsBelow_afterRejectedPullsExhausted
    {alpha support : List (LogicVar × String)}
    {qterm : Atom}
    {opened : OpenedCall}
    {finish : PreparedCursor} {selected : ClauseBranch}
    {selectedTail : List ClauseBranch}
    {next : PreparedCursor}
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
    (exhausted : ExhaustedCursorOffsetAgrees alpha next active)
    {referenceFloor executableFloor : Nat}
    (below :
      endpointsBelow payloadContext referenceFloor executableFloor) :
    endpointsBelow
      (afterRejectedPullsExhausted payloadContext pulls exhausted)
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
        next.reservedUntil ≤ referenceFloor ∧
          active.finalCounter ≤ executableFloor ∧
          endpointsBelow outerAgrees referenceFloor executableFloor
      exact
        ⟨by
            rw [
              _root_.PLeaTTa.PrologSupportedCallFrontierBridge.RejectedPullsN.preserves_reservedUntil
                pulls]
            exact below.1,
          below.2⟩

/-- Exhausting the active cursor preserves recursive allocation chronology.

The new cursor's reservation start can only advance through rejected pulls;
the active resource allocation seed and every outer chronology proof remain
literal. -/
theorem activationOrdered_afterRejectedPullsExhausted
    {alpha support : List (LogicVar × String)}
    {qterm : Atom}
    {opened : OpenedCall}
    {finish : PreparedCursor} {selected : ClauseBranch}
    {selectedTail : List ClauseBranch}
    {next : PreparedCursor}
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
    (exhausted : ExhaustedCursorOffsetAgrees alpha next active)
    (ordered : ActivationOrdered payloadContext) :
    ActivationOrdered
      (afterRejectedPullsExhausted payloadContext pulls exhausted) := by
  cases payloadContext with
  | cons currentBarrier currentScope nextScope finalScope segment segments
      resource retainedResources before retainedContext segmentAgrees
      resourceRest resourceQuery resourceBarrier resourceOwnership snapshot
      outerAgrees =>
      have beforeWellFormed :
          (finish.advance selected selectedTail).WellFormed :=
        PLeaTTa.PrologCurrentSessionFailurePayloadTransitionBridge.RetainedAlternativeSegment.owns_wellFormed
          resourceOwnership
      have startMono :
          (finish.advance selected selectedTail).reservationStart ≤
            next.reservationStart :=
        RetainedCallPayloadSnapshot.RejectedPullsN.reservationStart_le pulls
          beforeWellFormed
      exact
        ⟨endpointsBelow_mono outerAgrees ordered.1 startMono
            (Nat.le_refl _),
          ordered.2⟩

/-- The exhausted transformation changes no zipper cardinality. -/
theorem cellCount_afterRejectedPullsExhausted
    {alpha support : List (LogicVar × String)}
    {qterm : Atom}
    {opened : OpenedCall}
    {finish : PreparedCursor} {selected : ClauseBranch}
    {selectedTail : List ClauseBranch}
    {next : PreparedCursor}
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
    (exhausted : ExhaustedCursorOffsetAgrees alpha next active) :
    PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount
        (afterRejectedPullsExhausted payloadContext pulls exhausted) =
      PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount
        payloadContext := by
  cases payloadContext
  rfl

end ActiveProductPayloadContext

/-- Fully composed exhausted active-resource phase with its exact payload
zipper.

The operational source cursor, active resource descriptor, source/control
spines, executable successor, and payload cursor are shared indices.
Persistent endpoint bounds refer to the actual post-failure state, while
`activationOrdered` retains the historical allocation order needed after
later outer-cell pops. -/
structure SpinedExhaustedPayloadResourceRelatesAt
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (opened : OpenedCall)
    (pending : DemandDrivenCallStep.PendingCall)
    (bodyBarrier callerBarrier : Nat)
    (callerReferences : List PeTTaSpec.PrologCore.Goal)
    (callerExecutables : List PLeaTTa.Goal)
    (outer : List ControlSegment)
    (qterm : Atom)
    (cursor : PreparedCursor)
    (active : RetainedAlternativeSegment)
    (resources : List RetainedAlternativeSegment)
    (callerScope outerScope : CutScopeId)
    (context : ActiveProductContext)
    (baseAlts : List PLeaTTa.Alt)
    (predecessor : OpenConf)
    (source : Search) (successor : OpenConf)
    (payloadContext :
      ExhaustedProductPayloadContext alpha support qterm opened cursor
        bodyBarrier callerBarrier callerReferences callerExecutables outer
        active resources callerScope outerScope context) : Prop where
  core :
    SpinedExhaustedPostFailureOffsetRelates freshFrontier alpha opened
      pending bodyBarrier callerBarrier callerReferences callerExecutables
      outer qterm cursor active resources callerScope outerScope context
      baseAlts predecessor source successor
  endpointsCurrent :
    endpointsBelow payloadContext opened.session.resolver.nextFresh
      successor.persistent.counter
  activationOrdered : ActivationOrdered payloadContext

namespace SpinedActiveProductPayloadResourceRelatesAt

/-- Primitive equality failure with an empty active executable bank preserves
the complete payload zipper at the exact exhausted source cursor.

The resource theorem returns one counted `RejectedPullsN`; this theorem
passes that same value to `afterRejectedPullsExhausted`.  Thus the source
steps, cursor endpoint, ownership proof, and immutable payload transport
cannot choose different rejected prefixes. [SPEC metta.pl:251-256;
ISO:unification] -/
theorem afterUnifyFailureExhausted
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall}
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
      PrologCurrentSessionPayloadBridge.SpinedActiveProductPayloadResourceRelatesAt
        freshFrontier alpha support canonical referenceBase opened
        opened.session pending finish selected selectedTail altTail
        bodyBarrier callerBarrier (.unify left right :: bodyRest)
        bodyExecutables callerReferences callerExecutables outer current
        runtime qterm active resources callerScope outerScope context baseAlts
        source state payloadContext)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote right))
    (currentSafe : Substitution.BooleanAliasSafe current)
    (leftAliasSafe : TermBooleanAliasSafe left)
    (rightAliasSafe : TermBooleanAliasSafe right)
    (clash : ¬ ∃ result, UnifyResolution current left right result)
    (empty : active.alts = []) :
    ∃ (count : Nat)
        (skippedBranches : List ClauseBranch)
        (skippedClauses candidates : List PLeaTTa.Clause)
        (next : PreparedCursor)
        (pulls :
          RejectedPullsN count (finish.advance selected selectedTail) next)
        (exhausted : ExhaustedCursorOffsetAgrees alpha next active),
      selectedTail = skippedBranches ∧
      candidates = skippedClauses ∧
      skippedBranches.length = count ∧
      skippedClauses.length = count ∧
      (∀ clause ∈ skippedClauses,
        resolutionClauseRetained active.argsv
          (PLeaTTa.subst active.binding active.res) clause = false) ∧
      next.remaining = [] ∧
      StepsN (count + 1)
        (.running opened.session source)
        []
        (.running opened.session
          (ActiveProductContext.plug context
            (sourceProductFrontier callerScope opened next
              callerReferences))) ∧
      DemandDrivenCallStep.Step prog gt (.ready state)
        (.ready (unifyFailureSuccessor state)) ∧
      SpinedExhaustedPayloadResourceRelatesAt freshFrontier alpha support
        opened pending bodyBarrier callerBarrier callerReferences
        callerExecutables outer qterm next active resources callerScope
        outerScope context baseAlts state
        (ActiveProductContext.plug context
          (sourceProductFrontier callerScope opened next callerReferences))
        (unifyFailureSuccessor state)
        (ActiveProductPayloadContext.afterRejectedPullsExhausted
          payloadContext pulls exhausted) := by
  rcases
      PLeaTTa.PrologBodyFailureExhaustedResourceTransitionBridge.SpinedActiveProductResourceRelates.afterUnifyFailureExhausted
        agreement.core leftSupported rightSupported currentSafe leftAliasSafe
          rightAliasSafe clash empty with
    ⟨count, skippedBranches, skippedClauses, candidates, next, pulls,
      selectedTailEq, candidatesEq, branchCount, clauseCount,
      skippedRejected, nextRemainingEmpty, sourceSteps, executableStep,
      post⟩
  let nextPayloadContext :=
    ActiveProductPayloadContext.afterRejectedPullsExhausted payloadContext
      pulls post.exhausted
  have endpointsBefore :
      endpointsBelow nextPayloadContext opened.session.resolver.nextFresh
        state.persistent.counter :=
    ActiveProductPayloadContext.endpointsBelow_afterRejectedPullsExhausted
      payloadContext pulls post.exhausted agreement.endpointsCurrent
  have endpointsAfter :
      endpointsBelow nextPayloadContext opened.session.resolver.nextFresh
        (unifyFailureSuccessor state).persistent.counter := by
    simpa [unifyFailureSuccessor_persistent] using endpointsBefore
  have activationOrdered :
      ActivationOrdered nextPayloadContext :=
    ActiveProductPayloadContext.activationOrdered_afterRejectedPullsExhausted
      payloadContext pulls post.exhausted agreement.activationOrdered
  exact
    ⟨count, skippedBranches, skippedClauses, candidates, next, pulls,
      post.exhausted,
      selectedTailEq, candidatesEq, branchCount, clauseCount, skippedRejected,
      nextRemainingEmpty, sourceSteps, executableStep,
      ⟨post, endpointsAfter, activationOrdered⟩⟩

end SpinedActiveProductPayloadResourceRelatesAt

/-- The structural payload count is exactly the source control-segment
length.

This is proved over the dependent zipper itself.  It cannot be satisfied by
an independently counted resource list with a missing or duplicated payload
cell. -/
theorem payloadCellCount_eq_segments_length
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (payloadContext :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer) :
    PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount
        payloadContext =
      segments.length := by
  induction payloadContext with
  | nil =>
      rfl
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      simp only [
        PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount,
        List.length_cons]
      omega

private theorem aligned_currentBarrier_eq_headResource
    {alpha : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {frame : ActiveProductFrame} {context : ActiveProductContext}
    (alignment :
      SourceControlResourceContextAgrees alpha qterm currentBarrier
        (segment :: segments) (resource :: resources) inner
        (frame :: context) outer) :
    currentBarrier = resource.barrier := by
  cases alignment with
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership outerAgrees =>
      exact resourceBarrier.symm

/-- First-live outer-resource phase coupled to the exact surviving payload
suffix.

`droppedCellCount` accounts for the exhausted active cell plus every crossed
empty outer resource.  The surviving suffix begins at the same first
resource, source frame, control segment, scope, and barrier as `core`. -/
structure SpinedFirstLivePayloadResourceFrontierRelates
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (opened : OpenedCall)
    (pending : DemandDrivenCallStep.PendingCall)
    (qterm : Atom) (cursor : PreparedCursor)
    (bodyBarrier callerBarrier : Nat)
    (callerReferences : List PeTTaSpec.PrologCore.Goal)
    (callerExecutables : List PLeaTTa.Goal)
    (active : RetainedAlternativeSegment)
    (callerScope outerScope : CutScopeId)
    (segments : List ControlSegment)
    (resources : List RetainedAlternativeSegment)
    (context : ActiveProductContext)
    (baseAlts : List PLeaTTa.Alt)
    (predecessor : OpenConf)
    (partition :
      OuterResourceCatchupPartition alpha segments resources context)
    (source : Search) (successor : OpenConf)
    (beforePayload :
      ExhaustedProductPayloadContext alpha support qterm opened
        cursor bodyBarrier callerBarrier callerReferences callerExecutables
        segments active resources callerScope outerScope context)
    (payloadSuffix :
      FirstLivePayloadSuffix (support := support) partition qterm
        outerScope) : Prop where
  core :
    SpinedFirstLiveOuterResourceFrontierRelates freshFrontier alpha opened
      pending qterm outerScope payloadSuffix.suffixBarrier segments resources
      context baseAlts predecessor partition source successor
  droppedCellCount :
    PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount
        beforePayload =
      partition.crossedResources.length + 1 +
        PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount
          payloadSuffix.suffix

namespace SpinedExhaustedPayloadResourceRelatesAt

/-- Catch up from an exhausted active predicate to the first live outer
resource while dropping the payload zipper at exactly the same ranked rate.

The resource theorem supplies the source steps and executable endpoint.  The
payload suffix is derived independently from the literal tail of
`payloadContext`, then joined to the resource result through uniqueness of
the head resource's stored barrier. -/
theorem catchupFirstLive
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {opened : OpenedCall}
    {pending : DemandDrivenCallStep.PendingCall}
    {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {segments : List ControlSegment}
    {qterm : Atom}
    {cursor : PreparedCursor}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {predecessor : OpenConf}
    {source : Search} {successor : OpenConf}
    {payloadContext :
      ExhaustedProductPayloadContext alpha support qterm opened cursor
        bodyBarrier callerBarrier callerReferences callerExecutables segments
        active resources callerScope outerScope context}
    (agreement :
      SpinedExhaustedPayloadResourceRelatesAt freshFrontier alpha support
        opened pending bodyBarrier callerBarrier callerReferences
        callerExecutables segments qterm cursor active resources callerScope
        outerScope context baseAlts predecessor source successor
        payloadContext)
    (partition :
      OuterResourceCatchupPartition alpha segments resources context) :
    ∃ payloadSuffix :
        FirstLivePayloadSuffix (support := support) partition qterm
          outerScope,
      StepsN
          (partition.rejectionSteps +
            partition.crossedFrames.length + 1)
          (.running opened.session source)
          []
          (.running opened.session
            (firstLiveSourceFrontier partition)) ∧
        SpinedFirstLivePayloadResourceFrontierRelates freshFrontier alpha
          support opened pending qterm cursor bodyBarrier callerBarrier
          callerReferences callerExecutables active callerScope outerScope
          segments resources context baseAlts predecessor partition
          (firstLiveSourceFrontier partition) successor payloadContext
          payloadSuffix := by
  let outerPayload :=
    SourceControlResourcePayloadContextAgrees.tail payloadContext
  have outerOrdered : ActivationOrdered outerPayload :=
    ActivationOrdered.tail payloadContext agreement.activationOrdered
  let payloadSuffix :=
    PLeaTTa.PrologRetainedPayloadCatchupBridge.OuterResourceCatchupPartition.payloadAlignedSuffix
      partition outerPayload outerOrdered
  obtain ⟨suffixBarrier, sourceSteps, firstLive⟩ :=
    PLeaTTa.PrologBodyFailureOuterResourceCatchupBridge.SpinedExhaustedPostFailureOffsetRelates.catchupFirstLive
      agreement.core partition
  have coreBarrier :
      suffixBarrier = partition.first.barrier :=
    aligned_currentBarrier_eq_headResource firstLive.suffixAlignment
  have payloadBarrier :
      payloadSuffix.suffixBarrier = partition.first.barrier :=
    aligned_currentBarrier_eq_headResource payloadSuffix.suffix.alignment
  have barrierEq :
      suffixBarrier = payloadSuffix.suffixBarrier :=
    coreBarrier.trans payloadBarrier.symm
  have firstLiveExact :
      SpinedFirstLiveOuterResourceFrontierRelates freshFrontier alpha opened
        pending qterm outerScope payloadSuffix.suffixBarrier segments
        resources context baseAlts predecessor partition
        (firstLiveSourceFrontier partition) successor := by
    simpa only [barrierEq] using firstLive
  have droppedCellCount :
      PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount
          payloadContext =
        partition.crossedResources.length + 1 +
          PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount
            payloadSuffix.suffix := by
    have beforeCount :=
      payloadCellCount_eq_segments_length payloadContext
    have suffixCount :=
      payloadCellCount_eq_segments_length payloadSuffix.suffix
    rw [beforeCount, suffixCount]
    have segmentsLength :=
      congrArg List.length partition.segmentsEq
    have crossedLength :
        partition.crossedSegments.length =
          partition.crossedResources.length :=
      partition.crossedSegmentDepth
    simp only [List.length_cons, List.length_append] at segmentsLength ⊢
    omega
  exact
    ⟨payloadSuffix, sourceSteps,
      ⟨firstLiveExact, droppedCellCount⟩⟩

/-- Terminal outer-resource phase coupled to the original exhausted payload
zipper.

There is intentionally no target payload: the source is terminal.  Instead,
`consumedCellCount` proves that the active cell and every outer cell were
accounted for by the terminal catch-up. -/
structure SpinedTerminalOuterPayloadCatchupRelates
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (opened : OpenedCall)
    (pending : DemandDrivenCallStep.PendingCall)
    (qterm : Atom) (cursor : PreparedCursor)
    (bodyBarrier callerBarrier : Nat)
    (callerReferences : List PeTTaSpec.PrologCore.Goal)
    (callerExecutables : List PLeaTTa.Goal)
    (active : RetainedAlternativeSegment)
    (callerScope outerScope : CutScopeId)
    (segments : List ControlSegment)
    (resources : List RetainedAlternativeSegment)
    (context : ActiveProductContext)
    (baseAlts : List PLeaTTa.Alt)
    (predecessor : OpenConf)
    (partition :
      TerminalOuterResourceCatchupPartition alpha segments resources context
        baseAlts)
    (successor : OpenConf)
    (beforePayload :
      ExhaustedProductPayloadContext alpha support qterm opened cursor
        bodyBarrier callerBarrier callerReferences callerExecutables segments
        active resources callerScope outerScope context) : Prop where
  core :
    SpinedTerminalOuterResourceCatchupRelates freshFrontier alpha opened
      pending qterm callerBarrier callerScope outerScope segments resources
      context baseAlts predecessor partition successor
  consumedCellCount :
    PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount
        beforePayload =
      resources.length + 1

/-- Catch up through every empty outer local resource and the terminal base
bank, consuming the complete payload zipper.

The source step count is expressed directly in terms of the typed payload
cell count.  Therefore a payload zipper with one duplicated or omitted cell
cannot satisfy this terminal correspondence. -/
theorem catchupTerminal
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {opened : OpenedCall}
    {pending : DemandDrivenCallStep.PendingCall}
    {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {segments : List ControlSegment}
    {qterm : Atom}
    {cursor : PreparedCursor}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {predecessor : OpenConf}
    {source : Search} {successor : OpenConf}
    {payloadContext :
      ExhaustedProductPayloadContext alpha support qterm opened cursor
        bodyBarrier callerBarrier callerReferences callerExecutables segments
        active resources callerScope outerScope context}
    (agreement :
      SpinedExhaustedPayloadResourceRelatesAt freshFrontier alpha support
        opened pending bodyBarrier callerBarrier callerReferences
        callerExecutables segments qterm cursor active resources callerScope
        outerScope context baseAlts predecessor source successor
        payloadContext)
    (partition :
      TerminalOuterResourceCatchupPartition alpha segments resources context
        baseAlts) :
    StepsN
        (partition.rejectionSteps +
          PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount
            payloadContext)
        (.running opened.session source)
        [.completed]
        (.terminal opened.session .completed) ∧
      SpinedTerminalOuterPayloadCatchupRelates freshFrontier alpha support
        opened pending qterm cursor bodyBarrier callerBarrier
        callerReferences callerExecutables active callerScope outerScope
        segments resources context baseAlts predecessor partition successor
        payloadContext := by
  obtain ⟨sourceSteps, terminal⟩ :=
    PLeaTTa.PrologBodyFailureOuterResourceCatchupBridge.SpinedExhaustedPostFailureOffsetRelates.catchupTerminal
      agreement.core partition
  have consumedCellCount :
      PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount
          payloadContext =
        resources.length + 1 := by
    have payloadCount :=
      payloadCellCount_eq_segments_length payloadContext
    have segmentResourceLength :
        segments.length = resources.length :=
      partition.segmentDepth
    rw [payloadCount]
    simp only [List.length_cons]
    omega
  have resourceContextLength :
      resources.length = context.length :=
    partition.crossedWork.length_eq
  have stepCount :
      partition.rejectionSteps + context.length + 1 =
        partition.rejectionSteps +
          PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount
            payloadContext := by
    omega
  have sourceStepsExact :
      StepsN
          (partition.rejectionSteps +
            PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount
              payloadContext)
          (.running opened.session source)
          [.completed]
          (.terminal opened.session .completed) := by
    rw [← stepCount]
    exact sourceSteps
  exact
    ⟨sourceStepsExact, ⟨terminal, consumedCellCount⟩⟩

/-! ## Automatic payload-preserving catch-up -/

/-- Exhaustive payload-aware result after automatically classifying every
locally owned outer resource and the arbitrary older base.

The live-base constructor is intentionally only a boundary certificate:
there is no payload suffix or source transition for an executable bank which
is outside the local resource zipper. -/
inductive ExhaustedPayloadCatchupResult
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (opened : OpenedCall)
    (pending : DemandDrivenCallStep.PendingCall)
    (qterm : Atom) (cursor : PreparedCursor)
    (bodyBarrier callerBarrier : Nat)
    (callerReferences : List PeTTaSpec.PrologCore.Goal)
    (callerExecutables : List PLeaTTa.Goal)
    (active : RetainedAlternativeSegment)
    (callerScope outerScope : CutScopeId)
    (segments : List ControlSegment)
    (resources : List RetainedAlternativeSegment)
    (context : ActiveProductContext)
    (baseAlts : List PLeaTTa.Alt)
    (predecessor : OpenConf)
    (source : Search) (successor : OpenConf)
    (payloadContext :
      ExhaustedProductPayloadContext alpha support qterm opened cursor
        bodyBarrier callerBarrier callerReferences callerExecutables segments
        active resources callerScope outerScope context) : Prop where
  | firstLive
      (partition :
        OuterResourceCatchupPartition alpha segments resources context)
      (payloadSuffix :
        FirstLivePayloadSuffix (support := support) partition qterm outerScope)
      (sourceSteps :
        StepsN
          (partition.rejectionSteps +
            partition.crossedFrames.length + 1)
          (.running opened.session source)
          []
          (.running opened.session
            (firstLiveSourceFrontier partition)))
      (relation :
        SpinedFirstLivePayloadResourceFrontierRelates freshFrontier alpha
          support opened pending qterm cursor bodyBarrier callerBarrier
          callerReferences callerExecutables active callerScope outerScope
          segments resources context baseAlts predecessor partition
          (firstLiveSourceFrontier partition) successor payloadContext
          payloadSuffix) :
      ExhaustedPayloadCatchupResult freshFrontier alpha support opened pending
        qterm cursor bodyBarrier callerBarrier callerReferences
        callerExecutables active callerScope outerScope segments resources
        context baseAlts predecessor source successor payloadContext
  | baseLive
      (partition :
        BaseLiveOuterResourceCatchupPartition alpha segments resources context
          baseAlts) :
      ExhaustedPayloadCatchupResult freshFrontier alpha support opened pending
        qterm cursor bodyBarrier callerBarrier callerReferences
        callerExecutables active callerScope outerScope segments resources
        context baseAlts predecessor source successor payloadContext
  | baseCatchResume
      (partition :
        BaseCatchResumeOuterResourceCatchupPartition alpha segments resources
          context baseAlts) :
      ExhaustedPayloadCatchupResult freshFrontier alpha support opened pending
        qterm cursor bodyBarrier callerBarrier callerReferences
        callerExecutables active callerScope outerScope segments resources
        context baseAlts predecessor source successor payloadContext
  | terminal
      (partition :
        TerminalOuterResourceCatchupPartition alpha segments resources context
          baseAlts)
      (sourceSteps :
        StepsN
          (partition.rejectionSteps +
            PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount
              payloadContext)
          (.running opened.session source)
          [.completed]
          (.terminal opened.session .completed))
      (relation :
        SpinedTerminalOuterPayloadCatchupRelates freshFrontier alpha support
          opened pending qterm cursor bodyBarrier callerBarrier
          callerReferences callerExecutables active callerScope outerScope
          segments resources context baseAlts predecessor partition successor
          payloadContext) :
      ExhaustedPayloadCatchupResult freshFrontier alpha support opened pending
        qterm cursor bodyBarrier callerBarrier callerReferences
        callerExecutables active callerScope outerScope segments resources
        context baseAlts predecessor source successor payloadContext

/-- Automatically classify and execute all locally certified payload
catch-up cases.

The generated first-live and terminal partitions are consumed immediately by
the exact payload theorems.  An arbitrary base branch or dormant-catch
resumption remains an explicit uncomposed boundary outcome. -/
theorem catchupClassified
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {opened : OpenedCall}
    {pending : DemandDrivenCallStep.PendingCall}
    {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {segments : List ControlSegment}
    {qterm : Atom}
    {cursor : PreparedCursor}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {predecessor : OpenConf}
    {source : Search} {successor : OpenConf}
    {payloadContext :
      ExhaustedProductPayloadContext alpha support qterm opened cursor
        bodyBarrier callerBarrier callerReferences callerExecutables segments
        active resources callerScope outerScope context}
    (agreement :
      SpinedExhaustedPayloadResourceRelatesAt freshFrontier alpha support
        opened pending bodyBarrier callerBarrier callerReferences
        callerExecutables segments qterm cursor active resources callerScope
        outerScope context baseAlts predecessor source successor
        payloadContext) :
    ExhaustedPayloadCatchupResult freshFrontier alpha support opened pending
      qterm cursor bodyBarrier callerBarrier callerReferences callerExecutables
      active callerScope outerScope segments resources context baseAlts
      predecessor source successor payloadContext := by
  cases
      PLeaTTa.PrologBodyFailureExhaustedResourceTransitionBridge.SourceControlResourceContextAgrees.classifyCatchup
        agreement.core.outerAlignment baseAlts with
  | firstLive partition =>
      obtain ⟨payloadSuffix, sourceSteps, relation⟩ :=
        PLeaTTa.PrologCurrentSessionExhaustedPayloadCatchupBridge.SpinedExhaustedPayloadResourceRelatesAt.catchupFirstLive
          agreement partition
      exact .firstLive partition payloadSuffix sourceSteps relation
  | baseLive partition =>
      exact .baseLive partition
  | baseCatchResume partition =>
      exact .baseCatchResume partition
  | terminal partition =>
      obtain ⟨sourceSteps, relation⟩ :=
        PLeaTTa.PrologCurrentSessionExhaustedPayloadCatchupBridge.SpinedExhaustedPayloadResourceRelatesAt.catchupTerminal
          agreement partition
      exact .terminal partition sourceSteps relation

end SpinedExhaustedPayloadResourceRelatesAt

end PLeaTTa.PrologCurrentSessionExhaustedPayloadCatchupBridge
