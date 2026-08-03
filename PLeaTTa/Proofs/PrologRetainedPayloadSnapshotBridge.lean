-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologRetainedPayloadSnapshotBridge
Purpose: Preserve the pre-head cumulative logical payload required to
  reactivate one retained local-clause resource after later backtracking.
Trusted boundary: none
Main exports:
  RetainedCallControlOrigin,
  CallActivationOrigin,
  RetainedCallPayloadSnapshot,
  RetainedCallPayloadSnapshot.RestorationDataAgrees,
  installedBarrierCache,
  recordedBaseBarrierCache,
  ControlOriginSpineAgrees,
  ControlOriginSpineRelates,
  LocalCallFramesUninterleaved,
  LocalControlOriginSpineRelates,
  RetainedCallPayloadSnapshot.mono,
  RetainedCallPayloadSnapshot.transportCursor,
  RetainedCallPayloadSnapshot.afterRejectedPulls,
  RetainedCallPayloadSnapshot.afterPulledHead,
  RetainedCallPayloadSnapshot.afterRejectedPullsAndPulledHead,
  RetainedCallPayloadSnapshot.sourceBindingShape,
  RetainedCallPayloadSnapshot.currentRepresentative,
  SourceControlResourcePayloadContextAgrees.endpointsBelow_head,
  SpinedRepresentativeProductActivation.activeResourceStackWithSnapshot
-/
import PLeaTTa.Proofs.PrologBodyFailureResourceTransitionBridge

namespace PLeaTTa.PrologRetainedPayloadSnapshotBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologRecursiveCallPayloadBridge
open PrologAlphaFreshFrontierBridge
open PrologRepresentativeStepActivationBridge
open PrologControlSegmentSpineBridge
open PrologMguComposition
open PrologOrdinaryStepBridge
open PrologBodyFailureResourceTransitionBridge
open PrologPrefilterScanBridge
open PrologProductResourceContextBridge
open PrologProductResourceTransitionBridge
open PrologRepresentativeCallFrontierBridge
open PrologRepresentativeProductActivationBridge
open PrologRetainedCursorOwnershipBridge
open PrologSourceProductContextBridge
open PrologStateBridge
open PrologSupportedCursorAlternativeBridge

/-!
An executable retained alternative stores the pre-head runtime binding by
value.  Its semantic cursor stores the corresponding independent binding and
the immutable logical-update snapshot.  Neither object alone retains the
cumulative source/runtime valuation which justified the call.

This module packages that missing proof data at the only sound point: the
original call activation, where the pre-head `TaskSpinePayloadAgrees` and the
literal retained cursor are both present.  The snapshot contains no world,
database, or fresh allocator.  It retains only a compact control origin: the
outer alternatives, barrier-cache mode/value, frame stack, and exact cut-tag
equation needed to reactivate this occurrence.  Persistent world and allocator
state must always come from the current state.
-/

/-- Compact, non-persistent control provenance for one retained call.

The full historical `PendingCall` must not be retained: it contains a stale
world and allocation counter which would be unsound to restore after dynamic
updates or nested calls.  These are exactly the backtrack/control components
consumed by the active-product relation.  `bodyBarrierTag` records the actual
call-entry barrier equation rather than reconstructing it later from the
current cache, whose mode may differ after enclosing control has run. -/
structure RetainedCallControlOrigin where
  bodyBarrier : Nat
  outerAlts : List PLeaTTa.Alt
  outerBarriers : Option Nat
  frames : List Frame
  bodyBarrierTag :
    bodyBarrier =
      outerBarriers.getD (PLeaTTa.barrierCount outerAlts) + 1

namespace RetainedCallControlOrigin

/-- The compact origin was copied from the literal pending control at call
entry.  Persistent state is intentionally absent from both sides. -/
structure MatchesPendingControl
    (origin : RetainedCallControlOrigin)
    (pending : DemandDrivenCallStep.PendingCall) : Prop where
  outerAlts : origin.outerAlts = pending.outer.alts
  outerBarriers : origin.outerBarriers = pending.outer.barriers
  frames : origin.frames = pending.frames

end RetainedCallControlOrigin

/-! ## Persistent-free activation chronology

A retained cursor may later be selected from an outer call whose activation
predates the current database, world, and allocator state.  Retaining the old
`Session` would make it possible to restore persistent state on backtracking;
pairing the old cursor with the current `Session` would instead fabricate an
`OpenedCall` that never occurred.  The indexed origin below records exactly
the monotone activation facts needed by later composition and nothing which
can be restored.
-/

/-- Historical allocator frontiers for one real local-call activation.

The logical-update generation is a type index, not an ordinary field.  Thus a
cursor from one call-start generation cannot be silently retagged as another.
There is deliberately no database, world, control stack, or inverse
constructor back to `OpenedCall`.  Every stored field has a
generation-independent type; adding a generation-dependent field would
require a new transport argument rather than the value-preserving `reindex`
below. -/
structure CallActivationOrigin (generation : Generation) where
  nextFresh : Nat
  nextCutScope : Nat
  nextExceptionScope : Nat
  nextCollectionScope : Nat

namespace CallActivationOrigin

/-- One-way projection from a literal historical session.  Consumers may
retain this compact value, but cannot recover the discarded persistent state. -/
def ofSession (session : Session) :
    CallActivationOrigin session.resolver.database.generation :=
  { nextFresh := session.resolver.nextFresh
    nextCutScope := session.nextCutScope
    nextExceptionScope := session.nextExceptionScope
    nextCollectionScope := session.nextCollectionScope }

/-- Project a session at a propositionally equal generation without exposing
an inverse cast or permitting an unrelated generation to be chosen. -/
def ofSessionAt {generation : Generation} (session : Session)
    (_exact : generation = session.resolver.database.generation) :
    CallActivationOrigin generation :=
  { nextFresh := session.resolver.nextFresh
    nextCutScope := session.nextCutScope
    nextExceptionScope := session.nextExceptionScope
    nextCollectionScope := session.nextCollectionScope }

/-- Transport only the phantom generation index along the exact frozen-cursor
identity.  Every stored frontier remains definitionally unchanged. -/
def reindex {source target : Generation}
    (origin : CallActivationOrigin source) (_exact : target = source) :
    CallActivationOrigin target :=
  { nextFresh := origin.nextFresh
    nextCutScope := origin.nextCutScope
    nextExceptionScope := origin.nextExceptionScope
    nextCollectionScope := origin.nextCollectionScope }

/-- A current session monotonically extends an indexed historical activation.

All five coordinates are load-bearing.  In particular, database generation
is not inferred from allocator monotonicity, and distinct delimiter allocators
are never collapsed into the fresh-name counter. -/
structure Extends {generation : Generation}
    (origin : CallActivationOrigin generation) (current : Session) : Prop where
  generation : generation ≤ current.resolver.database.generation
  fresh : origin.nextFresh ≤ current.resolver.nextFresh
  cut : origin.nextCutScope ≤ current.nextCutScope
  exception : origin.nextExceptionScope ≤ current.nextExceptionScope
  collection : origin.nextCollectionScope ≤ current.nextCollectionScope

/-- The compact projection transports exactly along the already-proved
session chronology relation. -/
theorem ofSession_extends {before after : Session}
    (chronology : SessionHighWatersExtend before after) :
    Extends (ofSession before) after :=
  ⟨chronology.generation, chronology.fresh, chronology.cut,
    chronology.exception, chronology.collection⟩

/-- The compact chronology is reflexive at the activation session. -/
theorem ofSession_refl (session : Session) :
    Extends (ofSession session) session :=
  ofSession_extends (SessionHighWatersExtend.refl session)

/-- A propositionally indexed session projection inherits any later session
chronology without changing a frontier value. -/
theorem ofSessionAt_extends {generation : Generation}
    {before after : Session}
    (exact : generation = before.resolver.database.generation)
    (chronology : SessionHighWatersExtend before after) :
    Extends (ofSessionAt before exact) after := by
  refine
    ⟨?_, chronology.fresh, chronology.cut, chronology.exception,
      chronology.collection⟩
  simpa [exact] using chronology.generation

/-- Later non-backtrackable execution can only strengthen domination of a
fixed historical activation origin. -/
theorem Extends.transSession {generation : Generation}
    {origin : CallActivationOrigin generation} {middle after : Session}
    (before : Extends origin middle)
    (chronology : SessionHighWatersExtend middle after) :
    Extends origin after :=
  ⟨Nat.le_trans before.generation chronology.generation,
    Nat.le_trans before.fresh chronology.fresh,
    Nat.le_trans before.cut chronology.cut,
    Nat.le_trans before.exception chronology.exception,
    Nat.le_trans before.collection chronology.collection⟩

/-- Reindexing along exact cursor identity changes only the phantom generation
and preserves a current-session domination certificate. -/
theorem Extends.reindex {source target : Generation}
    {origin : CallActivationOrigin source} {current : Session}
    (before : Extends origin current) (exact : target = source) :
    Extends (origin.reindex exact) current := by
  subst target
  exact before

/-- Advancing both the logical-update generation and fresh high-water gives a
strict, non-identity activation chronology witness.  This prevents `Extends`
from being read as disguised equality. -/
theorem strict_generation_and_fresh_witness (session : Session) :
    let current : Session :=
      { session with
        resolver :=
          { session.resolver with
            database :=
              { session.resolver.database with
                generation :=
                  session.resolver.database.generation + 1 }
            nextFresh := session.resolver.nextFresh + 1 } }
    Extends (ofSession session) current ∧
      session.resolver.database.generation <
        current.resolver.database.generation ∧
      (ofSession session).nextFresh < current.resolver.nextFresh := by
  dsimp
  refine ⟨?_, Nat.lt_succ_self _, Nat.lt_succ_self _⟩
  exact
    ⟨Nat.le_succ _, Nat.le_succ _, Nat.le_refl _, Nat.le_refl _,
      Nat.le_refl _⟩

end CallActivationOrigin

/-- Immutable pre-head logical payload owned by one retained predicate
resource.

`currentAlpha` may grow while nested calls run.  `snapshotAlpha`,
`support`, the concrete residual representative, and the cumulative
substitution remain the values certified when this resource was created;
`support` is the fixed finite observation domain of that payload, not a
runtime occupied-name set.  Storing the representative as data is
load-bearing: later activation cannot reselect a different legal residual
orientation.  `alphaIncluded` is the only permitted graph transport to a
later alpha.  The caller segment and every older segment are stored exactly
so a later activation cannot retag or flatten distinct cut regions. -/
structure RetainedCallPayloadSnapshot
    (currentAlpha support : List (LogicVar × String))
    (resource : RetainedAlternativeSegment)
    (cursor : PreparedCursor)
    (caller : ControlSegment)
    (outer : List ControlSegment) where
  snapshotAlpha : List (LogicVar × String)
  canonical : TreeSubstitution
  referenceBase : Substitution
  referencePayload : List Term
  /-- One-way, persistent-free projection of the literal call activation.
  Its generation is indexed definitionally by the frozen cursor, so no
  separate equality field or freely chosen generation exists. -/
  activationOrigin : CallActivationOrigin cursor.callGeneration
  /-- The activation's fresh frontier is exactly the end of the cursor's
  eagerly reserved immutable clause bank. -/
  activationFresh : activationOrigin.nextFresh = cursor.reservedUntil
  controlOrigin : RetainedCallControlOrigin
  controlOriginBarrier : controlOrigin.bodyBarrier = resource.barrier
  alphaIncluded :
    ∀ pair, pair ∈ snapshotAlpha → pair ∈ currentAlpha
  /-- Current alpha entries avoid every source interval and executable seed
  still owned by this retained cursor/resource pair.  This is the chronology
  fact which makes later selected-head alpha merging safe. -/
  allocationGap :
    AlphaAllocationGap currentAlpha cursor.reservationStart
      cursor.reservedUntil resource.counter resource.finalCounter
  cursorArguments : cursor.arguments = referencePayload
  residualRepresentative : TreeSubstitution
  cumulative :
    AlphaCumulativeResidualVariantAgreesOnWith snapshotAlpha support canonical
      referenceBase resource.binding residualRepresentative
  materialized :
    MaterializedCallAgreesWith snapshotAlpha cursor.bindings referencePayload
      (resource.args.map (PLeaTTa.subst resource.binding))
      (PLeaTTa.subst resource.binding resource.res) residualRepresentative
      referenceBase
  queryReferenceBelow :
    GeneratedBelow cursor.reservationStart (snapshotAlpha.map Prod.fst)
  queryExecutableBelow :
    resolutionSeedHighWaterNames
        (resolutionOccupiedVars
          (resource.args.map (PLeaTTa.subst resource.binding))
          resource.res resource.rest resource.binding resource.qterm) ≤
      resource.counter
  resourceRest :
    resource.rest =
      caller.executables ++ flattenExecutables outer
  payload :
    TaskSpinePayloadAgrees snapshotAlpha support canonical referenceBase
      cursor.bindings resource.binding
      ({ barrier := caller.barrier
         references :=
           .call cursor.predicate referencePayload :: caller.references
         executables :=
           .call cursor.predicate resource.args resource.res ::
             caller.executables } ::
       outer)

namespace RetainedCallPayloadSnapshot

/-- Two retained snapshots carry the same immutable logical restore state.

Operational indices, current alpha graphs, and allocation-gap proofs may
differ after cursor motion or alpha growth.  These five data fields may not:
they determine the historical query payload and residual orientation that a
later backtrack resumes. -/
structure RestorationDataAgrees
    {leftAlpha leftSupport : List (LogicVar × String)}
    {leftResource : RetainedAlternativeSegment}
    {leftCursor : PreparedCursor}
    {leftCaller : ControlSegment} {leftOuter : List ControlSegment}
    (left :
      RetainedCallPayloadSnapshot leftAlpha leftSupport leftResource
        leftCursor leftCaller leftOuter)
    {rightAlpha rightSupport : List (LogicVar × String)}
    {rightResource : RetainedAlternativeSegment}
    {rightCursor : PreparedCursor}
    {rightCaller : ControlSegment} {rightOuter : List ControlSegment}
    (right :
      RetainedCallPayloadSnapshot rightAlpha rightSupport rightResource
        rightCursor rightCaller rightOuter) : Prop where
  snapshotAlpha : left.snapshotAlpha = right.snapshotAlpha
  canonical : left.canonical = right.canonical
  referenceBase : left.referenceBase = right.referenceBase
  referencePayload : left.referencePayload = right.referencePayload
  residualRepresentative :
    left.residualRepresentative = right.residualRepresentative

/-- Exact restore-data agreement is reflexive even when the operational
snapshot packages carry dependent indices. -/
theorem RestorationDataAgrees.refl
    {currentAlpha support : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {cursor : PreparedCursor}
    {caller : ControlSegment} {outer : List ControlSegment}
    (snapshot :
      RetainedCallPayloadSnapshot currentAlpha support resource cursor caller
        outer) :
    RestorationDataAgrees snapshot snapshot :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Restore-data agreement can be consumed in either orientation. -/
theorem RestorationDataAgrees.symm
    {leftAlpha leftSupport : List (LogicVar × String)}
    {leftResource : RetainedAlternativeSegment}
    {leftCursor : PreparedCursor}
    {leftCaller : ControlSegment} {leftOuter : List ControlSegment}
    {left :
      RetainedCallPayloadSnapshot leftAlpha leftSupport leftResource
        leftCursor leftCaller leftOuter}
    {rightAlpha rightSupport : List (LogicVar × String)}
    {rightResource : RetainedAlternativeSegment}
    {rightCursor : PreparedCursor}
    {rightCaller : ControlSegment} {rightOuter : List ControlSegment}
    {right :
      RetainedCallPayloadSnapshot rightAlpha rightSupport rightResource
        rightCursor rightCaller rightOuter}
    (agreement : RestorationDataAgrees left right) :
    RestorationDataAgrees right left :=
  ⟨agreement.snapshotAlpha.symm, agreement.canonical.symm,
    agreement.referenceBase.symm, agreement.referencePayload.symm,
    agreement.residualRepresentative.symm⟩

/-- Restore-data agreement composes across arbitrarily many retained-head
motions without re-exposing the proof-only fields of either snapshot. -/
theorem RestorationDataAgrees.trans
    {leftAlpha leftSupport : List (LogicVar × String)}
    {leftResource : RetainedAlternativeSegment}
    {leftCursor : PreparedCursor}
    {leftCaller : ControlSegment} {leftOuter : List ControlSegment}
    {left :
      RetainedCallPayloadSnapshot leftAlpha leftSupport leftResource
        leftCursor leftCaller leftOuter}
    {middleAlpha middleSupport : List (LogicVar × String)}
    {middleResource : RetainedAlternativeSegment}
    {middleCursor : PreparedCursor}
    {middleCaller : ControlSegment} {middleOuter : List ControlSegment}
    {middle :
      RetainedCallPayloadSnapshot middleAlpha middleSupport middleResource
        middleCursor middleCaller middleOuter}
    {rightAlpha rightSupport : List (LogicVar × String)}
    {rightResource : RetainedAlternativeSegment}
    {rightCursor : PreparedCursor}
    {rightCaller : ControlSegment} {rightOuter : List ControlSegment}
    {right :
      RetainedCallPayloadSnapshot rightAlpha rightSupport rightResource
        rightCursor rightCaller rightOuter}
    (leftMiddle : RestorationDataAgrees left middle)
    (middleRight : RestorationDataAgrees middle right) :
    RestorationDataAgrees left right :=
  ⟨leftMiddle.snapshotAlpha.trans middleRight.snapshotAlpha,
    leftMiddle.canonical.trans middleRight.canonical,
    leftMiddle.referenceBase.trans middleRight.referenceBase,
    leftMiddle.referencePayload.trans middleRight.referencePayload,
    leftMiddle.residualRepresentative.trans
      middleRight.residualRepresentative⟩

/-- Transport the two operational indices of a retained snapshot along exact
resource and cursor identities.

This constructor is preferable to an elaborator-generated dependent `cast`:
the equalities are explicit inputs, and independent payload projections have
stable reduction theorems below.  It cannot retag a snapshot across merely
similar resources or cursors. -/
def transportResourceCursor
    {currentAlpha support : List (LogicVar × String)}
    {sourceResource targetResource : RetainedAlternativeSegment}
    {sourceCursor targetCursor : PreparedCursor}
    {caller : ControlSegment} {outer : List ControlSegment}
    (resourceExact : sourceResource = targetResource)
    (cursorExact : sourceCursor = targetCursor)
    (snapshot :
      RetainedCallPayloadSnapshot currentAlpha support sourceResource
        sourceCursor caller outer) :
    RetainedCallPayloadSnapshot currentAlpha support targetResource
      targetCursor caller outer := by
  subst targetResource
  subst targetCursor
  exact snapshot

@[simp] theorem controlOrigin_transportResourceCursor
    {currentAlpha support : List (LogicVar × String)}
    {sourceResource targetResource : RetainedAlternativeSegment}
    {sourceCursor targetCursor : PreparedCursor}
    {caller : ControlSegment} {outer : List ControlSegment}
    (resourceExact : sourceResource = targetResource)
    (cursorExact : sourceCursor = targetCursor)
    (snapshot :
      RetainedCallPayloadSnapshot currentAlpha support sourceResource
        sourceCursor caller outer) :
    (transportResourceCursor resourceExact cursorExact snapshot).controlOrigin =
      snapshot.controlOrigin := by
  subst targetResource
  subst targetCursor
  rfl

@[simp] theorem activationNextFresh_transportResourceCursor
    {currentAlpha support : List (LogicVar × String)}
    {sourceResource targetResource : RetainedAlternativeSegment}
    {sourceCursor targetCursor : PreparedCursor}
    {caller : ControlSegment} {outer : List ControlSegment}
    (resourceExact : sourceResource = targetResource)
    (cursorExact : sourceCursor = targetCursor)
    (snapshot :
      RetainedCallPayloadSnapshot currentAlpha support sourceResource
        sourceCursor caller outer) :
    (transportResourceCursor resourceExact cursorExact snapshot).activationOrigin.nextFresh =
      snapshot.activationOrigin.nextFresh := by
  subst targetResource
  subst targetCursor
  rfl

@[simp] theorem activationNextCutScope_transportResourceCursor
    {currentAlpha support : List (LogicVar × String)}
    {sourceResource targetResource : RetainedAlternativeSegment}
    {sourceCursor targetCursor : PreparedCursor}
    {caller : ControlSegment} {outer : List ControlSegment}
    (resourceExact : sourceResource = targetResource)
    (cursorExact : sourceCursor = targetCursor)
    (snapshot :
      RetainedCallPayloadSnapshot currentAlpha support sourceResource
        sourceCursor caller outer) :
    (transportResourceCursor resourceExact cursorExact snapshot).activationOrigin.nextCutScope =
      snapshot.activationOrigin.nextCutScope := by
  subst targetResource
  subst targetCursor
  rfl

@[simp] theorem activationNextExceptionScope_transportResourceCursor
    {currentAlpha support : List (LogicVar × String)}
    {sourceResource targetResource : RetainedAlternativeSegment}
    {sourceCursor targetCursor : PreparedCursor}
    {caller : ControlSegment} {outer : List ControlSegment}
    (resourceExact : sourceResource = targetResource)
    (cursorExact : sourceCursor = targetCursor)
    (snapshot :
      RetainedCallPayloadSnapshot currentAlpha support sourceResource
        sourceCursor caller outer) :
    (transportResourceCursor resourceExact cursorExact snapshot).activationOrigin.nextExceptionScope =
      snapshot.activationOrigin.nextExceptionScope := by
  subst targetResource
  subst targetCursor
  rfl

@[simp] theorem activationNextCollectionScope_transportResourceCursor
    {currentAlpha support : List (LogicVar × String)}
    {sourceResource targetResource : RetainedAlternativeSegment}
    {sourceCursor targetCursor : PreparedCursor}
    {caller : ControlSegment} {outer : List ControlSegment}
    (resourceExact : sourceResource = targetResource)
    (cursorExact : sourceCursor = targetCursor)
    (snapshot :
      RetainedCallPayloadSnapshot currentAlpha support sourceResource
        sourceCursor caller outer) :
    (transportResourceCursor resourceExact cursorExact snapshot).activationOrigin.nextCollectionScope =
      snapshot.activationOrigin.nextCollectionScope := by
  subst targetResource
  subst targetCursor
  rfl

/-- Exact operational-index transport preserves domination by a current
session, including the phantom logical-update generation. -/
theorem activationExtends_transportResourceCursor
    {currentAlpha support : List (LogicVar × String)}
    {sourceResource targetResource : RetainedAlternativeSegment}
    {sourceCursor targetCursor : PreparedCursor}
    {caller : ControlSegment} {outer : List ControlSegment}
    {current : Session}
    (resourceExact : sourceResource = targetResource)
    (cursorExact : sourceCursor = targetCursor)
    (snapshot :
      RetainedCallPayloadSnapshot currentAlpha support sourceResource
        sourceCursor caller outer)
    (dominated : snapshot.activationOrigin.Extends current) :
    (transportResourceCursor resourceExact cursorExact snapshot).activationOrigin.Extends
      current := by
  subst targetResource
  subst targetCursor
  exact dominated

/-- Nested execution may extend the global alpha, but it cannot mutate a
retained resource's frozen pre-head payload. -/
def mono
    {smaller larger support : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {cursor : PreparedCursor}
    {caller : ControlSegment}
    {outer : List ControlSegment}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    (largerGap :
      AlphaAllocationGap larger cursor.reservationStart cursor.reservedUntil
        resource.counter resource.finalCounter)
    (snapshot :
      RetainedCallPayloadSnapshot smaller support resource cursor caller
        outer) :
    RetainedCallPayloadSnapshot larger support resource cursor caller outer :=
  { snapshot with
    alphaIncluded := fun pair member =>
      included pair (snapshot.alphaIncluded pair member)
    allocationGap := largerGap }

/-! ## Frozen-cursor transport

Rejected-prefix execution changes only a prepared cursor's remaining branch
list and reservation start.  The call identity, carried query, retained
resource, and payload support remain fixed.  These lemmas make that stronger
invariance explicit instead of treating `support` as dynamically extensible.
-/

/-- One advance through a well-formed reservation moves the start to the end
of the consumed branch's nonempty fresh interval. -/
theorem advance_reservationStart_le
    {cursor : PreparedCursor} {branch : ClauseBranch}
    {branches : List ClauseBranch}
    (wellFormed : cursor.WellFormed)
    (remaining : cursor.remaining = branch :: branches) :
    cursor.reservationStart ≤
      (cursor.advance branch branches).reservationStart := by
  rcases wellFormed with
    ⟨reserved, _dominated, _owned, _targetsReserved⟩
  unfold PreparedCursor.WellReserved at reserved
  rw [remaining] at reserved
  cases reserved with
  | cons freshSeed entered remaining finalFresh startsAbove nonemptyInterval
      tailReserved =>
      exact Nat.le_trans startsAbove nonemptyInterval

/-- A counted rejected prefix preserves the exact call identity and carried
query of its starting cursor. -/
theorem RejectedPullsN.preserves_callContext
    {count : Nat} {before after : PreparedCursor}
    (pulls : RejectedPullsN count before after) :
    CursorCallContext after before.callGeneration before.predicate
      before.arguments before.bindings := by
  induction pulls with
  | zero cursor =>
      exact CursorCallContext.refl cursor
  | succ count cursor branch branches finish remaining clash tail
      inductionHypothesis =>
      exact inductionHypothesis

/-- On a well-formed frozen cursor, consuming a counted rejected prefix never
rolls its reservation start back. -/
theorem RejectedPullsN.reservationStart_le
    {count : Nat} {before after : PreparedCursor}
    (pulls : RejectedPullsN count before after)
    (wellFormed : before.WellFormed) :
    before.reservationStart ≤ after.reservationStart := by
  induction pulls with
  | zero cursor =>
      exact Nat.le_refl _
  | succ count cursor branch branches finish remaining clash tail
      inductionHypothesis =>
      have one :
          cursor.reservationStart ≤
            (cursor.advance branch branches).reservationStart := by
        exact advance_reservationStart_le wellFormed remaining
      exact
        Nat.le_trans one
          (inductionHypothesis
            (cursor.advance_wellFormed wellFormed remaining))

/-- Retarget a frozen payload snapshot to a cursor reached by cursor-only
motion.

`support` is intentionally unchanged: it certifies the immutable payload.
The separate runtime-liveness field is expressed solely through the unchanged
resource, and the only varying bound is weakened along the cursor reservation
order. -/
def transportCursor
    {currentAlpha support : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {before after : PreparedCursor}
    {caller : ControlSegment}
    {outer : List ControlSegment}
    (context :
      CursorCallContext after before.callGeneration before.predicate
        before.arguments before.bindings)
    (reservationOrdered :
      before.reservationStart ≤ after.reservationStart)
    (reservedUntil :
      after.reservedUntil = before.reservedUntil)
    (snapshot :
      RetainedCallPayloadSnapshot currentAlpha support resource before caller
        outer) :
    RetainedCallPayloadSnapshot currentAlpha support resource after caller
      outer :=
  { snapshot with
    activationOrigin :=
      snapshot.activationOrigin.reindex context.generation
    activationFresh := by
      change snapshot.activationOrigin.nextFresh = after.reservedUntil
      rw [reservedUntil]
      exact snapshot.activationFresh
    cursorArguments := context.arguments_eq.trans snapshot.cursorArguments
    materialized := by
      simpa [context.bindings_eq] using snapshot.materialized
    queryReferenceBelow :=
      snapshot.queryReferenceBelow.mono reservationOrdered
    allocationGap := by
      have advanced :=
        snapshot.allocationGap.advance reservationOrdered (Nat.le_refl _)
      simpa [reservedUntil] using advanced
    payload := by
      simpa [context.predicate_eq, context.bindings_eq] using snapshot.payload }

@[simp] theorem controlOrigin_transportCursor
    {currentAlpha support : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {before after : PreparedCursor}
    {caller : ControlSegment} {outer : List ControlSegment}
    (context :
      CursorCallContext after before.callGeneration before.predicate
        before.arguments before.bindings)
    (reservationOrdered : before.reservationStart ≤ after.reservationStart)
    (reservedUntil : after.reservedUntil = before.reservedUntil)
    (snapshot :
      RetainedCallPayloadSnapshot currentAlpha support resource before caller
        outer) :
    (transportCursor context reservationOrdered reservedUntil snapshot).controlOrigin =
      snapshot.controlOrigin := rfl

@[simp] theorem activationNextCutScope_transportCursor
    {currentAlpha support : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {before after : PreparedCursor}
    {caller : ControlSegment} {outer : List ControlSegment}
    (context :
      CursorCallContext after before.callGeneration before.predicate
        before.arguments before.bindings)
    (reservationOrdered : before.reservationStart ≤ after.reservationStart)
    (reservedUntil : after.reservedUntil = before.reservedUntil)
    (snapshot :
      RetainedCallPayloadSnapshot currentAlpha support resource before caller
        outer) :
    (transportCursor context reservationOrdered reservedUntil snapshot).activationOrigin.nextCutScope =
      snapshot.activationOrigin.nextCutScope := rfl

/-- Cursor-only transport reindexes the activation origin along the cursor's
exact generation identity and therefore preserves current-session
domination. -/
theorem activationExtends_transportCursor
    {currentAlpha support : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {before after : PreparedCursor}
    {caller : ControlSegment} {outer : List ControlSegment}
    {current : Session}
    (context :
      CursorCallContext after before.callGeneration before.predicate
        before.arguments before.bindings)
    (reservationOrdered : before.reservationStart ≤ after.reservationStart)
    (reservedUntil : after.reservedUntil = before.reservedUntil)
    (snapshot :
      RetainedCallPayloadSnapshot currentAlpha support resource before caller
        outer)
    (dominated : snapshot.activationOrigin.Extends current) :
    (transportCursor context reservationOrdered reservedUntil snapshot).activationOrigin.Extends
      current := by
  simpa [transportCursor] using dominated.reindex context.generation

/-- Consume the executable alternative corresponding to the selected head
without changing any payload-bearing resource field.

The counter and alternative suffix are operational ownership data only.
Neither participates in the cumulative logical payload or its fixed support.
-/
def afterPulledHead
    {currentAlpha support : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {cursor : PreparedCursor}
    {caller : ControlSegment}
    {outer : List ControlSegment}
    (remainingAlts : List PLeaTTa.Alt)
    (snapshot :
      RetainedCallPayloadSnapshot currentAlpha support resource cursor caller
        outer) :
    RetainedCallPayloadSnapshot currentAlpha support
      (_root_.PLeaTTa.PrologBodyFailureResourceTransitionBridge.afterPulledHead
        resource remainingAlts)
      cursor caller outer := by
  refine
    { snapshotAlpha := snapshot.snapshotAlpha
      canonical := snapshot.canonical
      referenceBase := snapshot.referenceBase
      referencePayload := snapshot.referencePayload
      activationOrigin := snapshot.activationOrigin
      activationFresh := snapshot.activationFresh
      controlOrigin := by
        simpa
          [_root_.PLeaTTa.PrologBodyFailureResourceTransitionBridge.afterPulledHead]
          using snapshot.controlOrigin
      controlOriginBarrier := by
        simpa
          [_root_.PLeaTTa.PrologBodyFailureResourceTransitionBridge.afterPulledHead]
          using snapshot.controlOriginBarrier
      alphaIncluded := snapshot.alphaIncluded
      allocationGap := by
        have advanced :=
          snapshot.allocationGap.advance (Nat.le_refl _)
            (Nat.le_succ resource.counter)
        simpa
          [_root_.PLeaTTa.PrologBodyFailureResourceTransitionBridge.afterPulledHead]
          using advanced
      cursorArguments := snapshot.cursorArguments
      residualRepresentative := snapshot.residualRepresentative
      cumulative := by
        simpa
          [_root_.PLeaTTa.PrologBodyFailureResourceTransitionBridge.afterPulledHead]
          using snapshot.cumulative
      materialized := by
        simpa
          [_root_.PLeaTTa.PrologBodyFailureResourceTransitionBridge.afterPulledHead]
          using snapshot.materialized
      queryReferenceBelow := snapshot.queryReferenceBelow
      queryExecutableBelow := ?_
      resourceRest := ?_
      payload := ?_ }
  · have oldBound := snapshot.queryExecutableBelow
    simpa
      [_root_.PLeaTTa.PrologBodyFailureResourceTransitionBridge.afterPulledHead]
      using Nat.le_trans oldBound (Nat.le_succ resource.counter)
  · simpa
      [_root_.PLeaTTa.PrologBodyFailureResourceTransitionBridge.afterPulledHead]
      using snapshot.resourceRest
  · simpa
      [_root_.PLeaTTa.PrologBodyFailureResourceTransitionBridge.afterPulledHead]
      using snapshot.payload

/-- Transport one immutable payload cell through a counted rejected prefix
without consuming the executable alternative at the resulting head.

This is the exact pre-pull logical snapshot needed to retain activation
chronology across the executable-ahead offset. -/
def afterRejectedPulls
    {currentAlpha support : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {before finish : PreparedCursor}
    {count : Nat}
    {caller : ControlSegment}
    {outer : List ControlSegment}
    (snapshot :
      RetainedCallPayloadSnapshot currentAlpha support resource before caller
        outer)
    (beforeWellFormed : before.WellFormed)
    (pulls : RejectedPullsN count before finish) :
    RetainedCallPayloadSnapshot currentAlpha support resource finish caller
      outer :=
  transportCursor
    (RejectedPullsN.preserves_callContext pulls)
    (RejectedPullsN.reservationStart_le pulls beforeWellFormed)
    (_root_.PLeaTTa.PrologSupportedCallFrontierBridge.RejectedPullsN.preserves_reservedUntil
      pulls)
    snapshot

/-- Transport one immutable payload cell through a counted rejected prefix
and the immediately following eager pulled-head offset.

The rejected prefix changes only the frozen cursor suffix and its reservation
start.  Pulling the retained head then advances that cursor exactly once and
consumes exactly one executable alternative.  The payload support,
cumulative substitutions, caller segment, and every older segment stay
literal. -/
def afterRejectedPullsAndPulledHead
    {currentAlpha support : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {before finish : PreparedCursor}
    {count : Nat}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    {branchTail : List ClauseBranch} {copied : PLeaTTa.Clause}
    {remainingAlts : List PLeaTTa.Alt}
    {caller : ControlSegment}
    {outer : List ControlSegment}
    (snapshot :
      RetainedCallPayloadSnapshot currentAlpha support resource before caller
        outer)
    (beforeWellFormed : before.WellFormed)
    (pulls : RejectedPullsN count before finish)
    (offset :
      PulledHeadOffsetAgrees currentAlpha finish branch clause branchTail
        copied resource remainingAlts) :
    RetainedCallPayloadSnapshot currentAlpha support
      (_root_.PLeaTTa.PrologBodyFailureResourceTransitionBridge.afterPulledHead
        resource remainingAlts)
      (finish.advance branch branchTail) caller outer := by
  let atFinish := afterRejectedPulls snapshot beforeWellFormed pulls
  have advancedContext :
      CursorCallContext (finish.advance branch branchTail)
        finish.callGeneration finish.predicate finish.arguments
        finish.bindings :=
    (CursorCallContext.refl finish).advance branch branchTail
  let atAdvanced :=
    transportCursor advancedContext
      (advance_reservationStart_le offset.cursorWellFormed
        offset.cursorRemaining)
      rfl atFinish
  exact afterPulledHead remainingAlts atAdvanced

/-- The semantic binding restored on backtracking is exactly the cumulative
source substitution certified at resource creation. -/
theorem sourceBindingShape
    {currentAlpha support : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {cursor : PreparedCursor}
    {caller : ControlSegment}
    {outer : List ControlSegment}
    (snapshot :
      RetainedCallPayloadSnapshot currentAlpha support resource cursor caller
        outer) :
    cursor.bindings =
      TreeSubstitution.reify snapshot.canonical ++ snapshot.referenceBase :=
  snapshot.payload.data.bindingShape

/-- Recover the exact call-headed payload for the retained resource without
consulting any historical executable configuration. -/
theorem callPayload
    {currentAlpha support : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {cursor : PreparedCursor}
    {caller : ControlSegment}
    {outer : List ControlSegment}
    (snapshot :
      RetainedCallPayloadSnapshot currentAlpha support resource cursor caller
        outer) :
    TaskPayloadAgrees snapshot.snapshotAlpha support caller.barrier
      snapshot.canonical snapshot.referenceBase cursor.bindings
      resource.binding
      (.call cursor.predicate snapshot.referencePayload ::
        caller.references)
      (.call cursor.predicate resource.args resource.res ::
        caller.executables) :=
  snapshot.payload.headPayload

/-- Recover the representative exactly at snapshot creation, before any
ambient alpha extension caused by nested execution.

This is the payload-side input to retained activation: allocator history may
extend the ambient graph, but the hidden residual orientation and its
below-reservation proof remain certified on `snapshotAlpha`. -/
theorem representative
    {currentAlpha support : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {cursor : PreparedCursor}
    {caller : ControlSegment}
    {outer : List ControlSegment}
    (snapshot :
      RetainedCallPayloadSnapshot currentAlpha support resource cursor caller
        outer) :
    ∃ representative : TreeSubstitution,
      AlphaCumulativeResidualVariantAgreesOnWith
        snapshot.snapshotAlpha support snapshot.canonical
        snapshot.referenceBase resource.binding representative ∧
      RepresentativeNormalizedCallAgreesWith snapshot.snapshotAlpha cursor
        (resource.args.map (PLeaTTa.subst resource.binding))
        (PLeaTTa.subst resource.binding resource.res)
        representative snapshot.referenceBase :=
  ⟨snapshot.residualRepresentative, snapshot.cumulative,
    snapshot.materialized.toRepresentativeNormalizedCallAgreesWith cursor
      snapshot.cursorArguments rfl⟩

/-- Recover the one representative selected at snapshot creation and
transport that exact witness to the current alpha graph.

Only alpha-indexed coverage and valuation leaves are weakened.  The
representative, canonical substitution, older base, cursor, payload support,
and runtime binding remain literally unchanged.  `currentShared` is not
manufactured here; activation must separately obtain sharedness of the
current graph from the reachable-state invariant. -/
theorem currentRepresentative
    {currentAlpha support : List (LogicVar × String)}
    {resource : RetainedAlternativeSegment}
    {cursor : PreparedCursor}
    {caller : ControlSegment}
    {outer : List ControlSegment}
    (snapshot :
      RetainedCallPayloadSnapshot currentAlpha support resource cursor caller
        outer) :
    ∃ representative : TreeSubstitution,
      AlphaCumulativeResidualVariantAgreesOnWith
        currentAlpha support snapshot.canonical snapshot.referenceBase
        resource.binding representative ∧
      RepresentativeNormalizedCallAgreesWith currentAlpha cursor
        (resource.args.map (PLeaTTa.subst resource.binding))
        (PLeaTTa.subst resource.binding resource.res)
        representative snapshot.referenceBase := by
  obtain ⟨representative, cumulative, query⟩ :=
    snapshot.representative
  have currentCumulative :
      AlphaCumulativeResidualVariantAgreesOnWith
        currentAlpha support snapshot.canonical snapshot.referenceBase
        resource.binding representative := by
    refine
      { variants := cumulative.variants
        canonicalTopological := cumulative.canonicalTopological
        representativeCovered := ?_
        runtimeTopological := cumulative.runtimeTopological
        valuation := ?_ }
    · exact
        PLeaTTa.PrologRepresentativeTaskActivationBridge.TreeSubstitutionVariablesSatisfy.monoAlpha
          snapshot.alphaIncluded cumulative.representativeCovered
    · exact
        PLeaTTa.PrologRepresentativeTaskActivationBridge.AlphaValuationAgreesOn.monoAlpha
          snapshot.alphaIncluded cumulative.valuation
  have currentQuery :
      RepresentativeNormalizedCallAgreesWith currentAlpha cursor
        (resource.args.map (PLeaTTa.subst resource.binding))
        (PLeaTTa.subst resource.binding resource.res)
        representative snapshot.referenceBase := by
    refine
      { variants := query.variants
        residualCovered := ?_
        olderBaseIncluded := query.olderBaseIncluded
        arguments := ?_ }
    · exact
        PLeaTTa.PrologRepresentativeTaskActivationBridge.TreeSubstitutionVariablesSatisfy.monoAlpha
          snapshot.alphaIncluded query.residualCovered
    · exact
        List.Forall₂.imp
          (fun _term _atom agreement =>
            PLeaTTa.PrologRepresentativeActivationBridge.CanonicalRuntimeAgrees.mono
              snapshot.alphaIncluded agreement)
          query.arguments
  exact ⟨representative, currentCumulative, currentQuery⟩

end RetainedCallPayloadSnapshot

/-! ## Exact payload-bearing outer-resource zipper -/

/-- Arbitrary-depth alignment of source frames, executable resource
descriptors, caller control segments, and the immutable payload snapshot owned
by each retained predicate.

This strengthens `SourceControlResourceContextAgrees` without changing its
runtime indices.  Every constructor is one linear cell; there is no separate
snapshot list which could be permuted, shortened, or paired with a different
cursor. -/
inductive SourceControlResourcePayloadContextAgrees
    (alpha support : List (LogicVar × String)) (qterm : Atom) :
    Nat → List ControlSegment → List RetainedAlternativeSegment →
      CutScopeId → ActiveProductContext → CutScopeId → Type where
  | nil (currentBarrier : Nat) (scope : CutScopeId) :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier [] [] scope [] scope
  | cons (currentBarrier : Nat)
      (currentScope nextScope outerScope : CutScopeId)
      (segment : ControlSegment) (segments : List ControlSegment)
      (resource : RetainedAlternativeSegment)
      (resources : List RetainedAlternativeSegment)
      (cursor : PreparedCursor) (context : ActiveProductContext)
      (segmentAgrees : segment.Agrees alpha)
      (resourceRest :
        resource.rest =
          segment.executables ++ flattenExecutables segments)
      (resourceQuery : resource.qterm = qterm)
      (resourceBarrier : resource.barrier = currentBarrier)
      (resourceOwnership : resource.HasIndexedOwnershipAt alpha cursor)
      (snapshot :
        RetainedCallPayloadSnapshot alpha support resource cursor segment
          segments)
      (outerAgrees :
        SourceControlResourcePayloadContextAgrees alpha support qterm
          segment.barrier segments resources nextScope context outerScope) :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier (segment :: segments) (resource :: resources)
        currentScope
        ({ callerScope := nextScope
           predicateScope := currentScope
           retained := .clauses currentScope cursor
           callerRest := segment.references } ::
         context)
        outerScope

namespace SourceControlResourcePayloadContextAgrees

/-- Remove the unique head cell of a nonempty payload zipper.

The return type retains every outer cursor, resource, control segment, and
typed scope literally.  This is the generic linear tail operation used by
active, scheduled, committed, and post-failure payload relations. -/
def tail
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {frame : ActiveProductFrame} {context : ActiveProductContext}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier (segment :: segments) (resource :: resources) inner
        (frame :: context) outer) :
    SourceControlResourcePayloadContextAgrees alpha support qterm
      segment.barrier segments resources frame.callerScope context outer := by
  cases agreement with
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees =>
      exact outerAgrees

/-- Erasing only the immutable payload certificates recovers the exact
already-audited source/control/resource alignment. -/
def alignment
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext} :
    SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer →
      SourceControlResourceContextAgrees alpha qterm currentBarrier segments
        resources inner context outer
  | .nil currentBarrier scope => .nil currentBarrier scope
  | .cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership _snapshot outerAgrees =>
      .cons currentBarrier currentScope nextScope outerScope segment segments
        resource resources cursor context segmentAgrees resourceRest
        resourceQuery resourceBarrier resourceOwnership outerAgrees.alignment

/-- Nested calls may extend the shared alpha while every retained payload,
segment, cursor, and resource keeps its exact identity and order. -/
def mono
    {smaller larger support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    (gaps :
      ∀ {resource cursor segment outerSegments},
        RetainedCallPayloadSnapshot smaller support resource cursor segment
            outerSegments →
          AlphaAllocationGap larger cursor.reservationStart
            cursor.reservedUntil resource.counter resource.finalCounter) :
    SourceControlResourcePayloadContextAgrees smaller support qterm
        currentBarrier segments resources inner context outer →
      SourceControlResourcePayloadContextAgrees larger support qterm
        currentBarrier segments resources inner context outer
  | .nil currentBarrier scope => .nil currentBarrier scope
  | .cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees =>
      .cons currentBarrier currentScope nextScope outerScope segment segments
        resource resources cursor context (segmentAgrees.mono included)
        resourceRest resourceQuery resourceBarrier
        (resourceOwnership.mono included)
        (snapshot.mono included (gaps snapshot))
        (outerAgrees.mono included gaps)

/-- Every retained source reservation and executable alternative bank in
this exact payload zipper was created no later than the supplied allocator
floors.

The predicate recurses over the agreement itself rather than over separate
cursor/resource lists.  Consequently a domination proof cannot be permuted
or paired with a different payload cell. -/
def endpointsBelow
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer)
    (referenceFloor executableFloor : Nat) : Prop :=
  match agreement with
  | .nil _ _ => True
  | .cons _ _ _ _ _ _ resource _ cursor _ _ _ _ _ _ _ outerAgrees =>
      cursor.reservedUntil ≤ referenceFloor ∧
        resource.finalCounter ≤ executableFloor ∧
        endpointsBelow outerAgrees referenceFloor executableFloor

/-! ## Current-session activation-origin domination

The payload zipper is occurrence-indexed, so activation chronology must recurse
over that same dependent object.  A separate list of origins could be permuted
or paired with equal-looking cursors.  Each cell below therefore carries both
monotone domination by the current persistent session and the exact predicate
cut identity allocated by its historical call entry.
-/

/-- Every retained payload cell came from an activation no later than the
current session, and its cut high-water is exactly one past that cell's typed
predicate scope. -/
def LocalActivationOriginSpineRelates
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (session : Session) :
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer) → Prop
  | .nil _ _ => True
  | .cons _ currentScope _ _ _ _ _ _ _ _ _ _ _ _ _ snapshot outerAgrees =>
      snapshot.activationOrigin.Extends session ∧
        snapshot.activationOrigin.nextCutScope = currentScope + 1 ∧
        LocalActivationOriginSpineRelates session outerAgrees

namespace LocalActivationOriginSpineRelates

/-- The empty payload zipper contains no historical activation to dominate. -/
theorem nil
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    (session : Session) (currentBarrier : Nat) (scope : CutScopeId) :
    LocalActivationOriginSpineRelates session
      (SourceControlResourcePayloadContextAgrees.nil
        (alpha := alpha) (support := support) (qterm := qterm)
        currentBarrier scope) :=
  trivial

/-- Prepend one exact historical activation to an already-related literal
tail. -/
theorem cons
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {currentScope nextScope outerScope : CutScopeId}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {cursor : PreparedCursor} {context : ActiveProductContext}
    {segmentAgrees : segment.Agrees alpha}
    {resourceRest :
      resource.rest = segment.executables ++ flattenExecutables segments}
    {resourceQuery : resource.qterm = qterm}
    {resourceBarrier : resource.barrier = currentBarrier}
    {resourceOwnership : resource.HasIndexedOwnershipAt alpha cursor}
    {snapshot :
      RetainedCallPayloadSnapshot alpha support resource cursor segment
        segments}
    {outerAgrees :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        segment.barrier segments resources nextScope context outerScope}
    {session : Session}
    (head : snapshot.activationOrigin.Extends session)
    (cutExact : snapshot.activationOrigin.nextCutScope = currentScope + 1)
    (tail : LocalActivationOriginSpineRelates session outerAgrees) :
    LocalActivationOriginSpineRelates session
      (SourceControlResourcePayloadContextAgrees.cons currentBarrier
        currentScope nextScope outerScope segment segments resource resources
        cursor context segmentAgrees resourceRest resourceQuery resourceBarrier
        resourceOwnership snapshot outerAgrees) :=
  ⟨head, cutExact, tail⟩

/-- Popping the exact head occurrence preserves chronology for the literal
older suffix. -/
theorem tail
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {frame : ActiveProductFrame} {context : ActiveProductContext}
    {session : Session}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier (segment :: segments) (resource :: resources) inner
        (frame :: context) outer)
    (origins : LocalActivationOriginSpineRelates session agreement) :
    LocalActivationOriginSpineRelates session agreement.tail := by
  cases agreement
  exact origins.2.2

/-- A monotone current-session step preserves every older activation origin
without altering the payload zipper. -/
theorem advance
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {before after : Session}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer)
    (origins : LocalActivationOriginSpineRelates before agreement)
    (chronology : SessionHighWatersExtend before after) :
    LocalActivationOriginSpineRelates after agreement := by
  induction agreement with
  | nil => trivial
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      exact
        ⟨origins.1.transSession chronology, origins.2.1,
          inductionHypothesis origins.2.2⟩

/-- Ambient alpha growth changes proof annotations only and preserves every
activation-origin value and typed cut equation. -/
theorem mono
    {smaller larger support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {session : Session}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    (gaps :
      ∀ {resource cursor segment outerSegments},
        RetainedCallPayloadSnapshot smaller support resource cursor segment
            outerSegments →
          AlphaAllocationGap larger cursor.reservationStart
            cursor.reservedUntil resource.counter resource.finalCounter)
    (agreement :
      SourceControlResourcePayloadContextAgrees smaller support qterm
        currentBarrier segments resources inner context outer)
    (origins : LocalActivationOriginSpineRelates session agreement) :
    LocalActivationOriginSpineRelates session
      (agreement.mono included gaps) := by
  induction agreement with
  | nil => trivial
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      exact ⟨origins.1, origins.2.1, inductionHypothesis origins.2.2⟩

end LocalActivationOriginSpineRelates

/-! ## Exact historical control origins

Each payload snapshot stores the backtrackable control immediately outside
its local predicate call.  The fields are useful only when they are tied to
the literal older zipper suffix: otherwise a caller could pair a perfectly
well-formed logical snapshot with a forged alternative bank, barrier cache,
or frame stack.  The definitions below make that tie recursive and
occurrence-indexed.

The base barrier cache is computed by `recordedBaseBarrierCache`, walking the
literal snapshots to the outer boundary.  It is not guessed existentially and
no inverse of `pushBarrierCache` is used.  On a nonempty zipper the outermost
snapshot fixes the base cache, every inner snapshot fixes the next installed
cache, and the final equality fixes the live cache.  In disabled-cache mode
`pushBarrierCache none = none`, so uncached execution stays honestly uncached.
-/

/-- Barrier cache installed after entering every retained call in a payload
zipper, starting from the older base cache below the zipper. -/
def installedBarrierCache
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (baseBarriers : Option Nat) :
    SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer →
      Option Nat
  | .nil _ _ => baseBarriers
  | .cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ outerAgrees =>
      PLeaTTa.pushBarrierCache
        (installedBarrierCache baseBarriers outerAgrees)

/-- Adding one retained-call marker is injective even though disabled cache
mode remains `none`.  This lets a live installed cache identify the exact
outer cache without inventing a partial inverse. -/
theorem pushBarrierCache_injective :
    Function.Injective PLeaTTa.pushBarrierCache := by
  intro left right equal
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some right => simp at equal
  | some left =>
      cases right with
      | none => simp at equal
      | some right =>
          simp only [PLeaTTa.pushBarrierCache, Option.some.injEq] at equal
          congr
          omega

/-- Compute the unique recorded cache below a zipper by following its exact
outer-occurrence snapshots.  The live cache is used only for the empty case;
for a nonempty zipper every recursive step replaces it with the cache stored
by that occurrence. -/
def recordedBaseBarrierCache
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (liveBarriers : Option Nat) :
    SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer →
      Option Nat
  | .nil _ _ => liveBarriers
  | .cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ snapshot outerAgrees =>
      recordedBaseBarrierCache snapshot.controlOrigin.outerBarriers outerAgrees

/-- Every retained occurrence records exactly the alternatives and cache
immediately outside that call.

`resources` in the head equation is the literal dependent tail of the same
zipper constructor.  Thus neither an equal-looking resource list nor a
snapshot found by value search can satisfy the invariant for another
occurrence. -/
def ControlOriginSpineAgrees
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (baseAlts : List PLeaTTa.Alt) (baseBarriers : Option Nat) :
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer) → Prop
  | .nil _ _ => True
  | .cons _ _ _ _ _ _ _ resources _ _ _ _ _ _ _ snapshot outerAgrees =>
      snapshot.controlOrigin.outerAlts =
          flattenOwnedAlts resources baseAlts ∧
        snapshot.controlOrigin.outerBarriers =
          installedBarrierCache baseBarriers outerAgrees ∧
        ControlOriginSpineAgrees baseAlts baseBarriers outerAgrees

/-- The current local-call build has no typed delimiter boundary interleaved
between its retained predicate cells.

This restriction is deliberately separate from `ControlOriginSpineAgrees`:
the generic payload zipper can represent future chains crossing collection or
exception frames, while the present scheduled-history build proves that every
cell in one local chain saw the same literal frame stack. -/
def LocalCallFramesUninterleaved
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (frames : List Frame) :
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer) → Prop
  | .nil _ _ => True
  | .cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ snapshot outerAgrees =>
      snapshot.controlOrigin.frames = frames ∧
        LocalCallFramesUninterleaved frames outerAgrees

/-- A complete payload zipper is tied to one live installed barrier cache.
Its older base is computed from the occurrence-indexed snapshots, never
chosen by a consumer. -/
def ControlOriginSpineRelates
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (baseAlts : List PLeaTTa.Alt) (installedBarriers : Option Nat)
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer) : Prop :=
  let baseBarriers :=
    recordedBaseBarrierCache installedBarriers agreement
  ControlOriginSpineAgrees baseAlts baseBarriers agreement ∧
    installedBarrierCache baseBarriers agreement = installedBarriers

/-- Exact origin layout plus the explicit no-interleaved-frame property of
the current local-call chain.  Naming the restriction keeps catch/findall
extensions from silently inheriting a false global frame-constancy claim. -/
structure LocalControlOriginSpineRelates
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (baseAlts : List PLeaTTa.Alt) (frames : List Frame)
    (installedBarriers : Option Nat)
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer) : Prop where
  origins :
    ControlOriginSpineRelates baseAlts installedBarriers agreement
  framesUninterleaved : LocalCallFramesUninterleaved frames agreement

namespace LocalControlOriginSpineRelates

/-- The empty zipper relates any literal base control to itself. -/
def nil
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    (currentBarrier : Nat) (scope : CutScopeId)
    (baseAlts : List PLeaTTa.Alt) (frames : List Frame)
    (baseBarriers : Option Nat) :
    LocalControlOriginSpineRelates baseAlts frames baseBarriers
      (SourceControlResourcePayloadContextAgrees.nil
        (alpha := alpha) (support := support) (qterm := qterm)
        currentBarrier scope) :=
  { origins := by
      exact
        ⟨by simp [ControlOriginSpineAgrees], rfl⟩
    framesUninterleaved := by
      simp [LocalCallFramesUninterleaved] }

/-- Prepending one real call origin installs exactly one additional cache
level while preserving the older proof history literally. -/
def cons
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {currentScope nextScope outerScope : CutScopeId}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {cursor : PreparedCursor} {context : ActiveProductContext}
    {segmentAgrees : segment.Agrees alpha}
    {resourceRest :
      resource.rest = segment.executables ++ flattenExecutables segments}
    {resourceQuery : resource.qterm = qterm}
    {resourceBarrier : resource.barrier = currentBarrier}
    {resourceOwnership : resource.HasIndexedOwnershipAt alpha cursor}
    {snapshot :
      RetainedCallPayloadSnapshot alpha support resource cursor segment
        segments}
    {outerAgrees :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        segment.barrier segments resources nextScope context outerScope}
    {baseAlts : List PLeaTTa.Alt} {frames : List Frame}
    {outerInstalled : Option Nat}
    (tail :
      LocalControlOriginSpineRelates baseAlts frames outerInstalled
        outerAgrees)
    (outerAltsExact :
      snapshot.controlOrigin.outerAlts =
        flattenOwnedAlts resources baseAlts)
    (outerBarriersExact :
      snapshot.controlOrigin.outerBarriers = outerInstalled)
    (framesExact : snapshot.controlOrigin.frames = frames) :
    LocalControlOriginSpineRelates baseAlts frames
      (PLeaTTa.pushBarrierCache outerInstalled)
      (SourceControlResourcePayloadContextAgrees.cons currentBarrier
        currentScope nextScope outerScope segment segments resource resources
        cursor context segmentAgrees resourceRest resourceQuery resourceBarrier
        resourceOwnership snapshot outerAgrees) := by
  rcases tail.origins with ⟨tailOrigins, tailInstalled⟩
  refine
    { origins := ?_
      framesUninterleaved := ⟨framesExact, tail.framesUninterleaved⟩ }
  change
    ControlOriginSpineAgrees baseAlts
        (recordedBaseBarrierCache
          snapshot.controlOrigin.outerBarriers outerAgrees)
        (SourceControlResourcePayloadContextAgrees.cons currentBarrier
          currentScope nextScope outerScope segment segments resource
          resources cursor context segmentAgrees resourceRest resourceQuery
          resourceBarrier resourceOwnership snapshot outerAgrees) ∧
      installedBarrierCache
          (recordedBaseBarrierCache
            snapshot.controlOrigin.outerBarriers outerAgrees)
          (SourceControlResourcePayloadContextAgrees.cons currentBarrier
            currentScope nextScope outerScope segment segments resource
            resources cursor context segmentAgrees resourceRest resourceQuery
            resourceBarrier resourceOwnership snapshot outerAgrees) =
        PLeaTTa.pushBarrierCache outerInstalled
  rw [outerBarriersExact]
  exact
    ⟨⟨outerAltsExact,
        outerBarriersExact.trans tailInstalled.symm,
        tailOrigins⟩,
      by
        simp only [installedBarrierCache]
        rw [tailInstalled]⟩

/-- Popping the exact head cell recovers the historical control immediately
outside that occurrence.  No inverse of `pushBarrierCache` is used. -/
def tail
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {currentScope nextScope outerScope : CutScopeId}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {cursor : PreparedCursor} {context : ActiveProductContext}
    {segmentAgrees : segment.Agrees alpha}
    {resourceRest :
      resource.rest = segment.executables ++ flattenExecutables segments}
    {resourceQuery : resource.qterm = qterm}
    {resourceBarrier : resource.barrier = currentBarrier}
    {resourceOwnership : resource.HasIndexedOwnershipAt alpha cursor}
    {snapshot :
      RetainedCallPayloadSnapshot alpha support resource cursor segment
        segments}
    {outerAgrees :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        segment.barrier segments resources nextScope context outerScope}
    {baseAlts : List PLeaTTa.Alt} {frames : List Frame}
    {installedBarriers : Option Nat}
    (whole :
      LocalControlOriginSpineRelates baseAlts frames installedBarriers
        (SourceControlResourcePayloadContextAgrees.cons currentBarrier
          currentScope nextScope outerScope segment segments resource resources
          cursor context segmentAgrees resourceRest resourceQuery
          resourceBarrier resourceOwnership snapshot outerAgrees)) :
    LocalControlOriginSpineRelates baseAlts frames
      snapshot.controlOrigin.outerBarriers outerAgrees := by
  rcases whole.origins with ⟨origins, _installed⟩
  refine
    { origins := ?_
      framesUninterleaved := whole.framesUninterleaved.2 }
  exact ⟨origins.2.2, origins.2.1.symm⟩

end LocalControlOriginSpineRelates

/-- Expose all three domination components of a nonempty payload zipper.

The tail in the result is the exact linear eliminator applied to the supplied
zipper, so none of the three bounds can be paired with a different payload
cell. -/
theorem endpointsBelow_head
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {cursor : PreparedCursor}
    {currentScope nextScope outer : CutScopeId}
    {context : ActiveProductContext}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier (segment :: segments) (resource :: resources)
        currentScope
        ({ callerScope := nextScope
           predicateScope := currentScope
           retained := .clauses currentScope cursor
           callerRest := segment.references } ::
         context)
        outer)
    {referenceFloor executableFloor : Nat}
    (below :
      endpointsBelow agreement referenceFloor executableFloor) :
    cursor.reservedUntil ≤ referenceFloor ∧
      resource.finalCounter ≤ executableFloor ∧
      endpointsBelow (SourceControlResourcePayloadContextAgrees.tail agreement)
        referenceFloor executableFloor := by
  cases agreement with
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees =>
      exact below

/-- Advancing either persistent allocator preserves domination of every
frozen payload cell. -/
theorem endpointsBelow_mono
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {referenceBefore executableBefore referenceAfter executableAfter : Nat}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer)
    (below :
      endpointsBelow agreement referenceBefore executableBefore)
    (referenceMono : referenceBefore ≤ referenceAfter)
    (executableMono : executableBefore ≤ executableAfter) :
    endpointsBelow agreement referenceAfter executableAfter := by
  induction agreement with
  | nil =>
      trivial
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      simp only [endpointsBelow] at below ⊢
      exact
        ⟨Nat.le_trans below.1 referenceMono,
          Nat.le_trans below.2.1 executableMono,
          inductionHypothesis below.2.2⟩

/-- Every retained payload cell was allocated strictly after the complete
older payload tail which it encloses.

`endpointsBelow` at the current persistent high-waters is deliberately not
enough: after an inner call finishes, the newly exposed outer cell must still
dominate *its own* older tail at the historical source/executable allocation
seeds of that cell.  This recursive invariant stores exactly that chronology
at every zipper depth. -/
def ActivationOrdered
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext} :
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer) →
      Prop
  | .nil _ _ => True
  | .cons _ _ _ _ _ _ resource _ cursor _ _ _ _ _ _ _ outerAgrees =>
      endpointsBelow outerAgrees cursor.reservationStart resource.counter ∧
        ActivationOrdered outerAgrees

namespace ActivationOrdered

/-- The head chronology certificate is indexed by the literal tail of the
supplied zipper.  It cannot be paired with a shape-compatible reconstruction
of that tail. -/
theorem head
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {cursor : PreparedCursor}
    {currentScope nextScope outer : CutScopeId}
    {context : ActiveProductContext}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier (segment :: segments) (resource :: resources)
        currentScope
        ({ callerScope := nextScope
           predicateScope := currentScope
           retained := .clauses currentScope cursor
           callerRest := segment.references } ::
         context)
        outer)
    (ordered : ActivationOrdered agreement) :
    endpointsBelow
      (SourceControlResourcePayloadContextAgrees.tail agreement)
      cursor.reservationStart resource.counter := by
  cases agreement
  exact ordered.1

/-- Popping one exact payload cell preserves allocation chronology at every
remaining depth. -/
theorem tail
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {frame : ActiveProductFrame} {context : ActiveProductContext}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier (segment :: segments) (resource :: resources) inner
        (frame :: context) outer)
    (ordered : ActivationOrdered agreement) :
    ActivationOrdered
      (SourceControlResourcePayloadContextAgrees.tail agreement) := by
  cases agreement
  exact ordered.2

end ActivationOrdered

/-- Bounding two endpoints by the same current high-water does not order
those endpoints relative to each other.

This tiny counterexample is the arithmetic core of the nested-exhaustion
bug: global current-state domination cannot recover the historical
head-over-tail chronology required after a payload pop. -/
theorem current_domination_does_not_imply_relative_chronology :
    ∃ (headEndpoint tailEndpoint currentEndpoint : Nat),
      headEndpoint ≤ currentEndpoint ∧
        tailEndpoint ≤ currentEndpoint ∧
        ¬ tailEndpoint ≤ headEndpoint := by
  exact ⟨0, 1, 1, by omega⟩

/-- Extend every payload snapshot through one exact later alpha suffix.

The suffix floors dominate every cell's protected upper endpoints, so
`AlphaAllocationGap.extendAbove` derives each new gap.  No caller supplies a
gap directly, and the zipper recursion preserves the exact cell order. -/
def extendAbove
    {smaller larger support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {referenceFloor executableFloor : Nat}
    (extension :
      AlphaExtendsAbove smaller larger referenceFloor executableFloor) :
    (agreement :
      SourceControlResourcePayloadContextAgrees smaller support qterm
        currentBarrier segments resources inner context outer) →
    endpointsBelow agreement referenceFloor executableFloor →
      SourceControlResourcePayloadContextAgrees larger support qterm
        currentBarrier segments resources inner context outer
  | .nil currentBarrier scope, _ =>
      .nil currentBarrier scope
  | .cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees,
      below =>
      .cons currentBarrier currentScope nextScope outerScope segment segments
        resource resources cursor context
        (segmentAgrees.mono extension.included)
        resourceRest resourceQuery resourceBarrier
        (resourceOwnership.mono extension.included)
        (snapshot.mono extension.included
          (snapshot.allocationGap.extendAbove extension below.1 below.2.1))
        (extendAbove extension outerAgrees below.2.2)

/-- Exact alpha extension preserves the occurrence-indexed activation origins
because it changes neither cursor identity nor any historical frontier. -/
theorem LocalActivationOriginSpineRelates.extendAbove
    {smaller larger support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {referenceFloor executableFloor : Nat}
    {session : Session}
    (extension :
      AlphaExtendsAbove smaller larger referenceFloor executableFloor)
    (agreement :
      SourceControlResourcePayloadContextAgrees smaller support qterm
        currentBarrier segments resources inner context outer)
    (below : endpointsBelow agreement referenceFloor executableFloor)
    (origins : LocalActivationOriginSpineRelates session agreement) :
    LocalActivationOriginSpineRelates session
      (extendAbove extension agreement below) := by
  induction agreement with
  | nil => trivial
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      exact
        ⟨origins.1, origins.2.1,
          inductionHypothesis below.2.2 origins.2.2⟩

/-- Alpha transport changes proof annotations only; it cannot alter the
barrier-cache chronology computed from retained call occurrences. -/
theorem installedBarrierCache_extendAbove
    {smaller larger support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {referenceFloor executableFloor : Nat}
    (extension :
      AlphaExtendsAbove smaller larger referenceFloor executableFloor)
    (agreement :
      SourceControlResourcePayloadContextAgrees smaller support qterm
        currentBarrier segments resources inner context outer)
    (below : endpointsBelow agreement referenceFloor executableFloor)
    (baseBarriers : Option Nat) :
    installedBarrierCache baseBarriers
        (extendAbove extension agreement below) =
      installedBarrierCache baseBarriers agreement := by
  induction agreement with
  | nil => rfl
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      simp only [extendAbove, installedBarrierCache]
      rw [inductionHypothesis below.2.2]

/-- The computed outer base cache is invariant under alpha-only transport. -/
theorem recordedBaseBarrierCache_extendAbove
    {smaller larger support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {referenceFloor executableFloor : Nat}
    (extension :
      AlphaExtendsAbove smaller larger referenceFloor executableFloor)
    (agreement :
      SourceControlResourcePayloadContextAgrees smaller support qterm
        currentBarrier segments resources inner context outer)
    (below : endpointsBelow agreement referenceFloor executableFloor)
    (liveBarriers : Option Nat) :
    recordedBaseBarrierCache liveBarriers
        (extendAbove extension agreement below) =
      recordedBaseBarrierCache liveBarriers agreement := by
  induction agreement generalizing liveBarriers with
  | nil => rfl
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      simp only [extendAbove, recordedBaseBarrierCache]
      simpa [RetainedCallPayloadSnapshot.mono] using
        inductionHypothesis below.2.2 snapshot.controlOrigin.outerBarriers

/-- Alpha-only transport preserves every occurrence-indexed alternative and
cache-origin equation. -/
theorem ControlOriginSpineAgrees.extendAbove
    {smaller larger support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {referenceFloor executableFloor : Nat}
    (extension :
      AlphaExtendsAbove smaller larger referenceFloor executableFloor)
    (agreement :
      SourceControlResourcePayloadContextAgrees smaller support qterm
        currentBarrier segments resources inner context outer)
    (below : endpointsBelow agreement referenceFloor executableFloor)
    (baseAlts : List PLeaTTa.Alt) (baseBarriers : Option Nat)
    (origins :
      ControlOriginSpineAgrees baseAlts baseBarriers agreement) :
    ControlOriginSpineAgrees baseAlts baseBarriers
      (extendAbove extension agreement below) := by
  induction agreement with
  | nil => trivial
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      simp only [ControlOriginSpineAgrees] at origins ⊢
      exact
        ⟨origins.1,
          origins.2.1.trans
            (installedBarrierCache_extendAbove extension outerAgrees
              below.2.2 baseBarriers).symm,
          inductionHypothesis below.2.2 origins.2.2⟩

/-- Alpha-only transport cannot insert a typed delimiter between retained
local-call cells. -/
theorem LocalCallFramesUninterleaved.extendAbove
    {smaller larger support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {referenceFloor executableFloor : Nat}
    (extension :
      AlphaExtendsAbove smaller larger referenceFloor executableFloor)
    (agreement :
      SourceControlResourcePayloadContextAgrees smaller support qterm
        currentBarrier segments resources inner context outer)
    (below : endpointsBelow agreement referenceFloor executableFloor)
    (frames : List Frame)
    (uninterleaved : LocalCallFramesUninterleaved frames agreement) :
    LocalCallFramesUninterleaved frames
      (extendAbove extension agreement below) := by
  induction agreement with
  | nil => trivial
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      exact
        ⟨uninterleaved.1,
          inductionHypothesis below.2.2 uninterleaved.2⟩

/-- Transport the complete local origin relation through an exact alpha
extension without changing alternatives, cache mode, or frame identity. -/
theorem LocalControlOriginSpineRelates.extendAbove
    {smaller larger support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {referenceFloor executableFloor : Nat}
    (extension :
      AlphaExtendsAbove smaller larger referenceFloor executableFloor)
    (agreement :
      SourceControlResourcePayloadContextAgrees smaller support qterm
        currentBarrier segments resources inner context outer)
    (below : endpointsBelow agreement referenceFloor executableFloor)
    (baseAlts : List PLeaTTa.Alt) (frames : List Frame)
    (installedBarriers : Option Nat)
    (control :
      LocalControlOriginSpineRelates baseAlts frames installedBarriers
        agreement) :
    LocalControlOriginSpineRelates baseAlts frames installedBarriers
      (extendAbove extension agreement below) := by
  refine
    { origins := ?_
      framesUninterleaved :=
        control.framesUninterleaved.extendAbove extension agreement below
          frames }
  rcases control.origins with ⟨origins, installed⟩
  change
    ControlOriginSpineAgrees baseAlts
        (recordedBaseBarrierCache installedBarriers
          (SourceControlResourcePayloadContextAgrees.extendAbove extension
            agreement below))
        (SourceControlResourcePayloadContextAgrees.extendAbove extension
          agreement below) ∧
      installedBarrierCache
          (recordedBaseBarrierCache installedBarriers
            (SourceControlResourcePayloadContextAgrees.extendAbove extension
              agreement below))
          (SourceControlResourcePayloadContextAgrees.extendAbove extension
            agreement below) = installedBarriers
  rw [recordedBaseBarrierCache_extendAbove extension agreement below]
  exact
    ⟨origins.extendAbove extension agreement below baseAlts
        (recordedBaseBarrierCache installedBarriers agreement),
      (installedBarrierCache_extendAbove extension agreement below
        (recordedBaseBarrierCache installedBarriers agreement)).trans
        installed⟩

/-- Proof-relevant handoff between two exact payload zippers across one
ambient-alpha extension.

The predecessor and successor are indices of the proposition.  A caller
cannot satisfy this relation with a merely shape-compatible payload zipper:
the successor must be definitionally the canonical `extendAbove` transport of
the supplied predecessor at the actual allocation floors.  This is the
load-bearing link used by nested-call chains. -/
structure ExtendsAboveAt
    {smaller larger support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (referenceFloor executableFloor : Nat)
    (extension :
      AlphaExtendsAbove smaller larger referenceFloor executableFloor)
    (before :
      SourceControlResourcePayloadContextAgrees smaller support qterm
        currentBarrier segments resources inner context outer)
    (after :
      SourceControlResourcePayloadContextAgrees larger support qterm
        currentBarrier segments resources inner context outer) : Prop where
  below : endpointsBelow before referenceFloor executableFloor
  exact : after = extendAbove extension before below

/-- Alpha transport changes only proof annotations; it preserves the exact
cursor/resource endpoints and therefore the same domination certificate. -/
theorem extendAbove_endpointsBelow
    {smaller larger support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {referenceFloor executableFloor : Nat}
    (extension :
      AlphaExtendsAbove smaller larger referenceFloor executableFloor)
    (agreement :
      SourceControlResourcePayloadContextAgrees smaller support qterm
        currentBarrier segments resources inner context outer)
    (below :
      endpointsBelow agreement referenceFloor executableFloor) :
    endpointsBelow (extendAbove extension agreement below)
      referenceFloor executableFloor := by
  induction agreement with
  | nil =>
      trivial
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      simp only [endpointsBelow] at below ⊢
      exact
        ⟨below.1, below.2.1,
          inductionHypothesis below.2.2⟩

/-- Alpha transport preserves endpoint domination at any independently
supplied floors, not only at the newer floors used to justify the alpha
extension itself.  The transported zipper has identical cursor/resource
indices; only proof annotations change. -/
theorem extendAbove_endpointsBelow_at
    {smaller larger support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {extensionReferenceFloor extensionExecutableFloor : Nat}
    {referenceFloor executableFloor : Nat}
    (extension :
      AlphaExtendsAbove smaller larger extensionReferenceFloor
        extensionExecutableFloor)
    (agreement :
      SourceControlResourcePayloadContextAgrees smaller support qterm
        currentBarrier segments resources inner context outer)
    (extensionBelow :
      endpointsBelow agreement extensionReferenceFloor
        extensionExecutableFloor)
    (below :
      endpointsBelow agreement referenceFloor executableFloor) :
    endpointsBelow (extendAbove extension agreement extensionBelow)
      referenceFloor executableFloor := by
  induction agreement with
  | nil =>
      trivial
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      exact
        ⟨below.1, below.2.1,
          inductionHypothesis extensionBelow.2.2 below.2.2⟩

/-- Alpha extension changes proof annotations but no cursor/resource
allocation endpoint, so recursive activation chronology is preserved
literally at every zipper depth. -/
theorem ActivationOrdered.extendAbove
    {smaller larger support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {referenceFloor executableFloor : Nat}
    (extension :
      AlphaExtendsAbove smaller larger referenceFloor executableFloor)
    (agreement :
      SourceControlResourcePayloadContextAgrees smaller support qterm
        currentBarrier segments resources inner context outer)
    (below :
      endpointsBelow agreement referenceFloor executableFloor)
    (ordered : ActivationOrdered agreement) :
    ActivationOrdered (extendAbove extension agreement below) := by
  induction agreement with
  | nil =>
      trivial
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      exact
        ⟨extendAbove_endpointsBelow_at extension outerAgrees below.2.2
            ordered.1,
          inductionHypothesis below.2.2 ordered.2⟩

/-- The four spines are one-to-one: no payload certificate can be inserted,
deleted, or shifted independently of its source frame and executable
resource. -/
theorem lengths_eq
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer) :
    context.length = segments.length ∧
      segments.length = resources.length := by
  exact agreement.alignment.lengths_eq

/-- Drop an exact inner prefix while preserving the remaining payload cells
and all of their typed indices. -/
def dropAlignedPrefix
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer)
    (count : Nat) (within : count ≤ segments.length) :
    Σ nextBarrier, Σ nextInner,
      SourceControlResourcePayloadContextAgrees alpha support qterm
        nextBarrier (segments.drop count) (resources.drop count) nextInner
        (context.drop count) outer := by
  induction count generalizing currentBarrier segments resources inner
      context with
  | zero =>
      exact ⟨currentBarrier, inner, by simpa using agreement⟩
  | succ count inductionHypothesis =>
      cases agreement with
      | nil currentBarrier scope =>
          simp at within
      | cons currentBarrier currentScope nextScope outerScope segment
          segments resource resources cursor context segmentAgrees
          resourceRest resourceQuery resourceBarrier resourceOwnership
          snapshot outerAgrees =>
          have withinTail : count ≤ segments.length := by
            simpa using Nat.le_of_succ_le_succ within
          obtain ⟨nextBarrier, nextInner, suffix⟩ :=
            inductionHypothesis outerAgrees withinTail
          exact ⟨nextBarrier, nextInner, by simpa using suffix⟩

/-- Drop an exact aligned prefix and return the literal suffix together with
its recursive allocation chronology.

The suffix and proof are constructed in the same recursion.  This avoids a
second existential scan and avoids proof-indexed casts through the sigma
returned by the unadorned `dropAlignedPrefix`. -/
def ActivationOrdered.dropAlignedPrefix
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer)
    (ordered : ActivationOrdered agreement)
    (count : Nat) (within : count ≤ segments.length) :
    Σ nextBarrier, Σ nextInner,
      { suffix :
        SourceControlResourcePayloadContextAgrees alpha support qterm
          nextBarrier (segments.drop count) (resources.drop count) nextInner
          (context.drop count) outer //
        ActivationOrdered suffix } := by
  induction count generalizing currentBarrier segments resources inner
      context with
  | zero =>
      exact ⟨currentBarrier, inner, ⟨agreement, ordered⟩⟩
  | succ count inductionHypothesis =>
      cases agreement with
      | nil currentBarrier scope =>
          simp at within
      | cons currentBarrier currentScope nextScope outerScope segment
          segments resource resources cursor context segmentAgrees
          resourceRest resourceQuery resourceBarrier resourceOwnership
          snapshot outerAgrees =>
          have withinTail : count ≤ segments.length := by
            simpa using Nat.le_of_succ_le_succ within
          obtain ⟨nextBarrier, nextInner, ⟨suffix, suffixOrdered⟩⟩ :=
            inductionHypothesis outerAgrees ordered.2 withinTail
          exact ⟨nextBarrier, nextInner, ⟨suffix, suffixOrdered⟩⟩

/-- The first cell of a nonempty payload zipper exposes the exact retained
cursor and its immutable pre-head payload. -/
structure HeadCell
    (alpha support : List (LogicVar × String))
    (segment : ControlSegment)
    (segments : List ControlSegment)
    (resource : RetainedAlternativeSegment)
    (scope : CutScopeId)
    (frame : ActiveProductFrame) where
  cursor : PreparedCursor
  predicateScopeExact : frame.predicateScope = scope
  retainedShape :
    frame.retained = .clauses scope cursor
  callerRestExact : frame.callerRest = segment.references
  /-- Exact ownership at this same cursor.  Keeping it in the head package
  prevents a consumer from pairing the snapshot with a merely
  shape-compatible ownership proof extracted from another payload cell. -/
  ownership : resource.HasIndexedOwnershipAt alpha cursor
  snapshot :
    RetainedCallPayloadSnapshot alpha support resource cursor segment segments

/-- Extract the head payload cell without searching or comparing values.
Its position is forced by the strengthened zipper constructor. -/
def headCell
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {frame : ActiveProductFrame} {context : ActiveProductContext}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier (segment :: segments) (resource :: resources) inner
        (frame :: context) outer) :
    HeadCell alpha support segment segments resource inner frame := by
  cases agreement with
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees =>
      exact ⟨cursor, rfl, rfl, rfl, resourceOwnership, snapshot⟩

namespace LocalActivationOriginSpineRelates

/-- The nonempty zipper exposes current-session domination for its literal
head occurrence. -/
theorem headExtends
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {frame : ActiveProductFrame} {context : ActiveProductContext}
    {session : Session}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier (segment :: segments) (resource :: resources) inner
        (frame :: context) outer)
    (origins : LocalActivationOriginSpineRelates session agreement) :
    (headCell agreement).snapshot.activationOrigin.Extends session := by
  cases agreement
  exact origins.1

/-- The head origin's cut frontier is tied to the literal typed predicate
scope at that same zipper occurrence. -/
theorem headCutScope
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {frame : ActiveProductFrame} {context : ActiveProductContext}
    {session : Session}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier (segment :: segments) (resource :: resources) inner
        (frame :: context) outer)
    (origins : LocalActivationOriginSpineRelates session agreement) :
    (headCell agreement).snapshot.activationOrigin.nextCutScope = inner + 1 := by
  cases agreement
  exact origins.2.1

end LocalActivationOriginSpineRelates

namespace LocalControlOriginSpineRelates

/-! The explicit-constructor lemmas above are convenient at creation sites.
The two wrappers below eliminate an arbitrary nonempty dependent zipper once,
so downstream path consumers never rebuild or equality-search its head. -/

/-- Reattach one exact head occurrence to an already-related literal tail. -/
def prepend
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {frame : ActiveProductFrame} {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt} {frames : List Frame}
    {outerInstalled : Option Nat}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier (segment :: segments) (resource :: resources) inner
        (frame :: context) outer)
    (tailRelates :
      LocalControlOriginSpineRelates baseAlts frames outerInstalled
        (SourceControlResourcePayloadContextAgrees.tail agreement))
    (outerAltsExact :
      (headCell agreement).snapshot.controlOrigin.outerAlts =
        flattenOwnedAlts resources baseAlts)
    (outerBarriersExact :
      (headCell agreement).snapshot.controlOrigin.outerBarriers =
        outerInstalled)
    (framesExact :
      (headCell agreement).snapshot.controlOrigin.frames = frames) :
    LocalControlOriginSpineRelates baseAlts frames
      (PLeaTTa.pushBarrierCache outerInstalled) agreement := by
  cases agreement with
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees =>
      exact
        cons tailRelates outerAltsExact outerBarriersExact framesExact

/-- Remove one exact head occurrence and recover its recorded outer cache. -/
def pop
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {frame : ActiveProductFrame} {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt} {frames : List Frame}
    {installedBarriers : Option Nat}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier (segment :: segments) (resource :: resources) inner
        (frame :: context) outer)
    (whole :
      LocalControlOriginSpineRelates baseAlts frames installedBarriers
        agreement) :
    LocalControlOriginSpineRelates baseAlts frames
      (headCell agreement).snapshot.controlOrigin.outerBarriers
      (SourceControlResourcePayloadContextAgrees.tail agreement) := by
  cases agreement with
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees =>
      exact tail whole

/-- The exact head occurrence records the literal alternative bank owned by
its dependent resource tail. -/
theorem headOuterAlts_eq
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {frame : ActiveProductFrame} {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt} {frames : List Frame}
    {installedBarriers : Option Nat}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier (segment :: segments) (resource :: resources) inner
        (frame :: context) outer)
    (whole :
      LocalControlOriginSpineRelates baseAlts frames installedBarriers
        agreement) :
    (headCell agreement).snapshot.controlOrigin.outerAlts =
      flattenOwnedAlts resources baseAlts := by
  cases agreement with
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees =>
      exact whole.origins.1.1

/-- The exact head occurrence saw the same non-interleaved frame stack as the
complete current local-call chain. -/
theorem headFrames_eq
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {frame : ActiveProductFrame} {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt} {frames : List Frame}
    {installedBarriers : Option Nat}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier (segment :: segments) (resource :: resources) inner
        (frame :: context) outer)
    (whole :
      LocalControlOriginSpineRelates baseAlts frames installedBarriers
        agreement) :
    (headCell agreement).snapshot.controlOrigin.frames = frames := by
  cases agreement with
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees =>
      exact whole.framesUninterleaved.1

/-- A nonempty exact spine's live cache is precisely one push above its head
occurrence's recorded outer cache.  This is the forward equation used when a
cursor-only payload transform retains that occurrence. -/
theorem installedBarriers_eq_push_headOuter
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {frame : ActiveProductFrame} {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt} {frames : List Frame}
    {installedBarriers : Option Nat}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier (segment :: segments) (resource :: resources) inner
        (frame :: context) outer)
    (whole :
      LocalControlOriginSpineRelates baseAlts frames installedBarriers
        agreement) :
    installedBarriers =
      PLeaTTa.pushBarrierCache
        (headCell agreement).snapshot.controlOrigin.outerBarriers := by
  cases agreement with
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees =>
      rcases whole.origins with ⟨origins, installed⟩
      change
        ControlOriginSpineAgrees baseAlts
          (recordedBaseBarrierCache snapshot.controlOrigin.outerBarriers
            outerAgrees)
          (SourceControlResourcePayloadContextAgrees.cons currentBarrier
            inner nextScope outer segment segments resource
            resources cursor context segmentAgrees resourceRest resourceQuery
            resourceBarrier resourceOwnership snapshot outerAgrees) at origins
      change
        installedBarrierCache
            (recordedBaseBarrierCache snapshot.controlOrigin.outerBarriers
              outerAgrees)
            (SourceControlResourcePayloadContextAgrees.cons currentBarrier
              inner nextScope outer segment segments resource
              resources cursor context segmentAgrees resourceRest resourceQuery
              resourceBarrier resourceOwnership snapshot outerAgrees) =
          installedBarriers at installed
      calc
        installedBarriers =
            PLeaTTa.pushBarrierCache
              (installedBarrierCache
                (recordedBaseBarrierCache
                  snapshot.controlOrigin.outerBarriers outerAgrees)
                outerAgrees) := by
          simpa only [installedBarrierCache] using installed.symm
        _ = PLeaTTa.pushBarrierCache
              snapshot.controlOrigin.outerBarriers := by
          exact congrArg PLeaTTa.pushBarrierCache origins.2.1.symm

/-- If the live cache is known to be one pushed outer cache, the exact head
occurrence records that outer cache.  This is derived from the recursive
spine relation and injectivity, not retained as a duplicate field. -/
theorem headOuterBarriers_eq_of_installedPush
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId}
    {frame : ActiveProductFrame} {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt} {frames : List Frame}
    {outerInstalled : Option Nat}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier (segment :: segments) (resource :: resources) inner
        (frame :: context) outer)
    (whole :
      LocalControlOriginSpineRelates baseAlts frames
        (PLeaTTa.pushBarrierCache outerInstalled) agreement) :
    (headCell agreement).snapshot.controlOrigin.outerBarriers =
      outerInstalled := by
  cases agreement with
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees =>
      rcases whole.origins with ⟨origins, installed⟩
      apply pushBarrierCache_injective
      simp only [installedBarrierCache] at installed
      exact
        (congrArg PLeaTTa.pushBarrierCache origins.2.1).trans installed

end LocalControlOriginSpineRelates

end SourceControlResourcePayloadContextAgrees

/-- Move one currently active resource into the typed outer context of a
newly entered recursive call.

All resource equalities come from the actual active stack.  The caller's
control spelling and immutable pre-head payload are supplied independently,
so this constructor cannot manufacture either from a later machine state. -/
def ActiveProductResourceStackAgrees.prependPayloadContext
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {bodyBarrier callerBarrier : Nat}
    {pending : DemandDrivenCallStep.PendingCall}
    {cursor : PreparedCursor}
    {executableRest : List PLeaTTa.Goal}
    {altTail : List PLeaTTa.Alt}
    {active : RetainedAlternativeSegment}
    {caller : ControlSegment}
    {outer : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {predicateScope callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt} {state : OpenConf}
    (stack :
      ActiveProductResourceStackAgrees alpha qterm bodyBarrier callerBarrier
        pending cursor executableRest altTail active outer resources
        callerScope outerScope context baseAlts state)
    (callerRest : executableRest =
      caller.executables ++ flattenExecutables outer)
    (callerBarrierExact : caller.barrier = callerBarrier)
    (callerAgrees : caller.Agrees alpha)
    (snapshot :
      RetainedCallPayloadSnapshot alpha support active cursor caller outer)
    (outerPayloads :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        callerBarrier outer resources callerScope context outerScope) :
    SourceControlResourcePayloadContextAgrees alpha support qterm bodyBarrier
      (caller :: outer) (active :: resources) predicateScope
      ({ callerScope := callerScope
         predicateScope := predicateScope
         retained := .clauses predicateScope cursor
         callerRest := caller.references } ::
       context)
      outerScope := by
  have outerPayloadsAtCaller :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        caller.barrier outer resources callerScope context outerScope := by
    simpa [callerBarrierExact] using outerPayloads
  exact
    .cons bodyBarrier predicateScope callerScope outerScope caller outer active
      resources cursor context callerAgrees
      (stack.activeRest.trans callerRest)
      stack.activeQuery stack.activeBarrier stack.activeOwnership snapshot
      outerPayloadsAtCaller

/-! ## Construction at the real activation site -/

/-- The complete retained-resource value produced after one selected clause
head has been consumed.  Naming this constructor keeps every observable scan
coordinate recoverable from producer theorems; downstream proofs need not
reconstruct `argsv`, arguments, result, binding, or seed from existential
ownership evidence. -/
def retainedTailResource
    (cursor : PreparedCursor) (argsv args : List Atom) (res : Atom)
    (rest : List PLeaTTa.Goal) (binding : Subst) (qterm : Atom)
    (barrier startCounter : Nat) (alts : List PLeaTTa.Alt)
    (finalCounter : Nat) : RetainedAlternativeSegment :=
  { callIdentity := PreparedCallIdentity.ofCursor cursor
    argsv := argsv
    args := args
    res := res
    rest := rest
    binding := binding
    qterm := qterm
    barrier := barrier
    counter := startCounter + 1
    alts := alts
    finalCounter := finalCounter }

/- These projection equations are an anti-erasure guard for the producer
API below.  Each is definitional: if the retained-resource constructor ever
stops preserving one scan coordinate literally, its downstream adequacy
proofs fail here rather than reconstructing a merely compatible value. -/
@[simp] theorem retainedTailResource_argsv
    (cursor : PreparedCursor) (argsv args : List Atom) (res : Atom)
    (rest : List PLeaTTa.Goal) (binding : Subst) (qterm : Atom)
    (barrier startCounter : Nat) (alts : List PLeaTTa.Alt)
    (finalCounter : Nat) :
    (retainedTailResource cursor argsv args res rest binding qterm barrier
      startCounter alts finalCounter).argsv = argsv := rfl

@[simp] theorem retainedTailResource_args
    (cursor : PreparedCursor) (argsv args : List Atom) (res : Atom)
    (rest : List PLeaTTa.Goal) (binding : Subst) (qterm : Atom)
    (barrier startCounter : Nat) (alts : List PLeaTTa.Alt)
    (finalCounter : Nat) :
    (retainedTailResource cursor argsv args res rest binding qterm barrier
      startCounter alts finalCounter).args = args := rfl

@[simp] theorem retainedTailResource_res
    (cursor : PreparedCursor) (argsv args : List Atom) (res : Atom)
    (rest : List PLeaTTa.Goal) (binding : Subst) (qterm : Atom)
    (barrier startCounter : Nat) (alts : List PLeaTTa.Alt)
    (finalCounter : Nat) :
    (retainedTailResource cursor argsv args res rest binding qterm barrier
      startCounter alts finalCounter).res = res := rfl

@[simp] theorem retainedTailResource_binding
    (cursor : PreparedCursor) (argsv args : List Atom) (res : Atom)
    (rest : List PLeaTTa.Goal) (binding : Subst) (qterm : Atom)
    (barrier startCounter : Nat) (alts : List PLeaTTa.Alt)
    (finalCounter : Nat) :
    (retainedTailResource cursor argsv args res rest binding qterm barrier
      startCounter alts finalCounter).binding = binding := rfl

@[simp] theorem retainedTailResource_counter
    (cursor : PreparedCursor) (argsv args : List Atom) (res : Atom)
    (rest : List PLeaTTa.Goal) (binding : Subst) (qterm : Atom)
    (barrier startCounter : Nat) (alts : List PLeaTTa.Alt)
    (finalCounter : Nat) :
    (retainedTailResource cursor argsv args res rest binding qterm barrier
      startCounter alts finalCounter).counter = startCounter + 1 := rfl

/-- One real spined activation creates the active retained resource and its
immutable pre-head payload in the same construction, using the exact residual
representative selected for that activation.

The result uses the exact `RepresentativeRetainedCallFrontier`, rather than
destructing a later existential ownership proof and attempting to reconstruct
call-entry history.  Persistent world/session state is deliberately absent
from the snapshot and remains indexed only by the active state relation. -/
theorem
    SpinedRepresentativeProductActivation.activeResourceStackWithSnapshot
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {referenceBindings : Substitution}
    {opened : OpenedCall} {before : OpenConf}
    {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    {branchTail : List ClauseBranch} {clauseTail : List PLeaTTa.Clause}
    {altTail : List PLeaTTa.Alt} {copied : PLeaTTa.Clause}
    {referencePayload : List Term}
    {segmentReferenceRest : List PeTTaSpec.PrologCore.Goal}
    {argsv args : List Atom} {res : Atom}
    {segmentExecutableRest : List PLeaTTa.Goal}
    {outer : List ControlSegment} {binding : Subst}
    {qterm : Atom} {bodyBarrier callerBarrier startCounter : Nat}
    {callerScope outerScope : CutScopeId}
    {independentResult : Substitution}
    {representative : TreeSubstitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattenedRepresentative : TreeSubstitution}
    {installed : Subst}
    {resources : List RetainedAlternativeSegment}
    {context : ActiveProductContext}
    (retainedPosition : Nat)
    (positioned :
      CallScopedCursorPosition opened.cursor
        (finish.advance branch branchTail) retainedPosition)
    (frontier :
      RepresentativeRetainedCallFrontier alpha opened before pending finish
        branch clause branchTail clauseTail altTail copied argsv args res
        (segmentExecutableRest ++ flattenExecutables outer)
        binding qterm bodyBarrier startCounter)
    (preHeadPayload :
      TaskSpinePayloadAgrees alpha support canonical referenceBase
        referenceBindings binding
        ({ barrier := callerBarrier
           references :=
             .call opened.cursor.predicate referencePayload ::
               segmentReferenceRest
           executables :=
             .call opened.cursor.predicate args res ::
               segmentExecutableRest } ::
         outer))
    (oldCumulative :
      AlphaCumulativeResidualVariantAgreesOnWith alpha support canonical
        referenceBase binding representative)
    (materializedAtOpen :
      MaterializedCallAgreesWith alpha referenceBindings referencePayload
        (args.map (PLeaTTa.subst binding))
        (PLeaTTa.subst binding res) representative referenceBase)
    (openedArguments : opened.cursor.arguments = referencePayload)
    (openedBindings : opened.cursor.bindings = referenceBindings)
    (queryReferenceBelow :
      GeneratedBelow finish.reservationStart (alpha.map Prod.fst))
    (activation :
      SpinedRepresentativeProductActivation prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        segmentReferenceRest segmentExecutableRest outer qterm bodyBarrier
        callerBarrier startCounter callerScope independentResult representative
        nextAlpha sourceCanonical flattenedRepresentative installed)
    (outerPayloads :
      SourceControlResourcePayloadContextAgrees nextAlpha support qterm
        callerBarrier outer resources callerScope context outerScope)
    (baseAlts : List PLeaTTa.Alt)
    (outerAlts :
      pending.outer.alts = flattenOwnedAlts resources baseAlts) :
    ∃ active : RetainedAlternativeSegment,
      ∃ _snapshot : RetainedCallPayloadSnapshot nextAlpha support active
          (finish.advance branch branchTail)
          { barrier := callerBarrier
            references := segmentReferenceRest
            executables := segmentExecutableRest }
          outer,
        ∃ _payloadContext :
            SourceControlResourcePayloadContextAgrees nextAlpha support qterm
              bodyBarrier
              ({ barrier := callerBarrier
                 references := segmentReferenceRest
                 executables := segmentExecutableRest } ::
               outer)
              (active :: resources) opened.scope
              ({ callerScope := callerScope
                 predicateScope := opened.scope
                 retained :=
                   .clauses opened.scope
                     (finish.advance branch branchTail)
                 callerRest := segmentReferenceRest } ::
               context)
              outerScope,
          active.counter = startCounter + 1 ∧
            active =
              retainedTailResource (finish.advance branch branchTail) argsv
                args res
                (segmentExecutableRest ++ flattenExecutables outer) binding
                qterm bodyBarrier startCounter altTail
                pending.persistent.counter ∧
            (ActiveProductResourceStackAgrees nextAlpha qterm bodyBarrier
              callerBarrier pending (finish.advance branch branchTail)
              (segmentExecutableRest ++ flattenExecutables outer)
              altTail active outer resources callerScope outerScope context
              baseAlts
              (activatedOpenSuccessor pending copied
                (segmentExecutableRest ++ flattenExecutables outer)
                qterm installed)) ∧
            _snapshot.residualRepresentative = representative ∧
              _snapshot.controlOrigin.MatchesPendingControl pending ∧
                _snapshot.activationOrigin.Extends opened.session ∧
                  _snapshot.activationOrigin.nextCutScope =
                    opened.scope + 1 := by
  let advanced := finish.advance branch branchTail
  have advancedRemaining : advanced.remaining = branchTail := by
    simp [advanced, PreparedCursor.advance]
  have advancedContext :
      CursorCallContext advanced opened.cursor.callGeneration
        opened.cursor.predicate opened.cursor.arguments
        opened.cursor.bindings :=
    frontier.finishContext.advance branch branchTail
  have advancedWellFormed : advanced.WellFormed :=
    finish.advance_wellFormed frontier.finishWellFormed
      frontier.finishRemaining
  have queryAtAdvanced :
      RepresentativeNormalizedCallAgrees alpha advanced argsv
        (PLeaTTa.subst binding res) :=
    PLeaTTa.PrologRepresentativeCallFrontierBridge.CursorCallContext.representativeNormalizedCallAgrees
      advancedContext frontier.finishContext frontier.query
  have ownership :
      RetainedCursorAlternativeOwnership alpha advanced argsv args res
        (segmentExecutableRest ++ flattenExecutables outer)
        binding qterm bodyBarrier (startCounter + 1) altTail
        pending.persistent.counter :=
    retainedCursorAlternativeOwnership_of_scan advancedRemaining
      advancedContext advancedWellFormed queryAtAdvanced
      frontier.substitutedArgs frontier.tailSupported frontier.tailArities
      frontier.tailScan
  let active : RetainedAlternativeSegment :=
    retainedTailResource advanced argsv args res
      (segmentExecutableRest ++ flattenExecutables outer) binding qterm
      bodyBarrier startCounter altTail pending.persistent.counter
  have activeOwnership :
      active.Owns nextAlpha opened.cursor advanced retainedPosition :=
    ⟨rfl,
      RetainedCursorAlternativeOwnership.mono activation.alphaIncluded
        ownership,
      positioned⟩
  have alignment :
      SourceControlResourceContextAgrees nextAlpha qterm callerBarrier outer
        resources callerScope context outerScope :=
    outerPayloads.alignment
  have actualAlts :
      (activatedOpenSuccessor pending copied
        (segmentExecutableRest ++ flattenExecutables outer)
        qterm installed).control.alts =
        flattenOwnedAlts (active :: resources) baseAlts := by
    change
      (activatedExecutableSuccessor pending copied
        (segmentExecutableRest ++ flattenExecutables outer)
        qterm installed).alts =
          active.alts ++ PLeaTTa.Alt.barrier ::
            flattenOwnedAlts resources baseAlts
    rw [activation.retainedAlts, outerAlts]
    rfl
  have stack :
      ActiveProductResourceStackAgrees nextAlpha qterm bodyBarrier
        callerBarrier pending advanced
        (segmentExecutableRest ++ flattenExecutables outer)
        altTail active outer resources callerScope outerScope context
        baseAlts
        (activatedOpenSuccessor pending copied
          (segmentExecutableRest ++ flattenExecutables outer)
          qterm installed) := by
    exact
      ⟨rfl, rfl, rfl, rfl, rfl,
        ⟨opened.cursor, retainedPosition, activeOwnership⟩,
        alignment, outerAlts,
        actualAlts⟩
  have advancedArguments : advanced.arguments = referencePayload := by
    exact advancedContext.arguments_eq.trans openedArguments
  have advancedBindings : advanced.bindings = referenceBindings := by
    exact advancedContext.bindings_eq.trans openedBindings
  have advancedBelow :
      GeneratedBelow advanced.reservationStart (alpha.map Prod.fst) := by
    have reserved := frontier.finishWellFormed.1
    unfold PreparedCursor.WellReserved at reserved
    rw [frontier.finishRemaining] at reserved
    cases reserved with
    | cons _ _ _ _ startsAbove nonemptyInterval _ =>
        exact
          queryReferenceBelow.mono
            (Nat.le_trans startsAbove nonemptyInterval)
  let snapshot :
      RetainedCallPayloadSnapshot nextAlpha support active advanced
        { barrier := callerBarrier
          references := segmentReferenceRest
          executables := segmentExecutableRest }
        outer := by
    refine
      { snapshotAlpha := alpha
        canonical := canonical
        referenceBase := referenceBase
        referencePayload := referencePayload
        activationOrigin :=
          CallActivationOrigin.ofSessionAt opened.session
            (advancedContext.generation.trans activation.callGeneration)
        activationFresh := by
          change opened.session.resolver.nextFresh = advanced.reservedUntil
          rw [activation.sourceFresh]
          simpa [advanced, PreparedCursor.advance] using
            frontier.finishReservedUntil.symm
        controlOrigin :=
          { bodyBarrier := bodyBarrier
            outerAlts := pending.outer.alts
            outerBarriers := pending.outer.barriers
            frames := pending.frames
            bodyBarrierTag := activation.barrierTag }
        controlOriginBarrier := by
          rfl
        alphaIncluded := activation.alphaIncluded
        allocationGap := by
          apply AlphaAllocationGap.of_frontier
          simpa [active, retainedTailResource, advanced,
            PreparedCursor.advance] using
            activation.selectionFresh
        cursorArguments := advancedArguments
        residualRepresentative := representative
        cumulative := by
          simpa [active, retainedTailResource] using oldCumulative
        materialized := by
          simpa [active, retainedTailResource, advancedBindings] using
            materializedAtOpen
        queryReferenceBelow := advancedBelow
        queryExecutableBelow := ?_
        resourceRest := rfl
        payload := ?_ }
    · have oldBound :
          resolutionSeedHighWaterNames
              (resolutionOccupiedVars
                (args.map (PLeaTTa.subst binding)) res
                (segmentExecutableRest ++ flattenExecutables outer)
                binding qterm) ≤
            startCounter := by
        simpa only [frontier.substitutedArgs] using frontier.highWater
      simpa [active, retainedTailResource] using
        Nat.le_trans oldBound (Nat.le_succ startCounter)
    · simpa [active, retainedTailResource, advancedContext.predicate_eq,
        advancedBindings] using preHeadPayload
  let caller : ControlSegment :=
    { barrier := callerBarrier
      references := segmentReferenceRest
      executables := segmentExecutableRest }
  have callerAgrees : caller.Agrees nextAlpha := by
    simpa [caller] using activation.spinePayload.control.tail.head
  have payloadContext :
      SourceControlResourcePayloadContextAgrees nextAlpha support qterm
        bodyBarrier (caller :: outer) (active :: resources) opened.scope
        ({ callerScope := callerScope
           predicateScope := opened.scope
           retained := .clauses opened.scope advanced
           callerRest := caller.references } ::
         context)
        outerScope :=
    _root_.PLeaTTa.PrologRetainedPayloadSnapshotBridge.ActiveProductResourceStackAgrees.prependPayloadContext
      stack rfl rfl callerAgrees snapshot outerPayloads
  have payloadContextExact :
      SourceControlResourcePayloadContextAgrees nextAlpha support qterm
        bodyBarrier
        ({ barrier := callerBarrier
           references := segmentReferenceRest
           executables := segmentExecutableRest } ::
         outer)
        (active :: resources) opened.scope
        ({ callerScope := callerScope
           predicateScope := opened.scope
           retained := .clauses opened.scope advanced
           callerRest := segmentReferenceRest } ::
         context)
        outerScope := by
    simpa [caller] using payloadContext
  exact
    ⟨active, snapshot, payloadContextExact, rfl, rfl, stack, rfl,
      ⟨rfl, rfl, rfl⟩,
      by
        simpa [snapshot] using
          (CallActivationOrigin.ofSessionAt_extends
            (advancedContext.generation.trans activation.callGeneration)
            (SessionHighWatersExtend.refl opened.session)),
      by
        simpa [snapshot, CallActivationOrigin.ofSessionAt] using
          activation.cutScopeAdvanced⟩

end PLeaTTa.PrologRetainedPayloadSnapshotBridge
