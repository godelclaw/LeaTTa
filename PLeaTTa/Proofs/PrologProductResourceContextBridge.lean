-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologProductResourceContextBridge
Purpose: Relate arbitrarily nested retained source clause cursors to the
  executable alternative/barrier stack in exact inner-to-outer order.
Trusted boundary: none
Main exports:
  RetainedAlternativeSegment,
  SourceControlResourceContextAgrees,
  SpinedRepresentativeProductActivation.resources_throughAlignedContext
-/
import PLeaTTa.Proofs.PrologSpinedSourceActivationBridge
import PLeaTTa.Proofs.PrologRetainedCursorOwnershipBridge

namespace PLeaTTa.PrologProductResourceContextBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open PrologActivationMacro
open PrologStateBridge
open PrologControlSegmentSpineBridge
open PrologRepresentativeProductActivationBridge
open PrologRepresentativeStepActivationBridge
open PrologPrefilterScanBridge
open PrologRetainedCursorOwnershipBridge
open PrologSourceProductContextBridge
open PrologSpinedSourceActivationBridge

/-!
The source control zipper proves cursor order and scope safety, while the
activation core now owns the exact executable `altTail` for the innermost
call.  This module joins those facts at arbitrary depth.

Executable barriers are anonymous markers, not source `CutScopeId`s.  The
relation therefore never equates the two identity spaces.  It pairs them
positionally: every source predicate frame contributes one cursor-owned
branch suffix followed by exactly one executable `Alt.barrier`.

The shift between control and resource regions is load-bearing.  A frame's
retained cursor was compiled at the *current* executable predicate barrier,
while its caller goals are the head `ControlSegment`; the next outer frame is
compiled at that segment's stored barrier.  Its alternatives bake the whole
remaining executable continuation, not only the head segment.
-/

/-- Immutable identity of one prepared local-call activation.

`remaining` and `reservationStart` are deliberately absent: they advance
together as frozen occurrences are consumed.  Every field retained here is
fixed for the lifetime of the call.  Recording this projection prevents an
empty resolution bank from erasing which call occurrence it belonged to
without duplicating the candidate list or asserting whole-cursor equality. -/
structure PreparedCallIdentity where
  callGeneration : Generation
  predicate : String
  arguments : List Term
  bindings : Substitution
  reservedUntil : Nat
deriving Repr

namespace PreparedCallIdentity

def ofCursor (cursor : PreparedCursor) : PreparedCallIdentity :=
  { callGeneration := cursor.callGeneration
    predicate := cursor.predicate
    arguments := cursor.arguments
    bindings := cursor.bindings
    reservedUntil := cursor.reservedUntil }

@[simp] theorem ofCursor_advance
    (cursor : PreparedCursor) (branch : ClauseBranch)
    (remaining : List ClauseBranch) :
    ofCursor (cursor.advance branch remaining) = ofCursor cursor := by
  rfl

/-- The existing call-context zipper plus the frozen reservation ceiling is
exactly the information represented by `PreparedCallIdentity`. -/
theorem ofCursor_eq_of_callContext
    {source target : PreparedCursor}
    (context :
      PrologSupportedCursorAlternativeBridge.CursorCallContext target
        source.callGeneration source.predicate source.arguments
        source.bindings)
    (reservedUntil : target.reservedUntil = source.reservedUntil) :
    ofCursor target = ofCursor source := by
  cases source with
  | mk sourceGeneration sourcePredicate sourceArguments sourceBindings
      sourceStart sourceRemaining sourceUntil =>
      cases target with
      | mk targetGeneration targetPredicate targetArguments targetBindings
          targetStart targetRemaining targetUntil =>
          rcases context with
            ⟨generationEq, predicateEq, argumentsEq, bindingsEq⟩
          simp only at generationEq predicateEq argumentsEq bindingsEq
          simp only at reservedUntil
          subst targetGeneration
          subst targetPredicate
          subst targetArguments
          subst targetBindings
          subst targetUntil
          rfl

/-- Equal activation identities plus equal retained banks determine the whole
prepared cursor.  This is the non-tautological bridge used at exhaustion:
identity deliberately excludes `remaining`, so that equality must still be
supplied by the cursor phase. -/
theorem cursor_eq_of_eq_of_remaining_eq
    {left right : PreparedCursor}
    (identity : ofCursor left = ofCursor right)
    (reservationStart : left.reservationStart = right.reservationStart)
    (remaining : left.remaining = right.remaining) :
    left = right := by
  cases left with
  | mk leftGeneration leftPredicate leftArguments leftBindings
      leftStart leftRemaining leftUntil =>
      cases right with
      | mk rightGeneration rightPredicate rightArguments rightBindings
          rightStart rightRemaining rightUntil =>
          simp only [ofCursor] at identity
          injection identity with generationEq predicateEq argumentsEq
            bindingsEq untilEq
          simp only at reservationStart
          simp only at remaining
          subst rightGeneration
          subst rightPredicate
          subst rightArguments
          subst rightBindings
          subst rightStart
          subst rightRemaining
          subst rightUntil
          rfl

private theorem freshReservation_nil_eq
    {start finish : Nat}
    (reserved : FreshReservation start [] finish) :
    start = finish := by
  cases reserved
  rfl

/-- A well-formed exhausted cursor has consumed its whole reserved interval,
so its moving lower frontier has reached the fixed upper frontier. -/
theorem reservationStart_eq_reservedUntil_of_remaining_nil
    {cursor : PreparedCursor}
    (wellFormed : cursor.WellFormed)
    (empty : cursor.remaining = []) :
    cursor.reservationStart = cursor.reservedUntil := by
  have reserved :
      FreshReservation cursor.reservationStart [] cursor.reservedUntil := by
    simpa [PreparedCursor.WellFormed, PreparedCursor.WellReserved, empty]
      using wellFormed.1
  exact freshReservation_nil_eq reserved

end PreparedCallIdentity

/-- Absolute position of one current cursor suffix inside the immutable
call-start occurrence bank.

`position` indexes the occurrence at the head of `current.remaining`; when
that list is empty it is the one-past-the-end position.  The consumed prefix
is source-owned proof data, not a runtime token.  It counts every frozen
occurrence, including conservative rejections which emit no executable
alternative.  Consequently this coordinate must not be reconstructed from
the executable resolution counter.

The relation is call-scoped: `original` is the materialized cursor snapshot
for this activation.  Database updates may change later calls, but cannot
change this frozen bank. -/
def CallScopedCursorPosition
    (original current : PreparedCursor) (position : Nat) : Prop :=
  PreparedCallIdentity.ofCursor current =
      PreparedCallIdentity.ofCursor original /\
    exists consumedPrefix : List ClauseBranch,
      original.remaining = consumedPrefix ++ current.remaining /\
        consumedPrefix.length = position

namespace CallScopedCursorPosition

/-- At call entry the first candidate is at position zero. -/
theorem refl (cursor : PreparedCursor) :
    CallScopedCursorPosition cursor cursor 0 :=
  ⟨rfl, [], by simp, rfl⟩

/-- Consuming the current head advances the absolute occurrence position by
exactly one, independently of whether the occurrence was retained or
rejected by the executable prefilter. -/
theorem advance
    {original current : PreparedCursor} {position : Nat}
    {branch : ClauseBranch} {remaining : List ClauseBranch}
    (positionProof : CallScopedCursorPosition original current position)
    (currentHead : current.remaining = branch :: remaining) :
    CallScopedCursorPosition original
      (current.advance branch remaining) (position + 1) := by
  rcases positionProof with
    ⟨callIdentity, consumedPrefix, suffixExact, positionExact⟩
  refine
    ⟨(PreparedCallIdentity.ofCursor_advance current branch remaining).trans
        callIdentity,
      consumedPrefix ++ [branch], ?_, ?_⟩
  · rw [suffixExact, currentHead]
    simp [PreparedCursor.advance, List.append_assoc]
  · simp [positionExact]

/-- A real rejected-prefix derivation advances the same absolute coordinate
by its exact transition count.  `RejectedPullsN` remains responsible only for
the local clash-justified prefix; the cumulative coordinate comes from the
plain frozen-bank suffix equation above. -/
theorem afterRejected
    {count : Nat} {before after original : PreparedCursor}
    {position : Nat}
    (pulls : RejectedPullsN count before after)
    (positionProof : CallScopedCursorPosition original before position) :
    CallScopedCursorPosition original after (position + count) := by
  induction pulls generalizing position with
  | zero cursor =>
      simpa using positionProof
  | succ count cursor branch branches finish remaining clash tail
      inductionHypothesis =>
      have one :
          CallScopedCursorPosition original
            (cursor.advance branch branches) (position + 1) :=
        positionProof.advance remaining
      have many := inductionHypothesis one
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using many

/-- The definition's head-index convention is exposed directly: if the
current suffix begins with `branch`, the original bank has exactly `position`
occurrences before that selected occurrence. -/
theorem selectedOccurrence
    {original current : PreparedCursor} {position : Nat}
    {branch : ClauseBranch} {remaining : List ClauseBranch}
    (positionProof : CallScopedCursorPosition original current position)
    (currentHead : current.remaining = branch :: remaining) :
    exists consumed,
      original.remaining = consumed ++ (branch :: remaining) /\
        consumed.length = position := by
  rcases positionProof with
    ⟨_callIdentity, consumedPrefix, suffixExact, positionExact⟩
  exact
    ⟨consumedPrefix, by simpa [currentHead] using suffixExact,
      positionExact⟩

/-- The coordinate is exactly the length difference between the immutable
call-start bank and the current suffix. -/
theorem remaining_length_eq
    {original current : PreparedCursor} {position : Nat}
    (positionProof : CallScopedCursorPosition original current position) :
    original.remaining.length = position + current.remaining.length := by
  rcases positionProof with
    ⟨_callIdentity, consumedPrefix, suffixExact, positionExact⟩
  have lengths := congrArg List.length suffixExact
  simpa [positionExact] using lengths

/-- An exhausted current suffix is indexed one past the final call-start
occurrence, not at the final occurrence itself. -/
theorem onePastEnd
    {original current : PreparedCursor} {position : Nat}
    (positionProof : CallScopedCursorPosition original current position)
    (empty : current.remaining = []) :
    position = original.remaining.length := by
  have lengths := positionProof.remaining_length_eq
  simp [empty] at lengths
  omega

/-- A nonempty current suffix makes `position` a valid index of its head in
the immutable call-start bank. -/
theorem headPosition_lt
    {original current : PreparedCursor} {position : Nat}
    {branch : ClauseBranch} {remaining : List ClauseBranch}
    (positionProof : CallScopedCursorPosition original current position)
    (currentHead : current.remaining = branch :: remaining) :
    position < original.remaining.length := by
  have lengths := positionProof.remaining_length_eq
  simp [currentHead] at lengths
  omega

/-- For fixed original and current cursors, the absolute position is unique;
no proof can choose a cheaper or later prefix with the same endpoints. -/
theorem position_unique
    {original current : PreparedCursor} {left right : Nat}
    (leftAt : CallScopedCursorPosition original current left)
    (rightAt : CallScopedCursorPosition original current right) :
    left = right := by
  rcases leftAt with
    ⟨_leftIdentity, leftPrefix, leftSuffix, leftPosition⟩
  rcases rightAt with
    ⟨_rightIdentity, rightPrefix, rightSuffix, rightPosition⟩
  have leftLength := congrArg List.length leftSuffix
  have rightLength := congrArg List.length rightSuffix
  simp only [List.length_append] at leftLength rightLength
  rw [leftPosition] at leftLength
  rw [rightPosition] at rightLength
  omega

end CallScopedCursorPosition

/-- Every observable input and output of one retained resolution scan.

This is proof data rather than runtime state.  Keeping the fields explicit
prevents an arbitrary-depth relation from existentially changing the caller
continuation, binding, query term, or cut tag already embedded in `alts`. -/
structure RetainedAlternativeSegment where
  callIdentity : PreparedCallIdentity
  argsv : List Atom
  args : List Atom
  res : Atom
  rest : List PLeaTTa.Goal
  binding : Subst
  qterm : Atom
  barrier : Nat
  counter : Nat
  alts : List PLeaTTa.Alt
  finalCounter : Nat
deriving Repr

namespace RetainedAlternativeSegment

/-- One explicit resource descriptor is certified jointly by its immutable
call-start coordinate, current cursor suffix, and exact alternative scan.

Keeping `callStart`, `cursor`, and `position` as relation indices rather than
mutable-looking fields is load-bearing: a record update cannot silently carry
a stale source coordinate across rejected pulls or executable-head
consumption.  Authenticity of `callStart` as an actual `openedFor` cursor is
established by producer theorems; this relation couples that supplied origin
to the resource without manufacturing it. -/
structure Owns
    (alpha : List (LogicVar × String))
    (callStart cursor : PreparedCursor) (position : Nat)
    (resource : RetainedAlternativeSegment) : Prop where
  identity :
    resource.callIdentity = PreparedCallIdentity.ofCursor cursor
  scan :
    RetainedCursorAlternativeOwnership alpha cursor resource.argsv
      resource.args resource.res resource.rest resource.binding resource.qterm
      resource.barrier resource.counter resource.alts resource.finalCounter
  positioned : CallScopedCursorPosition callStart cursor position

/-- Exact ownership exposes the pre-existing ordered-scan certificate after
the activation identity has been checked. -/
theorem Owns.scanExact
    {alpha : List (LogicVar × String)}
    {callStart cursor : PreparedCursor} {position : Nat}
    {resource : RetainedAlternativeSegment}
    (ownership : resource.Owns alpha callStart cursor position) :
    RetainedCursorAlternativeOwnership alpha cursor resource.argsv
      resource.args resource.res resource.rest resource.binding resource.qterm
      resource.barrier resource.counter resource.alts resource.finalCounter :=
  ownership.scan

/-- Enlarging the alpha graph changes only the semantic scan certificate;
the exact call identity and every executable resource field remain fixed. -/
theorem Owns.mono
    {smaller larger : List (LogicVar × String)}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    {callStart cursor : PreparedCursor} {position : Nat}
    {resource : RetainedAlternativeSegment}
    (ownership : resource.Owns smaller callStart cursor position) :
    resource.Owns larger callStart cursor position :=
  ⟨ownership.identity,
    RetainedCursorAlternativeOwnership.mono included ownership.scan,
    ownership.positioned⟩

/-- Existential packaging for consumers that retain an exact indexed
ownership certificate but do not inspect its call-start coordinate.

This is intentionally not a defaulting constructor: callers must supply an
actual `Owns` proof, including its `CallScopedCursorPosition`.  Producer
theorems continue to expose the concrete call start and position whenever
those coordinates are semantically relevant. -/
def HasIndexedOwnershipAt
    (resource : RetainedAlternativeSegment)
    (alpha : List (LogicVar × String)) (cursor : PreparedCursor) : Prop :=
  ∃ callStart position, resource.Owns alpha callStart cursor position

namespace HasIndexedOwnershipAt

/-- Enlarging the alpha graph preserves the same hidden call-start coordinate
and absolute source position. -/
theorem mono
    {smaller larger : List (LogicVar × String)}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    {cursor : PreparedCursor} {resource : RetainedAlternativeSegment}
    (ownership : resource.HasIndexedOwnershipAt smaller cursor) :
    resource.HasIndexedOwnershipAt larger cursor := by
  rcases ownership with ⟨callStart, position, exactOwnership⟩
  exact ⟨callStart, position, exactOwnership.mono included⟩

/-- Existential packaging does not erase marker-freedom of the exact owned
alternative slice. -/
theorem barrierCount_zero
    {alpha : List (LogicVar × String)} {cursor : PreparedCursor}
    {resource : RetainedAlternativeSegment}
    (ownership : resource.HasIndexedOwnershipAt alpha cursor) :
    PLeaTTa.barrierCount resource.alts = 0 := by
  rcases ownership with ⟨_callStart, _position, exactOwnership⟩
  exact RetainedCursorAlternativeOwnership.barrierCount_zero
    exactOwnership.scan

/-- Existential packaging also retains the source-occurrence upper bound on
the executable alternative slice. -/
theorem alts_length_le
    {alpha : List (LogicVar × String)} {cursor : PreparedCursor}
    {resource : RetainedAlternativeSegment}
    (ownership : resource.HasIndexedOwnershipAt alpha cursor) :
    resource.alts.length ≤ cursor.remaining.length := by
  rcases ownership with ⟨_callStart, _position, exactOwnership⟩
  exact RetainedCursorAlternativeOwnership.alts_length_le
    exactOwnership.scan

end HasIndexedOwnershipAt

/-- One resource cannot own two different exhausted cursors.  At exhaustion
both retained banks are literally empty, while `Owns` fixes every immutable
call-entry field through `PreparedCallIdentity`; cursor extensionality then
closes the formerly ambiguous occurrence. -/
theorem Owns.exhausted_cursor_injective
    {alpha : List (LogicVar × String)}
    {leftStart rightStart left right : PreparedCursor}
    {leftPosition rightPosition : Nat}
    {resource : RetainedAlternativeSegment}
    (leftOwnership :
      resource.Owns alpha leftStart left leftPosition)
    (rightOwnership :
      resource.Owns alpha rightStart right rightPosition)
    (leftEmpty : left.remaining = [])
    (rightEmpty : right.remaining = []) :
    left = right := by
  have identity :=
    leftOwnership.identity.symm.trans rightOwnership.identity
  have leftWellFormed : left.WellFormed := by
    rcases leftOwnership.scan with
      ⟨_candidates, wellFormed, _query, _args, _supported, _arities, _scan⟩
    exact wellFormed
  have rightWellFormed : right.WellFormed := by
    rcases rightOwnership.scan with
      ⟨_candidates, wellFormed, _query, _args, _supported, _arities, _scan⟩
    exact wellFormed
  have leftStart : left.reservationStart = left.reservedUntil :=
    PreparedCallIdentity.reservationStart_eq_reservedUntil_of_remaining_nil
      leftWellFormed leftEmpty
  have rightStart : right.reservationStart = right.reservedUntil :=
    PreparedCallIdentity.reservationStart_eq_reservedUntil_of_remaining_nil
      rightWellFormed rightEmpty
  have untilEq : left.reservedUntil = right.reservedUntil :=
    congrArg PreparedCallIdentity.reservedUntil identity
  apply PreparedCallIdentity.cursor_eq_of_eq_of_remaining_eq identity
  · exact leftStart.trans (untilEq.trans rightStart.symm)
  · exact leftEmpty.trans rightEmpty.symm

/-- Owned frame alternatives never contain an anonymous predicate marker;
that marker is inserted once by `flattenOwnedAlts`. -/
theorem barrierCount_zero
    {alpha : List (LogicVar × String)}
    {callStart cursor : PreparedCursor} {position : Nat}
    {resource : RetainedAlternativeSegment}
    (ownership : resource.Owns alpha callStart cursor position) :
    PLeaTTa.barrierCount resource.alts = 0 :=
  RetainedCursorAlternativeOwnership.barrierCount_zero ownership.scan

/-- Conservative prefiltering can only reduce executable alternative count,
never create more alternatives than frozen source occurrences. -/
theorem alts_length_le
    {alpha : List (LogicVar × String)}
    {callStart cursor : PreparedCursor} {position : Nat}
    {resource : RetainedAlternativeSegment}
    (ownership : resource.Owns alpha callStart cursor position) :
    resource.alts.length ≤ cursor.remaining.length :=
  RetainedCursorAlternativeOwnership.alts_length_le ownership.scan

end RetainedAlternativeSegment

/-- Exact executable alternative layout for inner-to-outer retained predicate
regions above an arbitrary older base bank. -/
def flattenOwnedAlts :
    List RetainedAlternativeSegment → List PLeaTTa.Alt →
      List PLeaTTa.Alt
  | [], base => base
  | resource :: resources, base =>
      resource.alts ++ PLeaTTa.Alt.barrier ::
        flattenOwnedAlts resources base

@[simp] theorem flattenOwnedAlts_nil (base : List PLeaTTa.Alt) :
    flattenOwnedAlts [] base = base := rfl

@[simp] theorem flattenOwnedAlts_cons
    (resource : RetainedAlternativeSegment)
    (resources : List RetainedAlternativeSegment)
    (base : List PLeaTTa.Alt) :
    flattenOwnedAlts (resource :: resources) base =
      resource.alts ++ PLeaTTa.Alt.barrier ::
        flattenOwnedAlts resources base := rfl

/-- A pending-call ownership certificate exposes one explicit resource
descriptor with no loss of any indexed field. -/
theorem pendingOwnership_exists_segment
    {alpha : List (LogicVar × String)}
    {pending : DemandDrivenCallStep.PendingCall}
    {cursor : PreparedCursor}
    {rest : List PLeaTTa.Goal} {qterm : Atom} {barrier : Nat}
    {alts : List PLeaTTa.Alt}
    (callStart : PreparedCursor) (position : Nat)
    (positioned : CallScopedCursorPosition callStart cursor position)
    (ownership :
      PendingRetainedCursorAlternativeOwnership alpha pending cursor rest
        qterm barrier alts) :
    ∃ resource : RetainedAlternativeSegment,
      resource.rest = rest ∧
      resource.qterm = qterm ∧
      resource.barrier = barrier ∧
      resource.alts = alts ∧
      resource.finalCounter = pending.persistent.counter ∧
      resource.Owns alpha callStart cursor position := by
  rcases ownership with
    ⟨argsv, args, res, binding, counter, callHead, queryTerm, barrierExact,
      cursorOwnership⟩
  let resource : RetainedAlternativeSegment :=
    { callIdentity := PreparedCallIdentity.ofCursor cursor
      argsv := argsv
      args := args
      res := res
      rest := rest
      binding := binding
      qterm := qterm
      barrier := barrier
      counter := counter
      alts := alts
      finalCounter := pending.persistent.counter }
  exact
    ⟨resource, rfl, rfl, rfl, rfl, rfl,
      ⟨rfl, cursorOwnership, positioned⟩⟩

/-- Arbitrary-depth alignment of:

* one executable caller segment,
* one explicit retained-alternative descriptor,
* one source product frame whose right branch is exactly a prepared cursor.

`currentBarrier` belongs to the frame's retained predicate.  Recursion shifts
to `segment.barrier`, because the segment is the current frame's caller tail
and therefore names the next outer executable region. -/
inductive SourceControlResourceContextAgrees
    (alpha : List (LogicVar × String)) (qterm : Atom) :
    Nat → List ControlSegment → List RetainedAlternativeSegment →
      CutScopeId → ActiveProductContext → CutScopeId → Prop where
  | nil (currentBarrier : Nat) (scope : CutScopeId) :
      SourceControlResourceContextAgrees alpha qterm currentBarrier
        [] [] scope [] scope
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
      (resourceOwnership :
        ∃ callStart position,
          resource.Owns alpha callStart cursor position)
      (outerAgrees :
        SourceControlResourceContextAgrees alpha qterm segment.barrier
          segments resources nextScope context outerScope) :
      SourceControlResourceContextAgrees alpha qterm currentBarrier
        (segment :: segments) (resource :: resources) currentScope
        ({ callerScope := nextScope
           predicateScope := currentScope
           retained := .clauses currentScope cursor
           callerRest := segment.references } ::
         context)
        outerScope

namespace SourceControlResourceContextAgrees

/-- The head resource owns the exact prepared cursor stored by the head
source frame. -/
theorem headOwnership
    {alpha : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {currentScope nextScope outerScope : CutScopeId}
    {cursor : PreparedCursor} {context : ActiveProductContext}
    (agreement :
      SourceControlResourceContextAgrees alpha qterm currentBarrier
        (segment :: segments) (resource :: resources) currentScope
        ({ callerScope := nextScope
           predicateScope := currentScope
           retained := .clauses currentScope cursor
           callerRest := segment.references } :: context)
        outerScope) :
    resource.HasIndexedOwnershipAt alpha cursor := by
  cases agreement with
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership outerAgrees =>
      exact resourceOwnership

/-- The head resource carries the query identity indexed by the complete
alignment. -/
theorem headQuery
    {alpha : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {currentScope nextScope outerScope : CutScopeId}
    {cursor : PreparedCursor} {context : ActiveProductContext}
    (agreement :
      SourceControlResourceContextAgrees alpha qterm currentBarrier
        (segment :: segments) (resource :: resources) currentScope
        ({ callerScope := nextScope
           predicateScope := currentScope
           retained := .clauses currentScope cursor
           callerRest := segment.references } :: context)
        outerScope) :
    resource.qterm = qterm := by
  cases agreement with
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership outerAgrees =>
      exact resourceQuery

/-- Remove the head resource/control/frame cell with its shifted barrier and
scope indices intact. -/
def tail
    {alpha : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {currentScope nextScope outerScope : CutScopeId}
    {cursor : PreparedCursor} {context : ActiveProductContext}
    (agreement :
      SourceControlResourceContextAgrees alpha qterm currentBarrier
        (segment :: segments) (resource :: resources) currentScope
        ({ callerScope := nextScope
           predicateScope := currentScope
           retained := .clauses currentScope cursor
           callerRest := segment.references } :: context)
        outerScope) :
    SourceControlResourceContextAgrees alpha qterm segment.barrier segments
      resources nextScope context outerScope := by
  cases agreement with
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership outerAgrees =>
      exact outerAgrees

/-- Forgetting executable resources recovers the earlier exact
source/control-segment zipper. -/
theorem control
    {alpha : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (agreement :
      SourceControlResourceContextAgrees alpha qterm currentBarrier segments
        resources inner context outer) :
    SourceControlContextAgrees alpha inner segments context outer := by
  induction agreement with
  | nil currentBarrier scope =>
      exact .nil scope
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership outerAgrees
      inductionHypothesis =>
      exact
        .cons currentScope nextScope outerScope segment segments
          (.clauses currentScope cursor) context segmentAgrees
          (.clauses currentScope cursor) inductionHypothesis

/-- The three spines are genuinely one-to-one: no source frame, caller
segment, or retained executable resource can be inserted or dropped. -/
theorem lengths_eq
    {alpha : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (agreement :
      SourceControlResourceContextAgrees alpha qterm currentBarrier segments
        resources inner context outer) :
    context.length = segments.length ∧
      segments.length = resources.length := by
  induction agreement with
  | nil =>
      exact ⟨rfl, rfl⟩
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership outerAgrees
      inductionHypothesis =>
      exact
        ⟨congrArg Nat.succ inductionHypothesis.1,
          congrArg Nat.succ inductionHypothesis.2⟩

/-- Every related source frame contributes exactly one anonymous executable
predicate marker, in addition to the markers already owned by `base`.
Source scope identities never appear in this arithmetic statement. -/
theorem flattenOwnedAlts_barrierCount
    {alpha : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (agreement :
      SourceControlResourceContextAgrees alpha qterm currentBarrier segments
        resources inner context outer)
    (base : List PLeaTTa.Alt) :
    PLeaTTa.barrierCount (flattenOwnedAlts resources base) =
      resources.length + PLeaTTa.barrierCount base := by
  induction agreement with
  | nil =>
      simp [flattenOwnedAlts]
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership outerAgrees
      inductionHypothesis =>
      rcases resourceOwnership with
        ⟨callStart, position, resourceOwnership⟩
      rw [flattenOwnedAlts_cons, PLeaTTa.barrierCount_append,
        RetainedAlternativeSegment.barrierCount_zero resourceOwnership,
        PLeaTTa.barrierCount_cons_barrier, inductionHypothesis]
      simp only [List.length_cons]
      omega

end SourceControlResourceContextAgrees

/-- Two resource-bearing nesting levels are constructively alignable.

The witness uses two distinct constant output-last calls whose retained
candidate banks are empty.  Each empty `ResolutionScan` owns its exact empty
alternative suffix, while the two source frames still contribute two distinct
anonymous executable markers.  Thus the substantive `cons` case of
`SourceControlResourceContextAgrees` and the premises of the marker-linearity
witnesses are inhabited independently of an activation theorem. -/
theorem two_resource_frames_are_inhabited
    {alpha : List (LogicVar × String)}
    (qterm : Atom) (inner middle outer : CutScopeId)
    (currentBarrier : Nat)
    (first second : ControlSegment)
    (firstAgrees : first.Agrees alpha)
    (secondAgrees : second.Agrees alpha) :
    ∃ firstCursor secondCursor : PreparedCursor,
      ∃ firstResource secondResource : RetainedAlternativeSegment,
        SourceControlResourceContextAgrees alpha qterm currentBarrier
          [first, second] [firstResource, secondResource] inner
          [{ callerScope := middle
             predicateScope := inner
             retained := .clauses inner firstCursor
             callerRest := first.references },
           { callerScope := outer
             predicateScope := middle
             retained := .clauses middle secondCursor
             callerRest := second.references }]
          outer := by
  let cursorFor (predicate : String) : PreparedCursor :=
    { callGeneration := 0
      predicate := predicate
      arguments := [.atom "owned-output"]
      bindings := []
      reservationStart := 0
      remaining := []
      reservedUntil := 0 }
  let resourceFor (predicate : String) (rest : List PLeaTTa.Goal)
      (barrier : Nat) : RetainedAlternativeSegment :=
    { callIdentity := PreparedCallIdentity.ofCursor (cursorFor predicate)
      argsv := []
      args := []
      res := .sym "owned-output"
      rest := rest
      binding := []
      qterm := qterm
      barrier := barrier
      counter := 0
      alts := []
      finalCounter := 0 }
  have owns (predicate : String) (rest : List PLeaTTa.Goal)
      (barrier : Nat) :
      (resourceFor predicate rest barrier).Owns alpha
        (cursorFor predicate) (cursorFor predicate) 0 := by
    refine ⟨rfl, ?_, CallScopedCursorPosition.refl _⟩
    refine ⟨[], ?_, ?_, rfl, .nil, ?_, ?_⟩
    · refine ⟨.nil 0, ?_, ?_, ?_⟩
      · intro index member
        simp [cursorFor, termsVariables, termVariables,
          substitutionVariables] at member
      · intro branch member
        simp [cursorFor] at member
      · intro branch member
        simp [cursorFor] at member
    · apply
        PLeaTTa.PrologRecursiveCallPayloadBridge.NormalizedCallAgrees.representative
      constructor
      simpa [cursorFor, resourceFor] using
        (AlphaTermsAgree.cons
          (AlphaTermAgrees.atom (alpha := alpha) (by decide) (by decide))
          AlphaTermsAgree.nil)
    · intro clause member
      simp at member
    · exact ResolutionScan.nil 0
  let firstCursor := cursorFor "owned-first"
  let secondCursor := cursorFor "owned-second"
  let firstResource :=
    resourceFor "owned-first"
      (first.executables ++ flattenExecutables [second]) currentBarrier
  let secondResource :=
    resourceFor "owned-second" second.executables first.barrier
  refine ⟨firstCursor, secondCursor, firstResource, secondResource, ?_⟩
  exact
    .cons currentBarrier inner middle outer first [second] firstResource
      [secondResource] firstCursor
      [{ callerScope := outer
         predicateScope := middle
         retained := .clauses middle secondCursor
         callerRest := second.references }]
      firstAgrees rfl rfl rfl
      ⟨firstCursor, 0,
        owns "owned-first"
          (first.executables ++ flattenExecutables [second]) currentBarrier⟩
        (.cons first.barrier middle outer outer second [] secondResource []
        secondCursor [] secondAgrees (by simp [secondResource, resourceFor])
        rfl rfl
        ⟨secondCursor, 0,
          owns "owned-second" second.executables first.barrier⟩
        (.nil second.barrier outer))

/-- Deleting the anonymous marker after an owned retained suffix changes the
resource bank.  This is the positional anti-vacuity guard: equal cursor and
branch data cannot compensate for a dropped predicate boundary. -/
theorem dropped_owned_barrier_is_rejected
    {alpha : List (LogicVar × String)}
    {callStart cursor : PreparedCursor} {position : Nat}
    (resource : RetainedAlternativeSegment)
    (resources : List RetainedAlternativeSegment)
    (base : List PLeaTTa.Alt)
    (ownership : resource.Owns alpha callStart cursor position) :
    resource.alts ++ flattenOwnedAlts resources base ≠
      flattenOwnedAlts (resource :: resources) base := by
  intro equality
  have counts := congrArg PLeaTTa.barrierCount equality
  simp only [flattenOwnedAlts_cons, PLeaTTa.barrierCount_append,
    RetainedAlternativeSegment.barrierCount_zero ownership, Nat.zero_add,
    PLeaTTa.barrierCount_cons_barrier] at counts
  omega

/-- Duplicating the anonymous marker is equally observable.  This guards the
other linearity direction: one source frame cannot own two executable
predicate boundaries. -/
theorem extra_owned_barrier_is_rejected
    {alpha : List (LogicVar × String)}
    {callStart cursor : PreparedCursor} {position : Nat}
    (resource : RetainedAlternativeSegment)
    (resources : List RetainedAlternativeSegment)
    (base : List PLeaTTa.Alt)
    (ownership : resource.Owns alpha callStart cursor position) :
    resource.alts ++
        PLeaTTa.Alt.barrier :: PLeaTTa.Alt.barrier ::
          flattenOwnedAlts resources base ≠
      flattenOwnedAlts (resource :: resources) base := by
  intro equality
  have counts := congrArg PLeaTTa.barrierCount equality
  simp only [flattenOwnedAlts_cons, PLeaTTa.barrierCount_append,
    RetainedAlternativeSegment.barrierCount_zero ownership, Nat.zero_add,
    PLeaTTa.barrierCount_cons_barrier] at counts
  omega

/-- One spined activation plus a resource-enriched outer context yields the
exact complete executable alternative layout.

The theorem is indexed by the activated state's *actual* `alts`; it does not
merely construct an isomorphic list.  The new innermost resource is certified
at `bodyBarrier`, while the outer zipper begins at `callerBarrier`. -/
theorem
    _root_.PLeaTTa.PrologRepresentativeProductActivationBridge.SpinedRepresentativeProductActivation.resources_throughAlignedContext
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {copied : PLeaTTa.Clause}
    {segmentReferenceRest : List PeTTaSpec.PrologCore.Goal}
    {segmentExecutableRest : List PLeaTTa.Goal}
    {outer : List ControlSegment}
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
    (activation :
      SpinedRepresentativeProductActivation prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        segmentReferenceRest segmentExecutableRest outer qterm bodyBarrier
        callerBarrier startCounter callerScope independentResult representative
        nextAlpha sourceCanonical flattenedRepresentative installed)
    (alignment :
      SourceControlResourceContextAgrees nextAlpha qterm callerBarrier outer
        resources callerScope context outerScope)
    (baseAlts : List PLeaTTa.Alt)
    (outerAlts :
      pending.outer.alts = flattenOwnedAlts resources baseAlts) :
    ∃ active : RetainedAlternativeSegment,
      active.rest =
        segmentExecutableRest ++ flattenExecutables outer ∧
      active.qterm = qterm ∧
      active.barrier = bodyBarrier ∧
      active.alts = altTail ∧
      active.finalCounter = pending.persistent.counter ∧
      active.Owns nextAlpha opened.cursor
        (finish.advance branch branchTail) retainedPosition ∧
      (activatedExecutableSuccessor pending copied
        (segmentExecutableRest ++ flattenExecutables outer)
        qterm installed).alts =
          flattenOwnedAlts (active :: resources) baseAlts ∧
      PLeaTTa.barrierCount
          (activatedExecutableSuccessor pending copied
            (segmentExecutableRest ++ flattenExecutables outer)
            qterm installed).alts =
        (resources.length + 1) + PLeaTTa.barrierCount baseAlts ∧
      SourceControlContextAgrees nextAlpha callerScope outer context
        outerScope := by
  have liftedOwnership :
      PendingRetainedCursorAlternativeOwnership nextAlpha pending
        (finish.advance branch branchTail)
        (segmentExecutableRest ++ flattenExecutables outer)
        qterm bodyBarrier altTail :=
    PendingRetainedCursorAlternativeOwnership.mono activation.alphaIncluded
      activation.retainedCursorOwnership
  obtain
    ⟨active, activeRest, activeQuery, activeBarrier, activeAlts,
      activeFinalCounter, activeOwnership⟩ :=
    pendingOwnership_exists_segment opened.cursor retainedPosition positioned
      liftedOwnership
  have actualAlts :
      (activatedExecutableSuccessor pending copied
        (segmentExecutableRest ++ flattenExecutables outer)
        qterm installed).alts =
          flattenOwnedAlts (active :: resources) baseAlts := by
    rw [activation.retainedAlts, ← activeAlts, outerAlts]
    rfl
  have markerCount :
      PLeaTTa.barrierCount
          (activatedExecutableSuccessor pending copied
            (segmentExecutableRest ++ flattenExecutables outer)
            qterm installed).alts =
        (resources.length + 1) + PLeaTTa.barrierCount baseAlts := by
    rw [actualAlts, flattenOwnedAlts_cons,
      PLeaTTa.barrierCount_append,
      RetainedAlternativeSegment.barrierCount_zero activeOwnership,
      PLeaTTa.barrierCount_cons_barrier,
      alignment.flattenOwnedAlts_barrierCount]
    omega
  exact
    ⟨active, activeRest, activeQuery, activeBarrier, activeAlts,
      activeFinalCounter, activeOwnership, actualAlts, markerCount,
      alignment.control⟩

end PLeaTTa.PrologProductResourceContextBridge
