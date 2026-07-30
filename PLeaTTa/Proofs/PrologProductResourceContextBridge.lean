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

/-- Every observable input and output of one retained resolution scan.

This is proof data rather than runtime state.  Keeping the fields explicit
prevents an arbitrary-depth relation from existentially changing the caller
continuation, binding, query term, or cut tag already embedded in `alts`. -/
structure RetainedAlternativeSegment where
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

/-- One explicit resource descriptor is certified by the exact
cursor/alternative ownership relation. -/
def Owns
    (alpha : List (LogicVar × String))
    (cursor : PreparedCursor)
    (resource : RetainedAlternativeSegment) : Prop :=
  RetainedCursorAlternativeOwnership alpha cursor resource.argsv
    resource.args resource.res resource.rest resource.binding resource.qterm
    resource.barrier resource.counter resource.alts resource.finalCounter

/-- Owned frame alternatives never contain an anonymous predicate marker;
that marker is inserted once by `flattenOwnedAlts`. -/
theorem barrierCount_zero
    {alpha : List (LogicVar × String)}
    {cursor : PreparedCursor} {resource : RetainedAlternativeSegment}
    (ownership : resource.Owns alpha cursor) :
    PLeaTTa.barrierCount resource.alts = 0 :=
  RetainedCursorAlternativeOwnership.barrierCount_zero ownership

/-- Conservative prefiltering can only reduce executable alternative count,
never create more alternatives than frozen source occurrences. -/
theorem alts_length_le
    {alpha : List (LogicVar × String)}
    {cursor : PreparedCursor} {resource : RetainedAlternativeSegment}
    (ownership : resource.Owns alpha cursor) :
    resource.alts.length ≤ cursor.remaining.length :=
  RetainedCursorAlternativeOwnership.alts_length_le ownership

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
    (ownership :
      PendingRetainedCursorAlternativeOwnership alpha pending cursor rest
        qterm barrier alts) :
    ∃ resource : RetainedAlternativeSegment,
      resource.rest = rest ∧
      resource.qterm = qterm ∧
      resource.barrier = barrier ∧
      resource.alts = alts ∧
      resource.finalCounter = pending.persistent.counter ∧
      resource.Owns alpha cursor := by
  rcases ownership with
    ⟨argsv, args, res, binding, counter, callHead, queryTerm, barrierExact,
      cursorOwnership⟩
  let resource : RetainedAlternativeSegment :=
    { argsv := argsv
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
    ⟨resource, rfl, rfl, rfl, rfl, rfl, cursorOwnership⟩

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
      (resourceOwnership : resource.Owns alpha cursor)
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
      rw [flattenOwnedAlts_cons, PLeaTTa.barrierCount_append,
        resourceOwnership.barrierCount_zero,
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
  let resourceFor (rest : List PLeaTTa.Goal)
      (barrier : Nat) : RetainedAlternativeSegment :=
    { argsv := []
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
      (resourceFor rest barrier).Owns alpha (cursorFor predicate) := by
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
    resourceFor
      (first.executables ++ flattenExecutables [second]) currentBarrier
  let secondResource := resourceFor second.executables first.barrier
  refine ⟨firstCursor, secondCursor, firstResource, secondResource, ?_⟩
  exact
    .cons currentBarrier inner middle outer first [second] firstResource
      [secondResource] firstCursor
      [{ callerScope := outer
         predicateScope := middle
         retained := .clauses middle secondCursor
         callerRest := second.references }]
      firstAgrees rfl rfl rfl
      (owns "owned-first"
        (first.executables ++ flattenExecutables [second]) currentBarrier)
      (.cons first.barrier middle outer outer second [] secondResource []
        secondCursor [] secondAgrees (by simp [secondResource, resourceFor])
        rfl rfl
        (owns "owned-second" second.executables first.barrier)
        (.nil second.barrier outer))

/-- Deleting the anonymous marker after an owned retained suffix changes the
resource bank.  This is the positional anti-vacuity guard: equal cursor and
branch data cannot compensate for a dropped predicate boundary. -/
theorem dropped_owned_barrier_is_rejected
    {alpha : List (LogicVar × String)}
    {cursor : PreparedCursor}
    (resource : RetainedAlternativeSegment)
    (resources : List RetainedAlternativeSegment)
    (base : List PLeaTTa.Alt)
    (ownership : resource.Owns alpha cursor) :
    resource.alts ++ flattenOwnedAlts resources base ≠
      flattenOwnedAlts (resource :: resources) base := by
  intro equality
  have counts := congrArg PLeaTTa.barrierCount equality
  simp only [flattenOwnedAlts_cons, PLeaTTa.barrierCount_append,
    ownership.barrierCount_zero, Nat.zero_add,
    PLeaTTa.barrierCount_cons_barrier] at counts
  omega

/-- Duplicating the anonymous marker is equally observable.  This guards the
other linearity direction: one source frame cannot own two executable
predicate boundaries. -/
theorem extra_owned_barrier_is_rejected
    {alpha : List (LogicVar × String)}
    {cursor : PreparedCursor}
    (resource : RetainedAlternativeSegment)
    (resources : List RetainedAlternativeSegment)
    (base : List PLeaTTa.Alt)
    (ownership : resource.Owns alpha cursor) :
    resource.alts ++
        PLeaTTa.Alt.barrier :: PLeaTTa.Alt.barrier ::
          flattenOwnedAlts resources base ≠
      flattenOwnedAlts (resource :: resources) base := by
  intro equality
  have counts := congrArg PLeaTTa.barrierCount equality
  simp only [flattenOwnedAlts_cons, PLeaTTa.barrierCount_append,
    ownership.barrierCount_zero, Nat.zero_add,
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
    {qterm : Atom} {bodyBarrier callerBarrier : Nat}
    {callerScope outerScope : CutScopeId}
    {independentResult : Substitution}
    {representative : TreeSubstitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattenedRepresentative : TreeSubstitution}
    {installed : Subst}
    {resources : List RetainedAlternativeSegment}
    {context : ActiveProductContext}
    (activation :
      SpinedRepresentativeProductActivation prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        segmentReferenceRest segmentExecutableRest outer qterm bodyBarrier
        callerBarrier callerScope independentResult representative nextAlpha
        sourceCanonical flattenedRepresentative installed)
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
      active.Owns nextAlpha (finish.advance branch branchTail) ∧
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
    pendingOwnership_exists_segment liftedOwnership
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
      PLeaTTa.barrierCount_append, activeOwnership.barrierCount_zero,
      PLeaTTa.barrierCount_cons_barrier,
      alignment.flattenOwnedAlts_barrierCount]
    omega
  exact
    ⟨active, activeRest, activeQuery, activeBarrier, activeAlts,
      activeFinalCounter, activeOwnership, actualAlts, markerCount,
      alignment.control⟩

end PLeaTTa.PrologProductResourceContextBridge
