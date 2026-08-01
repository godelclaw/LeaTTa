-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologControlSegmentSpineBridge
Purpose: Preserve arbitrarily nested predicate cut regions across the sealed
  machine's flattened task list.
Trusted boundary: none
Main exports:
  ControlSegment,
  ControlSpineAgrees,
  TaskSpinePayloadAgrees,
  TaskSpinePayloadAgrees.activateLocalCall
-/
import PLeaTTa.Proofs.PrologTaskContinuationBridge

namespace PLeaTTa.PrologControlSegmentSpineBridge

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.OpenSubstitution
open PrologOrdinaryStepBridge

/-- One source/executable control region in a flattened task.

Each region retains the cut barrier at which its goals were compiled.  Keeping
the barrier inside the segment prevents an enclosing caller tail from being
silently retagged when another recursive predicate body is prepended. -/
structure ControlSegment where
  barrier : Nat
  references : List PeTTaSpec.PrologCore.Goal
  executables : List PLeaTTa.Goal

namespace ControlSegment

/-- Exact administrative-normalized agreement for one control region. -/
def Agrees (alpha : List (LogicVar × String))
    (segment : ControlSegment) : Prop :=
  NormalizedAlphaGoalsAgree alpha segment.barrier
    segment.references segment.executables

/-- The source goals represented by a segment. -/
def sourceGoals (segment : ControlSegment) :
    List PeTTaSpec.PrologCore.Goal :=
  segment.references

/-- The executable goals represented by a segment. -/
def executableGoals (segment : ControlSegment) : List PLeaTTa.Goal :=
  segment.executables

end ControlSegment

/-- Pointwise control agreement for an arbitrary-depth continuation spine.

The list order is execution order: the active predicate body is first, followed
by its caller remainder, then successively older caller regions.  Shared
substitution facts deliberately do not appear here; they are carried once by
`TaskSpinePayloadAgrees`. -/
inductive ControlSpineAgrees (alpha : List (LogicVar × String)) :
    List ControlSegment → Prop where
  | nil : ControlSpineAgrees alpha []
  | cons {segment : ControlSegment} {segments : List ControlSegment}
      (head : segment.Agrees alpha)
      (tail : ControlSpineAgrees alpha segments) :
      ControlSpineAgrees alpha (segment :: segments)

namespace ControlSpineAgrees

/-- Alpha extension preserves every region without changing any cut barrier. -/
theorem mono
    {smaller larger : List (LogicVar × String)}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    {segments : List ControlSegment}
    (agreement : ControlSpineAgrees smaller segments) :
    ControlSpineAgrees larger segments := by
  induction agreement with
  | nil =>
      exact .nil
  | cons head tail inductionHypothesis =>
      exact .cons (head.mono included) inductionHypothesis

/-- Recover the active control region. -/
theorem head
    {alpha : List (LogicVar × String)}
    {segment : ControlSegment} {segments : List ControlSegment}
    (agreement : ControlSpineAgrees alpha (segment :: segments)) :
    segment.Agrees alpha := by
  cases agreement with
  | cons head _ => exact head

/-- Recover all enclosing control regions. -/
theorem tail
    {alpha : List (LogicVar × String)}
    {segment : ControlSegment} {segments : List ControlSegment}
    (agreement : ControlSpineAgrees alpha (segment :: segments)) :
    ControlSpineAgrees alpha segments := by
  cases agreement with
  | cons _ tail => exact tail

/-- Every member of a certified spine is certified at its own stored barrier. -/
theorem member
    {alpha : List (LogicVar × String)}
    {segments : List ControlSegment}
    (agreement : ControlSpineAgrees alpha segments)
    {segment : ControlSegment} (present : segment ∈ segments) :
    segment.Agrees alpha := by
  induction agreement with
  | nil =>
      simp at present
  | @cons headSegment tailSegments head tail inductionHypothesis =>
      simp only [List.mem_cons] at present
      rcases present with rfl | present
      · exact head
      · exact inductionHypothesis present

/-- Concatenating two certified spines preserves exact region order. -/
theorem append
    {alpha : List (LogicVar × String)}
    {left right : List ControlSegment}
    (leftAgreement : ControlSpineAgrees alpha left)
    (rightAgreement : ControlSpineAgrees alpha right) :
    ControlSpineAgrees alpha (left ++ right) := by
  induction leftAgreement with
  | nil =>
      exact rightAgreement
  | cons head tail inductionHypothesis =>
      exact .cons head inductionHypothesis

end ControlSpineAgrees

/-- Flatten source regions without erasing their separately stored barriers. -/
def flattenReferences (segments : List ControlSegment) :
    List PeTTaSpec.PrologCore.Goal :=
  segments.flatMap ControlSegment.sourceGoals

/-- Flatten executable regions in the exact order used by the sealed task. -/
def flattenExecutables (segments : List ControlSegment) :
    List PLeaTTa.Goal :=
  segments.flatMap ControlSegment.executableGoals

@[simp] theorem flattenReferences_nil :
    flattenReferences [] = [] := rfl

@[simp] theorem flattenReferences_cons
    (segment : ControlSegment) (segments : List ControlSegment) :
    flattenReferences (segment :: segments) =
      segment.references ++ flattenReferences segments := rfl

@[simp] theorem flattenExecutables_nil :
    flattenExecutables [] = [] := rfl

@[simp] theorem flattenExecutables_cons
    (segment : ControlSegment) (segments : List ControlSegment) :
    flattenExecutables (segment :: segments) =
      segment.executables ++ flattenExecutables segments := rfl

namespace ControlSpineAgrees

/-- If every source continuation in a certified spine is literally empty,
the exact flattened executable continuation is empty as well.  The proof is
pointwise and order preserving; it does not infer emptiness from a length or
from the final machine state. -/
theorem flattenExecutables_eq_nil_of_all_references_eq_nil
    {alpha : List (LogicVar × String)} {segments : List ControlSegment}
    (agreement : ControlSpineAgrees alpha segments)
    (allEmpty :
      forall segment, segment ∈ segments -> segment.references = []) :
    flattenExecutables segments = [] := by
  induction agreement with
  | nil =>
      rfl
  | @cons segment segments head tail inductionHypothesis =>
      have referencesEmpty : segment.references = [] :=
        allEmpty segment (by simp)
      have executablesEmpty : segment.executables = [] :=
        PrologOrdinaryStepBridge.NormalizedAlphaGoalsAgree.executables_eq_nil_of_references_eq_nil
          head referencesEmpty
      have tailEmpty :
          forall candidate, candidate ∈ segments ->
            candidate.references = [] := by
        intro candidate member
        exact allEmpty candidate (by simp [member])
      simp only [flattenExecutables_cons, executablesEmpty, List.nil_append,
        inductionHypothesis tailEmpty]

end ControlSpineAgrees

/-- One logical task payload whose flattened control has arbitrarily many cut
regions.

Substitution shape and cumulative valuation occur exactly once.  The spine owns
only control certificates, so adding another recursive call cannot duplicate or
change the MGU proof. -/
structure TaskSpinePayloadAgrees
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase current : Substitution)
    (runtime : Metta.Subst) (segments : List ControlSegment) : Prop where
  data :
    TaskDataAgrees alpha support canonical referenceBase current runtime
  control : ControlSpineAgrees alpha segments

namespace TaskSpinePayloadAgrees

/-- A uniformly tagged task is the one-region base case. -/
theorem singleton
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      TaskPayloadAgrees alpha support barrier canonical referenceBase current
        runtime references executables) :
    TaskSpinePayloadAgrees alpha support canonical referenceBase current
      runtime
      [{ barrier := barrier
         references := references
         executables := executables }] :=
  ⟨agreement.data, .cons agreement.control .nil⟩

/-- The former two-region relation embeds exactly into the arbitrary spine. -/
theorem ofSegmented
    {alpha support : List (LogicVar × String)}
    {bodyBarrier callerBarrier : Nat}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {bodyReferences callerReferences :
      List PeTTaSpec.PrologCore.Goal}
    {bodyExecutables callerExecutables : List PLeaTTa.Goal}
    (agreement :
      SegmentedTaskPayloadAgrees alpha support bodyBarrier callerBarrier
        canonical referenceBase current runtime
        bodyReferences callerReferences bodyExecutables callerExecutables) :
    TaskSpinePayloadAgrees alpha support canonical referenceBase current
      runtime
      [{ barrier := bodyBarrier
         references := bodyReferences
         executables := bodyExecutables },
       { barrier := callerBarrier
         references := callerReferences
         executables := callerExecutables }] :=
  ⟨agreement.body.data,
    .cons agreement.body.control (.cons agreement.caller .nil)⟩

/-- Recover a conventional task payload for the active spine region. -/
theorem headPayload
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {segment : ControlSegment} {segments : List ControlSegment}
    (agreement :
      TaskSpinePayloadAgrees alpha support canonical referenceBase current
        runtime (segment :: segments)) :
    TaskPayloadAgrees alpha support segment.barrier canonical referenceBase
      current runtime segment.references segment.executables :=
  agreement.data.withControl agreement.control.head

/-- Completing the active region exposes the enclosing spine without changing
the shared substitution/valuation certificate. -/
theorem dropHead
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {segment : ControlSegment} {segments : List ControlSegment}
    (agreement :
      TaskSpinePayloadAgrees alpha support canonical referenceBase current
        runtime (segment :: segments)) :
    TaskSpinePayloadAgrees alpha support canonical referenceBase current
      runtime segments :=
  ⟨agreement.data, agreement.control.tail⟩

/-- Enter one more locally owned recursive predicate without retagging any
existing continuation region.

The call-headed active region is replaced by the new clause body followed by
the old region's residual tail.  Every still-older region is retained
pointwise.  The new body supplies the post-MGU data certificate; only the older
control certificates are weakened along the alpha extension. -/
theorem activateLocalCall
    {smaller larger support : List (LogicVar × String)}
    {oldCanonical newCanonical : TreeSubstitution}
    {referenceBase oldCurrent newCurrent : Substitution}
    {oldRuntime newRuntime : Metta.Subst}
    {predicate : String} {referencePayload : List Term}
    {referenceRest bodyReferences : List PeTTaSpec.PrologCore.Goal}
    {arguments : List Metta.Atom} {result : Metta.Atom}
    {executableRest bodyExecutables : List PLeaTTa.Goal}
    {callerBarrier bodyBarrier : Nat}
    {outer : List ControlSegment}
    (caller :
      TaskSpinePayloadAgrees smaller support oldCanonical referenceBase
        oldCurrent oldRuntime
        ({ barrier := callerBarrier
           references := .call predicate referencePayload :: referenceRest
           executables := .call predicate arguments result :: executableRest } ::
          outer))
    (body :
      TaskPayloadAgrees larger support bodyBarrier newCanonical referenceBase
        newCurrent newRuntime bodyReferences bodyExecutables)
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger) :
    TaskSpinePayloadAgrees larger support newCanonical referenceBase newCurrent
      newRuntime
      ({ barrier := bodyBarrier
         references := bodyReferences
         executables := bodyExecutables } ::
       { barrier := callerBarrier
         references := referenceRest
         executables := executableRest } ::
       outer) := by
  have callerHead := caller.control.head
  obtain
    ⟨_referenceArguments, _referenceResult, _payloadShape,
      _argumentAgreement, _resultAgreement, continuation⟩ :=
    PrologRecursiveCallPayloadBridge.NormalizedAlphaGoalsAgree.localCallHead
      callerHead
  exact
    ⟨body.data,
      .cons body.control
        (.cons (continuation.mono included)
          (caller.control.tail.mono included))⟩

/-- Flattening the spine produced by `activateLocalCall` exposes the callee
body first, then the current caller remainder, then every older caller
remainder in its stored order.  This equation prevents later consumers from
treating a pointwise-certified spine as permutation-invariant. -/
theorem flattenExecutables_activateLocalCall
    (bodyBarrier callerBarrier : Nat)
    (bodyReferences referenceRest : List PeTTaSpec.PrologCore.Goal)
    (bodyExecutables executableRest : List PLeaTTa.Goal)
    (outer : List ControlSegment) :
    flattenExecutables
      ({ barrier := bodyBarrier
         references := bodyReferences
         executables := bodyExecutables } ::
       { barrier := callerBarrier
         references := referenceRest
         executables := executableRest } ::
       outer) =
      bodyExecutables ++
        (executableRest ++ flattenExecutables outer) := by
  simp only [flattenExecutables_cons]

end TaskSpinePayloadAgrees

/-- A cut segment identifies its stored barrier exactly from its executable
spelling.  This is the per-region anti-retagging theorem used at arbitrary
spine depth. -/
theorem ControlSegment.cutBarrier_eq
    {alpha : List (LogicVar × String)} {segment : ControlSegment}
    {actualBarrier : Nat}
    (agreement : segment.Agrees alpha)
    (sourceCut : segment.references = [.cut])
    (executableCut : segment.executables = [.cutAt actualBarrier]) :
    segment.barrier = actualBarrier := by
  by_contra different
  exact
    PrologOrdinaryStepBridge.caller_cut_cannot_be_retagged alpha different
      (by simpa [ControlSegment.Agrees, sourceCut, executableCut] using agreement)

/-- Any cut-bearing member of a certified spine retains its own barrier,
regardless of how deeply it is nested. -/
theorem ControlSpineAgrees.member_cutBarrier_eq
    {alpha : List (LogicVar × String)}
    {segments : List ControlSegment} {segment : ControlSegment}
    {actualBarrier : Nat}
    (agreement : ControlSpineAgrees alpha segments)
    (present : segment ∈ segments)
    (sourceCut : segment.references = [.cut])
    (executableCut : segment.executables = [.cutAt actualBarrier]) :
    segment.barrier = actualBarrier :=
  ControlSegment.cutBarrier_eq (agreement.member present)
    sourceCut executableCut

/-- Canonical one-cut segment used by the anti-vacuity witnesses. -/
def cutSegment (barrier : Nat) : ControlSegment :=
  { barrier := barrier
    references := [.cut]
    executables := [.cutAt barrier] }

/-- Three nested predicate regions with three separately tagged cuts are
simultaneously inhabitable.  The spine is therefore not restricted to the old
body/caller pair. -/
theorem three_cut_regions_are_inhabited
    (alpha : List (LogicVar × String)) (inner middle outer : Nat) :
    ControlSpineAgrees alpha
      [cutSegment inner, cutSegment middle, cutSegment outer] := by
  exact
    .cons (.cons PrologGoalAlpha.AlphaGoalAgrees.cut .nil)
      (.cons (.cons PrologGoalAlpha.AlphaGoalAgrees.cut .nil)
        (.cons (.cons PrologGoalAlpha.AlphaGoalAgrees.cut .nil) .nil))

/-- Retagging the middle cut of a three-region spine is rejected even though
the inner and outer regions remain correctly tagged. -/
theorem wrong_middle_cut_region_is_rejected
    (alpha : List (LogicVar × String))
    {inner middle outer wrong : Nat} (different : wrong ≠ middle) :
    ¬ ControlSpineAgrees alpha
      [cutSegment inner,
       { barrier := wrong
         references := [.cut]
         executables := [.cutAt middle] },
       cutSegment outer] := by
  intro agreement
  have middleAgreement :=
    agreement.member
      (segment :=
        { barrier := wrong
          references := [.cut]
          executables := [.cutAt middle] })
      (by simp)
  exact different
    (ControlSegment.cutBarrier_eq middleAgreement (by rfl) (by rfl))

end PLeaTTa.PrologControlSegmentSpineBridge
