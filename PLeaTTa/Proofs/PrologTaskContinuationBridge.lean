-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologTaskContinuationBridge
Purpose: Extend an activated local-clause payload by the caller continuation
  flattened into the executable task spine.
Trusted boundary: none
Main exports:
  NormalizedAlphaGoalsAgree.mono,
  TaskPayloadAgrees.appendContinuation,
  SegmentedTaskPayloadAgrees
-/
import PLeaTTa.Proofs.PrologOrdinaryStepBridge
import PLeaTTa.Proofs.PrologRecursiveCallPayloadBridge

namespace PLeaTTa

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.OpenSubstitution
open PrologOrdinaryStepBridge
open PrologRecursiveCallPayloadBridge

namespace PrologOrdinaryStepBridge.NormalizedAlphaGoalsAgree

/-- Administrative-normalized goal agreement weakens along an alpha
inclusion without changing source structure, executable order, or the cut
barrier carried by any goal. -/
theorem mono
    {smaller larger : List (LogicVar × String)}
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    {barrier : Nat}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      NormalizedAlphaGoalsAgree smaller barrier references executables) :
    NormalizedAlphaGoalsAgree larger barrier references executables := by
  induction agreement with
  | nil =>
      exact .nil
  | truth tail inductionHypothesis =>
      exact .truth inductionHypothesis
  | cons head tail inductionHypothesis =>
      exact .cons
        (PLeaTTa.PrologGoalMguVariant.AlphaGoalAgrees.mono included head)
        inductionHypothesis
  | conjunction block tail blockIH tailIH =>
      exact .conjunction blockIH tailIH

end PrologOrdinaryStepBridge.NormalizedAlphaGoalsAgree

namespace PrologOrdinaryStepBridge.TaskPayloadAgrees

/-- Append a caller continuation to an activated task payload.

The cumulative valuation is a property of the carried source and executable
substitutions, not of one particular goal list, so it is retained exactly.
Only the control proof is extended: the older caller continuation is weakened
to the activated alpha and concatenated after the clause body.  This is the
certificate needed to compare Search's delayed `product` continuation with
the sealed machine's flattened `body ++ rest` task; it does not identify the
two control representations. -/
theorem appendContinuation
    {smaller larger support : List (LogicVar × String)}
    {barrier : Nat}
    {canonical : TreeSubstitution}
    {referenceBase current : Substitution}
    {runtime : Metta.Subst}
    {bodyReferences continuationReferences :
      List PeTTaSpec.PrologCore.Goal}
    {bodyExecutables continuationExecutables : List PLeaTTa.Goal}
    (body :
      TaskPayloadAgrees larger support barrier canonical referenceBase current
        runtime bodyReferences bodyExecutables)
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger)
    (continuation :
      NormalizedAlphaGoalsAgree smaller barrier
        continuationReferences continuationExecutables) :
    TaskPayloadAgrees larger support barrier canonical referenceBase current
      runtime
      (bodyReferences ++ continuationReferences)
      (bodyExecutables ++ continuationExecutables) :=
  ⟨body.alphaShared, body.canonicalWellFormed, body.bindingShape,
    body.control.append (continuation.mono included), body.valuation⟩

/-- Recover the caller continuation from the original output-last local call
and append it to the activated clause body.

The source search keeps this continuation outside the clause body in a
`product`; the sealed machine executes the flattened list.  This theorem
constructs only the shared payload certificate for that flattened list.  It
does not erase the source product boundary or its backtracking behavior. -/
theorem appendCallerContinuation
    {smaller larger support : List (LogicVar × String)}
    {barrier : Nat}
    {oldCanonical newCanonical : TreeSubstitution}
    {referenceBase oldCurrent newCurrent : Substitution}
    {oldRuntime newRuntime : Metta.Subst}
    {predicate : String} {referencePayload : List Term}
    {referenceRest bodyReferences : List PeTTaSpec.PrologCore.Goal}
    {arguments : List Metta.Atom} {result : Metta.Atom}
    {executableRest bodyExecutables : List PLeaTTa.Goal}
    (caller :
      TaskPayloadAgrees smaller support barrier oldCanonical referenceBase
        oldCurrent oldRuntime
        (.call predicate referencePayload :: referenceRest)
        (.call predicate arguments result :: executableRest))
    (body :
      TaskPayloadAgrees larger support barrier newCanonical referenceBase
        newCurrent newRuntime bodyReferences bodyExecutables)
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger) :
    TaskPayloadAgrees larger support barrier newCanonical referenceBase
      newCurrent newRuntime
      (bodyReferences ++ referenceRest)
      (bodyExecutables ++ executableRest) := by
  obtain
    ⟨_referenceArguments, _referenceResult, _payloadShape,
      _argumentAgreement, _resultAgreement, continuation⟩ :=
    NormalizedAlphaGoalsAgree.localCallHead caller.control
  exact body.appendContinuation included continuation

end PrologOrdinaryStepBridge.TaskPayloadAgrees

namespace PrologOrdinaryStepBridge

/-- One flattened executable task whose source control has two distinct cut
regions.

The selected clause body runs at `bodyBarrier`; the caller continuation,
which the sealed machine stores immediately after that body, remains tagged
at `callerBarrier`.  The shared substitution/valuation facts live in
`body`; only the caller's control certificate is separate.  Thus the type
cannot silently retag caller cuts as callee cuts. -/
structure SegmentedTaskPayloadAgrees
    (alpha support : List (LogicVar × String))
    (bodyBarrier callerBarrier : Nat)
    (canonical : TreeSubstitution) (referenceBase current : Substitution)
    (runtime : Metta.Subst)
    (bodyReferences callerReferences :
      List PeTTaSpec.PrologCore.Goal)
    (bodyExecutables callerExecutables : List PLeaTTa.Goal) : Prop where
  body :
    TaskPayloadAgrees alpha support bodyBarrier canonical referenceBase
      current runtime bodyReferences bodyExecutables
  caller :
    NormalizedAlphaGoalsAgree alpha callerBarrier
      callerReferences callerExecutables

namespace SegmentedTaskPayloadAgrees

/-- Split an activated clause body from the original caller continuation.
Alpha extension is permitted, but each control segment retains its own cut
barrier. -/
theorem ofCallerAndBody
    {smaller larger support : List (LogicVar × String)}
    {bodyBarrier callerBarrier : Nat}
    {oldCanonical newCanonical : TreeSubstitution}
    {referenceBase oldCurrent newCurrent : Substitution}
    {oldRuntime newRuntime : Metta.Subst}
    {predicate : String} {referencePayload : List Term}
    {referenceRest bodyReferences : List PeTTaSpec.PrologCore.Goal}
    {arguments : List Metta.Atom} {result : Metta.Atom}
    {executableRest bodyExecutables : List PLeaTTa.Goal}
    (caller :
      TaskPayloadAgrees smaller support callerBarrier oldCanonical
        referenceBase oldCurrent oldRuntime
        (.call predicate referencePayload :: referenceRest)
        (.call predicate arguments result :: executableRest))
    (body :
      TaskPayloadAgrees larger support bodyBarrier newCanonical referenceBase
        newCurrent newRuntime bodyReferences bodyExecutables)
    (included : ∀ pair, pair ∈ smaller → pair ∈ larger) :
    SegmentedTaskPayloadAgrees larger support bodyBarrier callerBarrier
      newCanonical referenceBase newCurrent newRuntime
      bodyReferences referenceRest bodyExecutables executableRest := by
  obtain
    ⟨_referenceArguments, _referenceResult, _payloadShape,
      _argumentAgreement, _resultAgreement, continuation⟩ :=
    NormalizedAlphaGoalsAgree.localCallHead caller.control
  exact ⟨body, continuation.mono included⟩

/-- Once a clause body has completed, its shared valuation facts and the
separately retained caller control form the exact caller task payload. -/
theorem callerPayload
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
    TaskPayloadAgrees alpha support callerBarrier canonical referenceBase
      current runtime callerReferences callerExecutables :=
  ⟨agreement.body.alphaShared, agreement.body.canonicalWellFormed,
    agreement.body.bindingShape, agreement.caller,
    agreement.body.valuation⟩

/-- Equal barriers recover the former uniformly tagged flattened payload.
The equality is explicit: this compatibility theorem cannot be used on a
genuine recursive call whose callee allocated a fresh barrier. -/
theorem flatten_of_eq
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
        bodyReferences callerReferences bodyExecutables callerExecutables)
    (same : bodyBarrier = callerBarrier) :
    TaskPayloadAgrees alpha support bodyBarrier canonical referenceBase
      current runtime
      (bodyReferences ++ callerReferences)
      (bodyExecutables ++ callerExecutables) := by
  subst callerBarrier
  exact
    agreement.body.appendContinuation
      (fun _pair member => member) agreement.caller

end SegmentedTaskPayloadAgrees

/-- A caller cut tagged at its own barrier cannot be laundered into a
distinct callee barrier by normalized task agreement. -/
theorem caller_cut_cannot_be_retagged
    (alpha : List (LogicVar × String))
    {calleeBarrier callerBarrier : Nat}
    (different : calleeBarrier ≠ callerBarrier) :
    ¬ NormalizedAlphaGoalsAgree alpha calleeBarrier
      [.cut] [.cutAt callerBarrier] := by
  intro agreement
  cases agreement with
  | cons head tail =>
      exact
        PLeaTTa.PrologGoalAlpha.wrong_alpha_cut_barrier_is_rejected
          alpha different head

/-- The negative retagging witness is non-vacuous: body and caller cuts are
each admitted at their own barrier, even when those barriers differ. -/
theorem distinct_cut_segments_are_inhabited
    (alpha : List (LogicVar × String))
    (bodyBarrier callerBarrier : Nat) :
    NormalizedAlphaGoalsAgree alpha bodyBarrier
        [.cut] [.cutAt bodyBarrier] ∧
      NormalizedAlphaGoalsAgree alpha callerBarrier
        [.cut] [.cutAt callerBarrier] := by
  exact
    ⟨.cons PLeaTTa.PrologGoalAlpha.AlphaGoalAgrees.cut .nil,
      .cons PLeaTTa.PrologGoalAlpha.AlphaGoalAgrees.cut .nil⟩

end PrologOrdinaryStepBridge

end PLeaTTa
