-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologScheduledPayloadOpenConfRegression
Purpose: Reject a stale enabled barrier cache after a selected scheduled
  payload crosses a nonempty prefix
Trusted boundary: none
-/
import PLeaTTa.Proofs.PrologScheduledPayloadOpenConfBridge

namespace PLeaTTa.PrologScheduledPayloadOpenConfRegression

open PeTTaSpec.PrologCore.GoalSemantics
open PLeaTTa.DemandDrivenStep
open PLeaTTa.PrologHeterogeneousPrefixBridge
open PLeaTTa.PrologPersistentFreeScheduledPayloadBridge
open PLeaTTa.PrologRootClosedAnswerBridge
open PLeaTTa.PrologScheduledPayloadLandingBridge
open PLeaTTa.PrologScheduledPayloadPostHeadBridge
open PLeaTTa.PrologScheduledPayloadOpenConfBridge

/-- Whenever the actual selected occurrence lies behind at least one empty
owned payload cell, inheriting the pre-answer enabled cache is observably
wrong.  The proof compares the real pre/post OpenConf fields, not just two
abstract barrier counts. -/
theorem nonempty_prefix_rejects_stale_cache
    {before : RepresentativePersistentFreeScheduledPayloadState}
    {ready : RootClosedAnswerReady before}
    {selection : ScheduledLocalSelection ready.result.historyBuild.cells}
    {scope : CutScopeId}
    (transition :
      ScheduledSelectedHeadTransition ready.payloadAlignment selection scope
        before.carrier.index.session)
    (cache : before.carrier.index.openConf.control.barriers =
      some (PLeaTTa.barrierCount
        before.carrier.index.openConf.control.alts))
    (earlierNonempty : selection.earlier ≠ []) :
    (privateAnswerTarget before.carrier.index.openConf
        before.carrier.index.runtime).control.barriers ≠
      before.carrier.index.openConf.control.barriers := by
  have postCache :=
    PLeaTTa.PrologScheduledPayloadOpenConfBridge.ScheduledSelectedHeadTransition.fineBarrierCacheExact
      transition cache
  have dropped :=
    PLeaTTa.PrologScheduledPayloadOpenConfBridge.ScheduledSelectedHeadTransition.fineBarrierCountDroppedExact
      transition
  have positive : 0 < selection.earlier.length := by
    cases cellsExact : selection.earlier with
    | nil => exact False.elim (earlierNonempty cellsExact)
    | cons head tail => simp
  have smaller :
      PLeaTTa.barrierCount
          (privateAnswerTarget before.carrier.index.openConf
            before.carrier.index.runtime).control.alts <
        PLeaTTa.barrierCount before.carrier.index.openConf.control.alts := by
    rw [dropped]
    omega
  intro stale
  rw [postCache, cache] at stale
  exact (Nat.ne_of_lt smaller) (Option.some.inj stale)

end PLeaTTa.PrologScheduledPayloadOpenConfRegression
