-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologRepresentativeProductActivationBridge
Purpose: Relate one retained semantic clause activation under its real
  product/cut wrappers to the sealed flattened clause-body successor.
Trusted boundary: none
Main exports:
  RepresentativeProductActivation,
  RepresentativeRetainedCallFrontier.activate_product_step
-/
import PLeaTTa.Proofs.PrologRepresentativeStepActivationBridge
import PLeaTTa.Proofs.PrologTaskContinuationBridge

namespace PLeaTTa.PrologRepresentativeProductActivationBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologAlphaFreshFrontierBridge
open PrologMguBridge
open PrologMguComposition
open PrologOrdinaryStepBridge
open PrologRecursiveCallPayloadBridge
open PrologRepresentativeCallFrontierBridge
open PrologRepresentativeStepActivationBridge
open PrologStateBridge

/-! ## Structural source states -/

/-- The source control state immediately before a retained clause is pulled.
The caller tail is outside the predicate cut boundary, hence cannot be
pruned by a cut inside the selected clause. -/
def sourceProductFrontier
    (callerScope : CutScopeId) (opened : OpenedCall)
    (finish : PreparedCursor)
    (referenceRest : List PeTTaSpec.PrologCore.Goal) : Search :=
  .product callerScope
    (.cutBoundary opened.scope (.clauses opened.scope finish))
    referenceRest

/-- The source control state immediately after a retained clause is pulled.
The selected body is the left branch and the remaining immutable cursor is
the right branch at the predicate scope; this is the structure that lets a
clause-local cut prune later clauses. -/
def activatedSourceProduct
    (callerScope : CutScopeId) (opened : OpenedCall)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (independentResult : Substitution)
    (referenceRest : List PeTTaSpec.PrologCore.Goal) : Search :=
  .product callerScope
    (.cutBoundary opened.scope
      (.choice opened.scope
        (.task opened.scope branch.body independentResult)
        (.clauses opened.scope (finish.advance branch branchTail))))
    referenceRest

/-! ## Exact paired activation package -/

/-- Exact product-level relation established by one retained clause
activation.

The source keeps the caller continuation in `product`; the executable
successor flattens it after the copied clause body.  `flattenedPayload`
certifies the common logical payload without identifying those different
control representations.  The retained executable alternatives are kept
explicit so later cut/backtracking correspondence cannot forget them. -/
structure RepresentativeProductActivation
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (opened : OpenedCall) (pending : DemandDrivenCallStep.PendingCall)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (altTail : List PLeaTTa.Alt)
    (copied : PLeaTTa.Clause)
    (referenceRest : List PeTTaSpec.PrologCore.Goal)
    (executableRest : List PLeaTTa.Goal)
    (qterm : Atom) (barrier : Nat) (callerScope : CutScopeId)
    (independentResult : Substitution)
    (representative : TreeSubstitution)
    (nextAlpha : List (LogicVar × String))
    (sourceCanonical flattenedRepresentative : TreeSubstitution)
    (installed : Subst) : Prop where
  nextShared : SharedRuntimeAlpha nextAlpha
  alphaIncluded : ∀ pair, pair ∈ alpha → pair ∈ nextAlpha
  freshFrontier :
    AlphaFreshFrontier nextAlpha branch.nextFresh pending.persistent.counter
  persistentAgreement :
    SessionRelatesPersistent (AlphaFreshFrontier nextAlpha)
      opened.session pending.persistent
  independentShape :
    independentResult =
      TreeSubstitution.reify (sourceCanonical ++ canonical) ++ referenceBase
  sourceOrdered :
    OrderedTreeMgu
      (denoteEquations branch.normalizedHeadEquations) sourceCanonical
  sourceStep :
    RawStep opened.session
      (sourceProductFrontier callerScope opened finish referenceRest)
      [] .none opened.session
      (.running
        (activatedSourceProduct callerScope opened finish branch branchTail
          independentResult referenceRest))
  executableStep :
    PLeaTTa.Step prog gt pending.pulled.toConf
      (activatedExecutableSuccessor pending copied executableRest qterm
        installed)
  fineExecutableStep :
    DemandDrivenCallStep.Step prog gt (.ready pending.pulled)
      (.ready
        (activatedOpenSuccessor pending copied executableRest qterm installed))
  cumulative :
    AlphaCumulativeResidualVariantAgreesOnWith
      nextAlpha support (sourceCanonical ++ canonical) referenceBase
      (PLeaTTa.trimFor (copied.body ++ executableRest) qterm installed)
      (flattenedRepresentative ++ representative)
  bodyPayload :
    TaskPayloadAgrees nextAlpha support barrier
      (sourceCanonical ++ canonical) referenceBase independentResult
      (PLeaTTa.trimFor (copied.body ++ executableRest) qterm installed)
      branch.body copied.body
  flattenedPayload :
    TaskPayloadAgrees nextAlpha support barrier
      (sourceCanonical ++ canonical) referenceBase independentResult
      (PLeaTTa.trimFor (copied.body ++ executableRest) qterm installed)
      (branch.body ++ referenceRest) (copied.body ++ executableRest)
  retainedAlts :
    (activatedExecutableSuccessor pending copied executableRest qterm
      installed).alts =
      altTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts
  worldPreserved :
    (activatedExecutableSuccessor pending copied executableRest qterm
      installed).world =
      pending.persistent.world
  counterPreserved :
    (activatedExecutableSuccessor pending copied executableRest qterm
      installed).counter =
      pending.persistent.counter

/-- The activated fine state carries the pending call's persistent component
exactly; only its backtrackable control is replaced by the clause body. -/
theorem RepresentativeProductActivation.activatedPersistent_eq
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {copied : PLeaTTa.Clause}
    {referenceRest : List PeTTaSpec.PrologCore.Goal}
    {executableRest : List PLeaTTa.Goal}
    {qterm : Atom} {barrier : Nat} {callerScope : CutScopeId}
    {independentResult : Substitution}
    {representative : TreeSubstitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattenedRepresentative : TreeSubstitution}
    {installed : Subst}
    (activation :
      RepresentativeProductActivation prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        referenceRest executableRest qterm barrier callerScope
        independentResult representative nextAlpha sourceCanonical
        flattenedRepresentative installed) :
    (activatedOpenSuccessor pending copied executableRest qterm
      installed).persistent =
      pending.persistent := by
  unfold activatedOpenSuccessor DemandDrivenStep.OpenConf.ofConf
    DemandDrivenStep.persistentOf
  rw [activation.worldPreserved, activation.counterPreserved]

/-- The persistent state relation established at activation is a relation to
the actual fine executable successor, not merely to an auxiliary pending
package. -/
theorem RepresentativeProductActivation.activatedSessionRelates
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {copied : PLeaTTa.Clause}
    {referenceRest : List PeTTaSpec.PrologCore.Goal}
    {executableRest : List PLeaTTa.Goal}
    {qterm : Atom} {barrier : Nat} {callerScope : CutScopeId}
    {independentResult : Substitution}
    {representative : TreeSubstitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattenedRepresentative : TreeSubstitution}
    {installed : Subst}
    (activation :
      RepresentativeProductActivation prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        referenceRest executableRest qterm barrier callerScope
        independentResult representative nextAlpha sourceCanonical
        flattenedRepresentative installed) :
    SessionRelatesPersistent (AlphaFreshFrontier nextAlpha) opened.session
      (activatedOpenSuccessor pending copied executableRest qterm
        installed).persistent := by
  rw [activation.activatedPersistent_eq]
  exact activation.persistentAgreement

/-! ## Construction from the actual frontier -/

/-- One actual retained semantic clause and the corresponding sealed
full-head equality step construct the exact product-level activation package.

This theorem adds no semantic premises beyond the existing retained
activation theorem.  The original call payload supplies the exact caller
tail; alpha inclusion weakens that control proof to the post-head alpha; and
the independent `clausesPull` is lifted through the real cut and product
wrappers with no observations. -/
theorem RepresentativeRetainedCallFrontier.activate_product_step
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {referenceBindings : Substitution}
    {opened : OpenedCall} {before : DemandDrivenStep.OpenConf}
    {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    {branchTail : List ClauseBranch} {clauseTail : List PLeaTTa.Clause}
    {altTail : List PLeaTTa.Alt} {copied : PLeaTTa.Clause}
    {referencePayload : List Term}
    {referenceRest : List PeTTaSpec.PrologCore.Goal}
    {argsv args : List Atom} {res : Atom}
    {executableRest : List PLeaTTa.Goal} {binding : Subst}
    {qterm : Atom} {barrier startCounter : Nat}
    {callerScope : CutScopeId}
    {independentResult : Substitution}
    (entry :
      RepresentativeSupportedCallEntryRelates alpha opened before pending
        argsv args res executableRest binding qterm barrier startCounter)
    (frontier :
      RepresentativeRetainedCallFrontier alpha opened before pending finish
        branch clause branchTail clauseTail altTail copied argsv args res
        executableRest binding qterm barrier startCounter)
    (payload :
      TaskPayloadAgrees alpha support barrier canonical referenceBase
        referenceBindings binding
        (.call opened.cursor.predicate referencePayload :: referenceRest)
        (.call opened.cursor.predicate args res :: executableRest))
    (payloadSupported :
      AlphaTermsSupported alpha support referencePayload)
    (openedArguments : opened.cursor.arguments = referencePayload)
    (openedBindings : opened.cursor.bindings = referenceBindings)
    (queryReferenceBelow :
      GeneratedBelow finish.reservationStart (alpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ alpha.map Prod.snd →
        name ∈
          resolutionOccupiedVars
            (args.map (PLeaTTa.subst binding)) res executableRest binding qterm)
    (live :
      AlphaRuntimeNamesLive support (copied.body ++ executableRest) qterm)
    (resolved : HeadResolution branch independentResult) :
    ∃ representative nextAlpha sourceCanonical flattenedRepresentative
        installed,
      RepresentativeProductActivation prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        referenceRest executableRest qterm barrier callerScope
        independentResult representative nextAlpha sourceCanonical
        flattenedRepresentative installed := by
  obtain
    ⟨representative, nextAlpha, sourceCanonical, flattened, installed,
      nextShared, alphaIncluded, selectionFresh, independentShape,
      sourceOrdered, sourceInnerStep, executableStep, cumulative, bodyPayload,
      retainedAlts, worldPreserved, counterPreserved⟩ :=
    PLeaTTa.PrologRepresentativeStepActivationBridge.RepresentativeRetainedCallFrontier.activate_task_step
      entry frontier payload payloadSupported openedArguments openedBindings
      queryReferenceBelow queryExecutableLive live resolved
  have normalizedSourceInnerStep :
      RawStep opened.session (.clauses opened.scope finish) [] .none
        opened.session
        (.running
          (.choice opened.scope
            (.task opened.scope branch.body independentResult)
            (.clauses opened.scope
              (finish.advance branch branchTail)))) := by
    simpa [ClauseBranch.enter] using sourceInnerStep
  have sourceCutStep :
      RawStep opened.session
        (.cutBoundary opened.scope (.clauses opened.scope finish))
        [] .none opened.session
        (.running
          (.cutBoundary opened.scope
            (.choice opened.scope
              (.task opened.scope branch.body independentResult)
              (.clauses opened.scope
                (finish.advance branch branchTail))))) :=
    .cutBoundaryProgress opened.scope _ _ [] opened.session opened.session
      normalizedSourceInnerStep
  have sourceProductStep :
      RawStep opened.session
        (sourceProductFrontier callerScope opened finish referenceRest)
        [] .none opened.session
        (.running
          (activatedSourceProduct callerScope opened finish branch branchTail
            independentResult referenceRest)) := by
    exact
      .productProgress callerScope _ _ referenceRest [] .none
        opened.session opened.session sourceCutStep (by simp [Trace.AnswerFree])
  have flattenedPayload :
      TaskPayloadAgrees nextAlpha support barrier
        (sourceCanonical ++ canonical) referenceBase independentResult
        (PLeaTTa.trimFor (copied.body ++ executableRest) qterm installed)
        (branch.body ++ referenceRest) (copied.body ++ executableRest) :=
    PrologOrdinaryStepBridge.TaskPayloadAgrees.appendCallerContinuation
      payload bodyPayload alphaIncluded
  have pulledHead :
      pending.pulled.toConf.cur =
        some
          (PLeaTTa.Goal.eq (.expr (args ++ [res]))
              (.expr (copied.params ++ [copied.result])) ::
            copied.body ++ executableRest,
            binding) := by
    rw [frontier.pulledExact]
  have notFindall : ¬ findallRunHead pending.pulled.toConf := by
    simp [findallRunHead, pulledHead]
  have notLocalCall :
      ¬ DemandDrivenCallStep.LocalResolveHead pending.pulled := by
    simp [DemandDrivenCallStep.LocalResolveHead, pulledHead]
  have openExecutableStep :
      DemandDrivenStep.Step prog gt pending.pulled
        (activatedOpenSuccessor pending copied executableRest qterm
          installed) := by
    have lifted :=
      DemandDrivenStep.Step.ordinary pending.pulled
        (activatedExecutableSuccessor pending copied executableRest qterm
          installed)
        notFindall executableStep
    simpa [activatedOpenSuccessor, DemandDrivenCallStep.PendingCall.pulled]
      using lifted
  have fineExecutableStep :
      DemandDrivenCallStep.Step prog gt (.ready pending.pulled)
        (.ready
          (activatedOpenSuccessor pending copied executableRest qterm
            installed)) :=
    .ordinary pending.pulled
      (activatedOpenSuccessor pending copied executableRest qterm installed)
      notLocalCall openExecutableStep
  have executableFrontierMono :
      startCounter + 1 ≤ pending.persistent.counter := by
    have exactCounter := frontier.tailScan.counter_exact
    omega
  have freshFrontier :
      AlphaFreshFrontier nextAlpha branch.nextFresh
        pending.persistent.counter :=
    selectionFresh.mono (Nat.le_refl _) executableFrontierMono
  have branchMember : branch ∈ finish.remaining := by
    rw [frontier.finishRemaining]
    simp
  have branchBelowFinish :
      branch.nextFresh ≤ finish.reservedUntil :=
    frontier.finishWellFormed.1.member_next_le_final branchMember
  have branchBelowSession :
      branch.nextFresh ≤ opened.session.resolver.nextFresh := by
    rw [entry.entry.sourceFresh]
    exact Nat.le_trans branchBelowFinish
      (Nat.le_of_eq frontier.finishReservedUntil)
  have persistentAgreement :
      SessionRelatesPersistent (AlphaFreshFrontier nextAlpha)
        opened.session pending.persistent :=
    ⟨entry.entry.database,
      freshFrontier.mono branchBelowSession (Nat.le_refl _)⟩
  refine
    ⟨representative, nextAlpha, sourceCanonical, flattened, installed, ?_⟩
  exact
    ⟨nextShared, alphaIncluded, freshFrontier, persistentAgreement,
      independentShape, sourceOrdered,
      sourceProductStep, executableStep, fineExecutableStep, cumulative,
      bodyPayload,
      flattenedPayload, retainedAlts, worldPreserved, counterPreserved⟩

end PLeaTTa.PrologRepresentativeProductActivationBridge
