-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologRepresentativeProductActivationBridge
Purpose: Relate one retained semantic clause activation under its real
  product/cut wrappers to the sealed flattened clause-body successor.
Trusted boundary: none
Main exports:
  RepresentativeProductActivation,
  SegmentedRepresentativeProductActivation,
  SpinedRepresentativeProductActivation,
  RepresentativeRetainedCallFrontier.activate_product_step_head_with,
  RepresentativeRetainedCallFrontier.activate_spined_product_step_with,
  RepresentativeRetainedCallFrontier.activate_spined_product_step,
  RepresentativeRetainedCallFrontier.activate_segmented_product_step,
  RepresentativeRetainedCallFrontier.activate_product_step
-/
import PLeaTTa.Proofs.PrologRepresentativeStepActivationBridge
import PLeaTTa.Proofs.PrologRetainedCursorOwnershipBridge
import PLeaTTa.Proofs.PrologControlSegmentSpineBridge

namespace PLeaTTa.PrologRepresentativeProductActivationBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologAlphaFreshFrontierBridge
open PrologControlSegmentSpineBridge
open PrologMguBridge
open PrologMguComposition
open PrologOrdinaryStepBridge
open PrologRecursiveCallPayloadBridge
open PrologRepresentativeCallFrontierBridge
open PrologRetainedCursorOwnershipBridge
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

/-- One pulled executable head carries the generated-MGU certificate for the
literal equality goal that is about to run.

The logical payload remains existential because `PendingCall` deliberately
owns only control/resources.  The equality with `pending.pulled.cur` prevents
the existential from describing a different call. -/
def PendingHeadMguAgrees
    (alpha : List (LogicVar × String))
    (flattenedRepresentative : TreeSubstitution) (installed : Subst)
    (pending : DemandDrivenCallStep.PendingCall) (copied : PLeaTTa.Clause)
    (executableRest : List PLeaTTa.Goal) : Prop :=
  ∃ base args result,
    pending.pulled.toConf.cur =
      some
        (PLeaTTa.Goal.eq (.expr (args ++ [result]))
            (.expr (copied.params ++ [copied.result])) ::
          copied.body ++ executableRest,
          base) ∧
    ActivatedHeadMguAgrees alpha flattenedRepresentative base installed args
      result copied

/-! ## Exact paired activation packages -/

/-- Shared semantic, executable, and ownership facts established by one
retained clause activation.

This core deliberately stops before relating the flattened executable tail:
that tail may be uniformly tagged only in the degenerate same-barrier case,
whereas a genuine recursive call has a callee body and caller continuation
at distinct cut barriers. -/
structure RepresentativeProductActivationCore
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (opened : OpenedCall) (pending : DemandDrivenCallStep.PendingCall)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (altTail : List PLeaTTa.Alt)
    (copied : PLeaTTa.Clause)
    (referenceRest : List PeTTaSpec.PrologCore.Goal)
    (executableRest : List PLeaTTa.Goal)
    (qterm : Atom) (barrier startCounter : Nat)
    (callerScope : CutScopeId)
    (independentResult : Substitution)
    (representative : TreeSubstitution)
    (nextAlpha : List (LogicVar × String))
    (sourceCanonical flattenedRepresentative : TreeSubstitution)
    (installed : Subst) : Prop where
  nextShared : SharedRuntimeAlpha nextAlpha
  alphaIncluded : ∀ pair, pair ∈ alpha → pair ∈ nextAlpha
  alphaExtension :
    AlphaExtendsAbove alpha nextAlpha branch.firstFresh startCounter
  freshFrontier :
    AlphaFreshFrontier nextAlpha branch.nextFresh pending.persistent.counter
  /-- Tight frontier of the selected clause itself, before widening to the
  complete prefiltered alternative bank.  Retained-payload chronology uses
  this to place every installed alpha entry below the advanced resource's
  new lower bounds. -/
  selectionFresh :
    AlphaFreshFrontier nextAlpha branch.nextFresh (startCounter + 1)
  persistentAgreement :
    SessionRelatesPersistent (AlphaFreshFrontier nextAlpha)
      opened.session pending.persistent
  independentShape :
    independentResult =
      TreeSubstitution.reify (sourceCanonical ++ canonical) ++ referenceBase
  sourceOrdered :
    OrderedTreeMgu
      (denoteEquations branch.normalizedHeadEquations) sourceCanonical
  headMgu :
    PendingHeadMguAgrees nextAlpha flattenedRepresentative installed pending
      copied executableRest
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
  materializedBodyHeads :
    MaterializedLocalCallHeadsAgreeWith nextAlpha independentResult branch.body
      copied.body
      (PLeaTTa.trimFor (copied.body ++ executableRest) qterm installed)
      (flattenedRepresentative ++ representative) referenceBase
  retainedAlts :
    (activatedExecutableSuccessor pending copied executableRest qterm
      installed).alts =
      altTail ++ PLeaTTa.Alt.barrier :: pending.outer.alts
  retainedCursorOwnership :
    PendingRetainedCursorAlternativeOwnership alpha pending
      (finish.advance branch branchTail) executableRest qterm barrier altTail
  retainedAltsZero : PLeaTTa.barrierCount altTail = 0
  retainedBarriers :
    (activatedExecutableSuccessor pending copied executableRest qterm
      installed).barriers =
      PLeaTTa.pushBarrierCache pending.outer.barriers
  barrierTag :
    barrier =
      pending.outer.barriers.getD
        (PLeaTTa.barrierCount pending.outer.alts) + 1
  worldPreserved :
    (activatedExecutableSuccessor pending copied executableRest qterm
      installed).world =
      pending.persistent.world
  counterPreserved :
    (activatedExecutableSuccessor pending copied executableRest qterm
      installed).counter =
      pending.persistent.counter

/-- Compatibility package for the old same-barrier flattened control
relation.  It remains useful for cut-free or deliberately uniform fragments,
but the stronger segmented package below is the general recursive-call
interface. -/
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
    (qterm : Atom) (barrier startCounter : Nat)
    (callerScope : CutScopeId)
    (independentResult : Substitution)
    (representative : TreeSubstitution)
    (nextAlpha : List (LogicVar × String))
    (sourceCanonical flattenedRepresentative : TreeSubstitution)
    (installed : Subst) : Prop
    extends
      RepresentativeProductActivationCore prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        referenceRest executableRest qterm barrier startCounter callerScope
        independentResult representative nextAlpha sourceCanonical
        flattenedRepresentative installed where
  flattenedPayload :
    TaskPayloadAgrees nextAlpha support barrier
      (sourceCanonical ++ canonical) referenceBase independentResult
      (PLeaTTa.trimFor (copied.body ++ executableRest) qterm installed)
      (branch.body ++ referenceRest) (copied.body ++ executableRest)

/-- General recursive-call package: the selected body and caller tail retain
their distinct cut barriers while sharing the exact same logical payload. -/
structure SegmentedRepresentativeProductActivation
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (opened : OpenedCall) (pending : DemandDrivenCallStep.PendingCall)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (altTail : List PLeaTTa.Alt)
    (copied : PLeaTTa.Clause)
    (referenceRest : List PeTTaSpec.PrologCore.Goal)
    (executableRest : List PLeaTTa.Goal)
    (qterm : Atom) (bodyBarrier callerBarrier startCounter : Nat)
    (callerScope : CutScopeId)
    (independentResult : Substitution)
    (representative : TreeSubstitution)
    (nextAlpha : List (LogicVar × String))
    (sourceCanonical flattenedRepresentative : TreeSubstitution)
    (installed : Subst) : Prop
    extends
      RepresentativeProductActivationCore prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        referenceRest executableRest qterm bodyBarrier startCounter callerScope
        independentResult representative nextAlpha sourceCanonical
        flattenedRepresentative installed where
  segmentedPayload :
    SegmentedTaskPayloadAgrees nextAlpha support bodyBarrier callerBarrier
      (sourceCanonical ++ canonical) referenceBase independentResult
      (PLeaTTa.trimFor (copied.body ++ executableRest) qterm installed)
      branch.body referenceRest copied.body executableRest

/-- Arbitrary-depth recursive-call package.

The independent source product owns only the current caller segment, while the
sealed executable tail is that segment followed by every older region
flattened in execution order.  Each region retains its own cut barrier in
`spinePayload`; the MGU and resource facts remain shared through the inherited
activation core. -/
structure SpinedRepresentativeProductActivation
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (opened : OpenedCall) (pending : DemandDrivenCallStep.PendingCall)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (altTail : List PLeaTTa.Alt)
    (copied : PLeaTTa.Clause)
    (segmentReferenceRest : List PeTTaSpec.PrologCore.Goal)
    (segmentExecutableRest : List PLeaTTa.Goal)
    (outer : List ControlSegment)
    (qterm : Atom) (bodyBarrier callerBarrier startCounter : Nat)
    (callerScope : CutScopeId)
    (independentResult : Substitution)
    (representative : TreeSubstitution)
    (nextAlpha : List (LogicVar × String))
    (sourceCanonical flattenedRepresentative : TreeSubstitution)
    (installed : Subst) : Prop
    extends
      RepresentativeProductActivationCore prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        segmentReferenceRest
        (segmentExecutableRest ++ flattenExecutables outer)
        qterm bodyBarrier startCounter callerScope independentResult
        representative nextAlpha sourceCanonical flattenedRepresentative
        installed where
  spinePayload :
    TaskSpinePayloadAgrees nextAlpha support
      (sourceCanonical ++ canonical) referenceBase independentResult
      (PLeaTTa.trimFor
        (copied.body ++
          (segmentExecutableRest ++ flattenExecutables outer))
        qterm installed)
      ({ barrier := bodyBarrier
         references := branch.body
         executables := copied.body } ::
       { barrier := callerBarrier
         references := segmentReferenceRest
         executables := segmentExecutableRest } ::
       outer)

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
    {qterm : Atom} {barrier startCounter : Nat}
    {callerScope : CutScopeId}
    {independentResult : Substitution}
    {representative : TreeSubstitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattenedRepresentative : TreeSubstitution}
    {installed : Subst}
    (activation :
      RepresentativeProductActivation prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        referenceRest executableRest qterm barrier startCounter callerScope
        independentResult representative nextAlpha sourceCanonical
        flattenedRepresentative installed) :
    (activatedOpenSuccessor pending copied executableRest qterm
      installed).persistent =
      pending.persistent := by
  unfold activatedOpenSuccessor DemandDrivenStep.OpenConf.stepOpen
    DemandDrivenStep.OpenConf.ofConfWith DemandDrivenStep.persistentOf
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
    {qterm : Atom} {barrier startCounter : Nat}
    {callerScope : CutScopeId}
    {independentResult : Substitution}
    {representative : TreeSubstitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattenedRepresentative : TreeSubstitution}
    {installed : Subst}
    (activation :
      RepresentativeProductActivation prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        referenceRest executableRest qterm barrier startCounter callerScope
        independentResult representative nextAlpha sourceCanonical
        flattenedRepresentative installed) :
    SessionRelatesPersistent (AlphaFreshFrontier nextAlpha) opened.session
      (activatedOpenSuccessor pending copied executableRest qterm
        installed).persistent := by
  rw [activation.activatedPersistent_eq]
  exact activation.persistentAgreement

/-! ## Construction from the actual frontier -/

/-- One actual retained semantic clause and the corresponding sealed
full-head equality step construct the control-independent product activation
core.

Only the local-call head and shared task data are consumed.  The caller tail's
control segmentation is deliberately absent: clause selection, ordered MGU
installation, resource ownership, and the local source `product` step do not
depend on how many older predicate regions the sealed task flattened after the
call. -/
theorem RepresentativeRetainedCallFrontier.activate_product_step_head_with
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {alpha support : List (LogicVar × String)}
    {canonical representative : TreeSubstitution}
    {referenceBase : Substitution}
    {opened : OpenedCall} {before : DemandDrivenStep.OpenConf}
    {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor}
    {branch : ClauseBranch} {clause : PLeaTTa.Clause}
    {branchTail : List ClauseBranch} {clauseTail : List PLeaTTa.Clause}
    {altTail : List PLeaTTa.Alt} {copied : PLeaTTa.Clause}
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
    (oldCumulative :
      AlphaCumulativeResidualVariantAgreesOnWith
        alpha support canonical referenceBase binding representative)
    (queryAtOpen :
      RepresentativeNormalizedCallAgreesWith alpha opened.cursor
        (args.map (PLeaTTa.subst binding))
        (PLeaTTa.subst binding res) representative referenceBase)
    (openedBindingShape :
      opened.cursor.bindings =
        TreeSubstitution.reify canonical ++ referenceBase)
    (canonicalWellFormed : canonical.WellFormed)
    (alphaShared : SharedRuntimeAlpha alpha)
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
    ∃ nextAlpha sourceCanonical flattenedRepresentative installed,
      RepresentativeProductActivationCore prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        referenceRest executableRest qterm barrier startCounter callerScope
        independentResult representative nextAlpha sourceCanonical
        flattenedRepresentative installed := by
  obtain
    ⟨nextAlpha, sourceCanonical, flattened, installed,
      nextShared, alphaIncluded, alphaExtension, selectionFresh,
      independentShape,
      sourceOrdered, headMgu, sourceInnerStep, executableStep, cumulative,
      bodyPayload, materializedBodyHeads, retainedAlts, worldPreserved,
      counterPreserved⟩ :=
    PLeaTTa.PrologRepresentativeStepActivationBridge.RepresentativeRetainedCallFrontier.activate_task_step_head_with
      entry frontier oldCumulative queryAtOpen openedBindingShape
      canonicalWellFormed alphaShared
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
  have pulledHead :
      pending.pulled.toConf.cur =
        some
          (PLeaTTa.Goal.eq (.expr (args ++ [res]))
              (.expr (copied.params ++ [copied.result])) ::
            copied.body ++ executableRest,
            binding) := by
    rw [frontier.pulledExact]
  have pendingHeadMgu :
      PendingHeadMguAgrees nextAlpha flattened installed pending copied
        executableRest :=
    ⟨binding, args, res, pulledHead, headMgu⟩
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
  have retainedBarriers :
      (activatedExecutableSuccessor pending copied executableRest qterm
        installed).barriers =
        PLeaTTa.pushBarrierCache pending.outer.barriers := by
    rw [activatedExecutableSuccessor_barriers, frontier.pulledExact]
    rfl
  have barrierTag :
      barrier =
        pending.outer.barriers.getD
          (PLeaTTa.barrierCount pending.outer.alts) + 1 := by
    rw [entry.entry.barrierExact, entry.entry.outer]
    rfl
  have retainedCursorOwnership :
      PendingRetainedCursorAlternativeOwnership alpha pending
        (finish.advance branch branchTail) executableRest qterm barrier
        altTail :=
    PLeaTTa.PrologRetainedCursorOwnershipBridge.RepresentativeRetainedCallFrontier.tailOwnership
      entry frontier
  refine
    ⟨nextAlpha, sourceCanonical, flattened, installed, ?_⟩
  exact
    ⟨nextShared, alphaIncluded, alphaExtension, freshFrontier, selectionFresh,
      persistentAgreement, independentShape, sourceOrdered,
      pendingHeadMgu, sourceProductStep, executableStep, fineExecutableStep,
      cumulative, bodyPayload, materializedBodyHeads, retainedAlts,
      retainedCursorOwnership,
      frontier.tailScan.barrierCount_zero,
      retainedBarriers, barrierTag,
      worldPreserved, counterPreserved⟩

/-- Compatibility wrapper which selects the residual representative once
from a raw supported payload and then enters the fixed-representative product
core. -/
theorem RepresentativeRetainedCallFrontier.activate_product_step_head
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
      LocalCallPayloadAgrees alpha support canonical referenceBase
        referenceBindings binding referencePayload args res)
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
      RepresentativeProductActivationCore prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        referenceRest executableRest qterm barrier startCounter callerScope
        independentResult representative nextAlpha sourceCanonical
        flattenedRepresentative installed := by
  obtain ⟨representative, oldCumulative, queryAtOpen⟩ :=
    PLeaTTa.PrologRecursiveCallPayloadBridge.LocalCallPayloadAgrees.representativeNormalizedCallAgreesWith
      payload payloadSupported opened.cursor openedArguments openedBindings
  obtain ⟨nextAlpha, sourceCanonical, flattened, installed, core⟩ :=
    RepresentativeRetainedCallFrontier.activate_product_step_head_with
      (prog := prog) (gt := gt) (referenceRest := referenceRest)
      (callerScope := callerScope) entry frontier oldCumulative queryAtOpen
      (by simpa only [openedBindings] using payload.bindingShape)
      payload.canonicalWellFormed payload.alphaShared queryReferenceBelow
      queryExecutableLive live resolved
  exact
    ⟨representative, nextAlpha, sourceCanonical, flattened, installed,
      core⟩

/-- One actual retained semantic clause and the corresponding sealed
full-head equality step construct the exact two-region compatibility package.

The proof delegates all MGU, resource, and transition reasoning to the
head-only activation core.  This wrapper supplies only the former body/caller
control certificate. -/
theorem RepresentativeRetainedCallFrontier.activate_segmented_product_step
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
    {qterm : Atom} {barrier callerBarrier startCounter : Nat}
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
      TaskPayloadAgrees alpha support callerBarrier canonical referenceBase
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
      SegmentedRepresentativeProductActivation prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        referenceRest executableRest qterm barrier callerBarrier startCounter
        callerScope independentResult representative nextAlpha sourceCanonical
        flattenedRepresentative installed := by
  obtain
    ⟨representative, nextAlpha, sourceCanonical, flattened, installed, core⟩ :=
    RepresentativeRetainedCallFrontier.activate_product_step_head
      (prog := prog) (gt := gt) (referenceRest := referenceRest)
      (callerScope := callerScope) entry frontier
      (PrologRecursiveCallPayloadBridge.TaskPayloadAgrees.localCallPayload
        payload)
      payloadSupported openedArguments openedBindings queryReferenceBelow
      queryExecutableLive live resolved
  have segmentedPayload :
      SegmentedTaskPayloadAgrees nextAlpha support barrier callerBarrier
        (sourceCanonical ++ canonical) referenceBase independentResult
        (PLeaTTa.trimFor (copied.body ++ executableRest) qterm installed)
        branch.body referenceRest copied.body executableRest :=
    PrologOrdinaryStepBridge.SegmentedTaskPayloadAgrees.ofCallerAndBody
      payload core.bodyPayload core.alphaIncluded
  exact
    ⟨representative, nextAlpha, sourceCanonical, flattened, installed,
      ⟨core, segmentedPayload⟩⟩

/-! ## Fixed-representative spined activation -/

/-- Enter a retained recursive clause from an arbitrary-depth control spine
while preserving one caller-selected residual representative.

The whole spine remains the source of caller-continuation agreement.  Only
the current call head is supplied in materialized form, so fresh or already
bound variables need not satisfy the stronger raw-syntax support predicate. -/
theorem RepresentativeRetainedCallFrontier.activate_spined_product_step_with
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {alpha support : List (LogicVar × String)}
    {canonical representative : TreeSubstitution}
    {referenceBase : Substitution}
    {referenceBindings : Substitution}
    {opened : OpenedCall} {before : DemandDrivenStep.OpenConf}
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
    {callerScope : CutScopeId}
    {independentResult : Substitution}
    (entry :
      RepresentativeSupportedCallEntryRelates alpha opened before pending
        argsv args res
        (segmentExecutableRest ++ flattenExecutables outer)
        binding qterm bodyBarrier startCounter)
    (frontier :
      RepresentativeRetainedCallFrontier alpha opened before pending finish
        branch clause branchTail clauseTail altTail copied argsv args res
        (segmentExecutableRest ++ flattenExecutables outer)
        binding qterm bodyBarrier startCounter)
    (payload :
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
    (queryAtOpen :
      RepresentativeNormalizedCallAgreesWith alpha opened.cursor
        (args.map (PLeaTTa.subst binding))
        (PLeaTTa.subst binding res) representative referenceBase)
    (openedBindings : opened.cursor.bindings = referenceBindings)
    (queryReferenceBelow :
      GeneratedBelow finish.reservationStart (alpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ alpha.map Prod.snd →
        name ∈
          resolutionOccupiedVars
            (args.map (PLeaTTa.subst binding)) res
            (segmentExecutableRest ++ flattenExecutables outer)
            binding qterm)
    (live :
      AlphaRuntimeNamesLive support
        (copied.body ++
          (segmentExecutableRest ++ flattenExecutables outer))
        qterm)
    (resolved : HeadResolution branch independentResult) :
    ∃ nextAlpha sourceCanonical flattenedRepresentative installed,
      SpinedRepresentativeProductActivation prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        segmentReferenceRest segmentExecutableRest outer qterm bodyBarrier
        callerBarrier startCounter callerScope independentResult representative
        nextAlpha sourceCanonical flattenedRepresentative installed := by
  have headPayload :
      TaskPayloadAgrees alpha support callerBarrier canonical referenceBase
        referenceBindings binding
        (.call opened.cursor.predicate referencePayload ::
          segmentReferenceRest)
        (.call opened.cursor.predicate args res :: segmentExecutableRest) :=
    PrologControlSegmentSpineBridge.TaskSpinePayloadAgrees.headPayload payload
  obtain
    ⟨nextAlpha, sourceCanonical, flattened, installed, core⟩ :=
    RepresentativeRetainedCallFrontier.activate_product_step_head_with
      (prog := prog) (gt := gt)
      (referenceRest := segmentReferenceRest)
      (callerScope := callerScope) entry frontier oldCumulative queryAtOpen
      (by
        calc
          opened.cursor.bindings = referenceBindings := openedBindings
          _ = TreeSubstitution.reify canonical ++ referenceBase :=
            (PrologRecursiveCallPayloadBridge.TaskPayloadAgrees.localCallPayload
              headPayload).bindingShape)
      headPayload.canonicalWellFormed headPayload.alphaShared
      queryReferenceBelow queryExecutableLive live resolved
  have spinePayload :
      TaskSpinePayloadAgrees nextAlpha support
        (sourceCanonical ++ canonical) referenceBase independentResult
        (PLeaTTa.trimFor
          (copied.body ++
            (segmentExecutableRest ++ flattenExecutables outer))
          qterm installed)
        ({ barrier := bodyBarrier
           references := branch.body
           executables := copied.body } ::
         { barrier := callerBarrier
           references := segmentReferenceRest
           executables := segmentExecutableRest } ::
         outer) :=
    PrologControlSegmentSpineBridge.TaskSpinePayloadAgrees.activateLocalCall
      payload core.bodyPayload core.alphaIncluded
  exact
    ⟨nextAlpha, sourceCanonical, flattened, installed,
      ⟨core, spinePayload⟩⟩

/-- Enter a retained recursive clause from an arbitrary-depth control spine.

The executable call entry and equality successor use the complete flattened
tail.  The independent source `product` stores only the residual goals of the
current segment; its older products remain represented by `outer`.  The
head-only activation core proves the MGU and transition facts once, and
`TaskSpinePayloadAgrees.activateLocalCall` prepends the new predicate region
without modifying any older barrier. -/
theorem RepresentativeRetainedCallFrontier.activate_spined_product_step
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
    {segmentReferenceRest : List PeTTaSpec.PrologCore.Goal}
    {argsv args : List Atom} {res : Atom}
    {segmentExecutableRest : List PLeaTTa.Goal}
    {outer : List ControlSegment} {binding : Subst}
    {qterm : Atom} {bodyBarrier callerBarrier startCounter : Nat}
    {callerScope : CutScopeId}
    {independentResult : Substitution}
    (entry :
      RepresentativeSupportedCallEntryRelates alpha opened before pending
        argsv args res
        (segmentExecutableRest ++ flattenExecutables outer)
        binding qterm bodyBarrier startCounter)
    (frontier :
      RepresentativeRetainedCallFrontier alpha opened before pending finish
        branch clause branchTail clauseTail altTail copied argsv args res
        (segmentExecutableRest ++ flattenExecutables outer)
        binding qterm bodyBarrier startCounter)
    (payload :
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
            (args.map (PLeaTTa.subst binding)) res
            (segmentExecutableRest ++ flattenExecutables outer)
            binding qterm)
    (live :
      AlphaRuntimeNamesLive support
        (copied.body ++
          (segmentExecutableRest ++ flattenExecutables outer))
        qterm)
    (resolved : HeadResolution branch independentResult) :
    ∃ representative nextAlpha sourceCanonical flattenedRepresentative
        installed,
      SpinedRepresentativeProductActivation prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        segmentReferenceRest segmentExecutableRest outer qterm bodyBarrier
        callerBarrier startCounter callerScope independentResult representative
        nextAlpha sourceCanonical flattenedRepresentative installed := by
  have headPayload :
      TaskPayloadAgrees alpha support callerBarrier canonical referenceBase
        referenceBindings binding
        (.call opened.cursor.predicate referencePayload ::
          segmentReferenceRest)
        (.call opened.cursor.predicate args res :: segmentExecutableRest) :=
    PrologControlSegmentSpineBridge.TaskSpinePayloadAgrees.headPayload payload
  obtain
    ⟨representative, nextAlpha, sourceCanonical, flattened, installed, core⟩ :=
    RepresentativeRetainedCallFrontier.activate_product_step_head
      (prog := prog) (gt := gt)
      (referenceRest := segmentReferenceRest)
      (callerScope := callerScope) entry frontier
      (PrologRecursiveCallPayloadBridge.TaskPayloadAgrees.localCallPayload
        headPayload)
      payloadSupported openedArguments openedBindings queryReferenceBelow
      queryExecutableLive live resolved
  have spinePayload :
      TaskSpinePayloadAgrees nextAlpha support
        (sourceCanonical ++ canonical) referenceBase independentResult
        (PLeaTTa.trimFor
          (copied.body ++
            (segmentExecutableRest ++ flattenExecutables outer))
          qterm installed)
        ({ barrier := bodyBarrier
           references := branch.body
           executables := copied.body } ::
         { barrier := callerBarrier
           references := segmentReferenceRest
           executables := segmentExecutableRest } ::
         outer) :=
    PrologControlSegmentSpineBridge.TaskSpinePayloadAgrees.activateLocalCall
      payload core.bodyPayload core.alphaIncluded
  exact
    ⟨representative, nextAlpha, sourceCanonical, flattened, installed,
      ⟨core, spinePayload⟩⟩

/-- Compatibility specialization of segmented activation when the caller
and callee are deliberately related at the same barrier.

The equality is witnessed by construction here.  General recursive calls
should consume `activate_segmented_product_step` instead. -/
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
        referenceRest executableRest qterm barrier startCounter callerScope
        independentResult representative nextAlpha sourceCanonical
        flattenedRepresentative installed := by
  obtain
    ⟨representative, nextAlpha, sourceCanonical, flattenedRepresentative,
      installed, activation⟩ :=
    PLeaTTa.PrologRepresentativeProductActivationBridge.RepresentativeRetainedCallFrontier.activate_segmented_product_step
      entry frontier payload payloadSupported openedArguments openedBindings
      queryReferenceBelow queryExecutableLive live resolved
  refine
    ⟨representative, nextAlpha, sourceCanonical, flattenedRepresentative,
      installed, ?_⟩
  exact
    ⟨activation.toRepresentativeProductActivationCore,
      activation.segmentedPayload.flatten_of_eq rfl⟩

end PLeaTTa.PrologRepresentativeProductActivationBridge
