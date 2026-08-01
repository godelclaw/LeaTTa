-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologFailureRebasePrefixBridge
Purpose: Extend the exact forward prefix with a snapshot-indexed
  post-failure phase and substitution rebase transitions.
Trusted boundary: none
Main exports:
  PostFailurePayloadState,
  ResolverPhaseState,
  ResolverCertifiedTransition,
  ResolverCertifiedPrefix
-/
import PLeaTTa.Proofs.PrologHeterogeneousPrefixBridge
import PLeaTTa.Proofs.PrologCurrentSessionPostFailureActivationBridge

namespace PLeaTTa.PrologFailureRebasePrefixBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologActivationMacro
open PrologAlphaFreshFrontierBridge
open PrologBodyFailureResourceTransitionBridge
open PrologBooleanAliasSafety
open PrologCallPayloadBridge
open PrologControlSegmentSpineBridge
open PrologCurrentSessionFailurePayloadTransitionBridge
open PrologCurrentSessionPayloadBridge
open PrologCurrentSessionPayloadTransitionBridge
open PrologHeterogeneousPrefixBridge
open PrologMguBridge
open PrologMguComposition
open PrologNestedCallChainBridge
open PrologNestedCallReadyBridge
open PrologOrdinaryStepBridge
open PrologPrefilterScanBridge
open PrologProductResourceContextBridge
open PrologProductResourceTransitionBridge
open PrologRepresentativeProductActivationBridge
open PrologRetainedCursorOwnershipBridge
open PrologRetainedPayloadActivationBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
open PrologSourceProductContextBridge
open PrologStateBridge

/-!
The forward-only heterogeneous prefix carries a representative that grows by
prepending residual MGUs.  That law is intentionally left unchanged.

Backtracking has a different law: a failed branch restores the representative
stored in the retained call's immutable payload snapshot, then the next
selected clause prepends its own MGU.  The phase below keeps that snapshot as
a literal dependent component.  Consequently an activation cannot be paired
with a merely shape-compatible snapshot supplied as a separate premise.
-/

/-! ## Exact post-failure phase -/

/-- Every data index of the executable-one-head-ahead post-failure frontier. -/
structure PostFailurePayloadIndex where
  freshFrontier : FreshFrontierRelation
  alpha : List (LogicVar × String)
  support : List (LogicVar × String)
  opened : OpenedCall
  session : Session
  pending : DemandDrivenCallStep.PendingCall
  bodyBarrier : Nat
  callerBarrier : Nat
  callerReferences : List PeTTaSpec.PrologCore.Goal
  callerExecutables : List PLeaTTa.Goal
  outer : List ControlSegment
  qterm : Atom
  cursor : PreparedCursor
  branch : ClauseBranch
  clause : PLeaTTa.Clause
  branchTail : List ClauseBranch
  copied : PLeaTTa.Clause
  resource : RetainedAlternativeSegment
  remainingAlts : List PLeaTTa.Alt
  resources : List RetainedAlternativeSegment
  callerScope : CutScopeId
  outerScope : CutScopeId
  context : ActiveProductContext
  baseAlts : List PLeaTTa.Alt
  source : Search
  openConf : OpenConf

namespace PostFailurePayloadIndex

abbrev PayloadContext (index : PostFailurePayloadIndex) :=
  PostFailurePayloadOffsetContext index.alpha index.support index.qterm
    index.opened index.cursor index.branch index.branchTail index.bodyBarrier
    index.callerBarrier index.callerReferences index.callerExecutables
    index.outer index.resource index.remainingAlts index.resources
    index.callerScope index.outerScope index.context

abbrev Relates (index : PostFailurePayloadIndex)
    (payloadContext : index.PayloadContext) :=
  SpinedPostFailureFrontierPayloadResourceRelatesAt index.freshFrontier
    index.alpha index.support index.opened index.session index.pending
    index.bodyBarrier index.callerBarrier index.callerReferences
    index.callerExecutables index.outer index.qterm index.cursor index.branch
    index.clause index.branchTail index.copied index.resource
    index.remainingAlts index.resources index.callerScope index.outerScope
    index.context index.baseAlts index.source index.openConf payloadContext

end PostFailurePayloadIndex

/-- One exact post-failure state.  Its payload contains the unique retained
snapshot to which logical bindings have backtracked. -/
structure PostFailurePayloadState where
  index : PostFailurePayloadIndex
  payloadContext : index.PayloadContext
  agreement : index.Relates payloadContext
  exactFresh :
    index.freshFrontier = AlphaFreshFrontier index.alpha

namespace PostFailurePayloadState

/-- Package an existing exact post-failure relation without erasing any
dependent cursor, resource, or snapshot index. -/
def ofAgreement
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {opened : OpenedCall} {session : Session}
    {pending : DemandDrivenCallStep.PendingCall}
    {bodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment} {qterm : Atom}
    {cursor : PreparedCursor} {branch : ClauseBranch}
    {clause : PLeaTTa.Clause} {branchTail : List ClauseBranch}
    {copied : PLeaTTa.Clause} {resource : RetainedAlternativeSegment}
    {remainingAlts : List PLeaTTa.Alt}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext} {baseAlts : List PLeaTTa.Alt}
    {source : Search} {openConf : OpenConf}
    {payloadContext :
      PostFailurePayloadOffsetContext alpha support qterm opened cursor branch
        branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer resource remainingAlts resources callerScope
        outerScope context}
    (agreement :
      SpinedPostFailureFrontierPayloadResourceRelatesAt freshFrontier alpha
        support opened session pending bodyBarrier callerBarrier
        callerReferences callerExecutables outer qterm cursor branch clause
        branchTail copied resource remainingAlts resources callerScope
        outerScope context baseAlts source openConf payloadContext) :
    freshFrontier = AlphaFreshFrontier alpha →
    PostFailurePayloadState :=
  fun exactFresh =>
  { index :=
      { freshFrontier := freshFrontier
        alpha := alpha
        support := support
        opened := opened
        session := session
        pending := pending
        bodyBarrier := bodyBarrier
        callerBarrier := callerBarrier
        callerReferences := callerReferences
        callerExecutables := callerExecutables
        outer := outer
        qterm := qterm
        cursor := cursor
        branch := branch
        clause := clause
        branchTail := branchTail
        copied := copied
        resource := resource
        remainingAlts := remainingAlts
        resources := resources
        callerScope := callerScope
        outerScope := outerScope
        context := context
        baseAlts := baseAlts
        source := source
        openConf := openConf }
    payloadContext := payloadContext
    agreement := agreement
    exactFresh := exactFresh }

def sourceState (state : PostFailurePayloadState) : State :=
  .running state.index.session state.index.source

def fineState (state : PostFailurePayloadState) :
    DemandDrivenCallStep.FineConf :=
  .ready state.index.openConf

def snapshot (state : PostFailurePayloadState) :=
  PostFailurePayloadOffsetContext.headSnapshot state.payloadContext

/-- The logical representative at a failure frontier is the exact immutable
representative stored by its retained payload, not the failed branch's later
representative. -/
def representative (state : PostFailurePayloadState) : TreeSubstitution :=
  state.snapshot.residualRepresentative

def cellIdentities (state : PostFailurePayloadState) :
    List PrologNestedCallChainBridge.PayloadCellIdentity :=
  PrologNestedCallChainBridge.SourceControlResourcePayloadContextAgrees.cellIdentities
    state.payloadContext

def cellCount (state : PostFailurePayloadState) : Nat :=
  PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount
    state.payloadContext

theorem cellIdentities_length (state : PostFailurePayloadState) :
    state.cellIdentities.length = state.cellCount :=
  PrologNestedCallChainBridge.SourceControlResourcePayloadContextAgrees.cellIdentities_length_eq_cellCount
    state.payloadContext

end PostFailurePayloadState

/-! ## Additive resolver phase -/

/-- The old forward phase is embedded unchanged.  Only the new constructor
admits a logical rollback frontier. -/
inductive ResolverPhaseState where
  | ordinary (state : ProductPhaseState)
  | postFailure (state : PostFailurePayloadState)

namespace ResolverPhaseState

def sourceState : ResolverPhaseState → State
  | .ordinary state => state.sourceState
  | .postFailure state => state.sourceState

def fineState : ResolverPhaseState → DemandDrivenCallStep.FineConf
  | .ordinary state => state.fineState
  | .postFailure state => state.fineState

def session : ResolverPhaseState → Session
  | .ordinary state => state.session
  | .postFailure state => state.index.session

def openConf : ResolverPhaseState → OpenConf
  | .ordinary state => state.openConf
  | .postFailure state => state.index.openConf

def alpha : ResolverPhaseState → List (LogicVar × String)
  | .ordinary state => state.alpha
  | .postFailure state => state.index.alpha

def representative : ResolverPhaseState → TreeSubstitution
  | .ordinary state => state.representative
  | .postFailure state => state.representative

def cellIdentities : ResolverPhaseState →
    List PrologNestedCallChainBridge.PayloadCellIdentity
  | .ordinary state => state.cellIdentities
  | .postFailure state => state.cellIdentities

def cellCount : ResolverPhaseState → Nat
  | .ordinary state => state.cellCount
  | .postFailure state => state.cellCount

theorem cellIdentities_length (state : ResolverPhaseState) :
    state.cellIdentities.length = state.cellCount := by
  cases state with
  | ordinary state => exact state.cellIdentities_length
  | postFailure state => exact state.cellIdentities_length

end ResolverPhaseState

/-! ## Exact failure and reactivation producers -/

/-- One retained failure successor with the source cursor catch-up, eager
fine-machine pull, and transformed payload all indexed by the same data.

The target payload is definitionally computed from `before.payloadContext`,
`pulls`, and `offset`.  A snapshot from any other retained cursor therefore
cannot be inserted into `after`. -/
structure RetainedFailureSuccessor
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (before : RepresentativeActivePayloadState) where
  exactFresh :
    before.carrier.index.freshFrontier =
      AlphaFreshFrontier before.carrier.index.alpha
  count : Nat
  next : PreparedCursor
  nextBranch : ClauseBranch
  nextClause : PLeaTTa.Clause
  nextBranchTail : List ClauseBranch
  nextAltTail : List PLeaTTa.Alt
  nextCopied : PLeaTTa.Clause
  pulls :
    RejectedPullsN count
      (before.carrier.index.finish.advance before.carrier.index.branch
        before.carrier.index.branchTail)
      next
  offset :
    PulledHeadOffsetAgrees before.carrier.index.alpha next nextBranch
      nextClause nextBranchTail nextCopied before.carrier.index.active
      nextAltTail
  sourceSteps :
    StepsN (count + 1) before.carrier.sourceState []
      (.running before.carrier.index.session
        (before.carrier.index.context.plug
          (sourceProductFrontier before.carrier.index.callerScope
            before.carrier.index.opened next
            before.carrier.index.callerReferences)))
  fineStep :
    DemandDrivenCallStep.Step prog gt before.carrier.fineState
      (.ready (unifyFailureSuccessor before.carrier.index.openConf))
  postAgreement :
    SpinedPostFailureFrontierPayloadResourceRelatesAt
      before.carrier.index.freshFrontier before.carrier.index.alpha
      before.carrier.index.support before.carrier.index.opened
      before.carrier.index.session before.carrier.index.pending
      before.carrier.index.bodyBarrier before.carrier.index.callerBarrier
      before.carrier.index.callerReferences
      before.carrier.index.callerExecutables before.carrier.index.outer
      before.carrier.index.qterm next nextBranch nextClause nextBranchTail
      nextCopied before.carrier.index.active nextAltTail
      before.carrier.index.resources before.carrier.index.callerScope
      before.carrier.index.outerScope before.carrier.index.context
      before.carrier.index.baseAlts
      (before.carrier.index.context.plug
        (sourceProductFrontier before.carrier.index.callerScope
          before.carrier.index.opened next
          before.carrier.index.callerReferences))
      (unifyFailureSuccessor before.carrier.index.openConf)
      (ActiveProductPayloadContext.afterRejectedPullsAndPulledHead
        before.carrier.payloadContext pulls offset)

namespace RetainedFailureSuccessor

def afterPayloadContext
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeActivePayloadState}
    (facts : RetainedFailureSuccessor prog gt before) :=
  ActiveProductPayloadContext.afterRejectedPullsAndPulledHead
    before.carrier.payloadContext facts.pulls facts.offset

/-- The exact post-failure midpoint constructed by this failure. -/
def after
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeActivePayloadState}
    (facts : RetainedFailureSuccessor prog gt before) :
    PostFailurePayloadState :=
  PostFailurePayloadState.ofAgreement facts.postAgreement facts.exactFresh

/-- Failure changes the active/pulled-head payload views but preserves the
immutable representative snapshot of the retained call.  This equality is
about the literal payload cell carried by `before`, not a separately chosen
compatible snapshot. -/
theorem after_representative_eq_before_snapshot
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeActivePayloadState}
    (facts : RetainedFailureSuccessor prog gt before) :
    facts.after.representative =
      (SourceControlResourcePayloadContextAgrees.headCell
        before.carrier.payloadContext).snapshot.residualRepresentative := by
  simpa [after, PostFailurePayloadState.representative,
    PostFailurePayloadState.snapshot, PostFailurePayloadState.ofAgreement,
    afterPayloadContext] using
    (ActiveProductPayloadContext.headSnapshotRepresentative_afterRejectedPullsAndPulledHead
      before.carrier.payloadContext facts.pulls facts.offset)

end RetainedFailureSuccessor

namespace RepresentativeActivePayloadState

/-- Produce the exact retained post-failure midpoint from one active
primitive-unification clash.  All scan witnesses discarded by this wrapper
remain internal to the already-proved failure theorem; the returned package
retains precisely the data required to identify and reactivate its head.
[SPEC metta.pl:251-256; ISO:unification] -/
theorem retainedFailureSuccessor
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (before : RepresentativeActivePayloadState)
    {left right : Term}
    {bodyRest : List PeTTaSpec.PrologCore.Goal}
    (referenceHead :
      before.carrier.index.bodyReferences = .unify left right :: bodyRest)
    (leftSupported :
      AlphaTreeSupported before.carrier.index.alpha
        before.carrier.index.support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported before.carrier.index.alpha
        before.carrier.index.support (Term.denote right))
    (currentSafe :
      Substitution.BooleanAliasSafe before.carrier.index.current)
    (leftAliasSafe : TermBooleanAliasSafe left)
    (rightAliasSafe : TermBooleanAliasSafe right)
    (clash :
      ¬ ∃ result,
        UnifyResolution before.carrier.index.current left right result)
    (exactFresh :
      before.carrier.index.freshFrontier =
        AlphaFreshFrontier before.carrier.index.alpha)
    (nonempty : before.carrier.index.active.alts ≠ []) :
    Nonempty (RetainedFailureSuccessor prog gt before) := by
  have shaped :
      SpinedActiveProductPayloadResourceRelatesAt
        before.carrier.index.freshFrontier before.carrier.index.alpha
        before.carrier.index.support before.carrier.index.canonical
        before.carrier.index.referenceBase before.carrier.index.opened
        before.carrier.index.session before.carrier.index.pending
        before.carrier.index.finish before.carrier.index.branch
        before.carrier.index.branchTail before.carrier.index.altTail
        before.carrier.index.bodyBarrier before.carrier.index.callerBarrier
        (.unify left right :: bodyRest)
        before.carrier.index.bodyExecutables
        before.carrier.index.callerReferences
        before.carrier.index.callerExecutables before.carrier.index.outer
        before.carrier.index.current before.carrier.index.runtime
        before.carrier.index.qterm before.carrier.index.active
        before.carrier.index.resources before.carrier.index.callerScope
        before.carrier.index.outerScope before.carrier.index.context
        before.carrier.index.baseAlts before.carrier.index.source
        before.carrier.index.openConf before.carrier.payloadContext := by
    simpa [ActivePayloadIndex.Relates, referenceHead] using
      before.carrier.agreement
  obtain
      ⟨count, _skippedBranches, _skippedClauses, _candidates, next,
        nextBranch, nextClause, nextBranchTail, _nextClauseTail, nextAltTail,
        nextCopied, pulls, offset, _selectedTailExact, _candidatesExact,
        _branchCount, _clauseCount, _skippedRejected, sourceSteps, fineStep,
        postAgreement⟩ :=
    PrologCurrentSessionFailurePayloadTransitionBridge.SpinedActiveProductPayloadResourceRelatesAt.afterUnifyFailureRetained
      (prog := prog) (gt := gt) shaped leftSupported rightSupported
      currentSafe leftAliasSafe rightAliasSafe clash nonempty
  exact
    ⟨{ exactFresh := exactFresh
       count := count
       next := next
       nextBranch := nextBranch
       nextClause := nextClause
       nextBranchTail := nextBranchTail
       nextAltTail := nextAltTail
       nextCopied := nextCopied
       pulls := pulls
       offset := offset
       sourceSteps := sourceSteps
       fineStep := fineStep
       postAgreement := postAgreement }⟩

end RepresentativeActivePayloadState

namespace PostFailurePayloadState

/-- Restore the exact pre-head logical snapshot stored in this midpoint. -/
def restoredSnapshot (before : PostFailurePayloadState) :=
  SelectedHeadActivationChronology.restoreSnapshot before.snapshot
    before.agreement.activationChronology
    before.agreement.core.resourceStack.offset

/-- The retained clause's source allocation floor is historical, but it is
still dominated by the current persistent source high-water.  This is the
honest bridge needed when a retry reuses a clause that was eagerly freshened
before the intervening failed body ran. -/
theorem selectedReferenceFloor_le_current
    (before : PostFailurePayloadState) :
    before.index.branch.firstFresh ≤
      before.index.session.resolver.nextFresh := by
  have endpointComponents :=
    SourceControlResourcePayloadContextAgrees.endpointsBelow_head
      before.payloadContext before.agreement.endpointsCurrent
  have cursorDominated :
      before.index.cursor.reservedUntil ≤
        before.index.session.resolver.nextFresh := by
    simpa [PreparedCursor.advance] using endpointComponents.1
  have branchMember :
      before.index.branch ∈ before.index.cursor.remaining := by
    rw [before.agreement.core.resourceStack.offset.cursorRemaining]
    simp
  calc
    before.index.branch.firstFresh ≤ before.index.branch.nextFresh :=
      before.agreement.core.resourceStack.offset.cursorWellFormed.1
        |>.member_first_le_next branchMember
    _ ≤ before.index.cursor.reservedUntil :=
      before.agreement.core.resourceStack.offset.cursorWellFormed.1
        |>.member_next_le_final branchMember
    _ ≤ before.index.session.resolver.nextFresh := cursorDominated

/-- The retained executable clause-head seed likewise predates the current
machine counter but cannot exceed it.  The strict reservation step is
recovered from the literal retained scan witness rather than assumed from a
global counter convention. -/
theorem selectedExecutableFloor_le_current
    (before : PostFailurePayloadState) :
    before.index.resource.counter ≤
      before.index.openConf.persistent.counter := by
  have endpointComponents :=
    SourceControlResourcePayloadContextAgrees.endpointsBelow_head
      before.payloadContext before.agreement.endpointsCurrent
  have resourceDominated :
      before.index.resource.finalCounter ≤
        before.index.openConf.persistent.counter := by
    simpa [afterPulledHead] using endpointComponents.2.1
  have seedReserved :
      before.index.resource.counter + 1 ≤
        before.index.resource.finalCounter := by
    rcases before.agreement.core.resourceStack.offset.tailOwnership with
      ⟨_callStart, _position, tailOwnership⟩
    rcases tailOwnership.scan with
      ⟨_candidates, _wellFormed, _query, _substitutedArgs, _supported,
        _arities, scan⟩
    have scanExact := scan.counter_exact
    simpa only [afterPulledHead_counter, afterPulledHead_finalCounter] using
      (show
        (afterPulledHead before.index.resource
            before.index.remainingAlts).counter ≤
          (afterPulledHead before.index.resource
            before.index.remainingAlts).finalCounter by
        omega)
  exact
    Nat.le_trans (Nat.le_trans (Nat.le_succ _) seedReserved)
      resourceDominated

end PostFailurePayloadState

/-- One selected-head activation whose successor representative is indexed
directly by the midpoint's own restored snapshot. -/
structure RetainedActivationSuccessor
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (before : PostFailurePayloadState) where
  independentResult : Substitution
  nextAlpha : List (LogicVar × String)
  sourceCanonical : TreeSubstitution
  flattened : TreeSubstitution
  installed : Subst
  extension :
    AlphaExtendsAbove before.index.alpha nextAlpha
      before.index.branch.firstFresh before.index.resource.counter
  nextPayloadContext :
    ActiveProductPayloadContext nextAlpha before.index.support
      before.index.qterm before.index.opened before.index.cursor
      before.index.branch before.index.branchTail before.index.bodyBarrier
      before.index.callerBarrier before.index.callerReferences
      before.index.callerExecutables before.index.outer
      (afterPulledHead before.index.resource before.index.remainingAlts)
      before.index.resources before.index.callerScope before.index.outerScope
      before.index.context
  shared : SharedRuntimeAlpha nextAlpha
  alphaIncluded :
    ∀ pair, pair ∈ before.index.alpha → pair ∈ nextAlpha
  outerPayloadExact :
    SourceControlResourcePayloadContextAgrees.tail nextPayloadContext =
      SourceControlResourcePayloadContextAgrees.extendAbove extension
        (SourceControlResourcePayloadContextAgrees.tail before.payloadContext)
        before.agreement.outerActivationEndpoints
  sourceStep :
    RawStep before.index.session before.index.source [] .none
      before.index.session
      (.running
        (before.index.context.plug
          (activatedSourceProduct before.index.callerScope
            before.index.opened before.index.cursor before.index.branch
            before.index.branchTail independentResult
            before.index.callerReferences)))
  sealedStep :
    PLeaTTa.Step prog gt before.index.openConf.toConf
      (unifySuccessor before.index.openConf
        (before.index.copied.body ++ before.index.resource.rest)
        installed).toConf
  fineStep :
    DemandDrivenCallStep.Step prog gt before.fineState
      (.ready
        (unifySuccessor before.index.openConf
          (before.index.copied.body ++ before.index.resource.rest)
          installed))
  cumulative :
    AlphaCumulativeResidualVariantAgreesOnWith nextAlpha before.index.support
      (sourceCanonical ++ before.restoredSnapshot.canonical)
      before.restoredSnapshot.referenceBase
      (PLeaTTa.trimFor
        (before.index.copied.body ++ before.index.resource.rest)
        before.index.openConf.control.qterm installed)
      (flattened ++ before.restoredSnapshot.residualRepresentative)
  targetAgreement :
    SpinedActiveProductPayloadResourceRelatesAt
      (AlphaFreshFrontier nextAlpha) nextAlpha before.index.support
      (sourceCanonical ++ before.restoredSnapshot.canonical)
      before.restoredSnapshot.referenceBase before.index.opened
      before.index.session before.index.pending before.index.cursor
      before.index.branch before.index.branchTail before.index.remainingAlts
      before.index.bodyBarrier before.index.callerBarrier
      before.index.branch.body before.index.copied.body
      before.index.callerReferences before.index.callerExecutables
      before.index.outer independentResult
      (PLeaTTa.trimFor
        (before.index.copied.body ++ before.index.resource.rest)
        before.index.openConf.control.qterm installed)
      before.index.qterm
      (afterPulledHead before.index.resource before.index.remainingAlts)
      before.index.resources before.index.callerScope before.index.outerScope
      before.index.context before.index.baseAlts
      (before.index.context.plug
        (activatedSourceProduct before.index.callerScope before.index.opened
          before.index.cursor before.index.branch before.index.branchTail
          independentResult before.index.callerReferences))
      (unifySuccessor before.index.openConf
        (before.index.copied.body ++ before.index.resource.rest) installed)
      nextPayloadContext

namespace RetainedActivationSuccessor

def afterCarrier
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : PostFailurePayloadState}
    (facts : RetainedActivationSuccessor prog gt before) :
    ActivePayloadState :=
  ActivePayloadState.ofAgreement facts.targetAgreement

/-- The successor carries the new clause-head MGU in front of the exact
representative restored from the retained snapshot. -/
def after
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : PostFailurePayloadState}
    (facts : RetainedActivationSuccessor prog gt before) :
    RepresentativeActivePayloadState :=
  { carrier := facts.afterCarrier
    representative :=
      facts.flattened ++ before.restoredSnapshot.residualRepresentative
    cumulative := by
      simpa [afterCarrier, ActivePayloadState.ofAgreement] using
        facts.cumulative }

end RetainedActivationSuccessor

namespace PostFailurePayloadState

/-- Produce one exact activation from this midpoint.  The wrapper consumes
this state's own agreement and returns a successor indexed by this state's
own restored snapshot; there is no snapshot argument. -/
theorem retainedActivationSuccessor
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {resolvedResult : Substitution}
    (before : PostFailurePayloadState)
    (currentShared : SharedRuntimeAlpha before.index.alpha)
    (below : ConfBelowResolutionCounter before.index.openConf.toConf)
    (live :
      AlphaRuntimeNamesLive before.index.support
        (before.index.copied.body ++ before.index.resource.rest)
        before.index.resource.qterm)
    (resolved :
      HeadResolution before.index.branch resolvedResult) :
    Nonempty (RetainedActivationSuccessor prog gt before) := by
  have exactAgreement := before.agreement
  dsimp only [PostFailurePayloadIndex.Relates] at exactAgreement
  rw [before.exactFresh] at exactAgreement
  obtain
      ⟨nextAlpha, sourceCanonical, flattened, installed, extension,
        nextPayloadContext, shared, alphaIncluded, outerPayloadExact,
        sourceStep, sealedStep, fineStep, cumulative, targetAgreement⟩ :=
    PrologCurrentSessionPostFailureActivationBridge.SpinedPostFailureFrontierPayloadResourceRelatesAt.activateSelectedHead
      (prog := prog) (gt := gt) exactAgreement currentShared below live
      resolved
  exact
    ⟨{ independentResult := resolvedResult
       nextAlpha := nextAlpha
       sourceCanonical := sourceCanonical
       flattened := flattened
       installed := installed
       extension := extension
       nextPayloadContext := nextPayloadContext
       shared := shared
       alphaIncluded := alphaIncluded
       outerPayloadExact := outerPayloadExact
       sourceStep := sourceStep
       sealedStep := sealedStep
       fineStep := fineStep
       cumulative := cumulative
       targetAgreement := targetAgreement }⟩

end PostFailurePayloadState

/-! ## Closed resolver transition vocabulary -/

inductive ResolverTransitionKind where
  | forward (kind : TransitionKind)
  | retainedFailure (rejected : Nat)
  | retainedActivation
deriving Repr

namespace ResolverTransitionKind

def sourceCost : ResolverTransitionKind → Nat
  | .forward kind => kind.sourceCost
  | .retainedFailure rejected => rejected + 1
  | .retainedActivation => 1

def sourceEvents : ResolverTransitionKind → List Observation
  | .forward kind => kind.sourceEvents
  | .retainedFailure _ => []
  | .retainedActivation => []

def fineCost : ResolverTransitionKind → Nat
  | .forward kind => kind.fineCost
  | .retainedFailure _ => 1
  | .retainedActivation => 1

/-- Exact alpha-graph effect of one resolver transition.

Forward work allocates above the incoming current high-waters.  Failure
preserves the graph literally.  Retained activation instead allocates above
the selected clause's historical reservation floors and separately proves
those floors are dominated by the current high-waters.  Conflating the first
and third cases would assert a false chronological freshness law on retry. -/
def AlphaEvolution (kind : ResolverTransitionKind)
    (before after : ResolverPhaseState) : Prop :=
  match kind with
  | .forward _ =>
      AlphaExtendsAbove before.alpha after.alpha
        before.session.resolver.nextFresh
        before.openConf.persistent.counter
  | .retainedFailure _ =>
      after.alpha = before.alpha
  | .retainedActivation =>
      match before with
      | .ordinary _ => False
      | .postFailure state =>
          AlphaExtendsAbove state.index.alpha after.alpha
              state.index.branch.firstFresh state.index.resource.counter ∧
            state.index.branch.firstFresh ≤
              state.index.session.resolver.nextFresh ∧
            state.index.resource.counter ≤
              state.index.openConf.persistent.counter

/-- Exact logical-representative effect of one resolver transition.

Forward work and activation prepend a certified residual MGU.  Failure is
intentionally different: it selects the literal retained snapshot carried by
the post-failure state.  Keeping the two cases distinct prevents a later
prefix theorem from assuming the false law that rollback extends the failed
branch's representative. -/
def RepresentativeEvolution (kind : ResolverTransitionKind)
    (before after : ResolverPhaseState) : Prop :=
  match kind with
  | .forward _ =>
      ∃ extension : TreeSubstitution,
        after.representative = extension ++ before.representative
  | .retainedFailure _ =>
      ∃ state : PostFailurePayloadState,
        after = .postFailure state ∧
          after.representative = state.snapshot.residualRepresentative
  | .retainedActivation =>
      ∃ extension : TreeSubstitution,
        after.representative = extension ++ before.representative

end ResolverTransitionKind

/-- Exact resolver transitions.  Forward transitions retain the existing
closed vocabulary verbatim; only failure and reactivation cross the new
snapshot-indexed phase. -/
inductive ResolverCertifiedTransition
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable) :
    ResolverTransitionKind → ResolverPhaseState → ResolverPhaseState → Type
    where
  | forward
      {kind : TransitionKind} {before after : ProductPhaseState}
      (step : CertifiedTransition prog gt kind before after) :
      ResolverCertifiedTransition prog gt (.forward kind)
        (.ordinary before) (.ordinary after)
  | retainedFailure
      {before : RepresentativeActivePayloadState}
      (facts : RetainedFailureSuccessor prog gt before) :
      ResolverCertifiedTransition prog gt (.retainedFailure facts.count)
        (.ordinary (.active before)) (.postFailure facts.after)
  | retainedActivation
      {before : PostFailurePayloadState}
      (facts : RetainedActivationSuccessor prog gt before) :
      ResolverCertifiedTransition prog gt .retainedActivation
        (.postFailure before) (.ordinary (.active facts.after))

namespace ResolverCertifiedTransition

theorem sourceSteps
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kind : ResolverTransitionKind} {before after : ResolverPhaseState}
    (step : ResolverCertifiedTransition prog gt kind before after) :
    StepsN kind.sourceCost before.sourceState kind.sourceEvents
      after.sourceState := by
  cases step with
  | forward step =>
      simpa [ResolverTransitionKind.sourceCost,
        ResolverTransitionKind.sourceEvents, ResolverPhaseState.sourceState]
        using step.sourceSteps
  | retainedFailure facts =>
      simpa [ResolverTransitionKind.sourceCost,
        ResolverTransitionKind.sourceEvents, ResolverPhaseState.sourceState,
        ProductPhaseState.sourceState, PostFailurePayloadState.sourceState,
        RetainedFailureSuccessor.after,
        PostFailurePayloadState.ofAgreement]
        using facts.sourceSteps
  | retainedActivation facts =>
      simpa [ResolverTransitionKind.sourceCost,
        ResolverTransitionKind.sourceEvents, ResolverPhaseState.sourceState,
        ProductPhaseState.sourceState,
        PostFailurePayloadState.sourceState,
        RetainedActivationSuccessor.after,
        RetainedActivationSuccessor.afterCarrier,
        ActivePayloadState.ofAgreement, ActivePayloadState.sourceState] using
        CertifiedTransition.oneSourceStep facts.sourceStep

theorem fineSteps
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kind : ResolverTransitionKind} {before after : ResolverPhaseState}
    (step : ResolverCertifiedTransition prog gt kind before after) :
    DemandDrivenCallStep.StepsN prog gt kind.fineCost before.fineState
      after.fineState := by
  cases step with
  | forward step =>
      simpa [ResolverTransitionKind.fineCost, ResolverPhaseState.fineState]
        using step.fineSteps
  | retainedFailure facts =>
      simpa [ResolverTransitionKind.fineCost, ResolverPhaseState.fineState,
        ProductPhaseState.fineState, PostFailurePayloadState.fineState,
        RetainedFailureSuccessor.after,
        PostFailurePayloadState.ofAgreement]
        using CertifiedTransition.oneFineStep facts.fineStep
  | retainedActivation facts =>
      simpa [ResolverTransitionKind.fineCost, ResolverPhaseState.fineState,
        ProductPhaseState.fineState,
        PostFailurePayloadState.fineState,
        RetainedActivationSuccessor.after,
        RetainedActivationSuccessor.afterCarrier,
        ActivePayloadState.ofAgreement, ActivePayloadState.fineState] using
        CertifiedTransition.oneFineStep facts.fineStep

/-- The representative effect is determined by the closed transition kind.
In particular, failure exposes the exact retained snapshot rather than an
arbitrary representative compatible with the same endpoints. -/
theorem representativeEvolution
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kind : ResolverTransitionKind} {before after : ResolverPhaseState}
    (step : ResolverCertifiedTransition prog gt kind before after) :
    kind.RepresentativeEvolution before after := by
  cases step with
  | forward step =>
      simpa [ResolverTransitionKind.RepresentativeEvolution,
        ResolverPhaseState.representative] using
        step.representativeExtension
  | retainedFailure facts =>
      exact ⟨facts.after, rfl, rfl⟩
  | retainedActivation facts =>
      refine ⟨facts.flattened, ?_⟩
      rfl

/-- Failure and activation do not restore an old persistent session.  The
new cases therefore compose with the four-high-water theorem already proved
for the forward fragment. -/
theorem sessionHighWaters
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kind : ResolverTransitionKind} {before after : ResolverPhaseState}
    (step : ResolverCertifiedTransition prog gt kind before after) :
    SessionHighWatersExtend before.session after.session := by
  cases step with
  | forward step =>
      simpa [ResolverPhaseState.session] using step.sessionHighWaters
  | retainedFailure facts =>
      exact SessionHighWatersExtend.refl _
  | retainedActivation facts =>
      exact SessionHighWatersExtend.refl _

/-- The fine executable allocation counter remains monotone through failure
and reactivation; neither transition rewinds persistent state. -/
theorem executableCounter_mono
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kind : ResolverTransitionKind} {before after : ResolverPhaseState}
    (step : ResolverCertifiedTransition prog gt kind before after) :
    before.openConf.persistent.counter ≤ after.openConf.persistent.counter := by
  cases step with
  | forward step =>
      simpa [ResolverPhaseState.openConf] using step.executableCounter_mono
  | @retainedFailure before facts =>
      change
        before.carrier.index.openConf.persistent.counter ≤
          (unifyFailureSuccessor
            before.carrier.index.openConf).persistent.counter
      rw [unifyFailureSuccessor_persistent]
  | @retainedActivation before facts =>
      change
        before.index.openConf.persistent.counter ≤
          (unifySuccessor before.index.openConf
            (before.index.copied.body ++ before.index.resource.rest)
            facts.installed).persistent.counter
      rw [unifySuccessor_persistent]

/-- Every alpha pair already live before a transition remains live after it.
Failure preserves the graph literally; activation exposes its producer's
exact inclusion proof. -/
theorem alphaIncluded
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kind : ResolverTransitionKind} {before after : ResolverPhaseState}
    (step : ResolverCertifiedTransition prog gt kind before after) :
    ∀ pair, pair ∈ before.alpha → pair ∈ after.alpha := by
  cases step with
  | forward step =>
      exact step.alphaExtension.included
  | retainedFailure facts =>
      intro pair present
      simpa [ResolverPhaseState.alpha, ProductPhaseState.alpha,
        RetainedFailureSuccessor.after,
        PostFailurePayloadState.ofAgreement] using present
  | retainedActivation facts =>
      intro pair present
      simpa [ResolverPhaseState.alpha, ProductPhaseState.alpha,
        RetainedActivationSuccessor.after,
        RetainedActivationSuccessor.afterCarrier,
        ActivePayloadState.ofAgreement] using
        facts.alphaIncluded pair present

/-- Alpha chronology follows the transition-kind-specific law.  In
particular this theorem exposes, rather than erases, the historical allocation
floors used by retained activation. -/
theorem alphaEvolution
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kind : ResolverTransitionKind} {before after : ResolverPhaseState}
    (step : ResolverCertifiedTransition prog gt kind before after) :
    kind.AlphaEvolution before after := by
  cases step with
  | forward step =>
      simpa [ResolverTransitionKind.AlphaEvolution,
        ResolverPhaseState.alpha, ResolverPhaseState.session,
        ResolverPhaseState.openConf] using step.alphaExtension
  | retainedFailure facts =>
      rfl
  | @retainedActivation before facts =>
      refine ⟨?_, before.selectedReferenceFloor_le_current,
        before.selectedExecutableFloor_le_current⟩
      simpa [ResolverTransitionKind.AlphaEvolution,
        ResolverPhaseState.alpha, RetainedActivationSuccessor.after,
        RetainedActivationSuccessor.afterCarrier,
        ActivePayloadState.ofAgreement, ProductPhaseState.alpha] using
        facts.extension

end ResolverCertifiedTransition

/-! ## Exact resolver prefixes -/

namespace ResolverTransitionSchedule

def sourceCost : List ResolverTransitionKind → Nat
  | [] => 0
  | kind :: kinds => kind.sourceCost + sourceCost kinds

def sourceEvents : List ResolverTransitionKind → List Observation
  | [] => []
  | kind :: kinds => kind.sourceEvents ++ sourceEvents kinds

def fineCost : List ResolverTransitionKind → Nat
  | [] => 0
  | kind :: kinds => kind.fineCost + fineCost kinds

/-- Exact chronological representative evolution, retaining every literal
midpoint at which extension or rollback was certified. -/
def RepresentativeEvolution :
    List ResolverTransitionKind → ResolverPhaseState →
      ResolverPhaseState → Prop
  | [], before, after => after = before
  | kind :: kinds, before, after =>
      ∃ middle,
        kind.RepresentativeEvolution before middle ∧
          RepresentativeEvolution kinds middle after

/-- Chronological alpha evolution retains each transition's literal midpoint
and therefore never tries to compose a historical retry allocation as though
it had occurred above a later current high-water. -/
def AlphaEvolution :
    List ResolverTransitionKind → ResolverPhaseState →
      ResolverPhaseState → Prop
  | [], before, after => after = before
  | kind :: kinds, before, after =>
      ∃ middle,
        kind.AlphaEvolution before middle ∧
          AlphaEvolution kinds middle after

end ResolverTransitionSchedule

/-- Proof-relevant finite resolver prefix.  The failure midpoint is the same
dependent state consumed by activation; no endpoint-compatible snapshot can
be substituted between the two constructors. -/
inductive ResolverCertifiedPrefix
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable) :
    List ResolverTransitionKind → ResolverPhaseState →
      ResolverPhaseState → Type where
  | nil (state : ResolverPhaseState) :
      ResolverCertifiedPrefix prog gt [] state state
  | cons
      {kind : ResolverTransitionKind}
      {kinds : List ResolverTransitionKind}
      {before middle after : ResolverPhaseState}
      (head : ResolverCertifiedTransition prog gt kind before middle)
      (tail : ResolverCertifiedPrefix prog gt kinds middle after) :
      ResolverCertifiedPrefix prog gt (kind :: kinds) before after

namespace ResolverCertifiedPrefix

/-- Exact independent source execution of the resolver prefix. -/
theorem sourceSteps
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List ResolverTransitionKind}
    {before after : ResolverPhaseState}
    (run : ResolverCertifiedPrefix prog gt kinds before after) :
    StepsN (ResolverTransitionSchedule.sourceCost kinds) before.sourceState
      (ResolverTransitionSchedule.sourceEvents kinds) after.sourceState := by
  induction run with
  | nil state => exact StepsN.zero state.sourceState
  | cons head tail ih =>
      simpa [ResolverTransitionSchedule.sourceCost,
        ResolverTransitionSchedule.sourceEvents] using
        StepsN.trans head.sourceSteps ih

/-- Exact fine executable execution of the same resolver prefix. -/
theorem fineSteps
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List ResolverTransitionKind}
    {before after : ResolverPhaseState}
    (run : ResolverCertifiedPrefix prog gt kinds before after) :
    DemandDrivenCallStep.StepsN prog gt
      (ResolverTransitionSchedule.fineCost kinds) before.fineState
      after.fineState := by
  induction run with
  | nil state => exact DemandDrivenCallStep.StepsN.zero state.fineState
  | cons head tail ih =>
      simpa [ResolverTransitionSchedule.fineCost] using
        DemandDrivenCallStep.StepsN.trans head.fineSteps ih

/-- Every source allocator high-water advances through a mixed prefix. -/
theorem sessionHighWaters
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List ResolverTransitionKind}
    {before after : ResolverPhaseState}
    (run : ResolverCertifiedPrefix prog gt kinds before after) :
    SessionHighWatersExtend before.session after.session := by
  induction run with
  | nil state => exact SessionHighWatersExtend.refl state.session
  | cons head tail ih =>
      exact SessionHighWatersExtend.trans head.sessionHighWaters ih

/-- The executable high-water cannot roll back through failure/retry. -/
theorem executableCounter_mono
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List ResolverTransitionKind}
    {before after : ResolverPhaseState}
    (run : ResolverCertifiedPrefix prog gt kinds before after) :
    before.openConf.persistent.counter ≤ after.openConf.persistent.counter := by
  induction run with
  | nil state => exact Nat.le_refl _
  | cons head tail ih =>
      exact Nat.le_trans head.executableCounter_mono ih

/-- Alpha membership is never lost across rollback and retry. -/
theorem alphaIncluded
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List ResolverTransitionKind}
    {before after : ResolverPhaseState}
    (run : ResolverCertifiedPrefix prog gt kinds before after) :
    ∀ pair, pair ∈ before.alpha → pair ∈ after.alpha := by
  induction run with
  | nil state =>
      intro pair present
      exact present
  | cons head tail ih =>
      intro pair present
      exact ih pair (head.alphaIncluded pair present)

/-- A mixed prefix preserves the exact kind-indexed alpha chronology at every
dependent midpoint. -/
theorem alphaEvolution
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List ResolverTransitionKind}
    {before after : ResolverPhaseState}
    (run : ResolverCertifiedPrefix prog gt kinds before after) :
    ResolverTransitionSchedule.AlphaEvolution kinds before after := by
  induction run with
  | nil state => rfl
  | @cons kind kinds before middle after head tail ih =>
      exact ⟨middle, head.alphaEvolution, ih⟩

/-- Mixed prefixes compose the kind-indexed extension/rebase law rather than
asserting the false global extension equation. -/
theorem representativeEvolution
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List ResolverTransitionKind}
    {before after : ResolverPhaseState}
    (run : ResolverCertifiedPrefix prog gt kinds before after) :
    ResolverTransitionSchedule.RepresentativeEvolution kinds before after := by
  induction run with
  | nil state => rfl
  | @cons kind kinds before middle after head tail ih =>
      exact ⟨middle, head.representativeEvolution, ih⟩

/-- Chronological list of the literal dependent phase states. -/
def states
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List ResolverTransitionKind}
    {before after : ResolverPhaseState} :
    ResolverCertifiedPrefix prog gt kinds before after →
      List ResolverPhaseState
  | .nil state => [state]
  | .cons _ tail => before :: states tail

@[simp] theorem states_length
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {kinds : List ResolverTransitionKind}
    {before after : ResolverPhaseState}
    (run : ResolverCertifiedPrefix prog gt kinds before after) :
    run.states.length = kinds.length + 1 := by
  induction run with
  | nil state => rfl
  | cons head tail ih =>
      simp only [states, List.length_cons, List.length, ih]

/-- The canonical retry segment shares the literal post-failure midpoint.
The activation package is indexed by `failure.after`, so a snapshot from a
different cursor cannot be inserted between these constructors. -/
def failureThenActivation
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeActivePayloadState}
    (failure : RetainedFailureSuccessor prog gt before)
    (activation : RetainedActivationSuccessor prog gt failure.after) :
    ResolverCertifiedPrefix prog gt
      [.retainedFailure failure.count, .retainedActivation]
      (.ordinary (.active before))
      (.ordinary (.active activation.after)) :=
  .cons (.retainedFailure failure)
    (.cons (.retainedActivation activation)
      (.nil (.ordinary (.active activation.after))))

@[simp] theorem failureThenActivation_states
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeActivePayloadState}
    (failure : RetainedFailureSuccessor prog gt before)
    (activation : RetainedActivationSuccessor prog gt failure.after) :
    (failureThenActivation failure activation).states =
      [.ordinary (.active before), .postFailure failure.after,
        .ordinary (.active activation.after)] := rfl

/-- Reactivation prepends its selected-head residual to the representative
stored by the exact retained snapshot. -/
theorem failureThenActivation_representative_exact
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeActivePayloadState}
    (failure : RetainedFailureSuccessor prog gt before)
    (activation : RetainedActivationSuccessor prog gt failure.after) :
    activation.after.representative =
      activation.flattened ++ failure.after.representative := by
  rfl

/-- Genuine rollback discriminator over a certified retained-failure edge.

If a failed branch carries any residual binding while its retained snapshot
is empty, exact rebasing cannot possibly be represented as prepending an
extension to the failed branch.  Thus the additive failure phase is
semantically necessary; it is not merely an alternative state encoding. -/
theorem retainedFailure_not_representativeExtension_of_empty_snapshot
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeActivePayloadState}
    (failure : RetainedFailureSuccessor prog gt before)
    (beforeNonempty : before.representative ≠ [])
    (snapshotEmpty : failure.after.representative = []) :
    ¬ ∃ extension : TreeSubstitution,
        failure.after.representative = extension ++ before.representative := by
  rintro ⟨extension, exactExtension⟩
  rw [snapshotEmpty] at exactExtension
  have beforeEmpty : before.representative = [] := by
    apply List.eq_nil_of_length_eq_zero
    have lengths := congrArg List.length exactExtension
    simp only [List.length_nil, List.length_append] at lengths
    omega
  exact beforeNonempty beforeEmpty

end ResolverCertifiedPrefix

end PLeaTTa.PrologFailureRebasePrefixBridge
