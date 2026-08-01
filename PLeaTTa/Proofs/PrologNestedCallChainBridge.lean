-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologNestedCallChainBridge
Purpose: Compose proof-relevant nested-call payload handoffs without allowing
  successive depths to choose unrelated zipper witnesses.
Trusted boundary: none
Main exports:
  SourceControlResourcePayloadContextAgrees.cellCount_cons_of_tail_handoff,
  SourceControlResourcePayloadContextAgrees.two_nested_payload_pushes_exact
-/
import PLeaTTa.Proofs.PrologNestedCallEntryPayloadBridge

namespace PLeaTTa.PrologNestedCallChainBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologBodyFailureResourceTransitionBridge
open PrologAlphaFreshFrontierBridge
open PrologCallStepBridge
open PrologControlSegmentSpineBridge
open PrologCurrentSessionPayloadBridge
open PrologCurrentSessionPayloadTransitionBridge
open PrologMguComposition
open PrologNestedCallEntryPayloadBridge
open PrologPrefilterScanBridge
open PrologProductResourceContextBridge
open PrologProductResourceTransitionBridge
open PrologRepresentativeCallFrontierBridge
open PrologRepresentativeProductActivationBridge
open PrologRepresentativeStepActivationBridge
open PrologRecursiveCallPayloadBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
open PrologSourceProductContextBridge
open PrologStateBridge

/-! ## Proof-relevant coupled active states -/

/-- The runtime identity of one retained payload cell, erasing only logical
proof annotations that may grow under alpha transport.

The segment, executable resource, prepared cursor, and all three scope
indices remain visible.  Consequently this spine can witness exact stack
extension without comparing dependent proof terms. -/
structure PayloadCellIdentity where
  currentBarrier : Nat
  currentScope : CutScopeId
  nextScope : CutScopeId
  outerScope : CutScopeId
  segment : ControlSegment
  resource : RetainedAlternativeSegment
  cursor : PreparedCursor

namespace SourceControlResourcePayloadContextAgrees

/-- Erase one dependent payload zipper to its exact ordered runtime cells. -/
def cellIdentities
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext} :
    SourceControlResourcePayloadContextAgrees alpha support qterm currentBarrier
        segments resources inner context outer →
      List PayloadCellIdentity
  | .nil _ _ => []
  | .cons currentBarrier currentScope nextScope outerScope segment _segments
      resource _resources cursor _context _segmentAgrees _resourceRest
      _resourceQuery _resourceBarrier _resourceOwnership _snapshot
      outerAgrees =>
      { currentBarrier := currentBarrier
        currentScope := currentScope
        nextScope := nextScope
        outerScope := outerScope
        segment := segment
        resource := resource
        cursor := cursor } ::
        cellIdentities outerAgrees

/-- Alpha transport changes payload proofs but preserves every runtime cell
identity and its order. -/
theorem cellIdentities_extendAbove
    {smaller larger support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {referenceFloor executableFloor : Nat}
    (extension :
      AlphaExtendsAbove smaller larger referenceFloor executableFloor)
    (agreement :
      SourceControlResourcePayloadContextAgrees smaller support qterm
        currentBarrier segments resources inner context outer)
    (below : endpointsBelow agreement referenceFloor executableFloor) :
    cellIdentities
        (SourceControlResourcePayloadContextAgrees.extendAbove extension
          agreement below) =
      cellIdentities agreement := by
  induction agreement with
  | nil => rfl
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      simp only [SourceControlResourcePayloadContextAgrees.extendAbove,
        cellIdentities]
      rw [inductionHypothesis]

/-- An exact alpha handoff preserves the complete runtime-cell spine. -/
theorem ExtendsAboveAt.cellIdentities_eq
    {smaller larger support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {referenceFloor executableFloor : Nat}
    {extension :
      AlphaExtendsAbove smaller larger referenceFloor executableFloor}
    {before :
      SourceControlResourcePayloadContextAgrees smaller support qterm
        currentBarrier segments resources inner context outer}
    {after :
      SourceControlResourcePayloadContextAgrees larger support qterm
        currentBarrier segments resources inner context outer}
    (handoff :
      ExtendsAboveAt referenceFloor executableFloor extension before after) :
    cellIdentities after = cellIdentities before := by
  calc
    cellIdentities after =
        cellIdentities
          (SourceControlResourcePayloadContextAgrees.extendAbove extension
            before handoff.below) :=
      congrArg cellIdentities handoff.exact
    _ = cellIdentities before :=
      cellIdentities_extendAbove extension before handoff.below

/-- The erased runtime-cell spine and the dependent zipper have the same
length. -/
theorem cellIdentities_length_eq_cellCount
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat} {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer) :
    (cellIdentities agreement).length =
      ActiveProductPayloadContext.cellCount agreement := by
  induction agreement with
  | nil => rfl
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees
      inductionHypothesis =>
      simp only [cellIdentities, ActiveProductPayloadContext.cellCount,
        List.length_cons]
      omega

end SourceControlResourcePayloadContextAgrees

/-- All data indices of one active payload-coupled local-product state.

The dependent payload proof is deliberately not stored here.  It lives in
`ActivePayloadState`, so two push certificates can share one literal middle
carrier without relying on equality between proof objects. -/
structure ActivePayloadIndex where
  freshFrontier : FreshFrontierRelation
  alpha : List (LogicVar × String)
  support : List (LogicVar × String)
  canonical : TreeSubstitution
  referenceBase : Substitution
  opened : OpenedCall
  session : Session
  pending : DemandDrivenCallStep.PendingCall
  finish : PreparedCursor
  branch : ClauseBranch
  branchTail : List ClauseBranch
  altTail : List PLeaTTa.Alt
  bodyBarrier : Nat
  callerBarrier : Nat
  bodyReferences : List PeTTaSpec.PrologCore.Goal
  bodyExecutables : List PLeaTTa.Goal
  callerReferences : List PeTTaSpec.PrologCore.Goal
  callerExecutables : List PLeaTTa.Goal
  outer : List ControlSegment
  current : Substitution
  runtime : Subst
  qterm : Atom
  active : RetainedAlternativeSegment
  resources : List RetainedAlternativeSegment
  callerScope : CutScopeId
  outerScope : CutScopeId
  context : ActiveProductContext
  baseAlts : List PLeaTTa.Alt
  source : Search
  openConf : OpenConf

namespace ActivePayloadIndex

abbrev PayloadContext (index : ActivePayloadIndex) :=
  ActiveProductPayloadContext index.alpha index.support index.qterm
    index.opened index.finish index.branch index.branchTail index.bodyBarrier
    index.callerBarrier index.callerReferences index.callerExecutables
    index.outer index.active index.resources index.callerScope index.outerScope
    index.context

abbrev Relates (index : ActivePayloadIndex)
    (payloadContext : index.PayloadContext) :=
  SpinedActiveProductPayloadResourceRelatesAt index.freshFrontier index.alpha
    index.support index.canonical index.referenceBase index.opened index.session
    index.pending index.finish index.branch index.branchTail index.altTail
    index.bodyBarrier index.callerBarrier index.bodyReferences
    index.bodyExecutables index.callerReferences index.callerExecutables
    index.outer index.current index.runtime index.qterm index.active
    index.resources index.callerScope index.outerScope index.context
    index.baseAlts index.source index.openConf payloadContext

end ActivePayloadIndex

/-- One proof-relevant carrier jointly owning a source state, fine executable
state, and exact retained payload zipper. -/
structure ActivePayloadState where
  index : ActivePayloadIndex
  payloadContext : index.PayloadContext
  agreement : index.Relates payloadContext

namespace ActivePayloadState

/-- Package an existing exact active relation without weakening any index. -/
def ofAgreement
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {session : Session}
    {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {bodyReferences : List PeTTaSpec.PrologCore.Goal}
    {bodyExecutables : List PLeaTTa.Goal}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {current : Substitution} {runtime : Subst} {qterm : Atom}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext} {baseAlts : List PLeaTTa.Alt}
    {source : Search} {openConf : OpenConf}
    {payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish branch
        branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context}
    (agreement :
      SpinedActiveProductPayloadResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened session pending finish branch branchTail
        altTail bodyBarrier callerBarrier bodyReferences bodyExecutables
        callerReferences callerExecutables outer current runtime qterm active
        resources callerScope outerScope context baseAlts source openConf
        payloadContext) :
    ActivePayloadState :=
  { index :=
      { freshFrontier := freshFrontier
        alpha := alpha
        support := support
        canonical := canonical
        referenceBase := referenceBase
        opened := opened
        session := session
        pending := pending
        finish := finish
        branch := branch
        branchTail := branchTail
        altTail := altTail
        bodyBarrier := bodyBarrier
        callerBarrier := callerBarrier
        bodyReferences := bodyReferences
        bodyExecutables := bodyExecutables
        callerReferences := callerReferences
        callerExecutables := callerExecutables
        outer := outer
        current := current
        runtime := runtime
        qterm := qterm
        active := active
        resources := resources
        callerScope := callerScope
        outerScope := outerScope
        context := context
        baseAlts := baseAlts
        source := source
        openConf := openConf }
    payloadContext := payloadContext
    agreement := agreement }

def sourceState (state : ActivePayloadState) : State :=
  .running state.index.session state.index.source

def fineState (state : ActivePayloadState) : DemandDrivenCallStep.FineConf :=
  .ready state.index.openConf

def cellIdentities (state : ActivePayloadState) : List PayloadCellIdentity :=
  SourceControlResourcePayloadContextAgrees.cellIdentities
    state.payloadContext

def cellCount (state : ActivePayloadState) : Nat :=
  ActiveProductPayloadContext.cellCount state.payloadContext

def outerPayload (state : ActivePayloadState) :=
  ActiveProductPayloadContext.outerPayload state.payloadContext

theorem cellIdentities_length (state : ActivePayloadState) :
    state.cellIdentities.length = state.cellCount :=
  SourceControlResourcePayloadContextAgrees.cellIdentities_length_eq_cellCount
    state.payloadContext

end ActivePayloadState

/-- The successor's exact dependent outer payload is the canonical alpha
transport of the predecessor payload.

`HEq` is load-bearing here: the successor's retained segments, resources,
scopes, and context are data indices of its outer payload.  Heterogeneous
equality therefore forces those indices to be the predecessor's exact shape
while allowing the alpha proof index to grow. -/
def ExactPayloadHandoff
    (before after : ActivePayloadState) : Prop :=
  ∃ referenceFloor executableFloor : Nat,
    ∃ extension :
        AlphaExtendsAbove before.index.alpha after.index.alpha
          referenceFloor executableFloor,
      ∃ below :
          SourceControlResourcePayloadContextAgrees.endpointsBelow
            before.payloadContext referenceFloor executableFloor,
        HEq after.outerPayload
          (SourceControlResourcePayloadContextAgrees.extendAbove extension
            before.payloadContext below)

namespace ExactPayloadHandoff

/-- The existential handoff's target alpha is definitionally the successor
carrier's alpha, so inclusion is directly consumable without recovering a
type equality from `HEq`. -/
theorem alphaIncluded
    {before after : ActivePayloadState}
    (handoff : ExactPayloadHandoff before after) :
    ∀ pair, pair ∈ before.index.alpha → pair ∈ after.index.alpha := by
  rcases handoff with
    ⟨referenceFloor, executableFloor, extension, below, exact⟩
  exact extension.included

end ExactPayloadHandoff

/-- One exact nested local-call push, with all three evolving objects indexed
by the same predecessor and successor carriers.

It is impossible to supply source steps from one run, fine steps from another,
and a payload handoff from a third: every field is indexed by `before` and
`after`. -/
structure NestedCallPushCertificate
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (rejects : Nat) (request : CallRequest)
    (before after : ActivePayloadState) : Prop where
  sourceSteps :
    StepsN (rejects + 2) before.sourceState [.opened request]
      after.sourceState
  fineSteps :
    DemandDrivenCallStep.StepsN prog gt 3 before.fineState after.fineState
  exactPayload : ExactPayloadHandoff before after
  payloadCells :
    ∃ head : PayloadCellIdentity,
      after.cellIdentities = head :: before.cellIdentities

namespace SourceControlResourcePayloadContextAgrees

/-- Prepending one concrete source cursor/resource cell above an exact alpha
handoff increases the proof-relevant zipper by exactly one cell.

The `after` indices are the literal source frame installed by a nested call.
The predecessor is related to `tail after`, not to an independently selected
zipper of the same shape. -/
theorem cellCount_cons_of_tail_handoff
    {smaller larger support : List (LogicVar × String)} {qterm : Atom}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {cursor : PreparedCursor}
    {inner currentScope outer : CutScopeId}
    {context : ActiveProductContext}
    {nextBarrier referenceFloor executableFloor : Nat}
    {extension :
      AlphaExtendsAbove smaller larger referenceFloor executableFloor}
    (before :
      SourceControlResourcePayloadContextAgrees smaller support qterm
        segment.barrier segments resources inner context outer)
    (after :
      SourceControlResourcePayloadContextAgrees larger support qterm
        nextBarrier (segment :: segments) (resource :: resources) currentScope
        ({ callerScope := inner
           predicateScope := currentScope
           retained := .clauses currentScope cursor
           callerRest := segment.references } ::
         context)
        outer)
    (handoff :
      ExtendsAboveAt referenceFloor executableFloor extension before
        (tail after)) :
    ActiveProductPayloadContext.cellCount after =
      ActiveProductPayloadContext.cellCount before + 1 := by
  have afterCount :
      ActiveProductPayloadContext.cellCount after =
        ActiveProductPayloadContext.cellCount (tail after) + 1 := by
    cases after
    rfl
  rw [afterCount, handoff.cellCount_eq]

/-- The same handoff exposes the exact new runtime cell above the literal
predecessor spine.  Alpha transport is erased only after its equality has
been consumed, so no shape-compatible payload can be substituted. -/
theorem cellIdentities_cons_of_tail_handoff
    {smaller larger support : List (LogicVar × String)} {qterm : Atom}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {cursor : PreparedCursor}
    {inner currentScope outer : CutScopeId}
    {context : ActiveProductContext}
    {nextBarrier referenceFloor executableFloor : Nat}
    {extension :
      AlphaExtendsAbove smaller larger referenceFloor executableFloor}
    (before :
      SourceControlResourcePayloadContextAgrees smaller support qterm
        segment.barrier segments resources inner context outer)
    (after :
      SourceControlResourcePayloadContextAgrees larger support qterm
        nextBarrier (segment :: segments) (resource :: resources) currentScope
        ({ callerScope := inner
           predicateScope := currentScope
           retained := .clauses currentScope cursor
           callerRest := segment.references } ::
         context)
        outer)
    (handoff :
      ExtendsAboveAt referenceFloor executableFloor extension before
        (tail after)) :
    ∃ head : PayloadCellIdentity,
      cellIdentities after = head :: cellIdentities before := by
  cases after with
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership snapshot outerAgrees =>
      refine
        ⟨{ currentBarrier := nextBarrier
           currentScope := currentScope
           nextScope := inner
           outerScope := outer
           segment := segment
           resource := resource
           cursor := cursor }, ?_⟩
      have outerCells :
          cellIdentities outerAgrees = cellIdentities before := by
        simpa [SourceControlResourcePayloadContextAgrees.tail] using
          (PLeaTTa.PrologNestedCallChainBridge.SourceControlResourcePayloadContextAgrees.ExtendsAboveAt.cellIdentities_eq
            handoff)
      simp only [cellIdentities]
      exact congrArg
        (fun cells =>
          ({ currentBarrier := nextBarrier
             currentScope := currentScope
             nextScope := inner
             outerScope := outer
             segment := segment
             resource := resource
             cursor := cursor } : PayloadCellIdentity) :: cells)
        outerCells

/-- Two nested calls add two exact payload cells while retaining the complete
depth-one payload as the second successor's literal tail.

The second handoff is indexed by `first`, not merely by the original `base`.
Consequently a depth-two implementation that truncates the intervening caller
cell would force equal payload counts that this theorem refutes. -/
theorem two_nested_payload_pushes_exact
    {alpha0 alpha1 alpha2 support : List (LogicVar × String)}
    {qterm : Atom}
    {firstSegment : ControlSegment} {segments : List ControlSegment}
    {firstResource secondResource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {firstCursor secondCursor : PreparedCursor}
    {baseScope firstScope secondScope outer : CutScopeId}
    {context : ActiveProductContext}
    {secondReferences : List PeTTaSpec.PrologCore.Goal}
    {secondExecutables : List PLeaTTa.Goal}
    {firstBarrier secondBarrier : Nat}
    {firstReferenceFloor firstExecutableFloor : Nat}
    {secondReferenceFloor secondExecutableFloor : Nat}
    {firstExtension :
      AlphaExtendsAbove alpha0 alpha1 firstReferenceFloor
        firstExecutableFloor}
    {secondExtension :
      AlphaExtendsAbove alpha1 alpha2 secondReferenceFloor
        secondExecutableFloor}
    (base :
      SourceControlResourcePayloadContextAgrees alpha0 support qterm
        firstSegment.barrier segments resources baseScope context outer)
    (first :
      SourceControlResourcePayloadContextAgrees alpha1 support qterm
        firstBarrier (firstSegment :: segments)
        (firstResource :: resources) firstScope
        ({ callerScope := baseScope
           predicateScope := firstScope
           retained := .clauses firstScope firstCursor
           callerRest := firstSegment.references } ::
         context)
        outer)
    (second :
      SourceControlResourcePayloadContextAgrees alpha2 support qterm
        secondBarrier
        ({ barrier := firstBarrier
           references := secondReferences
           executables := secondExecutables } ::
         firstSegment :: segments)
        (secondResource :: firstResource :: resources) secondScope
        ({ callerScope := firstScope
           predicateScope := secondScope
           retained := .clauses secondScope secondCursor
           callerRest := secondReferences } ::
         { callerScope := baseScope
           predicateScope := firstScope
           retained := .clauses firstScope firstCursor
           callerRest := firstSegment.references } ::
         context)
        outer)
    (firstHandoff :
      ExtendsAboveAt firstReferenceFloor firstExecutableFloor firstExtension
        base (tail first))
    (secondHandoff :
      ExtendsAboveAt secondReferenceFloor secondExecutableFloor secondExtension
        first (tail second)) :
    ActiveProductPayloadContext.cellCount first =
        ActiveProductPayloadContext.cellCount base + 1 ∧
      ActiveProductPayloadContext.cellCount (tail second) =
        ActiveProductPayloadContext.cellCount base + 1 ∧
      ActiveProductPayloadContext.cellCount second =
        ActiveProductPayloadContext.cellCount base + 2 ∧
      ActiveProductPayloadContext.cellCount (tail second) ≠
        ActiveProductPayloadContext.cellCount base := by
  have firstCount :
      ActiveProductPayloadContext.cellCount first =
        ActiveProductPayloadContext.cellCount base + 1 :=
    cellCount_cons_of_tail_handoff base first firstHandoff
  have secondTailCount :
      ActiveProductPayloadContext.cellCount (tail second) =
        ActiveProductPayloadContext.cellCount first :=
    secondHandoff.cellCount_eq
  have secondCount :
      ActiveProductPayloadContext.cellCount second =
        ActiveProductPayloadContext.cellCount first + 1 :=
    cellCount_cons_of_tail_handoff first second secondHandoff
  refine ⟨firstCount, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

end SourceControlResourcePayloadContextAgrees

/-! ## One exact operational nested-call push -/

/-- One call-headed active payload state reaches the exact next active payload
state through a divergence-sensitive finite prefix.

The source pays one observed call-open transition, the supplied exact number
of silent conservative prefilter rejections, and one silent clause activation.
The fine executable pays exactly `callEnter`, `callPull`, and the selected
head equality.  The successor relation, alpha handoff, and `+1` payload count
are all produced internally by the nested activation theorem.

[SPEC metta.pl:251-256] -/
theorem
    SpinedRepresentativeProductActivation.spinedNestedProductPayloadPrefix
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {callerOpened : OpenedCall} {session : Session}
    {callerPending : DemandDrivenCallStep.PendingCall}
    {callerFinish : PreparedCursor} {callerBranch : ClauseBranch}
    {callerBranchTail : List ClauseBranch}
    {callerAltTail : List PLeaTTa.Alt}
    {currentBodyBarrier callerBarrier : Nat}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {current : Substitution} {runtime : Subst} {qterm : Atom}
    {currentActive : RetainedAlternativeSegment}
    {currentResources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {currentContext : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {currentSource : Search} {state : OpenConf}
    {predicate : String} {referencePayload : List Term}
    {nestedReferenceRest : List PeTTaSpec.PrologCore.Goal}
    {argsv args : List Atom} {res : Atom}
    {nestedExecutableRest : List PLeaTTa.Goal}
    {nestedPending : DemandDrivenCallStep.PendingCall}
    {nestedFinish : PreparedCursor}
    {nestedBranch : ClauseBranch} {nestedClause : PLeaTTa.Clause}
    {nestedBranchTail : List ClauseBranch}
    {nestedClauseTail : List PLeaTTa.Clause}
    {nestedAltTail : List PLeaTTa.Alt} {copied : PLeaTTa.Clause}
    {nestedBodyBarrier : Nat}
    {independentResult : Substitution}
    {representative : TreeSubstitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattenedRepresentative : TreeSubstitution}
    {installed : Subst}
    {count : Nat}
    {currentPayloadContext :
      ActiveProductPayloadContext alpha support qterm callerOpened callerFinish
        callerBranch callerBranchTail currentBodyBarrier callerBarrier
        callerReferences callerExecutables outer currentActive currentResources
        callerScope outerScope currentContext}
    (currentAgreement :
      SpinedActiveProductPayloadResourceRelatesAt freshFrontier alpha support
        canonical referenceBase callerOpened session callerPending callerFinish
        callerBranch callerBranchTail callerAltTail currentBodyBarrier
        callerBarrier
        (.call predicate referencePayload :: nestedReferenceRest)
        (.call predicate args res :: nestedExecutableRest)
        callerReferences callerExecutables outer current runtime qterm
        currentActive currentResources callerScope outerScope currentContext
        baseAlts currentSource state currentPayloadContext)
    (entry :
      CallEntryBankRelates
        (openedFor session predicate referencePayload current)
        state nestedPending argsv args res
        (nestedExecutableRest ++
          flattenExecutables
            ({ barrier := callerBarrier
               references := callerReferences
               executables := callerExecutables } :: outer))
        runtime qterm nestedBodyBarrier state.persistent.counter)
    (frontier :
      RepresentativeRetainedCallFrontier alpha
        (openedFor session predicate referencePayload current)
        state nestedPending nestedFinish nestedBranch nestedClause
        nestedBranchTail nestedClauseTail nestedAltTail copied argsv args res
        (nestedExecutableRest ++
          flattenExecutables
            ({ barrier := callerBarrier
               references := callerReferences
               executables := callerExecutables } :: outer))
        runtime qterm nestedBodyBarrier state.persistent.counter)
    (pulls :
      RejectedPullsN count
        (openedFor session predicate referencePayload current).cursor
        nestedFinish)
    (oldCumulative :
      AlphaCumulativeResidualVariantAgreesOnWith alpha support canonical
        referenceBase runtime representative)
    (materializedAtOpen :
      MaterializedCallAgreesWith alpha current referencePayload
        (args.map (PLeaTTa.subst runtime))
        (PLeaTTa.subst runtime res) representative referenceBase)
    (queryReferenceBelow :
      GeneratedBelow nestedFinish.reservationStart (alpha.map Prod.fst))
    (activation :
      SpinedRepresentativeProductActivation prog gt alpha support canonical
        referenceBase
        (openedFor session predicate referencePayload current)
        nestedPending nestedFinish nestedBranch nestedBranchTail nestedAltTail
        copied nestedReferenceRest nestedExecutableRest
        ({ barrier := callerBarrier
           references := callerReferences
           executables := callerExecutables } :: outer)
        qterm nestedBodyBarrier currentBodyBarrier state.persistent.counter
        callerOpened.scope independentResult representative nextAlpha
        sourceCanonical flattenedRepresentative installed)
    (notThrow : ¬ BuiltinThrowCall predicate referencePayload)
    (notDatabase :
      DatabaseActions.recognizeDatabaseAction predicate referencePayload =
        none)
    (fineEntry :
      DemandDrivenCallStep.Step prog gt (.ready state)
        (.callPending nestedPending)) :
    ∃ nestedActive : RetainedAlternativeSegment,
      ∃ nestedPayloadContext :
          ActiveProductPayloadContext nextAlpha support qterm
            (openedFor session predicate referencePayload current)
            nestedFinish nestedBranch nestedBranchTail nestedBodyBarrier
            currentBodyBarrier nestedReferenceRest nestedExecutableRest
            ({ barrier := callerBarrier
               references := callerReferences
               executables := callerExecutables } :: outer)
            nestedActive (currentActive :: currentResources)
            callerOpened.scope outerScope
            ({ callerScope := callerScope
               predicateScope := callerOpened.scope
               retained :=
                 .clauses callerOpened.scope
                   (callerFinish.advance callerBranch callerBranchTail)
               callerRest := callerReferences } :: currentContext),
        StepsN (count + 2) (.running session currentSource)
          [.opened (requestFor predicate referencePayload current)]
          (.running
            (openedFor session predicate referencePayload current).session
            (ActiveProductContext.plug
              ({ callerScope := callerScope
                 predicateScope := callerOpened.scope
                 retained :=
                   .clauses callerOpened.scope
                     (callerFinish.advance callerBranch callerBranchTail)
                 callerRest := callerReferences } :: currentContext)
              (activatedSourceProduct callerOpened.scope
                (openedFor session predicate referencePayload current)
                nestedFinish nestedBranch nestedBranchTail independentResult
                nestedReferenceRest))) ∧
          DemandDrivenCallStep.StepsN prog gt 3 (.ready state)
            (.ready
              (activatedOpenSuccessor nestedPending copied
                (nestedExecutableRest ++
                  flattenExecutables
                    ({ barrier := callerBarrier
                       references := callerReferences
                       executables := callerExecutables } :: outer))
                qterm installed)) ∧
          ∃ nestedAgreement :
            SpinedActiveProductPayloadResourceRelatesAt
            (AlphaFreshFrontier nextAlpha) nextAlpha support
            (sourceCanonical ++ canonical) referenceBase
            (openedFor session predicate referencePayload current)
            (openedFor session predicate referencePayload current).session
            nestedPending nestedFinish nestedBranch nestedBranchTail
            nestedAltTail nestedBodyBarrier currentBodyBarrier nestedBranch.body
            copied.body nestedReferenceRest nestedExecutableRest
            ({ barrier := callerBarrier
               references := callerReferences
               executables := callerExecutables } :: outer)
            independentResult
            (PLeaTTa.trimFor
              (copied.body ++
                (nestedExecutableRest ++
                  flattenExecutables
                    ({ barrier := callerBarrier
                       references := callerReferences
                       executables := callerExecutables } :: outer)))
              qterm installed)
            qterm nestedActive (currentActive :: currentResources)
            callerOpened.scope outerScope
            ({ callerScope := callerScope
               predicateScope := callerOpened.scope
               retained :=
                 .clauses callerOpened.scope
                   (callerFinish.advance callerBranch callerBranchTail)
               callerRest := callerReferences } :: currentContext)
            baseAlts
            (ActiveProductContext.plug
              ({ callerScope := callerScope
                 predicateScope := callerOpened.scope
                 retained :=
                   .clauses callerOpened.scope
                     (callerFinish.advance callerBranch callerBranchTail)
                 callerRest := callerReferences } :: currentContext)
              (activatedSourceProduct callerOpened.scope
                (openedFor session predicate referencePayload current)
                nestedFinish nestedBranch nestedBranchTail independentResult
                nestedReferenceRest))
            (activatedOpenSuccessor nestedPending copied
              (nestedExecutableRest ++
                flattenExecutables
                  ({ barrier := callerBarrier
                     references := callerReferences
                     executables := callerExecutables } :: outer))
              qterm installed)
            nestedPayloadContext,
          ExtendsAboveAt nestedBranch.firstFresh state.persistent.counter
            activation.alphaExtension currentPayloadContext
            (SourceControlResourcePayloadContextAgrees.tail
              nestedPayloadContext) ∧
          ActiveProductPayloadContext.cellCount nestedPayloadContext =
              ActiveProductPayloadContext.cellCount currentPayloadContext + 1 ∧
          NestedCallPushCertificate prog gt count
            (requestFor predicate referencePayload current)
            (ActivePayloadState.ofAgreement currentAgreement)
            (ActivePayloadState.ofAgreement nestedAgreement) := by
  let nextOpened := openedFor session predicate referencePayload current
  let nestedFrame : ActiveProductFrame :=
    { callerScope := callerScope
      predicateScope := callerOpened.scope
      retained :=
        .clauses callerOpened.scope
          (callerFinish.advance callerBranch callerBranchTail)
      callerRest := callerReferences }
  let nestedContext : ActiveProductContext := nestedFrame :: currentContext
  have sourceEntry :=
    PLeaTTa.PrologNestedCallEntryPayloadBridge.SpinedActiveProductPayloadResourceRelatesAt.sourceCallEntry
      currentAgreement notThrow notDatabase
  have sourceEntryTransition :
      Transition (.running session currentSource)
        [.opened (requestFor predicate referencePayload current)]
        (.running nextOpened.session
          (ActiveProductContext.plug nestedContext
            (sourceProductFrontier callerOpened.scope nextOpened
              nextOpened.cursor nestedReferenceRest))) := by
    exact Transition.ordinary _ _ _ _ _ sourceEntry
  have entrySteps :
      StepsN 1 (.running session currentSource)
        [.opened (requestFor predicate referencePayload current)]
        (.running nextOpened.session
          (ActiveProductContext.plug nestedContext
            (sourceProductFrontier callerOpened.scope nextOpened
              nextOpened.cursor nestedReferenceRest))) := by
    simpa using
      StepsN.succ 0 (.running session currentSource)
        (.running nextOpened.session
          (ActiveProductContext.plug nestedContext
            (sourceProductFrontier callerOpened.scope nextOpened
              nextOpened.cursor nestedReferenceRest)))
        (.running nextOpened.session
          (ActiveProductContext.plug nestedContext
            (sourceProductFrontier callerOpened.scope nextOpened
              nextOpened.cursor nestedReferenceRest)))
        [.opened (requestFor predicate referencePayload current)] []
        sourceEntryTransition (.zero _)
  have rejectedSteps :
      StepsN count
        (.running nextOpened.session
          (ActiveProductContext.plug nestedContext
            (sourceProductFrontier callerOpened.scope nextOpened
              nextOpened.cursor nestedReferenceRest)))
        []
        (.running nextOpened.session
          (ActiveProductContext.plug nestedContext
            (sourceProductFrontier callerOpened.scope nextOpened
              nestedFinish nestedReferenceRest))) := by
    simpa [nextOpened] using
      PrologBodyFailureResourceTransitionBridge.RejectedPullsN.sourceProductContextStepsNAt
        pulls nestedContext callerOpened.scope nextOpened nextOpened.session
          nestedReferenceRest
  have activationRaw :
      RawStep nextOpened.session
        (ActiveProductContext.plug nestedContext
          (sourceProductFrontier callerOpened.scope nextOpened nestedFinish
            nestedReferenceRest))
        [] .none nextOpened.session
        (.running
          (ActiveProductContext.plug nestedContext
            (activatedSourceProduct callerOpened.scope nextOpened nestedFinish
              nestedBranch nestedBranchTail independentResult
              nestedReferenceRest))) := by
    simpa [nextOpened] using activation.sourceStep_throughContext nestedContext
  have activationTransition :
      Transition
        (.running nextOpened.session
          (ActiveProductContext.plug nestedContext
            (sourceProductFrontier callerOpened.scope nextOpened nestedFinish
              nestedReferenceRest)))
        []
        (.running nextOpened.session
          (ActiveProductContext.plug nestedContext
            (activatedSourceProduct callerOpened.scope nextOpened nestedFinish
              nestedBranch nestedBranchTail independentResult
              nestedReferenceRest))) :=
    Transition.ordinary _ _ _ _ _ activationRaw
  have activationSteps :
      StepsN 1
        (.running nextOpened.session
          (ActiveProductContext.plug nestedContext
            (sourceProductFrontier callerOpened.scope nextOpened nestedFinish
              nestedReferenceRest)))
        []
        (.running nextOpened.session
          (ActiveProductContext.plug nestedContext
            (activatedSourceProduct callerOpened.scope nextOpened nestedFinish
              nestedBranch nestedBranchTail independentResult
              nestedReferenceRest))) := by
    simpa using
      StepsN.succ 0 _ _ _ [] [] activationTransition (.zero _)
  have sourceSteps :
      StepsN (count + 2) (.running session currentSource)
        [.opened (requestFor predicate referencePayload current)]
        (.running nextOpened.session
          (ActiveProductContext.plug nestedContext
            (activatedSourceProduct callerOpened.scope nextOpened nestedFinish
              nestedBranch nestedBranchTail independentResult
              nestedReferenceRest))) := by
    have combined := StepsN.trans entrySteps
      (StepsN.trans rejectedSteps activationSteps)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using combined
  have fineSteps :
      DemandDrivenCallStep.StepsN prog gt 3 (.ready state)
        (.ready
          (activatedOpenSuccessor nestedPending copied
            (nestedExecutableRest ++
              flattenExecutables
                ({ barrier := callerBarrier
                   references := callerReferences
                   executables := callerExecutables } :: outer))
            qterm installed)) := by
    simpa using
      DemandDrivenCallStep.StepsN.succ 2 (.ready state)
        (.callPending nestedPending)
        (.ready
          (activatedOpenSuccessor nestedPending copied
            (nestedExecutableRest ++
              flattenExecutables
                ({ barrier := callerBarrier
                   references := callerReferences
                   executables := callerExecutables } :: outer))
            qterm installed))
        fineEntry
        (DemandDrivenCallStep.StepsN.succ 1
          (.callPending nestedPending) (.ready nestedPending.pulled)
          (.ready
            (activatedOpenSuccessor nestedPending copied
              (nestedExecutableRest ++
                flattenExecutables
                  ({ barrier := callerBarrier
                     references := callerReferences
                     executables := callerExecutables } :: outer))
              qterm installed))
          (.callPull nestedPending)
          (DemandDrivenCallStep.StepsN.succ 0
            (.ready nestedPending.pulled)
            (.ready
              (activatedOpenSuccessor nestedPending copied
                (nestedExecutableRest ++
                  flattenExecutables
                    ({ barrier := callerBarrier
                       references := callerReferences
                       executables := callerExecutables } :: outer))
                qterm installed))
            (.ready
              (activatedOpenSuccessor nestedPending copied
                (nestedExecutableRest ++
                  flattenExecutables
                    ({ barrier := callerBarrier
                       references := callerReferences
                       executables := callerExecutables } :: outer))
                qterm installed))
            activation.fineExecutableStep
            (DemandDrivenCallStep.StepsN.zero _)))
  obtain
      ⟨nestedActive, nestedPayloadContext, nestedAgreement, payloadHandoff,
        countGrowth⟩ :=
    PLeaTTa.PrologNestedCallEntryPayloadBridge.SpinedRepresentativeProductActivation.spinedNestedProductPayloadResourceRelates
      currentAgreement entry frontier oldCumulative materializedAtOpen
        queryReferenceBelow activation
  have sourceExact :
      StepsN (count + 2) (.running session currentSource)
        [.opened (requestFor predicate referencePayload current)]
        (.running
          (openedFor session predicate referencePayload current).session
          (ActiveProductContext.plug
            ({ callerScope := callerScope
               predicateScope := callerOpened.scope
               retained :=
                 .clauses callerOpened.scope
                   (callerFinish.advance callerBranch callerBranchTail)
               callerRest := callerReferences } :: currentContext)
            (activatedSourceProduct callerOpened.scope
              (openedFor session predicate referencePayload current)
              nestedFinish nestedBranch nestedBranchTail independentResult
              nestedReferenceRest))) := by
    simpa [nextOpened, nestedContext, nestedFrame] using sourceSteps
  have payloadCells :=
    SourceControlResourcePayloadContextAgrees.cellIdentities_cons_of_tail_handoff
      currentPayloadContext nestedPayloadContext payloadHandoff
  have exactPayload :
      ExactPayloadHandoff
        (ActivePayloadState.ofAgreement currentAgreement)
        (ActivePayloadState.ofAgreement nestedAgreement) := by
    refine
      ⟨nestedBranch.firstFresh, state.persistent.counter,
        activation.alphaExtension, payloadHandoff.below, ?_⟩
    change
      HEq (ActiveProductPayloadContext.outerPayload nestedPayloadContext)
        (SourceControlResourcePayloadContextAgrees.extendAbove
          activation.alphaExtension currentPayloadContext
          payloadHandoff.below)
    apply heq_of_eq
    calc
      ActiveProductPayloadContext.outerPayload nestedPayloadContext =
          SourceControlResourcePayloadContextAgrees.tail
            nestedPayloadContext :=
        ActiveProductPayloadContext.outerPayload_eq_tail nestedPayloadContext
      _ =
          SourceControlResourcePayloadContextAgrees.extendAbove
            activation.alphaExtension currentPayloadContext
            payloadHandoff.below := payloadHandoff.exact
  refine
    ⟨nestedActive, nestedPayloadContext, sourceExact, fineSteps,
      nestedAgreement, payloadHandoff, countGrowth, ?_⟩
  exact
    { sourceSteps := sourceExact
      fineSteps := fineSteps
      exactPayload := exactPayload
      payloadCells := payloadCells }

/-- Low-level arithmetic for three independently supplied compatible chains.

This lemma deliberately remains private: it does not couple the payload chain
to the source and fine states.  The public theorem below consumes two
`NestedCallPushCertificate`s instead, where one carrier owns all three. -/
private theorem independent_nested_chains_arithmetic
    {alpha0 alpha1 alpha2 support : List (LogicVar × String)}
    {qterm : Atom}
    {firstSegment : ControlSegment} {segments : List ControlSegment}
    {firstResource secondResource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {firstCursor secondCursor : PreparedCursor}
    {baseScope firstScope secondScope outer : CutScopeId}
    {context : ActiveProductContext}
    {secondReferences : List PeTTaSpec.PrologCore.Goal}
    {secondExecutables : List PLeaTTa.Goal}
    {firstBarrier secondBarrier : Nat}
    {firstReferenceFloor firstExecutableFloor : Nat}
    {secondReferenceFloor secondExecutableFloor : Nat}
    {firstExtension :
      AlphaExtendsAbove alpha0 alpha1 firstReferenceFloor
        firstExecutableFloor}
    {secondExtension :
      AlphaExtendsAbove alpha1 alpha2 secondReferenceFloor
        secondExecutableFloor}
    (base :
      SourceControlResourcePayloadContextAgrees alpha0 support qterm
        firstSegment.barrier segments resources baseScope context outer)
    (first :
      SourceControlResourcePayloadContextAgrees alpha1 support qterm
        firstBarrier (firstSegment :: segments)
        (firstResource :: resources) firstScope
        ({ callerScope := baseScope
           predicateScope := firstScope
           retained := .clauses firstScope firstCursor
           callerRest := firstSegment.references } :: context)
        outer)
    (second :
      SourceControlResourcePayloadContextAgrees alpha2 support qterm
        secondBarrier
        ({ barrier := firstBarrier
           references := secondReferences
           executables := secondExecutables } :: firstSegment :: segments)
        (secondResource :: firstResource :: resources) secondScope
        ({ callerScope := firstScope
           predicateScope := secondScope
           retained := .clauses secondScope secondCursor
           callerRest := secondReferences } ::
         { callerScope := baseScope
           predicateScope := firstScope
           retained := .clauses firstScope firstCursor
           callerRest := firstSegment.references } :: context)
        outer)
    (firstHandoff :
      ExtendsAboveAt firstReferenceFloor firstExecutableFloor firstExtension
        base (tail first))
    (secondHandoff :
      ExtendsAboveAt secondReferenceFloor secondExecutableFloor secondExtension
        first (tail second))
    {firstRejects secondRejects : Nat}
    {sourceStart sourceMiddle sourceFinish : State}
    {firstRequest secondRequest : CallRequest}
    (firstSource :
      StepsN (firstRejects + 2) sourceStart [.opened firstRequest]
        sourceMiddle)
    (secondSource :
      StepsN (secondRejects + 2) sourceMiddle [.opened secondRequest]
        sourceFinish)
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {fineStart fineMiddle fineFinish : DemandDrivenCallStep.FineConf}
    (firstFine :
      DemandDrivenCallStep.StepsN prog gt 3 fineStart fineMiddle)
    (secondFine :
      DemandDrivenCallStep.StepsN prog gt 3 fineMiddle fineFinish) :
    StepsN (firstRejects + secondRejects + 4) sourceStart
        [.opened firstRequest, .opened secondRequest] sourceFinish ∧
      DemandDrivenCallStep.StepsN prog gt 6 fineStart fineFinish ∧
      ActiveProductPayloadContext.cellCount first =
        ActiveProductPayloadContext.cellCount base + 1 ∧
      ActiveProductPayloadContext.cellCount (tail second) =
        ActiveProductPayloadContext.cellCount base + 1 ∧
      ActiveProductPayloadContext.cellCount second =
        ActiveProductPayloadContext.cellCount base + 2 ∧
      ActiveProductPayloadContext.cellCount (tail second) ≠
        ActiveProductPayloadContext.cellCount base := by
  have sourceCombined := StepsN.trans firstSource secondSource
  have sourceExact :
      StepsN (firstRejects + secondRejects + 4) sourceStart
        [.opened firstRequest, .opened secondRequest] sourceFinish := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using sourceCombined
  have fineCombined :=
    DemandDrivenCallStep.StepsN.trans firstFine secondFine
  have fineExact :
      DemandDrivenCallStep.StepsN prog gt 6 fineStart fineFinish := by
    simpa using fineCombined
  have payloadExact :=
    SourceControlResourcePayloadContextAgrees.two_nested_payload_pushes_exact
      base first second firstHandoff secondHandoff
  exact
    ⟨sourceExact, fineExact, payloadExact.1, payloadExact.2.1,
      payloadExact.2.2.1, payloadExact.2.2.2⟩

/-- Two exact nested-call certificates compose through one literal middle
carrier without quotienting source observations, fine executable phases, or
retained payload cells.

Because `middle` owns its source state, fine state, alpha graph, and dependent
payload relation jointly, a caller cannot combine compatible-looking evidence
from different runs.  The exact erased cell spine also proves that the final
payload contains both new cells and that dropping exactly two recovers the
original predecessor. -/
theorem two_nested_operational_prefixes_exact
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before middle after : ActivePayloadState}
    {firstRejects secondRejects : Nat}
    {firstRequest secondRequest : CallRequest}
    (first :
      NestedCallPushCertificate prog gt firstRejects firstRequest before
        middle)
    (second :
      NestedCallPushCertificate prog gt secondRejects secondRequest middle
        after) :
    StepsN (firstRejects + secondRejects + 4) before.sourceState
        [.opened firstRequest, .opened secondRequest] after.sourceState ∧
      DemandDrivenCallStep.StepsN prog gt 6 before.fineState
        after.fineState ∧
      (∀ pair, pair ∈ before.index.alpha → pair ∈ after.index.alpha) ∧
      middle.cellCount = before.cellCount + 1 ∧
      after.cellCount = before.cellCount + 2 ∧
      ∃ firstHead secondHead : PayloadCellIdentity,
        middle.cellIdentities = firstHead :: before.cellIdentities ∧
          after.cellIdentities = secondHead :: middle.cellIdentities ∧
          after.cellIdentities =
            secondHead :: firstHead :: before.cellIdentities ∧
          after.cellIdentities.drop 2 = before.cellIdentities ∧
          after.cellIdentities.tail ≠ before.cellIdentities := by
  have sourceCombined := StepsN.trans first.sourceSteps second.sourceSteps
  have sourceExact :
      StepsN (firstRejects + secondRejects + 4) before.sourceState
        [.opened firstRequest, .opened secondRequest] after.sourceState := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using sourceCombined
  have fineCombined :=
    DemandDrivenCallStep.StepsN.trans first.fineSteps second.fineSteps
  have fineExact :
      DemandDrivenCallStep.StepsN prog gt 6 before.fineState
        after.fineState := by
    simpa using fineCombined
  have alphaIncluded :
      ∀ pair, pair ∈ before.index.alpha → pair ∈ after.index.alpha := by
    intro pair present
    exact second.exactPayload.alphaIncluded pair
      (first.exactPayload.alphaIncluded pair present)
  obtain ⟨firstHead, firstCells⟩ := first.payloadCells
  obtain ⟨secondHead, secondCells⟩ := second.payloadCells
  have firstCount : middle.cellCount = before.cellCount + 1 := by
    calc
      middle.cellCount = middle.cellIdentities.length :=
        middle.cellIdentities_length.symm
      _ = (firstHead :: before.cellIdentities).length :=
        congrArg List.length firstCells
      _ = before.cellCount + 1 := by
        rw [List.length_cons, before.cellIdentities_length]
  have secondCount : after.cellCount = before.cellCount + 2 := by
    calc
      after.cellCount = after.cellIdentities.length :=
        after.cellIdentities_length.symm
      _ = (secondHead :: middle.cellIdentities).length :=
        congrArg List.length secondCells
      _ = before.cellCount + 2 := by
        rw [List.length_cons, middle.cellIdentities_length, firstCount]
  have exactCells :
      after.cellIdentities =
        secondHead :: firstHead :: before.cellIdentities := by
    calc
      after.cellIdentities = secondHead :: middle.cellIdentities := secondCells
      _ = secondHead :: firstHead :: before.cellIdentities :=
        congrArg (fun cells => secondHead :: cells) firstCells
  have dropTwo : after.cellIdentities.drop 2 = before.cellIdentities := by
    rw [exactCells]
    rfl
  have tailNotBase :
      after.cellIdentities.tail ≠ before.cellIdentities := by
    intro truncated
    have afterTail : after.cellIdentities.tail = middle.cellIdentities := by
      rw [secondCells]
      rfl
    have cycle :
        firstHead :: before.cellIdentities = before.cellIdentities := by
      calc
        firstHead :: before.cellIdentities = middle.cellIdentities :=
          firstCells.symm
        _ = after.cellIdentities.tail := afterTail.symm
        _ = before.cellIdentities := truncated
    have impossible := congrArg List.length cycle
    simp at impossible
  exact
    ⟨sourceExact, fineExact, alphaIncluded, firstCount, secondCount,
      firstHead, secondHead, firstCells, secondCells, exactCells, dropTwo,
      tailNotBase⟩

end PLeaTTa.PrologNestedCallChainBridge
