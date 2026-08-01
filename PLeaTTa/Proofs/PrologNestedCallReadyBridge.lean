-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologNestedCallReadyBridge
Purpose: Derive one nested local-call frontier from the literal active payload
  carrier, before adding the selected clause's new resolver facts.
Trusted boundary: none
Main exports:
  NestedCallHead,
  RepresentativeActivePayloadState,
  NestedCallOperationalReady,
  NestedCallReady,
  MaterializedNestedCallReady,
  NestedCallSuccessorFacts,
  RepresentativeNestedCallSuccessorFacts,
  NestedCallReady.pushDetailed,
  NestedCallReady.pushTwice
-/
import PLeaTTa.Proofs.PrologNestedCallChainBridge

namespace PLeaTTa.PrologNestedCallReadyBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologAlphaFreshFrontierBridge
open PrologCallEntryBridge
open PrologCallStepBridge
open PrologControlSegmentSpineBridge
open PrologCurrentSessionPayloadBridge
open PrologNestedCallChainBridge
open PrologNestedCallEntryPayloadBridge
open PrologOrdinaryStepBridge
open PrologMguBridge
open PrologMguComposition
open PrologPrefilterCallBridge
open PrologPrefilterScanBridge
open PrologProductResourceTransitionBridge
open PrologRepresentativeCallFrontierBridge
open PrologRepresentativeProductActivationBridge
open PrologRecursiveCallPayloadBridge
open PrologSourceProductContextBridge
open PrologStateBridge
open PrologSupportedCallFrontierBridge

namespace RejectedPullsN

/-- A singleton cursor cannot reject any prefix and still finish at a
nonempty retained frontier.  Coupling this inversion to the actual pull path
rules out a context-compatible but unreachable forged frontier. -/
theorem eq_zero_of_singleton_of_finish_nonempty
    {count : Nat} {start finish : PreparedCursor} {only : ClauseBranch}
    (singleton : start.remaining = [only])
    (pulls : RejectedPullsN count start finish)
    (finishNonempty : finish.remaining ≠ []) :
    count = 0 ∧ finish = start := by
  cases pulls with
  | zero cursor => exact ⟨rfl, rfl⟩
  | succ count cursor branch branches finish remaining clash tail =>
      rw [singleton] at remaining
      have branchesNil : branches = [] := by
        exact (List.cons.inj remaining).2.symm
      subst branches
      cases tail with
      | zero advanced =>
          exact False.elim (finishNonempty (by
            simp [PreparedCursor.advance]))
      | succ tailCount advanced tailBranch tailBranches tailFinish
          advancedRemaining tailClash tailPulls =>
          have impossible :
              ([] : List ClauseBranch) = tailBranch :: tailBranches := by
            simp [PreparedCursor.advance] at advancedRemaining
          simp at impossible

end RejectedPullsN

namespace DemandDrivenCallStep.Step

/-- A fine install-only local-call entry retains the exact sealed call step
to the post-pull configuration.  The transient pending phase contributes no
new sealed behavior. -/
theorem ready_callPending_projects_to_sealed
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {state : DemandDrivenStep.OpenConf}
    {pending : DemandDrivenCallStep.PendingCall}
    (step : DemandDrivenCallStep.Step prog gt (.ready state)
      (.callPending pending)) :
    PLeaTTa.Step prog gt state.toConf pending.pulled.toConf := by
  cases step with
  | callEnter state f args res rest binding branches counter head
      headNonempty arityPresent scanned =>
      exact DemandDrivenCallStep.callEnter_projects_to_sealed head
        headNonempty arityPresent scanned

end DemandDrivenCallStep.Step

namespace ActivePayloadState

/-- Repackaging the literal agreement stored by a carrier changes no index,
payload witness, or state identity. -/
@[simp] theorem ofAgreement_self (state : ActivePayloadState) :
    ActivePayloadState.ofAgreement state.agreement = state := by
  cases state
  rfl

end ActivePayloadState

/-! ## A call head indexed by its exact active carrier -/

/-- The source and executable spelling of the next local call, indexed by the
literal active state that owns both lists.

Only syntax is selected here.  Payload agreement, persistent-state agreement,
resource ownership, allocator endpoints, and activation order remain fields of
`state.agreement` and cannot be supplied again by a caller. -/
structure NestedCallHead (state : ActivePayloadState) where
  predicate : String
  referencePayload : List Term
  referenceRest : List PeTTaSpec.PrologCore.Goal
  arguments : List Atom
  result : Atom
  executableRest : List PLeaTTa.Goal
  referenceHead :
    state.index.bodyReferences =
      .call predicate referencePayload :: referenceRest
  executableHead :
    state.index.bodyExecutables =
      .call predicate arguments result :: executableRest

namespace NestedCallHead

/-- Consume the two head equations once to expose the exact call-headed
carrier relation.  No other index is changed. -/
theorem carrierAgreement {state : ActivePayloadState}
    (head : NestedCallHead state) :
    SpinedActiveProductPayloadResourceRelatesAt
      state.index.freshFrontier state.index.alpha state.index.support
      state.index.canonical state.index.referenceBase state.index.opened
      state.index.session state.index.pending state.index.finish
      state.index.branch state.index.branchTail state.index.altTail
      state.index.bodyBarrier state.index.callerBarrier
      (.call head.predicate head.referencePayload :: head.referenceRest)
      (.call head.predicate head.arguments head.result :: head.executableRest)
      state.index.callerReferences state.index.callerExecutables
      state.index.outer state.index.current state.index.runtime
      state.index.qterm state.index.active state.index.resources
      state.index.callerScope state.index.outerScope state.index.context
      state.index.baseAlts state.index.source state.index.openConf
      state.payloadContext := by
  simpa [ActivePayloadIndex.Relates, head.referenceHead,
    head.executableHead] using state.agreement

/-- Exposing the call head and repackaging its agreement preserves the literal
carrier identity, not merely an isomorphic state. -/
theorem carrierStateEq {state : ActivePayloadState}
    (head : NestedCallHead state) :
    ActivePayloadState.ofAgreement head.carrierAgreement = state := by
  cases state with
  | mk index payloadContext agreement =>
      cases index
      simp_all [ActivePayloadState.ofAgreement]
      exact ⟨head.referenceHead.symm, head.executableHead.symm⟩

/-- The exact current-region payload is recovered from the carrier's control
spine.  It is not a readiness premise. -/
theorem payload {state : ActivePayloadState} (head : NestedCallHead state) :
    TaskPayloadAgrees state.index.alpha state.index.support
      state.index.bodyBarrier state.index.canonical state.index.referenceBase
      state.index.current state.index.runtime
      (.call head.predicate head.referencePayload :: head.referenceRest)
      (.call head.predicate head.arguments head.result ::
        head.executableRest) := by
  have current :=
    PrologControlSegmentSpineBridge.TaskSpinePayloadAgrees.headPayload
      state.agreement.core.control.ready.2.2.2
  rw [head.referenceHead, head.executableHead] at current
  exact current

/-- The complete segmented continuation is recovered without retagging older
predicate regions at the active barrier. -/
theorem spinePayload {state : ActivePayloadState}
    (head : NestedCallHead state) :
    TaskSpinePayloadAgrees state.index.alpha state.index.support
      state.index.canonical state.index.referenceBase state.index.current
      state.index.runtime
      ({ barrier := state.index.bodyBarrier
         references :=
           .call head.predicate head.referencePayload :: head.referenceRest
         executables :=
           .call head.predicate head.arguments head.result ::
             head.executableRest } ::
       { barrier := state.index.callerBarrier
         references := state.index.callerReferences
         executables := state.index.callerExecutables } ::
       state.index.outer) := by
  have current := state.agreement.core.control.ready.2.2.2
  rw [head.referenceHead, head.executableHead] at current
  exact current

/-- Source output-last arity follows from the call-head payload relation. -/
theorem arity {state : ActivePayloadState} (head : NestedCallHead state) :
    head.referencePayload.length = head.arguments.length + 1 := by
  obtain
    ⟨referenceArguments, referenceResult, referenceShape, arguments,
      result, _tail⟩ :=
    NormalizedAlphaGoalsAgree.localCallHead head.payload.control
  have argumentsLength :
      referenceArguments.length = head.arguments.length :=
    PLeaTTa.PrologPrefilterBridge.AlphaTermsAgree.length_eq arguments
  rw [referenceShape, List.length_append, List.length_singleton,
    argumentsLength]

/-- A zero-argument executable local call exposes its unique source payload
as the alpha-related result leaf.

This is an inversion of the certified output-last call spelling, not a new
agreement premise.  It lets later transitions use the literal result atom
without learning or reconstructing its generated runtime variable name. -/
theorem resultAgrees_of_singletonPayload {state : ActivePayloadState}
    (head : NestedCallHead state) {referenceResult : Term}
    (payloadExact : head.referencePayload = [referenceResult])
    (argumentsExact : head.arguments = []) :
    AlphaTermAgrees state.index.alpha referenceResult head.result := by
  obtain
    ⟨referenceArguments, actualResult, referenceShape, arguments,
      result, _tail⟩ :=
    NormalizedAlphaGoalsAgree.localCallHead head.payload.control
  have referenceArgumentsLength : referenceArguments.length = 0 := by
    have lengths :=
      PLeaTTa.PrologPrefilterBridge.AlphaTermsAgree.length_eq arguments
    simpa [argumentsExact] using lengths
  have referenceArgumentsExact : referenceArguments = [] :=
    List.eq_nil_of_length_eq_zero referenceArgumentsLength
  subst referenceArguments
  simp only [List.nil_append] at referenceShape
  have actualResultExact : actualResult = referenceResult := by
    rw [payloadExact] at referenceShape
    exact (List.cons.inj referenceShape).1.symm
  subst actualResult
  exact result

/-- The executable call head and its complete flattened continuation are
forced by the carrier's literal control spine. -/
theorem executableStateHead {state : ActivePayloadState}
    (head : NestedCallHead state) :
    state.index.openConf.toConf.cur =
      some
        (.call head.predicate head.arguments head.result ::
            (head.executableRest ++
              flattenExecutables
                ({ barrier := state.index.callerBarrier
                   references := state.index.callerReferences
                   executables := state.index.callerExecutables } ::
                 state.index.outer)),
          state.index.runtime) := by
  have current := state.agreement.core.control.ready.2.1
  rw [head.executableHead] at current
  simpa [OpenConf.toConf, Control.toConf, flattenExecutables,
    ControlSegment.executableGoals] using current

/-- The carrier stores the public query term independently of executable
control spelling, but pins it to the literal open state. -/
theorem qtermEq {state : ActivePayloadState} (_head : NestedCallHead state) :
    state.index.openConf.control.qterm = state.index.qterm :=
  state.agreement.core.control.ready.2.2.1

/-- Current logical-update database agreement is a projection of the carrier,
not a separately chosen bridge. -/
theorem database {state : ActivePayloadState} (_head : NestedCallHead state) :
    DatabaseRelatesWorld state.index.session.resolver.database
      state.index.openConf.persistent.world :=
  state.agreement.core.control.ready.1.database

/-- The source call-opening transition is forced by the carrier's exact source
focus and retained product context. -/
theorem sourceEntry {state : ActivePayloadState} (head : NestedCallHead state)
    (notThrow : ¬ BuiltinThrowCall head.predicate head.referencePayload)
    (notDatabase :
      DatabaseActions.recognizeDatabaseAction head.predicate
        head.referencePayload = none) :
    RawStep state.index.session state.index.source
      [.opened
        (requestFor head.predicate head.referencePayload state.index.current)]
      .none
      (openedFor state.index.session head.predicate head.referencePayload
        state.index.current).session
      (.running
        (ActiveProductContext.plug
          ({ callerScope := state.index.callerScope
             predicateScope := state.index.opened.scope
             retained :=
               .clauses state.index.opened.scope
                 (state.index.finish.advance state.index.branch
                   state.index.branchTail)
             callerRest := state.index.callerReferences } ::
           state.index.context)
          (sourceProductFrontier state.index.opened.scope
            (openedFor state.index.session head.predicate
              head.referencePayload state.index.current)
            (openedFor state.index.session head.predicate
              head.referencePayload state.index.current).cursor
            head.referenceRest))) := by
  apply
    PrologNestedCallEntryPayloadBridge.SpinedActiveProductPayloadResourceRelatesAt.sourceCallEntry
      (agreement := head.carrierAgreement)
      (predicate := head.predicate)
      (referencePayload := head.referencePayload)
      (nestedReferenceRest := head.referenceRest)
      (args := head.arguments)
      (res := head.result)
      (nestedExecutableRest := head.executableRest)
      notThrow notDatabase

end NestedCallHead

/-! ## Computed resolver readiness -/

namespace NestedCallHead

/-- The complete executable continuation after the current call head. -/
def executableTail {state : ActivePayloadState} (head : NestedCallHead state) :
    List PLeaTTa.Goal :=
  head.executableRest ++
    flattenExecutables
      ({ barrier := state.index.callerBarrier
         references := state.index.callerReferences
         executables := state.index.callerExecutables } :: state.index.outer)

/-- The actual executable resolver scan, computed once from the literal fine
state and the literal call head. -/
def scan {state : ActivePayloadState} (head : NestedCallHead state) :
    List PLeaTTa.Alt × Nat :=
  resolveAlts
    (state.index.openConf.persistent.world.resolutionCandidates
      head.predicate head.arguments.length)
    (head.arguments.map (PLeaTTa.subst state.index.runtime)) head.arguments
    head.result head.executableTail state.index.runtime
    state.index.openConf.toConf.qterm
    (barrierDepth state.index.openConf.toConf + 1)
    state.index.openConf.toConf.counter

def pending {state : ActivePayloadState} (head : NestedCallHead state) :
    DemandDrivenCallStep.PendingCall :=
  DemandDrivenCallStep.pendingCallOf state.index.openConf head.scan.1 head.scan.2

abbrev Frontier {state : ActivePayloadState} (head : NestedCallHead state)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (clause : PLeaTTa.Clause) (branchTail : List ClauseBranch)
    (clauseTail : List PLeaTTa.Clause) (altTail : List PLeaTTa.Alt)
    (copied : PLeaTTa.Clause) :=
  RepresentativeRetainedCallFrontier state.index.alpha
    (openedFor state.index.session head.predicate head.referencePayload
      state.index.current)
    state.index.openConf head.pending finish branch clause branchTail clauseTail
    altTail copied
    (head.arguments.map (PLeaTTa.subst state.index.runtime)) head.arguments
    head.result head.executableTail state.index.runtime state.index.qterm
    (barrierDepth state.index.openConf.toConf + 1)
    state.index.openConf.toConf.counter

end NestedCallHead

/-- One active payload carrier together with the concrete residual
representative used to interpret its runtime substitution.

The representative is data, not a freshly eliminated existential proof.
Keeping it in the carrier makes orientation continuity available to the next
recursive activation without any large elimination from `Prop`. -/
structure RepresentativeActivePayloadState where
  carrier : ActivePayloadState
  representative : TreeSubstitution
  cumulative :
    AlphaCumulativeResidualVariantAgreesOnWith carrier.index.alpha
      carrier.index.support carrier.index.canonical carrier.index.referenceBase
      carrier.index.runtime representative

/-- Runtime facts needed to select the next locally owned clause, excluding
the semantic interpretation of the call payload.

The structure deliberately contains no payload agreement, persistent-state
bridge, resource bank, cursor frontier, alpha handoff, or endpoint/order
certificate.  Those are derived from `state`.  Its `selected` field adds only
the new semantic fact that the deterministically selected retained occurrence
has a full-head MGU and a live executable continuation. -/
structure NestedCallOperationalReady (state : ActivePayloadState)
    (head : NestedCallHead state) : Prop where
  exactFresh :
    state.index.freshFrontier = AlphaFreshFrontier state.index.alpha
  indexReady : state.index.openConf.persistent.world.clauseIndexReady = true
  below : ConfBelowResolutionCounter state.index.openConf.toConf
  candidateSupported :
    SupportedCandidateBank head.predicate
      (state.index.session.resolver.database.visibleClausesAt
        state.index.session.resolver.database.generation head.predicate
        head.referencePayload.length)
      (state.index.openConf.persistent.world.resolutionCandidates
        head.predicate head.arguments.length)
  sourceNonempty :
    state.index.session.resolver.database.visibleClausesAt
      state.index.session.resolver.database.generation head.predicate
      head.referencePayload.length ≠ []
  scanNonempty : head.scan.1 ≠ []
  selected :
    ∀ {count : Nat} {finish : PreparedCursor} {branch : ClauseBranch}
      {clause : PLeaTTa.Clause} {branchTail : List ClauseBranch}
      {clauseTail : List PLeaTTa.Clause} {altTail : List PLeaTTa.Alt}
      {copied : PLeaTTa.Clause},
      RejectedPullsN count
          (openedFor state.index.session head.predicate head.referencePayload
            state.index.current).cursor
          finish →
        head.Frontier finish branch clause branchTail clauseTail altTail copied →
        ∃ independentResult : Substitution,
          HeadResolution branch independentResult ∧
            AlphaRuntimeNamesLive state.index.support
              (copied.body ++ head.executableTail) state.index.qterm
  notThrow : ¬ BuiltinThrowCall head.predicate head.referencePayload
  notDatabase :
    DatabaseActions.recognizeDatabaseAction head.predicate
      head.referencePayload = none

/-- Compatibility readiness for callers whose raw source payload is wholly
inside the fixed observable support.  New non-ground recursive callers should
use `MaterializedNestedCallReady`; raw syntax support is strictly stronger
than what the resolver consumes. -/
structure NestedCallReady (state : ActivePayloadState)
    (head : NestedCallHead state) : Prop
    extends NestedCallOperationalReady state head where
  payloadSupported :
    AlphaTermsSupported state.index.alpha state.index.support
      head.referencePayload

/-- Exact readiness for a representative-indexed active state.

The call is certified after materializing its arguments and result under the
current executable substitution.  The certificate shares the carrier's
representative, so activation, retained snapshots, and the successor
cumulative valuation cannot choose independent alias orientations. -/
structure MaterializedNestedCallReady
    (state : RepresentativeActivePayloadState)
    (head : NestedCallHead state.carrier) : Prop
    extends NestedCallOperationalReady state.carrier head where
  materialized :
    MaterializedCallAgreesWith state.carrier.index.alpha
      state.carrier.index.current head.referencePayload
      (head.arguments.map (PLeaTTa.subst state.carrier.index.runtime))
      (PLeaTTa.subst state.carrier.index.runtime head.result)
      state.representative state.carrier.index.referenceBase

/-- Exact facts exported by one readiness elimination for use by the next
nested call.  Every datum is indexed by the literal predecessor and
successor; the occurrence-bank equations and pull path prevent a selected
branch or executable clause from being swapped after the fact. -/
structure NestedCallSuccessorFacts
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (before : ActivePayloadState) (head : NestedCallHead before)
    (count : Nat) (skippedBranches : List ClauseBranch)
    (skippedClauses : List PLeaTTa.Clause)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (clause : PLeaTTa.Clause) (branchTail : List ClauseBranch)
    (clauseTail : List PLeaTTa.Clause) (altTail : List PLeaTTa.Alt)
    (copied : PLeaTTa.Clause) (installed : Subst)
    (after : ActivePayloadState) : Prop where
  sourceBank :
    (openedFor before.index.session head.predicate head.referencePayload
      before.index.current).cursor.remaining =
      skippedBranches ++ (branch :: branchTail)
  executableBank :
    before.index.openConf.persistent.world.resolutionCandidates
        head.predicate head.arguments.length =
      skippedClauses ++ (clause :: clauseTail)
  sourceSkipCount : skippedBranches.length = count
  executableSkipCount : skippedClauses.length = count
  pulls :
    RejectedPullsN count
      (openedFor before.index.session head.predicate head.referencePayload
        before.index.current).cursor
      finish
  frontier :
    head.Frontier finish branch clause branchTail clauseTail altTail copied
  resolution : HeadResolution branch after.index.current
  bodyReferences : after.index.bodyReferences = branch.body
  bodyExecutables : after.index.bodyExecutables = copied.body
  activationStep :
    PLeaTTa.Step prog gt head.pending.pulled.toConf
      (PrologRepresentativeStepActivationBridge.activatedExecutableSuccessor
        head.pending copied head.executableTail before.index.qterm installed)
  runtimeExact :
    after.index.runtime =
      PLeaTTa.trimFor (copied.body ++ head.executableTail)
        before.index.qterm installed
  alphaExtension :
    AlphaExtendsAbove before.index.alpha after.index.alpha branch.firstFresh
      before.index.openConf.toConf.counter
  selectionFresh :
    AlphaFreshFrontier after.index.alpha branch.nextFresh
      (before.index.openConf.toConf.counter + 1)
  supportPreserved : after.index.support = before.index.support
  freshFrontierExact :
    after.index.freshFrontier = AlphaFreshFrontier after.index.alpha
  sessionExact :
    after.index.session =
      (openedFor before.index.session head.predicate head.referencePayload
        before.index.current).session
  worldPreserved :
    after.index.openConf.persistent.world =
      before.index.openConf.persistent.world
  qtermPreserved : after.index.qterm = before.index.qterm
  below : ConfBelowResolutionCounter after.index.openConf.toConf
  certificate :
    NestedCallPushCertificate prog gt count
      (requestFor head.predicate head.referencePayload before.index.current)
      before after

/-- Successor facts retaining the concrete representative across one nested
activation.  `representativeExtension` records that the newly generated MGU
is prepended to, rather than substituted for, the predecessor's semantic
orientation. -/
structure RepresentativeNestedCallSuccessorFacts
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (before : RepresentativeActivePayloadState)
    (head : NestedCallHead before.carrier)
    (count : Nat) (skippedBranches : List ClauseBranch)
    (skippedClauses : List PLeaTTa.Clause)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (clause : PLeaTTa.Clause) (branchTail : List ClauseBranch)
    (clauseTail : List PLeaTTa.Clause) (altTail : List PLeaTTa.Alt)
    (copied : PLeaTTa.Clause) (installed : Subst)
    (after : RepresentativeActivePayloadState) : Prop
    extends NestedCallSuccessorFacts prog gt before.carrier head count
      skippedBranches skippedClauses finish branch clause branchTail clauseTail
      altTail copied installed after.carrier where
  representativeExtension :
    ∃ extension : TreeSubstitution,
      after.representative = extension ++ before.representative
  generatedMguExtension :
    ∃ extension : TreeSubstitution,
      after.representative = extension ++ before.representative ∧
        PendingHeadMguAgrees after.carrier.index.alpha extension installed
          head.pending copied head.executableTail
  materializedBodyHeads :
    MaterializedLocalCallHeadsAgreeWith after.carrier.index.alpha
      after.carrier.index.current after.carrier.index.bodyReferences
      after.carrier.index.bodyExecutables after.carrier.index.runtime
      after.representative after.carrier.index.referenceBase

/-- The activated body certificate supplies the semantic payload for its
literal next local call.  Operational readiness remains independent; this
lemma adds only the representative-indexed materialization that fresh body
variables cannot obtain from the older raw-support interface. -/
theorem RepresentativeNestedCallSuccessorFacts.materializedReady
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeActivePayloadState}
    {head : NestedCallHead before.carrier}
    {count : Nat} {skippedBranches : List ClauseBranch}
    {skippedClauses : List PLeaTTa.Clause}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {clause : PLeaTTa.Clause} {branchTail : List ClauseBranch}
    {clauseTail : List PLeaTTa.Clause} {altTail : List PLeaTTa.Alt}
    {copied : PLeaTTa.Clause} {installed : Subst}
    {after : RepresentativeActivePayloadState}
    (facts :
      RepresentativeNestedCallSuccessorFacts prog gt before head count
        skippedBranches skippedClauses finish branch clause branchTail
        clauseTail altTail copied installed after)
    (nextHead : NestedCallHead after.carrier)
    (operational : NestedCallOperationalReady after.carrier nextHead) :
    MaterializedNestedCallReady after nextHead := by
  refine
    { toNestedCallOperationalReady := operational
      materialized := ?_ }
  exact facts.materializedBodyHeads nextHead.referenceHead
    nextHead.executableHead

namespace NestedCallOperationalReady

/-- The carrier's actual persistent allocator inhabits the exact alpha
frontier named by readiness.  This is the reusable executable-name bound for
recursive activation; it does not require every historical name to remain in
the current call syntax. -/
theorem alphaFresh {state : ActivePayloadState}
    {head : NestedCallHead state}
    (ready : NestedCallOperationalReady state head) :
    AlphaFreshFrontier state.index.alpha
      state.index.session.resolver.nextFresh
      state.index.openConf.persistent.counter := by
  rw [← ready.exactFresh]
  exact state.agreement.core.control.ready.1.fresh

/-- Operational readiness alone determines the executable entry step; no
source payload-support premise participates in scan scheduling. -/
theorem fineEntry {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {state : ActivePayloadState} {head : NestedCallHead state}
    (ready : NestedCallOperationalReady state head) :
    DemandDrivenCallStep.Step prog gt (.ready state.index.openConf)
      (.callPending head.pending) := by
  have paired :=
    taskCall_callEnter_bank_correspondence (prog := prog) (gt := gt)
      head.database ready.indexReady state.index.opened.scope head.predicate
      head.referencePayload head.referenceRest state.index.current
      head.arguments head.result head.executableTail state.index.runtime
      head.scan.1 head.scan.2 head.arity ready.notThrow ready.notDatabase
      ready.sourceNonempty head.executableStateHead
      (by
        change head.scan = (head.scan.1, head.scan.2)
        exact (Prod.eta head.scan).symm)
  simpa [NestedCallHead.pending] using paired.2.1

/-- Once semantic call entry is supplied, the operational layer computes the
unique maximal rejected prefix and first retained frontier. -/
theorem retainedFrontierOfEntry
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {state : ActivePayloadState} {head : NestedCallHead state}
    (ready : NestedCallOperationalReady state head)
    (entry :
      RepresentativeSupportedCallEntryRelates state.index.alpha
        (openedFor state.index.session head.predicate head.referencePayload
          state.index.current)
        state.index.openConf head.pending
        (head.arguments.map (PLeaTTa.subst state.index.runtime)) head.arguments
        head.result head.executableTail state.index.runtime state.index.qterm
        (barrierDepth state.index.openConf.toConf + 1)
        state.index.openConf.toConf.counter) :
    ∃ count : Nat, ∃ skippedBranches : List ClauseBranch,
      ∃ skippedClauses : List PLeaTTa.Clause,
      ∃ finish : PreparedCursor, ∃ branch : ClauseBranch,
      ∃ clause : PLeaTTa.Clause, ∃ branchTail : List ClauseBranch,
      ∃ clauseTail : List PLeaTTa.Clause, ∃ altTail : List PLeaTTa.Alt,
      ∃ copied : PLeaTTa.Clause,
        (openedFor state.index.session head.predicate head.referencePayload
            state.index.current).cursor.remaining =
          skippedBranches ++ (branch :: branchTail) ∧
        state.index.openConf.persistent.world.resolutionCandidates
            head.predicate head.arguments.length =
          skippedClauses ++ (clause :: clauseTail) ∧
        skippedBranches.length = count ∧
        skippedClauses.length = count ∧
        RejectedPullsN count
          (openedFor state.index.session head.predicate head.referencePayload
            state.index.current).cursor
          finish ∧
        head.Frontier finish branch clause branchTail clauseTail altTail copied := by
  obtain
    ⟨count, skippedBranches, skippedClauses, finish, branch, clause,
      branchTail, clauseTail, altTail, copied, branchesEq, clausesEq,
      branchCount, clauseCount, pulls, _sourceSteps, _finePull, frontier⟩ :=
    RepresentativeSupportedCallEntryRelates.callPull_retained_frontier
      (prog := prog) (gt := gt) entry ready.below
      (by
        simpa [NestedCallHead.pending, DemandDrivenCallStep.pendingCallOf]
          using ready.scanNonempty)
  exact
    ⟨count, skippedBranches, skippedClauses, finish, branch, clause,
      branchTail, clauseTail, altTail, copied, branchesEq, clausesEq,
      branchCount, clauseCount, pulls, frontier⟩

/-- The selected source cursor remains above the active alpha graph; this is
pure allocator chronology and is independent of raw versus materialized call
interpretation. -/
theorem queryReferenceBelow {state : ActivePayloadState}
    {head : NestedCallHead state}
    (ready : NestedCallOperationalReady state head)
    {finish : PreparedCursor} {branch : ClauseBranch}
    {clause : PLeaTTa.Clause} {branchTail : List ClauseBranch}
    {clauseTail : List PLeaTTa.Clause} {altTail : List PLeaTTa.Alt}
    {copied : PLeaTTa.Clause}
    (frontier :
      head.Frontier finish branch clause branchTail clauseTail altTail copied) :
    GeneratedBelow finish.reservationStart (state.index.alpha.map Prod.fst) := by
  apply ready.alphaFresh.1.mono
  exact Nat.le_trans
    (openLocalCall_reservationStart_ge state.index.session
      (requestFor head.predicate head.referencePayload state.index.current))
    frontier.finishReservationStart

end NestedCallOperationalReady

namespace NestedCallReady

/-- Readiness reconstructs the exact supported source/executable call-entry
relation from the carrier and the computed scan. -/
theorem entryRelates {state : ActivePayloadState} {head : NestedCallHead state}
    (ready : NestedCallReady state head) :
    RepresentativeSupportedCallEntryRelates state.index.alpha
      (openedFor state.index.session head.predicate head.referencePayload
        state.index.current)
      state.index.openConf head.pending
      (head.arguments.map (PLeaTTa.subst state.index.runtime)) head.arguments
      head.result head.executableTail state.index.runtime state.index.qterm
      (barrierDepth state.index.openConf.toConf + 1)
      state.index.openConf.toConf.counter := by
  have scanned :
      resolveAlts
          (state.index.openConf.persistent.world.resolutionCandidates
            head.predicate head.arguments.length)
          (head.arguments.map (PLeaTTa.subst state.index.runtime))
          head.arguments head.result head.executableTail state.index.runtime
          state.index.openConf.control.qterm
          (barrierDepth state.index.openConf.toConf + 1)
          state.index.openConf.toConf.counter =
        (head.scan.1, head.scan.2) := by
    change head.scan = (head.scan.1, head.scan.2)
    exact (Prod.eta head.scan).symm
  have constructed :=
    openedFor_pendingCallOf_representative_supported_relates
      head.database ready.indexReady head.predicate head.referencePayload
      state.index.current state.index.alpha head.arguments head.result
      head.executableTail state.index.runtime head.scan.1 head.scan.2 head.arity
      head.executableStateHead scanned
      (PrologRecursiveCallPayloadBridge.TaskPayloadAgrees.representativeNormalizedCallAgrees
        head.payload ready.payloadSupported
        (openedFor state.index.session head.predicate head.referencePayload
          state.index.current).cursor
        (by simp [openedFor, openLocalCall, requestFor, prepareCall])
        (by simp [openedFor, openLocalCall, requestFor, prepareCall]))
      ready.candidateSupported
  simpa [NestedCallHead.pending, head.qtermEq] using constructed

/-- The executable entry step is derived from the same computed scan and the
same literal state. -/
theorem fineEntry {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {state : ActivePayloadState} {head : NestedCallHead state}
    (ready : NestedCallReady state head) :
    DemandDrivenCallStep.Step prog gt (.ready state.index.openConf)
      (.callPending head.pending) := by
  have paired :=
    taskCall_callEnter_bank_correspondence (prog := prog) (gt := gt)
      head.database ready.indexReady state.index.opened.scope head.predicate
      head.referencePayload head.referenceRest state.index.current
      head.arguments head.result head.executableTail state.index.runtime
      head.scan.1 head.scan.2 head.arity ready.notThrow ready.notDatabase
      ready.sourceNonempty head.executableStateHead
      (by
        change head.scan = (head.scan.1, head.scan.2)
        exact (Prod.eta head.scan).symm)
  simpa [NestedCallHead.pending] using paired.2.1

/-- Compute the maximal exact rejected prefix and first retained frontier.
Neither cursor nor frontier is accepted as an input. -/
theorem retainedFrontier {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {state : ActivePayloadState} {head : NestedCallHead state}
    (ready : NestedCallReady state head) :
    ∃ count : Nat, ∃ skippedBranches : List ClauseBranch,
      ∃ skippedClauses : List PLeaTTa.Clause,
      ∃ finish : PreparedCursor, ∃ branch : ClauseBranch,
      ∃ clause : PLeaTTa.Clause, ∃ branchTail : List ClauseBranch,
      ∃ clauseTail : List PLeaTTa.Clause, ∃ altTail : List PLeaTTa.Alt,
      ∃ copied : PLeaTTa.Clause,
        (openedFor state.index.session head.predicate head.referencePayload
            state.index.current).cursor.remaining =
          skippedBranches ++ (branch :: branchTail) ∧
        state.index.openConf.persistent.world.resolutionCandidates
            head.predicate head.arguments.length =
          skippedClauses ++ (clause :: clauseTail) ∧
        skippedBranches.length = count ∧
        skippedClauses.length = count ∧
        RejectedPullsN count
          (openedFor state.index.session head.predicate head.referencePayload
            state.index.current).cursor
          finish ∧
        head.Frontier finish branch clause branchTail clauseTail altTail copied := by
  obtain
    ⟨count, skippedBranches, skippedClauses, finish, branch, clause,
      branchTail, clauseTail, altTail, copied, branchesEq, clausesEq,
      branchCount, clauseCount, pulls, _sourceSteps, _finePull, frontier⟩ :=
    RepresentativeSupportedCallEntryRelates.callPull_retained_frontier
      (prog := prog) (gt := gt) ready.entryRelates ready.below
      (by
        simpa [NestedCallHead.pending, DemandDrivenCallStep.pendingCallOf]
          using ready.scanNonempty)
  exact
    ⟨count, skippedBranches, skippedClauses, finish, branch, clause,
      branchTail, clauseTail, altTail, copied, branchesEq, clausesEq,
      branchCount, clauseCount, pulls, frontier⟩

/-- The selected source cursor remains above every independent generated name
in the active alpha graph.  The bound is transported from the literal session
frontier through call opening and the exact rejected prefix. -/
theorem queryReferenceBelow {state : ActivePayloadState}
    {head : NestedCallHead state} (ready : NestedCallReady state head)
    {finish : PreparedCursor} {branch : ClauseBranch}
    {clause : PLeaTTa.Clause} {branchTail : List ClauseBranch}
    {clauseTail : List PLeaTTa.Clause} {altTail : List PLeaTTa.Alt}
    {copied : PLeaTTa.Clause}
    (frontier :
      head.Frontier finish branch clause branchTail clauseTail altTail copied) :
    GeneratedBelow finish.reservationStart (state.index.alpha.map Prod.fst) := by
  have exactFrontier :
      AlphaFreshFrontier state.index.alpha
        state.index.session.resolver.nextFresh
        state.index.openConf.persistent.counter := by
    rw [← ready.exactFresh]
    exact state.agreement.core.control.ready.1.fresh
  apply exactFrontier.1.mono
  exact Nat.le_trans
    (openLocalCall_reservationStart_ge state.index.session
      (requestFor head.predicate head.referencePayload state.index.current))
    frontier.finishReservationStart

end NestedCallReady

namespace MaterializedNestedCallReady

/-- Install the literal opened cursor around the already-materialized call
without changing its fixed representative. -/
theorem queryAtOpen
    {state : RepresentativeActivePayloadState}
    {head : NestedCallHead state.carrier}
    (ready : MaterializedNestedCallReady state head) :
    RepresentativeNormalizedCallAgreesWith state.carrier.index.alpha
      (openedFor state.carrier.index.session head.predicate
        head.referencePayload state.carrier.index.current).cursor
      (head.arguments.map (PLeaTTa.subst state.carrier.index.runtime))
      (PLeaTTa.subst state.carrier.index.runtime head.result)
      state.representative state.carrier.index.referenceBase :=
  ready.materialized.toRepresentativeNormalizedCallAgreesWith
    (openedFor state.carrier.index.session head.predicate
      head.referencePayload state.carrier.index.current).cursor
    (by simp [openedFor, openLocalCall, requestFor, prepareCall])
    (by simp [openedFor, openLocalCall, requestFor, prepareCall])

/-- Materialized readiness reconstructs call entry from the carrier's fixed
representative.  No raw source-support premise is introduced. -/
theorem entryRelates
    {state : RepresentativeActivePayloadState}
    {head : NestedCallHead state.carrier}
    (ready : MaterializedNestedCallReady state head) :
    RepresentativeSupportedCallEntryRelates state.carrier.index.alpha
      (openedFor state.carrier.index.session head.predicate head.referencePayload
        state.carrier.index.current)
      state.carrier.index.openConf head.pending
      (head.arguments.map (PLeaTTa.subst state.carrier.index.runtime))
      head.arguments head.result head.executableTail state.carrier.index.runtime
      state.carrier.index.qterm
      (barrierDepth state.carrier.index.openConf.toConf + 1)
      state.carrier.index.openConf.toConf.counter := by
  have scanned :
      resolveAlts
          (state.carrier.index.openConf.persistent.world.resolutionCandidates
            head.predicate head.arguments.length)
          (head.arguments.map (PLeaTTa.subst state.carrier.index.runtime))
          head.arguments head.result head.executableTail
          state.carrier.index.runtime
          state.carrier.index.openConf.control.qterm
          (barrierDepth state.carrier.index.openConf.toConf + 1)
          state.carrier.index.openConf.toConf.counter =
        (head.scan.1, head.scan.2) := by
    change head.scan = (head.scan.1, head.scan.2)
    exact (Prod.eta head.scan).symm
  have constructed :=
    openedFor_pendingCallOf_representative_supported_relates
      head.database ready.indexReady head.predicate head.referencePayload
      state.carrier.index.current state.carrier.index.alpha head.arguments
      head.result head.executableTail state.carrier.index.runtime head.scan.1
      head.scan.2 head.arity head.executableStateHead scanned ready.queryAtOpen.weak
      ready.candidateSupported
  simpa [NestedCallHead.pending, head.qtermEq] using constructed

theorem fineEntry {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {state : RepresentativeActivePayloadState}
    {head : NestedCallHead state.carrier}
    (ready : MaterializedNestedCallReady state head) :
    DemandDrivenCallStep.Step prog gt (.ready state.carrier.index.openConf)
      (.callPending head.pending) :=
  ready.toNestedCallOperationalReady.fineEntry

theorem retainedFrontier
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {state : RepresentativeActivePayloadState}
    {head : NestedCallHead state.carrier}
    (ready : MaterializedNestedCallReady state head) :
    ∃ count : Nat, ∃ skippedBranches : List ClauseBranch,
      ∃ skippedClauses : List PLeaTTa.Clause,
      ∃ finish : PreparedCursor, ∃ branch : ClauseBranch,
      ∃ clause : PLeaTTa.Clause, ∃ branchTail : List ClauseBranch,
      ∃ clauseTail : List PLeaTTa.Clause, ∃ altTail : List PLeaTTa.Alt,
      ∃ copied : PLeaTTa.Clause,
        (openedFor state.carrier.index.session head.predicate
            head.referencePayload state.carrier.index.current).cursor.remaining =
          skippedBranches ++ (branch :: branchTail) ∧
        state.carrier.index.openConf.persistent.world.resolutionCandidates
            head.predicate head.arguments.length =
          skippedClauses ++ (clause :: clauseTail) ∧
        skippedBranches.length = count ∧
        skippedClauses.length = count ∧
        RejectedPullsN count
          (openedFor state.carrier.index.session head.predicate
            head.referencePayload state.carrier.index.current).cursor
          finish ∧
        head.Frontier finish branch clause branchTail clauseTail altTail copied :=
  ready.toNestedCallOperationalReady.retainedFrontierOfEntry
    (prog := prog) (gt := gt) ready.entryRelates

theorem queryReferenceBelow
    {state : RepresentativeActivePayloadState}
    {head : NestedCallHead state.carrier}
    (ready : MaterializedNestedCallReady state head)
    {finish : PreparedCursor} {branch : ClauseBranch}
    {clause : PLeaTTa.Clause} {branchTail : List ClauseBranch}
    {clauseTail : List PLeaTTa.Clause} {altTail : List PLeaTTa.Alt}
    {copied : PLeaTTa.Clause}
    (frontier :
      head.Frontier finish branch clause branchTail clauseTail altTail copied) :
    GeneratedBelow finish.reservationStart
      (state.carrier.index.alpha.map Prod.fst) :=
  ready.toNestedCallOperationalReady.queryReferenceBelow frontier

/-- Eliminate readiness without erasing the selected occurrence or the
activation facts needed by the next nested call.  The occurrence equations,
pull path, frontier, and literal successor all come from one invocation of
the underlying producer. -/
theorem pushDetailed {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {state : RepresentativeActivePayloadState}
    {head : NestedCallHead state.carrier}
    (ready : MaterializedNestedCallReady state head) :
    ∃ count : Nat, ∃ skippedBranches : List ClauseBranch,
      ∃ skippedClauses : List PLeaTTa.Clause,
      ∃ finish : PreparedCursor, ∃ branch : ClauseBranch,
      ∃ clause : PLeaTTa.Clause, ∃ branchTail : List ClauseBranch,
      ∃ clauseTail : List PLeaTTa.Clause, ∃ altTail : List PLeaTTa.Alt,
      ∃ copied : PLeaTTa.Clause, ∃ installed : Subst,
      ∃ after : RepresentativeActivePayloadState,
        RepresentativeNestedCallSuccessorFacts prog gt state head count
          skippedBranches
          skippedClauses finish branch clause branchTail clauseTail altTail
          copied installed after := by
  obtain
    ⟨count, skippedBranches, skippedClauses, finish, branch, clause,
      branchTail, clauseTail, altTail, copied, branchesEq, clausesEq,
      branchCount, clauseCount, pulls, frontier⟩ :=
    ready.retainedFrontier (prog := prog) (gt := gt)
  obtain ⟨independentResult, resolved, live⟩ := ready.selected pulls frontier
  let callerSegment : ControlSegment :=
    { barrier := state.carrier.index.callerBarrier
      references := state.carrier.index.callerReferences
      executables := state.carrier.index.callerExecutables }
  obtain
    ⟨nextAlpha, sourceCanonical, flattenedRepresentative, installed,
      activation⟩ :=
    RepresentativeRetainedCallFrontier.activate_spined_product_step_with
      (prog := prog) (gt := gt)
      (referencePayload := head.referencePayload)
      (segmentReferenceRest := head.referenceRest)
      (segmentExecutableRest := head.executableRest)
      (outer := callerSegment :: state.carrier.index.outer)
      (callerBarrier := state.carrier.index.bodyBarrier)
      (callerScope := state.carrier.index.opened.scope)
      ready.entryRelates frontier head.spinePayload state.cumulative
      ready.queryAtOpen
      (by simp [openedFor, openLocalCall, requestFor, prepareCall])
      (ready.queryReferenceBelow frontier)
      (by
        simpa [OpenConf.toConf, Control.toConf] using
          ready.toNestedCallOperationalReady.alphaFresh.2) live
      resolved
  obtain
    ⟨nestedActive, nestedPayloadContext, _sourceSteps, _fineSteps,
      nestedAgreement, _payloadHandoff, _countGrowth, certificate⟩ :=
    SpinedRepresentativeProductActivation.spinedNestedProductPayloadPrefix
      (prog := prog) (gt := gt)
      (currentAgreement := head.carrierAgreement)
      (entry := ready.entryRelates.entry)
      (frontier := frontier) (pulls := pulls)
      state.cumulative ready.materialized (ready.queryReferenceBelow frontier)
      activation ready.notThrow ready.notDatabase
      ready.fineEntry
  have sealedEntry :
      PLeaTTa.Step prog gt state.carrier.index.openConf.toConf
        head.pending.pulled.toConf :=
    DemandDrivenCallStep.Step.ready_callPending_projects_to_sealed
      ready.fineEntry
  have activatedBelow :
      ConfBelowResolutionCounter
        (PrologRepresentativeStepActivationBridge.activatedExecutableSuccessor
          head.pending copied head.executableTail state.carrier.index.qterm
          installed) :=
    activation.executableStep.preserves_belowResolutionCounter
      (sealedEntry.preserves_belowResolutionCounter ready.below)
  rw [head.carrierStateEq] at certificate
  let afterCarrier := ActivePayloadState.ofAgreement nestedAgreement
  have afterCumulative :
      AlphaCumulativeResidualVariantAgreesOnWith afterCarrier.index.alpha
        afterCarrier.index.support afterCarrier.index.canonical
        afterCarrier.index.referenceBase afterCarrier.index.runtime
        (flattenedRepresentative ++ state.representative) := by
    change
      AlphaCumulativeResidualVariantAgreesOnWith nextAlpha
        state.carrier.index.support
        (sourceCanonical ++ state.carrier.index.canonical)
        state.carrier.index.referenceBase
        (PLeaTTa.trimFor
          (copied.body ++
            (head.executableRest ++
              (callerSegment.executables ++
                flattenExecutables state.carrier.index.outer)))
          state.carrier.index.qterm installed)
        (flattenedRepresentative ++ state.representative)
    exact activation.cumulative
  let after : RepresentativeActivePayloadState :=
    { carrier := afterCarrier
      representative := flattenedRepresentative ++ state.representative
      cumulative := afterCumulative }
  refine
    ⟨count, skippedBranches, skippedClauses, finish, branch, clause,
      branchTail, clauseTail, altTail, copied, installed, after, ?_⟩
  refine
    { sourceBank := branchesEq
      executableBank := clausesEq
      sourceSkipCount := branchCount
      executableSkipCount := clauseCount
      pulls := pulls
      frontier := frontier
      resolution := ?_
      bodyReferences := ?_
      bodyExecutables := ?_
      activationStep := ?_
      runtimeExact := ?_
      alphaExtension := ?_
      selectionFresh := ?_
      supportPreserved := ?_
      freshFrontierExact := ?_
      sessionExact := ?_
      worldPreserved := ?_
      qtermPreserved := ?_
      below := ?_
      certificate := certificate
      representativeExtension := ⟨flattenedRepresentative, rfl⟩
      generatedMguExtension := ?_
      materializedBodyHeads := ?_ }
  · change HeadResolution branch independentResult
    exact resolved
  · rfl
  · rfl
  · exact activation.executableStep
  · rfl
  · change
      AlphaExtendsAbove state.carrier.index.alpha nextAlpha branch.firstFresh
        state.carrier.index.openConf.toConf.counter
    exact activation.alphaExtension
  · change
      AlphaFreshFrontier nextAlpha branch.nextFresh
        (state.carrier.index.openConf.toConf.counter + 1)
    exact activation.selectionFresh
  · rfl
  · rfl
  · rfl
  · change
      (PrologRepresentativeStepActivationBridge.activatedExecutableSuccessor
          head.pending copied head.executableTail state.carrier.index.qterm
          installed).world = state.carrier.index.openConf.persistent.world
    simpa [NestedCallHead.pending, DemandDrivenCallStep.pendingCallOf] using
      activation.worldPreserved
  · rfl
  · change
      ConfBelowResolutionCounter
        (PrologRepresentativeStepActivationBridge.activatedOpenSuccessor
          head.pending copied head.executableTail state.carrier.index.qterm
          installed).toConf
    simpa using activatedBelow
  · refine ⟨flattenedRepresentative, rfl, ?_⟩
    change
      PendingHeadMguAgrees nextAlpha flattenedRepresentative installed
        head.pending copied
        (head.executableRest ++
          (callerSegment.executables ++
            flattenExecutables state.carrier.index.outer))
    exact activation.headMgu
  · change
      MaterializedLocalCallHeadsAgreeWith nextAlpha independentResult
        branch.body copied.body
        (PLeaTTa.trimFor
          (copied.body ++
            (head.executableRest ++
              (callerSegment.executables ++
                flattenExecutables state.carrier.index.outer)))
          state.carrier.index.qterm installed)
        (flattenedRepresentative ++ state.representative)
        state.carrier.index.referenceBase
    exact activation.materializedBodyHeads

/-- Compact representative-preserving elimination.

Unlike the legacy `NestedCallReady.push`, this theorem never forgets which
residual representative was selected.  The returned extension equation is
the exact handoff consumed by a later materialized recursive call. -/
theorem push {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {state : RepresentativeActivePayloadState}
    {head : NestedCallHead state.carrier}
    (ready : MaterializedNestedCallReady state head) :
    ∃ count : Nat, ∃ after : RepresentativeActivePayloadState,
      NestedCallPushCertificate prog gt count
          (requestFor head.predicate head.referencePayload
            state.carrier.index.current)
          state.carrier after.carrier ∧
        ∃ extension : TreeSubstitution,
          after.representative = extension ++ state.representative := by
  obtain
    ⟨count, skippedBranches, skippedClauses, finish, branch, clause,
      branchTail, clauseTail, altTail, copied, installed, after, facts⟩ :=
    ready.pushDetailed (prog := prog) (gt := gt)
  exact
    ⟨count, after, facts.certificate, facts.representativeExtension⟩

/-- Two materialized readiness eliminations compose while retaining one
explicit representative lineage through both literal successors. -/
theorem pushTwice {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : RepresentativeActivePayloadState}
    {firstHead : NestedCallHead before.carrier}
    (firstReady : MaterializedNestedCallReady before firstHead)
    (nextReady :
      ∀ {firstRejects : Nat} {skippedBranches : List ClauseBranch}
          {skippedClauses : List PLeaTTa.Clause}
          {finish : PreparedCursor} {branch : ClauseBranch}
          {clause : PLeaTTa.Clause} {branchTail : List ClauseBranch}
          {clauseTail : List PLeaTTa.Clause} {altTail : List PLeaTTa.Alt}
          {copied : PLeaTTa.Clause} {installed : Subst}
          {middle : RepresentativeActivePayloadState},
        RepresentativeNestedCallSuccessorFacts prog gt before firstHead
            firstRejects skippedBranches skippedClauses finish branch clause
            branchTail clauseTail altTail copied installed middle →
          ∃ secondHead : NestedCallHead middle.carrier,
            MaterializedNestedCallReady middle secondHead) :
    ∃ firstRejects : Nat, ∃ middle : RepresentativeActivePayloadState,
      ∃ _first : NestedCallPushCertificate prog gt firstRejects
          (requestFor firstHead.predicate firstHead.referencePayload
            before.carrier.index.current)
          before.carrier middle.carrier,
        (∃ extension : TreeSubstitution,
            middle.representative = extension ++ before.representative) ∧
          ∃ secondHead : NestedCallHead middle.carrier,
            ∃ secondRejects : Nat,
              ∃ after : RepresentativeActivePayloadState,
                NestedCallPushCertificate prog gt secondRejects
                    (requestFor secondHead.predicate secondHead.referencePayload
                      middle.carrier.index.current)
                    middle.carrier after.carrier ∧
                  ∃ extension : TreeSubstitution,
                    after.representative =
                      extension ++ middle.representative := by
  obtain
    ⟨firstRejects, skippedBranches, skippedClauses, finish, branch, clause,
      branchTail, clauseTail, altTail, copied, installed, middle,
      firstFacts⟩ :=
    firstReady.pushDetailed (prog := prog) (gt := gt)
  obtain ⟨secondHead, secondReady⟩ := nextReady firstFacts
  obtain ⟨secondRejects, after, second, secondExtension⟩ :=
    secondReady.push (prog := prog) (gt := gt)
  exact
    ⟨firstRejects, middle, firstFacts.certificate,
      firstFacts.representativeExtension, secondHead, secondRejects, after,
      second, secondExtension⟩

end MaterializedNestedCallReady

namespace NestedCallReady

/-- Compatibility elimination for raw-supported callers.

The raw payload chooses one representative exactly once.  The actual
activation then runs entirely through `MaterializedNestedCallReady`, and only
the representative annotation is projected away from the returned carrier. -/
theorem pushDetailed {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {state : ActivePayloadState} {head : NestedCallHead state}
    (ready : NestedCallReady state head) :
    ∃ count : Nat, ∃ skippedBranches : List ClauseBranch,
      ∃ skippedClauses : List PLeaTTa.Clause,
      ∃ finish : PreparedCursor, ∃ branch : ClauseBranch,
      ∃ clause : PLeaTTa.Clause, ∃ branchTail : List ClauseBranch,
      ∃ clauseTail : List PLeaTTa.Clause, ∃ altTail : List PLeaTTa.Alt,
      ∃ copied : PLeaTTa.Clause, ∃ installed : Subst,
      ∃ after : ActivePayloadState,
        NestedCallSuccessorFacts prog gt state head count skippedBranches
          skippedClauses finish branch clause branchTail clauseTail altTail
          copied installed after := by
  obtain ⟨representative, cumulative, materialized⟩ :=
    (PrologRecursiveCallPayloadBridge.TaskPayloadAgrees.localCallPayload
      head.payload).materializedCallAgreesWith ready.payloadSupported
  let before : RepresentativeActivePayloadState :=
    { carrier := state
      representative := representative
      cumulative := cumulative }
  have materializedReady : MaterializedNestedCallReady before head := by
    refine
      { toNestedCallOperationalReady := ready.toNestedCallOperationalReady
        materialized := ?_ }
    simpa [before] using materialized
  obtain
    ⟨count, skippedBranches, skippedClauses, finish, branch, clause,
      branchTail, clauseTail, altTail, copied, installed, after, facts⟩ :=
    materializedReady.pushDetailed (prog := prog) (gt := gt)
  exact
    ⟨count, skippedBranches, skippedClauses, finish, branch, clause,
      branchTail, clauseTail, altTail, copied, installed, after.carrier,
      facts.toNestedCallSuccessorFacts⟩

/-- Compatibility projection retaining the original compact certificate API.
The richer occurrence and activation facts remain available through
`pushDetailed` for recursive readiness. -/
theorem push {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {state : ActivePayloadState} {head : NestedCallHead state}
    (ready : NestedCallReady state head) :
    ∃ count : Nat, ∃ after : ActivePayloadState,
      NestedCallPushCertificate prog gt count
        (requestFor head.predicate head.referencePayload state.index.current)
        state after := by
  obtain
    ⟨count, skippedBranches, skippedClauses, finish, branch, clause,
      branchTail, clauseTail, altTail, copied, installed, after, facts⟩ :=
    ready.pushDetailed (prog := prog) (gt := gt)
  exact ⟨count, after, facts.certificate⟩

/-- Two readiness eliminations compose through the first elimination's
literal successor.  The dependent continuation cannot be instantiated with a
shape-compatible state from another run. -/
theorem pushTwice {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : ActivePayloadState} {firstHead : NestedCallHead before}
    (firstReady : NestedCallReady before firstHead)
    (nextReady :
      ∀ {firstRejects : Nat} {skippedBranches : List ClauseBranch}
          {skippedClauses : List PLeaTTa.Clause}
          {finish : PreparedCursor} {branch : ClauseBranch}
          {clause : PLeaTTa.Clause} {branchTail : List ClauseBranch}
          {clauseTail : List PLeaTTa.Clause} {altTail : List PLeaTTa.Alt}
          {copied : PLeaTTa.Clause} {installed : Subst}
          {middle : ActivePayloadState},
        NestedCallSuccessorFacts prog gt before firstHead firstRejects
            skippedBranches skippedClauses finish branch clause branchTail
            clauseTail altTail copied installed middle →
          ∃ secondHead : NestedCallHead middle,
            NestedCallReady middle secondHead) :
    ∃ firstRejects : Nat, ∃ middle : ActivePayloadState,
      ∃ _first :
        NestedCallPushCertificate prog gt firstRejects
          (requestFor firstHead.predicate firstHead.referencePayload
            before.index.current)
          before middle,
        ∃ secondHead : NestedCallHead middle, ∃ secondRejects : Nat,
          ∃ after : ActivePayloadState,
            NestedCallPushCertificate prog gt secondRejects
              (requestFor secondHead.predicate secondHead.referencePayload
                middle.index.current)
              middle after := by
  obtain
    ⟨firstRejects, skippedBranches, skippedClauses, finish, branch, clause,
      branchTail, clauseTail, altTail, copied, installed, middle, firstFacts⟩ :=
    firstReady.pushDetailed (prog := prog) (gt := gt)
  obtain ⟨secondHead, secondReady⟩ := nextReady firstFacts
  obtain ⟨secondRejects, after, second⟩ := secondReady.push
  exact
    ⟨firstRejects, middle, firstFacts.certificate, secondHead, secondRejects,
      after, second⟩

end NestedCallReady

end PLeaTTa.PrologNestedCallReadyBridge
