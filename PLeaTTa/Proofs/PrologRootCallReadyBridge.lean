-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologRootCallReadyBridge
Purpose: Construct one exact representative local-call activation from a
  literal root task, with derived rejected-prefix cost on the source side.
Trusted boundary: none
Main exports:
  RepresentativeRootCallSuccessorFacts,
  RepresentativeSupportedCallEntryRelates.activate_literal_root
-/
import PLeaTTa.Proofs.PrologNestedCallReadyBridge

namespace PLeaTTa.PrologRootCallReadyBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open OpenBindingAgreement
open PrologAlphaFreshFrontierBridge
open PrologCallEntryBridge
open PrologCallStepBridge
open PrologControlSegmentSpineBridge
open PrologCurrentSessionPayloadBridge
open PrologHeadFailureContinuationBridge
open PrologMguBridge
open PrologMguComposition
open PrologNestedCallChainBridge
open PrologNestedCallReadyBridge
open PrologOrdinaryStepBridge
open PrologPrefilterScanBridge
open PrologProductResourceContextBridge
open PrologRepresentativeCallFrontierBridge
open PrologRepresentativeProductActivationBridge
open PrologRecursiveCallPayloadBridge
open PrologRetainedPayloadSnapshotBridge
open PrologSourceProductContextBridge
open PrologStateBridge
open PrologSupportedCallFrontierBridge
open SourceControlResourcePayloadContextAgrees

/-- Exact facts produced by entering and activating one literal root call.

The rejected-prefix count and both skipped occurrence banks are outputs.  A
caller therefore cannot choose a cheaper source prefix than the actual
source-ordered scan aligned with the executable prefilter.  The fine lane
always takes call-entry, call-pull, and head-activation: exactly three steps,
independently of the number of omitted source occurrences that the source
cursor must reject explicitly.

The active carrier owns the complete payload/resource zipper.  `openSession`
is deliberately separate because that carrier relates persistent state and
resources, whereas this root theorem additionally preserves all three typed
control allocator frontiers. -/
structure RepresentativeRootCallSuccessorFacts
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (session : Session) (before : OpenConf) (scope : CutScopeId)
    (predicate : String) (referencePayload : List Term)
    (referenceBindings : Substitution)
    (args : List Atom) (res : Atom) (binding : Subst)
    (branches : List PLeaTTa.Alt) (finalCounter callerBarrier : Nat)
    (rejects : Nat) (skippedBranches : List ClauseBranch)
    (skippedClauses : List PLeaTTa.Clause)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (clause : PLeaTTa.Clause) (branchTail : List ClauseBranch)
    (clauseTail : List PLeaTTa.Clause) (altTail : List PLeaTTa.Alt)
    (copied : PLeaTTa.Clause) (independentResult : Substitution)
    (representative : TreeSubstitution)
    (nextAlpha : List (LogicVar × String))
    (sourceCanonical flattenedRepresentative : TreeSubstitution)
    (installed : Subst)
    (after : RepresentativeActivePayloadState) : Prop where
  sourceBank :
    (openedFor session predicate referencePayload referenceBindings).cursor.remaining =
      skippedBranches ++ (branch :: branchTail)
  executableBank :
    before.persistent.world.resolutionCandidates predicate args.length =
      skippedClauses ++ (clause :: clauseTail)
  sourceSkipCount : skippedBranches.length = rejects
  executableSkipCount : skippedClauses.length = rejects
  pulls :
    RejectedPullsN rejects
      (openedFor session predicate referencePayload referenceBindings).cursor
      finish
  frontier :
    RepresentativeRetainedCallFrontier alpha
      (openedFor session predicate referencePayload referenceBindings)
      before (DemandDrivenCallStep.pendingCallOf before branches finalCounter)
      finish branch clause branchTail clauseTail altTail copied
      (args.map (PLeaTTa.subst binding)) args res [] binding
      before.control.qterm (barrierDepth before.toConf + 1)
      before.toConf.counter
  bodyReferences : after.carrier.index.bodyReferences = branch.body
  bodyExecutables : after.carrier.index.bodyExecutables = copied.body
  resolution : HeadResolution branch after.carrier.index.current
  oldCumulative :
    AlphaCumulativeResidualVariantAgreesOnWith alpha support canonical
      referenceBase binding representative
  materializedAtOpen :
    MaterializedCallAgreesWith alpha referenceBindings referencePayload
      (args.map (PLeaTTa.subst binding)) (PLeaTTa.subst binding res)
      representative referenceBase
  activation :
    SpinedRepresentativeProductActivation prog gt alpha support canonical
      referenceBase
      (openedFor session predicate referencePayload referenceBindings)
      (DemandDrivenCallStep.pendingCallOf before branches finalCounter)
      finish branch branchTail altTail copied [] [] [] before.control.qterm
      (barrierDepth before.toConf + 1) callerBarrier before.toConf.counter
      scope independentResult representative nextAlpha sourceCanonical
      flattenedRepresentative installed
  carrierAlpha : after.carrier.index.alpha = nextAlpha
  carrierSupport : after.carrier.index.support = support
  carrierCurrent : after.carrier.index.current = independentResult
  retainedCursorExact :
    after.carrier.index.finish.advance after.carrier.index.branch
        after.carrier.index.branchTail =
      finish.advance branch branchTail
  activeAltsExact : after.carrier.index.active.alts = altTail
  activeResourceExact :
    after.carrier.index.active =
      retainedTailResource (finish.advance branch branchTail)
        (args.map (PLeaTTa.subst binding)) args res [] binding
        before.control.qterm (barrierDepth before.toConf + 1)
        before.toConf.counter altTail finalCounter
  carrierRepresentative :
    after.representative = flattenedRepresentative ++ representative
  snapshotRepresentative :
    (SourceControlResourcePayloadContextAgrees.headCell
      after.carrier.payloadContext).snapshot.residualRepresentative =
        representative
  sourceStateExact :
    after.carrier.sourceState =
      .running
        (openedFor session predicate referencePayload
          referenceBindings).session
        (activatedSourceProduct scope
          (openedFor session predicate referencePayload referenceBindings)
          finish branch branchTail independentResult [])
  fineStateExact :
    after.carrier.fineState =
      .ready
        (PrologRepresentativeStepActivationBridge.activatedOpenSuccessor
          (DemandDrivenCallStep.pendingCallOf before branches finalCounter)
          copied [] before.control.qterm installed)
  materializedBodyHeads :
    MaterializedLocalCallHeadsAgreeWith after.carrier.index.alpha
      after.carrier.index.current after.carrier.index.bodyReferences
      after.carrier.index.bodyExecutables after.carrier.index.runtime
      after.representative after.carrier.index.referenceBase
  sourceSteps :
    StepsN (rejects + 2)
      (.running session
        (.task scope [.call predicate referencePayload] referenceBindings))
      [.opened (requestFor predicate referencePayload referenceBindings)]
      after.carrier.sourceState
  fineSteps :
    DemandDrivenCallStep.StepsN prog gt 3 (.ready before)
      after.carrier.fineState
  below : ConfBelowResolutionCounter after.carrier.index.openConf.toConf
  framesEmpty : after.carrier.index.openConf.frames = []
  outerEmpty : after.carrier.index.outer = []
  resourcesEmpty : after.carrier.index.resources = []
  contextEmpty : after.carrier.index.context = []
  baseAltsEmpty : after.carrier.index.baseAlts = []
  callerReferencesEmpty : after.carrier.index.callerReferences = []
  callerExecutablesEmpty : after.carrier.index.callerExecutables = []
  freshFrontierExact :
    after.carrier.index.freshFrontier =
      AlphaFreshFrontier after.carrier.index.alpha
  supportPreserved : after.carrier.index.support = support
  sessionExact :
    after.carrier.index.session =
      (openedFor session predicate referencePayload referenceBindings).session
  worldPreserved :
    after.carrier.index.openConf.persistent.world = before.persistent.world
  qtermPreserved : after.carrier.index.qterm = before.control.qterm
  openSession :
    SessionRelatesOpenConf
      (AlphaFreshFrontier after.carrier.index.alpha) ExactControlFrontiers
      after.carrier.index.session after.carrier.index.openConf
  alphaExtension :
    AlphaExtendsAbove alpha after.carrier.index.alpha branch.firstFresh
      before.toConf.counter
  selectionFresh :
    AlphaFreshFrontier after.carrier.index.alpha branch.nextFresh
      (before.toConf.counter + 1)

/-- Construct a literal-root activation from the real entry bank and one
selected semantic clause.

All root-only control/resource arguments are fixed here: there is no outer
segment, retained resource, frame context, or base alternative.  In
particular, the returned source prefix starts at the literal `.task`, not at
an already-open cursor.  Consequently the selected liveness premise ranges
over `copied.body` alone: the executable caller tail is fixed to `[]` here and
cannot later be generalized independently. -/
theorem RepresentativeSupportedCallEntryRelates.activate_literal_root
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {session : Session} {before : OpenConf} {scope : CutScopeId}
    {predicate : String} {referencePayload : List Term}
    {referenceBindings : Substitution}
    {args : List Atom} {res : Atom} {binding : Subst}
    {branches : List PLeaTTa.Alt} {finalCounter callerBarrier : Nat}
    (entry :
      RepresentativeSupportedCallEntryRelates alpha
        (openedFor session predicate referencePayload referenceBindings)
        before (DemandDrivenCallStep.pendingCallOf before branches finalCounter)
        (args.map (PLeaTTa.subst binding)) args res [] binding
        before.control.qterm (barrierDepth before.toConf + 1)
        before.toConf.counter)
    (payload :
      TaskSpinePayloadAgrees alpha support canonical referenceBase
        referenceBindings binding
        [{ barrier := callerBarrier
           references := [.call predicate referencePayload]
           executables := [.call predicate args res] }])
    (payloadSupported : AlphaTermsSupported alpha support referencePayload)
    (beforeSession :
      SessionRelatesOpenConf (AlphaFreshFrontier alpha) ExactControlFrontiers
        session before)
    (rootAlts : before.control.alts = [])
    (rootFrames : before.frames = [])
    (below : ConfBelowResolutionCounter before.toConf)
    (nonempty : branches ≠ [])
    (selected :
      ∀ {count : Nat} {finish : PreparedCursor} {branch : ClauseBranch}
        {clause : PLeaTTa.Clause} {branchTail : List ClauseBranch}
        {clauseTail : List PLeaTTa.Clause} {altTail : List PLeaTTa.Alt}
        {copied : PLeaTTa.Clause},
        RejectedPullsN count
            (openedFor session predicate referencePayload
              referenceBindings).cursor finish →
          RepresentativeRetainedCallFrontier alpha
            (openedFor session predicate referencePayload referenceBindings)
            before
            (DemandDrivenCallStep.pendingCallOf before branches finalCounter)
            finish branch clause branchTail clauseTail altTail copied
            (args.map (PLeaTTa.subst binding)) args res [] binding
            before.control.qterm (barrierDepth before.toConf + 1)
            before.toConf.counter →
          ∃ independentResult : Substitution,
            HeadResolution branch independentResult ∧
              AlphaRuntimeNamesLive support copied.body before.control.qterm)
    (notThrow : ¬ BuiltinThrowCall predicate referencePayload)
    (notDatabase :
      DatabaseActions.recognizeDatabaseAction predicate referencePayload = none) :
    ∃ rejects skippedBranches skippedClauses finish branch clause branchTail
        clauseTail altTail copied independentResult representative nextAlpha
        sourceCanonical flattenedRepresentative installed after,
      RepresentativeRootCallSuccessorFacts prog gt alpha support canonical
        referenceBase session before scope predicate referencePayload
        referenceBindings args res binding branches finalCounter callerBarrier
        rejects skippedBranches skippedClauses finish branch clause branchTail
        clauseTail altTail copied independentResult representative nextAlpha
        sourceCanonical flattenedRepresentative installed after := by
  let opened :=
    openedFor session predicate referencePayload referenceBindings
  let pending :=
    DemandDrivenCallStep.pendingCallOf before branches finalCounter
  obtain
      ⟨rejects, skippedBranches, skippedClauses, finish, branch, clause,
        branchTail, clauseTail, altTail, copied, sourceBank, executableBank,
        sourceSkipCount, executableSkipCount, pulls, sourcePulls, finePull,
        frontier⟩ :=
    entry.callPull_retained_frontier (prog := prog) (gt := gt) below nonempty
  obtain ⟨independentResult, resolved, live⟩ := selected pulls frontier
  have preHeadTask :
      TaskPayloadAgrees alpha support callerBarrier canonical referenceBase
        referenceBindings binding [.call predicate referencePayload]
        [.call predicate args res] :=
    TaskSpinePayloadAgrees.headPayload payload
  obtain ⟨representative, oldCumulative, materializedAtOpen⟩ :=
    (PrologRecursiveCallPayloadBridge.TaskPayloadAgrees.localCallPayload
      preHeadTask).materializedCallAgreesWith payloadSupported
  have queryAtOpen :
      RepresentativeNormalizedCallAgreesWith alpha opened.cursor
        (args.map (PLeaTTa.subst binding)) (PLeaTTa.subst binding res)
        representative referenceBase := by
    exact materializedAtOpen.toRepresentativeNormalizedCallAgreesWith
      opened.cursor (by rfl) (by rfl)
  have queryReferenceBelow :
      GeneratedBelow finish.reservationStart (alpha.map Prod.fst) := by
    intro index member
    exact lt_of_lt_of_le
      (beforeSession.persistent.fresh.1 index member)
      (Nat.le_trans
        (openLocalCall_reservationStart_ge session
          (requestFor predicate referencePayload referenceBindings))
        frontier.finishReservationStart)
  have queryExecutableBelow :
      resolutionSeedHighWaterNames (alpha.map Prod.snd) ≤
        before.toConf.counter :=
    beforeSession.persistent.fresh.2
  obtain
      ⟨nextAlpha, sourceCanonical, flattenedRepresentative, installed,
        activation⟩ :=
    RepresentativeRetainedCallFrontier.activate_spined_product_step_with
      (prog := prog) (gt := gt) (referencePayload := referencePayload)
      (segmentReferenceRest := []) (segmentExecutableRest := [])
      (outer := []) (callerBarrier := callerBarrier) (callerScope := scope)
      entry frontier payload oldCumulative queryAtOpen (by rfl)
      queryReferenceBelow queryExecutableBelow
      (by
        intro identity name member
        simpa using live member)
      resolved
  let outerPayloads :
      SourceControlResourcePayloadContextAgrees alpha support
        before.control.qterm callerBarrier [] [] scope [] scope :=
    .nil callerBarrier scope
  have outerEndpoints :
      endpointsBelow outerPayloads opened.cursor.reservationStart
        before.toConf.counter := by
    trivial
  have outerOrdered : ActivationOrdered outerPayloads := by
    trivial
  have outerActivationOrigins :
      LocalActivationOriginSpineRelates opened.session outerPayloads := by
    simpa [outerPayloads] using
      (LocalActivationOriginSpineRelates.nil
        (alpha := alpha) (support := support)
        (qterm := before.control.qterm) opened.session callerBarrier scope)
  have outerAlts : pending.outer.alts = flattenOwnedAlts [] [] := by
    rw [entry.entry.outer]
    simp [rootAlts]
  have outerControlOrigins :
      LocalControlOriginSpineRelates [] pending.frames
        pending.outer.barriers outerPayloads := by
    simpa [outerPayloads] using
      (LocalControlOriginSpineRelates.nil
        (alpha := alpha) (support := support)
        (qterm := before.control.qterm) callerBarrier scope []
        pending.frames pending.outer.barriers)
  have finishPositioned :
      CallScopedCursorPosition opened.cursor finish rejects := by
    simpa using
      (CallScopedCursorPosition.afterRejected pulls
        (CallScopedCursorPosition.refl opened.cursor))
  have retainedPositioned :
      CallScopedCursorPosition opened.cursor
        (finish.advance branch branchTail) (rejects + 1) :=
    finishPositioned.advance frontier.finishRemaining
  obtain
      ⟨active, payloadContext, agreement, _outerExact,
        snapshotRepresentative, activeExact⟩ :=
    SpinedRepresentativeProductActivation.spinedProductPayloadResourceRelates
      (prog := prog) (gt := gt) (alpha := alpha) (support := support)
      (canonical := canonical) (referenceBase := referenceBase)
      (referenceBindings := referenceBindings)
      (argsv := args.map (PLeaTTa.subst binding)) (args := args) (res := res)
      (segmentReferenceRest := []) (segmentExecutableRest := [])
      (outer := []) (binding := binding) (qterm := before.control.qterm)
      (callerBarrier := callerBarrier) (callerScope := scope)
      (outerScope := scope) (resources := []) (context := [])
      (rejects + 1) retainedPositioned frontier payload oldCumulative
      materializedAtOpen (by rfl) (by rfl) queryReferenceBelow activation
      entry.entry.sourceFresh outerPayloads
      outerEndpoints outerOrdered outerActivationOrigins [] outerAlts
      outerControlOrigins
  let carrier := ActivePayloadState.ofAgreement agreement
  have carrierCumulative :
      AlphaCumulativeResidualVariantAgreesOnWith carrier.index.alpha
        carrier.index.support carrier.index.canonical
        carrier.index.referenceBase carrier.index.runtime
        (flattenedRepresentative ++ representative) := by
    simpa [carrier, ActivePayloadState.ofAgreement] using activation.cumulative
  let after : RepresentativeActivePayloadState :=
    { carrier := carrier
      representative := flattenedRepresentative ++ representative
      cumulative := carrierCumulative }
  have sourceNonempty :
      session.resolver.database.visibleClausesAt
        session.resolver.database.generation predicate
        referencePayload.length ≠ [] := by
    intro empty
    have cursorEmpty : opened.cursor.remaining = [] := by
      simp [opened, openedFor, openLocalCall, requestFor, prepareCall,
        empty, reserveVisible]
    rw [cursorEmpty] at sourceBank
    simp at sourceBank
  have scanned :
      resolveAlts
          (before.toConf.world.resolutionCandidates predicate args.length)
          (args.map (PLeaTTa.subst binding)) args res [] binding
          before.toConf.qterm (barrierDepth before.toConf + 1)
          before.toConf.counter =
        (branches, finalCounter) := by
    rw [PrologActivationMacro.resolveAlts_eq_scanResolution]
    exact entry.entry.bank.scan.result_eq
  obtain ⟨sourceEntryRaw, fineEntry, _entryAgain⟩ :=
    taskCall_callEnter_bank_correspondence
      (prog := prog) (gt := gt) (session := session) (state := before)
      beforeSession.persistent.database entry.indexReady scope predicate
      referencePayload [] referenceBindings args res [] binding branches
      finalCounter entry.entry.arity notThrow notDatabase sourceNonempty
      entry.entry.callHead scanned
  have sourceEntry :
      Transition
        (.running session
          (.task scope [.call predicate referencePayload] referenceBindings))
        [.opened (requestFor predicate referencePayload referenceBindings)]
        (.running opened.session
          (sourceProductFrontier scope opened opened.cursor [])) := by
    exact Transition.ordinary _ _ _ _ _ sourceEntryRaw
  have sourceActivation :
      Transition
        (.running opened.session
          (sourceProductFrontier scope opened finish [])) []
        carrier.sourceState := by
    change
      Transition
        (.running opened.session
          (sourceProductFrontier scope opened finish [])) []
        (.running opened.session
          (activatedSourceProduct scope opened finish branch branchTail
            independentResult []))
    exact Transition.ordinary _ _ _ _ _ activation.sourceStep
  have rootSourceSteps :
      StepsN (rejects + 2)
        (.running session
          (.task scope [.call predicate referencePayload] referenceBindings))
        [.opened (requestFor predicate referencePayload referenceBindings)]
        carrier.sourceState := by
    have entrySteps :
        StepsN 1
          (.running session
            (.task scope [.call predicate referencePayload]
              referenceBindings))
          [.opened (requestFor predicate referencePayload referenceBindings)]
          (.running opened.session
            (sourceProductFrontier scope opened opened.cursor [])) :=
      StepsN.succ 0 _ _ _ _ _ sourceEntry (StepsN.zero _)
    have pulledSteps :=
      PrologHeadFailureContinuationBridge.RejectedPullsN.sourceProductStepsN
        pulls scope opened []
    have activationSteps :
        StepsN 1
          (.running opened.session
            (sourceProductFrontier scope opened finish [])) []
          carrier.sourceState :=
      StepsN.succ 0 _ _ _ _ _ sourceActivation (StepsN.zero _)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (entrySteps.trans (pulledSteps.trans activationSteps))
  have rootFineSteps :
      DemandDrivenCallStep.StepsN prog gt 3 (.ready before)
        carrier.fineState := by
    change
      DemandDrivenCallStep.StepsN prog gt 3 (.ready before)
        (.ready
          (PrologRepresentativeStepActivationBridge.activatedOpenSuccessor
            pending copied [] before.control.qterm installed))
    simpa using
      DemandDrivenCallStep.StepsN.succ 2 _ _ _ fineEntry
        (DemandDrivenCallStep.StepsN.succ 1 _ _ _ finePull
          (DemandDrivenCallStep.StepsN.succ 0 _ _ _
            activation.fineExecutableStep
            (DemandDrivenCallStep.StepsN.zero _)))
  have sealedEntry :
      PLeaTTa.Step prog gt before.toConf pending.pulled.toConf :=
    PLeaTTa.PrologNestedCallReadyBridge.DemandDrivenCallStep.Step.ready_callPending_projects_to_sealed
      fineEntry
  have activeBelow :
      ConfBelowResolutionCounter
        (PrologRepresentativeStepActivationBridge.activatedExecutableSuccessor
          pending copied [] before.control.qterm installed) :=
    activation.executableStep.preserves_belowResolutionCounter
      (sealedEntry.preserves_belowResolutionCounter below)
  have afterOpenSession :
      SessionRelatesOpenConf (AlphaFreshFrontier nextAlpha)
        ExactControlFrontiers opened.session
        (PrologRepresentativeStepActivationBridge.activatedOpenSuccessor
          pending copied [] before.control.qterm installed) := by
    have persistentExact :
        (PrologRepresentativeStepActivationBridge.activatedOpenSuccessor
          pending copied [] before.control.qterm installed).persistent =
          pending.persistent := by
      unfold
        PrologRepresentativeStepActivationBridge.activatedOpenSuccessor
        OpenConf.stepOpen OpenConf.ofConfWith persistentOf
      have worldExact :
          (PrologRepresentativeStepActivationBridge.activatedExecutableSuccessor
            pending copied [] before.control.qterm installed).world =
            pending.persistent.world := by
        simpa [pending] using activation.worldPreserved
      have counterExact :
          (PrologRepresentativeStepActivationBridge.activatedExecutableSuccessor
            pending copied [] before.control.qterm installed).counter =
            pending.persistent.counter := by
        simpa [pending] using activation.counterPreserved
      rw [worldExact, counterExact]
    have persistent :
        SessionRelatesPersistent (AlphaFreshFrontier nextAlpha)
          opened.session
          (PrologRepresentativeStepActivationBridge.activatedOpenSuccessor
            pending copied [] before.control.qterm installed).persistent := by
      rw [persistentExact]
      exact activation.persistentAgreement
    have scopes :
        (PrologRepresentativeStepActivationBridge.activatedOpenSuccessor
          pending copied [] before.control.qterm installed).scopes =
          before.scopes.afterLocalCall := by
      simp [PrologRepresentativeStepActivationBridge.activatedOpenSuccessor,
        pending, DemandDrivenCallStep.pendingCallOf,
        DemandDrivenCallStep.PendingCall.pulled, OpenConf.stepOpen,
        OpenConf.ofConfWith]
    refine ⟨persistent, ?_, ?_, ?_⟩
    · change
        opened.session.nextCutScope =
          (PrologRepresentativeStepActivationBridge.activatedOpenSuccessor
            pending copied [] before.control.qterm installed).scopes.nextCutScope
      rw [scopes]
      change session.nextCutScope + 1 = before.scopes.nextCutScope + 1
      exact congrArg Nat.succ beforeSession.cut
    · change
        opened.session.nextExceptionScope =
          (PrologRepresentativeStepActivationBridge.activatedOpenSuccessor
            pending copied [] before.control.qterm installed).scopes.nextExceptionScope
      rw [scopes]
      exact beforeSession.exception
    · change
        opened.session.nextCollectionScope =
          (PrologRepresentativeStepActivationBridge.activatedOpenSuccessor
            pending copied [] before.control.qterm installed).scopes.nextCollectionScope
      rw [scopes]
      exact beforeSession.collection
  have afterOpenSessionExact :
      SessionRelatesOpenConf
        (AlphaFreshFrontier after.carrier.index.alpha) ExactControlFrontiers
        after.carrier.index.session after.carrier.index.openConf := by
    exact afterOpenSession
  refine
    ⟨rejects, skippedBranches, skippedClauses, finish, branch, clause,
      branchTail, clauseTail, altTail, copied, independentResult,
      representative, nextAlpha, sourceCanonical, flattenedRepresentative,
      installed, after, ?_⟩
  refine
    { sourceBank := sourceBank
      executableBank := ?_
      sourceSkipCount := sourceSkipCount
      executableSkipCount := executableSkipCount
      pulls := pulls
      frontier := frontier
      bodyReferences := rfl
      bodyExecutables := rfl
      resolution := ?_
      oldCumulative := oldCumulative
      materializedAtOpen := materializedAtOpen
      activation := activation
      carrierAlpha := rfl
      carrierSupport := rfl
      carrierCurrent := rfl
      retainedCursorExact := rfl
      activeAltsExact := by
        simpa [after, carrier, ActivePayloadState.ofAgreement] using
          agreement.core.resourceStack.activeAlts
      activeResourceExact := by
        simpa [after, carrier, ActivePayloadState.ofAgreement, pending,
          DemandDrivenCallStep.pendingCallOf] using activeExact
      carrierRepresentative := rfl
      snapshotRepresentative := by
        simpa [after, carrier, ActivePayloadState.ofAgreement] using
          snapshotRepresentative
      sourceStateExact := rfl
      fineStateExact := rfl
      materializedBodyHeads := ?_
      sourceSteps := rootSourceSteps
      fineSteps := rootFineSteps
      below := ?_
      framesEmpty := ?_
      outerEmpty := rfl
      resourcesEmpty := rfl
      contextEmpty := rfl
      baseAltsEmpty := rfl
      callerReferencesEmpty := rfl
      callerExecutablesEmpty := rfl
      freshFrontierExact := rfl
      supportPreserved := rfl
      sessionExact := rfl
      worldPreserved := ?_
      qtermPreserved := rfl
      openSession := afterOpenSessionExact
      alphaExtension := activation.alphaExtension
      selectionFresh := ?_ }
  · simpa [pending, opened, openedFor, openLocalCall, requestFor,
      prepareCall] using executableBank
  · change HeadResolution branch independentResult
    exact resolved
  · change
      MaterializedLocalCallHeadsAgreeWith
        (ActivePayloadState.ofAgreement agreement).index.alpha
        (ActivePayloadState.ofAgreement agreement).index.current
        (ActivePayloadState.ofAgreement agreement).index.bodyReferences
        (ActivePayloadState.ofAgreement agreement).index.bodyExecutables
        (ActivePayloadState.ofAgreement agreement).index.runtime
        (flattenedRepresentative ++ representative)
        (ActivePayloadState.ofAgreement agreement).index.referenceBase
    simp only [ActivePayloadState.ofAgreement, List.nil_append,
      flattenExecutables]
    exact activation.materializedBodyHeads
  · simpa [after, carrier, ActivePayloadState.ofAgreement,
      PrologRepresentativeStepActivationBridge.activatedOpenSuccessor]
      using activeBelow
  · change
      (PrologRepresentativeStepActivationBridge.activatedOpenSuccessor
        pending copied [] before.control.qterm installed).frames = []
    rw [PrologRepresentativeStepActivationBridge.activatedOpenSuccessor_frames]
    simpa [pending, DemandDrivenCallStep.pendingCallOf] using rootFrames
  · change
      (PrologRepresentativeStepActivationBridge.activatedExecutableSuccessor
        pending copied [] before.control.qterm installed).world =
        before.persistent.world
    simpa [pending, DemandDrivenCallStep.pendingCallOf] using
      activation.worldPreserved
  · change
      AlphaFreshFrontier nextAlpha branch.nextFresh
        (before.toConf.counter + 1)
    exact activation.selectionFresh

end PLeaTTa.PrologRootCallReadyBridge
