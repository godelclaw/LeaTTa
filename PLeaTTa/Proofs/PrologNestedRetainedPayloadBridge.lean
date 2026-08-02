-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologNestedRetainedPayloadBridge
Purpose: Transport every retained payload snapshot through one real nested
  local-clause activation while preserving allocator chronology.
Trusted boundary: none
Main exports:
  SourceControlResourcePayloadContextAgrees.endpointsBelow_openLocalCall,
  SpinedRepresentativeProductActivation.activeResourceStackWithNestedSnapshots
-/
import PLeaTTa.Proofs.PrologRetainedPayloadSnapshotBridge

namespace PLeaTTa.PrologNestedRetainedPayloadBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologRecursiveCallPayloadBridge
open PrologAlphaFreshFrontierBridge
open PrologRepresentativeStepActivationBridge
open PrologControlSegmentSpineBridge
open PrologMguComposition
open PrologOrdinaryStepBridge
open PrologBodyFailureResourceTransitionBridge
open PrologPrefilterScanBridge
open PrologProductResourceContextBridge
open PrologProductResourceTransitionBridge
open PrologRepresentativeCallFrontierBridge
open PrologRepresentativeProductActivationBridge
open PrologRetainedPayloadSnapshotBridge
open PrologSourceProductContextBridge
open PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees

/-- Opening the next nested call advances every older payload endpoint from
the incoming source high-water to the actual eager-reservation start.

This is the source-side recursive handoff: the previous activation returns
`endpointsBelow` at its current session, and the next concrete
`openLocalCall` turns that certificate into the precondition consumed by
`activeResourceStackWithNestedSnapshots`. -/
theorem
    SourceControlResourcePayloadContextAgrees.endpointsBelow_openLocalCall
    {alpha support : List (LogicVar × String)} {qterm : Atom}
    {currentBarrier : Nat}
    {segments : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {inner outer : CutScopeId} {context : ActiveProductContext}
    {executableFloor : Nat}
    (agreement :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        currentBarrier segments resources inner context outer)
    (session : Session) (request : CallRequest)
    (below :
      endpointsBelow agreement session.resolver.nextFresh executableFloor) :
    endpointsBelow agreement
      (openLocalCall session request).cursor.reservationStart
      executableFloor :=
  endpointsBelow_mono agreement below
    (openLocalCall_reservationStart_ge session request) (Nat.le_refl _)

/-- One real nested activation transports the complete outer payload zipper,
creates the new innermost snapshot, and returns domination of every retained
allocator endpoint by the current persistent high-waters.

The caller supplies no enlarged allocation gap.  `alphaExtension` from the
actual selected-clause activation and the structurally aligned
`endpointsBelow` certificate derive every outer gap.  The new head endpoint
is then pinned by the real prepared cursor and executable alternative bank. -/
theorem
    SpinedRepresentativeProductActivation.activeResourceStackWithNestedSnapshots
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {referenceBindings : Substitution}
    {opened : OpenedCall} {before : OpenConf}
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
    {callerScope outerScope : CutScopeId}
    {independentResult : Substitution}
    {representative : TreeSubstitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattenedRepresentative : TreeSubstitution}
    {installed : Subst}
    {resources : List RetainedAlternativeSegment}
    {context : ActiveProductContext}
    (retainedPosition : Nat)
    (positioned :
      CallScopedCursorPosition opened.cursor
        (finish.advance branch branchTail) retainedPosition)
    (frontier :
      RepresentativeRetainedCallFrontier alpha opened before pending finish
        branch clause branchTail clauseTail altTail copied argsv args res
        (segmentExecutableRest ++ flattenExecutables outer)
        binding qterm bodyBarrier startCounter)
    (preHeadPayload :
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
    (materializedAtOpen :
      MaterializedCallAgreesWith alpha referenceBindings referencePayload
        (args.map (PLeaTTa.subst binding))
        (PLeaTTa.subst binding res) representative referenceBase)
    (openedArguments : opened.cursor.arguments = referencePayload)
    (openedBindings : opened.cursor.bindings = referenceBindings)
    (queryReferenceBelow :
      GeneratedBelow finish.reservationStart (alpha.map Prod.fst))
    (activation :
      SpinedRepresentativeProductActivation prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        segmentReferenceRest segmentExecutableRest outer qterm bodyBarrier
        callerBarrier startCounter callerScope independentResult representative
        nextAlpha sourceCanonical flattenedRepresentative installed)
    (sourceFresh :
      opened.session.resolver.nextFresh = opened.cursor.reservedUntil)
    (outerPayloads :
      SourceControlResourcePayloadContextAgrees alpha support qterm
        callerBarrier outer resources callerScope context outerScope)
    (outerEndpoints :
      endpointsBelow outerPayloads opened.cursor.reservationStart
        startCounter)
    (outerOrdered : ActivationOrdered outerPayloads)
    (outerActivationOrigins :
      LocalActivationOriginSpineRelates opened.session outerPayloads)
    (baseAlts : List PLeaTTa.Alt)
    (outerAlts :
      pending.outer.alts = flattenOwnedAlts resources baseAlts) :
    ∃ active : RetainedAlternativeSegment,
      ∃ _snapshot : RetainedCallPayloadSnapshot nextAlpha support active
          (finish.advance branch branchTail)
          { barrier := callerBarrier
            references := segmentReferenceRest
            executables := segmentExecutableRest }
          outer,
        ∃ payloadContext :
            SourceControlResourcePayloadContextAgrees nextAlpha support qterm
              bodyBarrier
              ({ barrier := callerBarrier
                 references := segmentReferenceRest
                 executables := segmentExecutableRest } ::
               outer)
              (active :: resources) opened.scope
              ({ callerScope := callerScope
                 predicateScope := opened.scope
                 retained :=
                   .clauses opened.scope
                     (finish.advance branch branchTail)
                 callerRest := segmentReferenceRest } ::
               context)
              outerScope,
          endpointsBelow payloadContext
              opened.session.resolver.nextFresh
              pending.persistent.counter ∧
            ActivationOrdered payloadContext ∧
              LocalActivationOriginSpineRelates opened.session
                payloadContext ∧
              ExtendsAboveAt branch.firstFresh startCounter
                activation.alphaExtension outerPayloads
                (SourceControlResourcePayloadContextAgrees.tail
                  payloadContext) ∧
              endpointsBelow
                (SourceControlResourcePayloadContextAgrees.tail payloadContext)
                (finish.advance branch branchTail).reservationStart
                active.counter ∧
              (ActiveProductResourceStackAgrees nextAlpha qterm bodyBarrier
                callerBarrier pending (finish.advance branch branchTail)
                (segmentExecutableRest ++ flattenExecutables outer)
                altTail active outer resources callerScope outerScope context
                baseAlts
                (activatedOpenSuccessor pending copied
                  (segmentExecutableRest ++ flattenExecutables outer)
                  qterm installed)) ∧
              (SourceControlResourcePayloadContextAgrees.headCell
                payloadContext).snapshot.residualRepresentative =
                  representative ∧
                (SourceControlResourcePayloadContextAgrees.headCell
                  payloadContext).snapshot.controlOrigin.MatchesPendingControl
                    pending := by
  have branchMember : branch ∈ finish.remaining := by
    rw [frontier.finishRemaining]
    simp
  have selectedStart :
      opened.cursor.reservationStart ≤ branch.firstFresh :=
    Nat.le_trans frontier.finishReservationStart
      (frontier.finishWellFormed.1.start_le_member_first branchMember)
  have outerAtSelected :
      endpointsBelow outerPayloads branch.firstFresh startCounter :=
    endpointsBelow_mono outerPayloads outerEndpoints selectedStart
      (Nat.le_refl _)
  let outerNext :=
    extendAbove activation.alphaExtension outerPayloads outerAtSelected
  have outerNextAtSelected :
      endpointsBelow outerNext branch.firstFresh startCounter := by
    simpa [outerNext] using
      extendAbove_endpointsBelow activation.alphaExtension outerPayloads
        outerAtSelected
  have outerNextOrdered : ActivationOrdered outerNext := by
    exact
      ActivationOrdered.extendAbove activation.alphaExtension outerPayloads
        outerAtSelected outerOrdered
  have outerNextActivationOrigins :
      LocalActivationOriginSpineRelates opened.session outerNext := by
    exact
      outerActivationOrigins.extendAbove activation.alphaExtension
        outerPayloads outerAtSelected
  obtain ⟨active, snapshot, _existingContext, result⟩ :=
    PLeaTTa.PrologRetainedPayloadSnapshotBridge.SpinedRepresentativeProductActivation.activeResourceStackWithSnapshot
      retainedPosition positioned frontier preHeadPayload oldCumulative
      materializedAtOpen openedArguments
      openedBindings queryReferenceBelow activation
      outerNext baseAlts outerAlts
  have activeCounter : active.counter = startCounter + 1 := result.1
  have stack :
      ActiveProductResourceStackAgrees nextAlpha qterm bodyBarrier
        callerBarrier pending (finish.advance branch branchTail)
        (segmentExecutableRest ++ flattenExecutables outer)
        altTail active outer resources callerScope outerScope context
        baseAlts
        (activatedOpenSuccessor pending copied
          (segmentExecutableRest ++ flattenExecutables outer)
          qterm installed) := result.2.1
  have snapshotRepresentative :
      snapshot.residualRepresentative = representative := result.2.2.1
  have snapshotOrigin :
      snapshot.controlOrigin.MatchesPendingControl pending :=
    result.2.2.2.1
  have snapshotActivationExtends :
      snapshot.activationOrigin.Extends opened.session :=
    result.2.2.2.2.1
  have snapshotCutExact :
      snapshot.activationOrigin.nextCutScope = opened.scope + 1 :=
    result.2.2.2.2.2
  have branchFirstBelowSession :
      branch.firstFresh ≤ opened.session.resolver.nextFresh := by
    calc
      branch.firstFresh ≤ branch.nextFresh :=
        frontier.finishWellFormed.1.member_first_le_next branchMember
      _ ≤ finish.reservedUntil :=
        frontier.finishWellFormed.1.member_next_le_final branchMember
      _ = opened.cursor.reservedUntil := frontier.finishReservedUntil
      _ = opened.session.resolver.nextFresh := sourceFresh.symm
  have executableFrontierMono :
      startCounter + 1 ≤ pending.persistent.counter := by
    have exactCounter := frontier.tailScan.counter_exact
    omega
  have outerNextCurrent :
      endpointsBelow outerNext opened.session.resolver.nextFresh
        pending.persistent.counter :=
    endpointsBelow_mono outerNext outerNextAtSelected
      branchFirstBelowSession
      (Nat.le_trans (Nat.le_succ startCounter) executableFrontierMono)
  have headReferenceBelow :
      (finish.advance branch branchTail).reservedUntil ≤
        opened.session.resolver.nextFresh := by
    calc
      (finish.advance branch branchTail).reservedUntil =
          finish.reservedUntil := rfl
      _ = opened.cursor.reservedUntil := frontier.finishReservedUntil
      _ = opened.session.resolver.nextFresh := sourceFresh.symm
      _ ≤ opened.session.resolver.nextFresh := Nat.le_refl _
  have headExecutableBelow :
      active.finalCounter ≤ pending.persistent.counter :=
    Nat.le_of_eq stack.activeFinalCounter
  have callerAgrees :
      ({ barrier := callerBarrier
         references := segmentReferenceRest
         executables := segmentExecutableRest } :
        ControlSegment).Agrees nextAlpha := by
    simpa using activation.spinePayload.control.tail.head
  let payloadContextExact :
      SourceControlResourcePayloadContextAgrees nextAlpha support qterm
        bodyBarrier
        ({ barrier := callerBarrier
           references := segmentReferenceRest
           executables := segmentExecutableRest } ::
         outer)
        (active :: resources) opened.scope
        ({ callerScope := callerScope
           predicateScope := opened.scope
           retained :=
             .clauses opened.scope (finish.advance branch branchTail)
           callerRest := segmentReferenceRest } ::
         context)
        outerScope :=
      .cons bodyBarrier opened.scope callerScope outerScope
        { barrier := callerBarrier
          references := segmentReferenceRest
          executables := segmentExecutableRest }
        outer active resources (finish.advance branch branchTail) context
        callerAgrees stack.activeRest stack.activeQuery stack.activeBarrier
        stack.activeOwnership snapshot outerNext
  have payloadContextExactBelow :
      endpointsBelow payloadContextExact opened.session.resolver.nextFresh
        pending.persistent.counter := by
    simp only [payloadContextExact, endpointsBelow]
    exact
      ⟨headReferenceBelow, headExecutableBelow, outerNextCurrent⟩
  have outerNextAtActivation :
      endpointsBelow outerNext
        (finish.advance branch branchTail).reservationStart active.counter :=
    endpointsBelow_mono outerNext outerNextAtSelected
      (by
        simpa [PreparedCursor.advance] using
          frontier.finishWellFormed.1.member_first_le_next branchMember)
      (by
        rw [activeCounter]
        exact Nat.le_succ startCounter)
  have outerActivationEndpoints :
      endpointsBelow
        (SourceControlResourcePayloadContextAgrees.tail payloadContextExact)
        (finish.advance branch branchTail).reservationStart active.counter := by
    simpa [payloadContextExact,
      SourceControlResourcePayloadContextAgrees.tail] using
      outerNextAtActivation
  have outerPayloadExact :
      ExtendsAboveAt branch.firstFresh startCounter
        activation.alphaExtension outerPayloads
        (SourceControlResourcePayloadContextAgrees.tail
          payloadContextExact) := by
    refine ⟨outerAtSelected, ?_⟩
    simp [payloadContextExact, outerNext,
      SourceControlResourcePayloadContextAgrees.tail]
  have payloadContextExactOrdered :
      ActivationOrdered payloadContextExact := by
    exact ⟨outerNextAtActivation, outerNextOrdered⟩
  have payloadContextExactActivationOrigins :
      LocalActivationOriginSpineRelates opened.session
        payloadContextExact := by
    exact
      ⟨snapshotActivationExtends, snapshotCutExact,
        outerNextActivationOrigins⟩
  exact
    ⟨active, snapshot, payloadContextExact, payloadContextExactBelow,
      payloadContextExactOrdered, payloadContextExactActivationOrigins,
      outerPayloadExact, outerActivationEndpoints, ⟨stack, by
        simpa [payloadContextExact,
          SourceControlResourcePayloadContextAgrees.headCell] using
          snapshotRepresentative,
        by
          simpa [payloadContextExact,
            SourceControlResourcePayloadContextAgrees.headCell] using
            snapshotOrigin⟩⟩

end PLeaTTa.PrologNestedRetainedPayloadBridge
