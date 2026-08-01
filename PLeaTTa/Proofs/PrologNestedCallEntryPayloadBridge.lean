-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologNestedCallEntryPayloadBridge
Purpose: Derive the suspended resource bank and payload chronology of one
  nested local call from the active caller state at which that call opens.
Trusted boundary: none
Main exports:
  CallEntryBankRelates.pendingOuterAlts_of_activeResourceStack
-/
import PLeaTTa.Proofs.PrologCurrentSessionPayloadTransitionBridge

namespace PLeaTTa.PrologNestedCallEntryPayloadBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologActivatedProductStepBridge
open PrologAlphaFreshFrontierBridge
open PrologCallStepBridge
open PrologControlSegmentSpineBridge
open PrologCurrentSessionPayloadBridge
open PrologMguComposition
open PrologNestedRetainedPayloadBridge
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

/-! ## Call-entry ownership transport -/

/-- Opening a nested local call transfers the caller's complete executable
alternative bank into the pending call's suspended outer control.

The equality is derived from two independently useful relations: the active
resource stack owns the exact pre-call bank, and the call-entry relation pins
the pending package's `outer` control to that same pre-call control.  The
older base bank remains arbitrary; collection closure is obtained later by
specializing it to `[]`, not by assuming closure at every call. -/
theorem callEntry_pendingOuterAlts_of_activeResourceStack
    {nextOpened : OpenedCall} {before : OpenConf}
    {nextPending : DemandDrivenCallStep.PendingCall}
    {argsv args : List Atom} {res : Atom}
    {rest : List PLeaTTa.Goal} {binding : Subst}
    {qterm : Atom} {nextBarrier startCounter : Nat}
    {alpha : List (LogicVar × String)}
    {currentBarrier callerBarrier : Nat}
    {pending : DemandDrivenCallStep.PendingCall}
    {cursor : PreparedCursor} {executableRest : List PLeaTTa.Goal}
    {altTail : List PLeaTTa.Alt}
    {active : RetainedAlternativeSegment}
    {outer : List ControlSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    (entry :
      CallEntryBankRelates nextOpened before nextPending argsv args res rest
        binding qterm nextBarrier startCounter)
    (stack :
      ActiveProductResourceStackAgrees alpha qterm currentBarrier callerBarrier
        pending cursor executableRest altTail active outer resources callerScope
        outerScope context baseAlts before) :
    nextPending.outer.alts =
      flattenOwnedAlts (active :: resources) baseAlts := by
  rw [entry.outer]
  exact stack.actualAlts

/-- A nested executable call cannot forget the flattened continuations of
older source control segments.  If any older executable goal is live, a
`CallEntryBankRelates` indexed only by the current segment's residual tail
contradicts the exact ready-state control spine.

This is the negative guard for the nested composition below: independent
source products keep segments separate, whereas the executable machine sees
their left-to-right flattening in one goal list. -/
theorem callEntry_rejects_truncated_flattened_tail
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase current : Substitution}
    {session : Session} {runtime : Subst} {qterm : Atom}
    {state : OpenConf} {currentBodyBarrier : Nat}
    {predicate : String} {referencePayload : List Term}
    {nestedReferenceRest : List PeTTaSpec.PrologCore.Goal}
    {argsv args : List Atom} {res : Atom}
    {nestedExecutableRest : List PLeaTTa.Goal}
    {older : List ControlSegment}
    {pending : DemandDrivenCallStep.PendingCall}
    {nextBarrier startCounter : Nat}
    (ready :
      SpinedReadyTaskRelates freshFrontier alpha support canonical
        referenceBase session current runtime qterm
        ({ barrier := currentBodyBarrier
           references :=
             .call predicate referencePayload :: nestedReferenceRest
           executables :=
             .call predicate args res :: nestedExecutableRest } :: older)
        state)
    (entry :
      CallEntryBankRelates
        (openedFor session predicate referencePayload current)
        state pending argsv args res nestedExecutableRest runtime qterm
        nextBarrier startCounter)
    (olderLive : flattenExecutables older ≠ []) : False := by
  have entryHead :
      state.control.cur =
        some (.call predicate args res :: nestedExecutableRest, runtime) := by
    simpa [OpenConf.toConf, Control.toConf, openedFor, openLocalCall,
      requestFor, prepareCall] using entry.callHead
  have pairEq :
      (.call predicate args res :: nestedExecutableRest, runtime) =
        (flattenExecutables
          ({ barrier := currentBodyBarrier
             references :=
               .call predicate referencePayload :: nestedReferenceRest
             executables :=
               .call predicate args res :: nestedExecutableRest } :: older),
          runtime) :=
    Option.some.inj (entryHead.symm.trans ready.2.1)
  have goalsEq := congrArg Prod.fst pairEq
  change
    (.call predicate args res :: nestedExecutableRest) =
      (.call predicate args res :: nestedExecutableRest) ++
        flattenExecutables older at goalsEq
  have tailLength : (flattenExecutables older).length = 0 := by
    have lengths := congrArg List.length goalsEq
    simp only [List.length_append] at lengths
    omega
  exact olderLive (List.eq_nil_of_length_eq_zero tailLength)

/-! ## One nested activation from the current active invariant -/

/-- A local call at the head of the active clause body opens beneath the
current predicate frame and every older active frame in one real source step.

The target context is constructed from the active relation's literal retained
cursor.  No caller supplies a shape-compatible deeper context, so the opened
cursor cannot displace or reorder an older retained continuation.

[SPEC metta.pl:251-256] -/
theorem SpinedActiveProductPayloadResourceRelatesAt.sourceCallEntry
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
    {args : List Atom} {res : Atom}
    {nestedExecutableRest : List PLeaTTa.Goal}
    {currentPayloadContext :
      ActiveProductPayloadContext alpha support qterm callerOpened callerFinish
        callerBranch callerBranchTail currentBodyBarrier callerBarrier
        callerReferences callerExecutables outer currentActive currentResources
        callerScope outerScope currentContext}
    (agreement :
      SpinedActiveProductPayloadResourceRelatesAt freshFrontier alpha support
        canonical referenceBase callerOpened session callerPending callerFinish
        callerBranch callerBranchTail callerAltTail currentBodyBarrier
        callerBarrier
        (.call predicate referencePayload :: nestedReferenceRest)
        (.call predicate args res :: nestedExecutableRest)
        callerReferences callerExecutables outer current runtime qterm
        currentActive currentResources callerScope outerScope currentContext
        baseAlts currentSource state currentPayloadContext)
    (notThrow : ¬ BuiltinThrowCall predicate referencePayload)
    (notDatabase :
      DatabaseActions.recognizeDatabaseAction predicate referencePayload =
        none) :
    RawStep session currentSource
      [.opened (requestFor predicate referencePayload current)] .none
      (openedFor session predicate referencePayload current).session
      (.running
        (ActiveProductContext.plug
          ({ callerScope := callerScope
             predicateScope := callerOpened.scope
             retained :=
               .clauses callerOpened.scope
                 (callerFinish.advance callerBranch callerBranchTail)
             callerRest := callerReferences } ::
           currentContext)
          (sourceProductFrontier callerOpened.scope
            (openedFor session predicate referencePayload current)
            (openedFor session predicate referencePayload current).cursor
            nestedReferenceRest))) := by
  have leaf :
      RawStep session
        (.task callerOpened.scope
          (.call predicate referencePayload :: nestedReferenceRest) current)
        [.opened (requestFor predicate referencePayload current)] .none
        (openedFor session predicate referencePayload current).session
        (.running
          (sourceProductFrontier callerOpened.scope
            (openedFor session predicate referencePayload current)
            (openedFor session predicate referencePayload current).cursor
            nestedReferenceRest)) := by
    exact .taskCall callerOpened.scope predicate referencePayload
      nestedReferenceRest current session notThrow notDatabase
  let currentFrame : ActiveProductFrame :=
    { callerScope := callerScope
      predicateScope := callerOpened.scope
      retained :=
        .clauses callerOpened.scope
          (callerFinish.advance callerBranch callerBranchTail)
      callerRest := callerReferences }
  have throughCurrent :
      RawStep session
        (currentFrame.wrap
          (.task callerOpened.scope
            (.call predicate referencePayload :: nestedReferenceRest) current))
        [.opened (requestFor predicate referencePayload current)] .none
        (openedFor session predicate referencePayload current).session
        (.running
          (currentFrame.wrap
            (sourceProductFrontier callerOpened.scope
              (openedFor session predicate referencePayload current)
              (openedFor session predicate referencePayload current).cursor
              nestedReferenceRest))) :=
    currentFrame.liftProgress leaf (by simp [Trace.AnswerFree])
  have throughOuter :=
    ActiveProductContext.liftProgress currentContext throughCurrent
      (by simp [Trace.AnswerFree])
  rw [agreement.core.sourceShape]
  simpa [currentFrame, activeSourceProduct,
    ActiveProductFrame.wrap, ActiveProductContext.plug] using throughOuter

/-- A call-headed active product supplies the complete outer invariant for
the next nested representative activation.

No caller supplies the nested call's suspended alternative equation, live
task payload, outer payload zipper, allocator endpoints, activation order, or
source fresh endpoint.  They are projected from the current active relation
and the concrete `openedFor` call-entry relation.  The older executable base
bank is preserved parametrically, so specializing `baseAlts` to `[]` yields
the collection-bounded induction step without claiming every call starts at
a collection boundary.

[SPEC metta.pl:251-256] -/
theorem
    SpinedRepresentativeProductActivation.spinedNestedProductPayloadResourceRelates
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
        sourceCanonical flattenedRepresentative installed) :
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
            nestedPayloadContext ∧
          ExtendsAboveAt nestedBranch.firstFresh state.persistent.counter
            activation.alphaExtension currentPayloadContext
            (SourceControlResourcePayloadContextAgrees.tail
              nestedPayloadContext) ∧
          PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount
              nestedPayloadContext =
            PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount
                currentPayloadContext +
              1 := by
  have preHeadPayload :
      TaskSpinePayloadAgrees alpha support canonical referenceBase current
        runtime
        ({ barrier := currentBodyBarrier
           references :=
             .call predicate referencePayload :: nestedReferenceRest
           executables :=
             .call predicate args res :: nestedExecutableRest } ::
         { barrier := callerBarrier
           references := callerReferences
           executables := callerExecutables } :: outer) :=
    currentAgreement.core.control.ready.2.2.2
  have outerEndpoints :
      endpointsBelow currentPayloadContext
        (openedFor session predicate referencePayload current).cursor.reservationStart
        state.persistent.counter := by
    simpa [openedFor] using
      _root_.PLeaTTa.PrologNestedRetainedPayloadBridge.SourceControlResourcePayloadContextAgrees.endpointsBelow_openLocalCall
        currentPayloadContext session
        (requestFor predicate referencePayload current)
        currentAgreement.endpointsCurrent
  have outerAlts :
      nestedPending.outer.alts =
        flattenOwnedAlts (currentActive :: currentResources) baseAlts :=
    callEntry_pendingOuterAlts_of_activeResourceStack entry
      currentAgreement.core.resourceStack
  obtain
      ⟨nestedActive, nestedPayloadContext, nestedAgreement, payloadHandoff⟩ :=
    SpinedRepresentativeProductActivation.spinedProductPayloadResourceRelates
      frontier preHeadPayload oldCumulative materializedAtOpen (by rfl) (by rfl)
      queryReferenceBelow activation entry.sourceFresh
      currentPayloadContext outerEndpoints currentAgreement.activationOrdered
      baseAlts outerAlts
  refine
    ⟨nestedActive, nestedPayloadContext, nestedAgreement, payloadHandoff, ?_⟩
  calc
    PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount
        nestedPayloadContext =
      PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount
          (PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.outerPayload
            nestedPayloadContext) +
        1 :=
      PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount_outerPayload
        nestedPayloadContext
    _ =
      PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount
          (SourceControlResourcePayloadContextAgrees.tail
            nestedPayloadContext) +
        1 := by
      rw [
        PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.outerPayload_eq_tail]
    _ =
      PrologCurrentSessionPayloadTransitionBridge.ActiveProductPayloadContext.cellCount
          currentPayloadContext +
        1 := by
      rw [payloadHandoff.cellCount_eq]

end PLeaTTa.PrologNestedCallEntryPayloadBridge
