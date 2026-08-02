-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologCurrentSessionUnifyTransitionBridge
Purpose: Lift one successful primitive unification through the complete
  active product/resource/payload context.
Trusted boundary: none
Main exports:
  SpinedActiveProductPayloadResourceRelatesAt.afterUnifySuccessWith,
  SpinedActiveProductPayloadResourceRelatesAt.afterUnifySuccess
-/
import PLeaTTa.Proofs.PrologCurrentSessionPayloadTransitionBridge

namespace PLeaTTa.PrologCurrentSessionUnifyTransitionBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologActivatedProductStepBridge
open PrologControlSegmentSpineBridge
open PrologCurrentSessionPayloadBridge
open PrologCurrentSessionPayloadTransitionBridge
open PrologGoalAlpha
open PrologMguBridge
open PrologMguComposition
open PrologOrdinaryStepBridge
open PrologProductResourceContextBridge
open PrologProductResourceTransitionBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
open PrologSourceProductContextBridge
open PrologStateBridge

/-!
The old two-segment unification bridge proved the MGU/install step for one
body and one caller tail.  A recursive activation can have arbitrarily many
older caller regions, each with its own cut barrier and retained resource.
Flattening those regions back into the two-segment relation would silently
retag older cuts.

The theorem below keeps the arbitrary-depth control spine.  The MGU proof is
performed once on the shared `TaskDataAgrees`; only the active head segment is
advanced, while every outer control certificate, retained cursor, alternative
bank, barrier, frame, query term, and immutable payload cell is preserved
literally.  [SPEC ISO:unification; metta.pl:251-256]
-/

/-- One successful source/executable primitive equality transition through
an arbitrary active predicate stack.

The support and liveness premises are the same explicit obligations as the
leaf theorem.  They prevent a successful executable unifier or its subsequent
`trimFor` from losing an alpha link that remains observable in the flattened
body/caller/outer continuation. -/
theorem SpinedActiveProductPayloadResourceRelatesAt.afterUnifySuccessWithLive
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical representative : TreeSubstitution}
    {referenceBase : Substitution}
    {opened : OpenedCall} {session : Session}
    {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {left right : Term} {result : Substitution}
    {bodyRest : List PeTTaSpec.PrologCore.Goal}
    {bodyExecutables : List PLeaTTa.Goal}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {current : Substitution} {runtime : Subst} {qterm : Atom}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {source : Search} {state : OpenConf}
    {payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish branch
        branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context}
    (agreement :
      SpinedActiveProductPayloadResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened session pending finish branch branchTail
        altTail bodyBarrier callerBarrier
        (.unify left right :: bodyRest) bodyExecutables callerReferences
        callerExecutables outer current runtime qterm active resources
        callerScope outerScope context baseAlts source state payloadContext)
    (selected :
      AlphaCumulativeResidualVariantAgreesOnWith alpha support canonical
        referenceBase runtime representative)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote right))
    (continuationLive : ReadyUnifyContinuationLive support state)
    (resolved : UnifyResolution current left right result) :
    ∃ (spelling :
          NormalizedAlphaGoalsAgree.ExecutableUnifySpelling)
        (executableLeft executableRight : Atom)
        (bodyExecutableTail : List PLeaTTa.Goal)
        (sourceExtension executableExtension : TreeSubstitution)
        (generated installed : Subst),
      let executableTail :=
        bodyExecutableTail ++
          (callerExecutables ++ flattenExecutables outer)
      let executableAfter :=
        unifySuccessor state executableTail installed
      let nextSource :=
        ActiveProductContext.plug context
          (activeSourceProduct callerScope opened finish branch branchTail
            result bodyRest callerReferences)
      AlphaTermAgrees alpha left executableLeft ∧
        AlphaTermAgrees alpha right executableRight ∧
        state.control.cur =
          some
            (spelling.goal executableLeft executableRight ::
              executableTail,
              runtime) ∧
        SelectedUnifySuccessData alpha support canonical representative
          referenceBase current runtime left right left right executableLeft
          executableRight result sourceExtension executableExtension generated
          installed ∧
        RawStep session source [] .none session
          (.running nextSource) ∧
        DemandDrivenCallStep.Step prog gt (.ready state)
          (.ready executableAfter) ∧
        SpinedActiveProductPayloadResourceRelatesAt freshFrontier alpha support
          (sourceExtension ++ canonical) referenceBase opened session pending
          finish branch branchTail altTail bodyBarrier callerBarrier bodyRest
          bodyExecutableTail callerReferences callerExecutables outer result
          (PLeaTTa.trimFor executableTail qterm installed) qterm active
          resources callerScope outerScope context baseAlts nextSource
          executableAfter payloadContext ∧
        AlphaCumulativeResidualVariantAgreesOnWith alpha support
          (sourceExtension ++ canonical) referenceBase
          (PLeaTTa.trimFor executableTail qterm installed)
          (executableExtension ++ representative) := by
  rcases agreement.core.control.ready with
    ⟨persistent, currentControl, queryTerm, spinePayload⟩
  have bodyPayload :
      TaskPayloadAgrees alpha support bodyBarrier canonical referenceBase
        current runtime (.unify left right :: bodyRest) bodyExecutables :=
    spinePayload.headPayload
  rcases bodyPayload.control.unifyHead with
    ⟨spelling, executableLeft, executableRight, bodyExecutableTail,
      bodyShape, leftAgreement, rightAgreement, bodyTailControl⟩
  have executableHead :
      state.control.cur =
        some
          (spelling.goal executableLeft executableRight ::
            (bodyExecutableTail ++
              (callerExecutables ++ flattenExecutables outer)),
            runtime) := by
    calc
      state.control.cur =
          some
            (bodyExecutables ++
              (callerExecutables ++ flattenExecutables outer),
              runtime) :=
        currentControl
      _ =
          some
            ((spelling.goal executableLeft executableRight ::
                bodyExecutableTail) ++
              (callerExecutables ++ flattenExecutables outer),
              runtime) := by rw [bodyShape]
      _ =
          some
            (spelling.goal executableLeft executableRight ::
              (bodyExecutableTail ++
                (callerExecutables ++ flattenExecutables outer)),
              runtime) := by rfl
  have live :
      AlphaRuntimeNamesLive support
        (bodyExecutableTail ++
          (callerExecutables ++ flattenExecutables outer))
        state.control.qterm :=
    continuationLive executableHead
  obtain
    ⟨sourceExtension, executableExtension, generated, selectedSuccess⟩ :=
    bodyPayload.data.afterUnifySuccessDataWith_of_equivalentGeneral selected
      (by intro binding; rfl) leftAgreement rightAgreement leftSupported
      rightSupported resolved
  let installed :=
    PrologMguComposition.installGenerated generated runtime
  have installedExact :
      PLeaTTa.unifyB runtime executableLeft executableRight =
        some installed := by
    simpa [installed] using selectedSuccess.installedExact
  have nextData :
      TaskDataAgrees alpha support (sourceExtension ++ canonical)
        referenceBase result installed := by
    simpa [installed] using
      selectedSuccess.taskData bodyPayload.alphaShared
  have nextSelected :
      AlphaCumulativeResidualVariantAgreesOnWith alpha support
        (sourceExtension ++ canonical) referenceBase
        (PLeaTTa.trimFor
          (bodyExecutableTail ++
            (callerExecutables ++ flattenExecutables outer))
          qterm installed)
        (executableExtension ++ representative) := by
    apply selectedSuccess.nextCumulative.trimFor
    intro identity name linked
    simpa [queryTerm] using
      (live (identity := identity) (name := name) linked)

  have child :
      RawStep session
        (.task opened.scope (.unify left right :: bodyRest) current)
        [] .none session
        (.running (.task opened.scope bodyRest result)) :=
    .taskUnifySuccess opened.scope left right bodyRest current result session
      resolved
  have activeSourceStep :
      RawStep session
        (activeSourceProduct callerScope opened finish branch branchTail
          current (.unify left right :: bodyRest) callerReferences)
        [] .none session
        (.running
          (activeSourceProduct callerScope opened finish branch branchTail
            result bodyRest callerReferences)) := by
    simpa using
      ActiveProductFrame.liftProgress
        (ActiveProductFrame.ofActiveProduct callerScope opened finish branch
          branchTail callerReferences)
        child (by simp [Trace.AnswerFree])
  have sourceStep :
      RawStep session source [] .none session
        (.running
          (ActiveProductContext.plug context
            (activeSourceProduct callerScope opened finish branch branchTail
              result bodyRest callerReferences))) := by
    rw [agreement.core.sourceShape]
    exact
      ActiveProductContext.liftProgress context activeSourceStep
        (by simp [Trace.AnswerFree])

  let executableTail :=
    bodyExecutableTail ++
      (callerExecutables ++ flattenExecutables outer)
  let executableAfter := unifySuccessor state executableTail installed
  have executableStep :
      DemandDrivenCallStep.Step prog gt (.ready state)
        (.ready executableAfter) := by
    apply
      executable_unify_step state spelling executableLeft executableRight
        executableTail runtime installed
    · exact executableHead
    · exact installedExact

  have nextSpinePayload :
      TaskSpinePayloadAgrees alpha support (sourceExtension ++ canonical)
        referenceBase result
        (PLeaTTa.trimFor executableTail qterm installed)
        ({ barrier := bodyBarrier
           references := bodyRest
           executables := bodyExecutableTail } ::
         { barrier := callerBarrier
           references := callerReferences
           executables := callerExecutables } ::
         outer) := by
    refine
      ⟨nextData.trimFor ?_,
        .cons bodyTailControl spinePayload.control.tail⟩
    intro identity name linked
    simpa [executableTail, queryTerm] using
      (live (identity := identity) (name := name) linked)

  have nextReady :
      SpinedReadyTaskRelates freshFrontier alpha support
        (sourceExtension ++ canonical) referenceBase session result
        (PLeaTTa.trimFor executableTail qterm installed) qterm
        ({ barrier := bodyBarrier
           references := bodyRest
           executables := bodyExecutableTail } ::
         { barrier := callerBarrier
           references := callerReferences
           executables := callerExecutables } ::
         outer)
        executableAfter := by
    refine ⟨?_, ?_, ?_, nextSpinePayload⟩
    · simpa [executableAfter] using persistent
    · simp [executableAfter, executableTail, queryTerm, flattenExecutables,
        ControlSegment.executableGoals]
    · simpa [executableAfter] using queryTerm

  have nextControl :
      SpinedActiveProductRelatesAt freshFrontier alpha support
        (sourceExtension ++ canonical) referenceBase opened session pending
        finish branch branchTail altTail bodyBarrier callerBarrier bodyRest
        bodyExecutableTail callerReferences callerExecutables outer result
        (PLeaTTa.trimFor executableTail qterm installed) qterm
        executableAfter := by
    refine
      ⟨nextReady, agreement.core.control.sessionAdvanced,
        ?_, agreement.core.control.retainedAltsZero, ?_,
        agreement.core.control.bodyBarrierTag, ?_⟩
    · simpa [executableAfter] using agreement.core.control.retainedAlts
    · simpa [executableAfter] using agreement.core.control.retainedBarriers
    · simpa [executableAfter] using agreement.core.control.frames

  have nextResourceStack :
      ActiveProductResourceStackAgrees alpha qterm bodyBarrier callerBarrier
        pending (finish.advance branch branchTail)
        (callerExecutables ++ flattenExecutables outer) altTail active outer
        resources callerScope outerScope context baseAlts executableAfter := by
    rcases agreement.core.resourceStack with
      ⟨activeRest, activeQuery, activeBarrier, activeAlts,
        activeFinalCounter, activeOwnership, outerAlignment,
        suspendedOuterAlts, actualAlts⟩
    exact
      ⟨activeRest, activeQuery, activeBarrier, activeAlts,
        activeFinalCounter, activeOwnership, outerAlignment,
        suspendedOuterAlts, by simpa [executableAfter] using actualAlts⟩

  let nextSource :=
    ActiveProductContext.plug context
      (activeSourceProduct callerScope opened finish branch branchTail
        result bodyRest callerReferences)
  have nextCore :
      SpinedActiveProductResourceRelatesAt freshFrontier alpha support
        (sourceExtension ++ canonical) referenceBase opened session pending
        finish branch branchTail altTail bodyBarrier callerBarrier bodyRest
        bodyExecutableTail callerReferences callerExecutables outer result
        (PLeaTTa.trimFor executableTail qterm installed) qterm active resources
        callerScope outerScope context baseAlts nextSource executableAfter :=
    ⟨nextControl, nextResourceStack, rfl⟩

  have nextEndpoints :
      endpointsBelow payloadContext session.resolver.nextFresh
        executableAfter.persistent.counter := by
    simpa [executableAfter] using agreement.endpointsCurrent

  have nextControlOrigins :
      LocalControlOriginSpineRelates baseAlts executableAfter.frames
        executableAfter.control.barriers payloadContext := by
    simpa [executableAfter] using agreement.controlOrigins

  exact
    ⟨spelling, executableLeft, executableRight, bodyExecutableTail,
      sourceExtension, executableExtension, generated, installed,
      leftAgreement, rightAgreement,
      executableHead, by simpa [installed] using selectedSuccess,
      sourceStep, executableStep,
      ⟨nextCore, nextEndpoints, agreement.activationOrdered,
        nextControlOrigins⟩,
      by simpa [executableTail] using nextSelected⟩

/-- Compatibility entry point for callers carrying the older conservative
runtime-avoidance invariant.  Only its liveness projection is needed by the
arbitrary-base proof. -/
theorem SpinedActiveProductPayloadResourceRelatesAt.afterUnifySuccessWith
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical representative : TreeSubstitution}
    {referenceBase : Substitution}
    {opened : OpenedCall} {session : Session}
    {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {left right : Term} {result : Substitution}
    {bodyRest : List PeTTaSpec.PrologCore.Goal}
    {bodyExecutables : List PLeaTTa.Goal}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {current : Substitution} {runtime : Subst} {qterm : Atom}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {source : Search} {state : OpenConf}
    {payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish branch
        branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context}
    (agreement :
      SpinedActiveProductPayloadResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened session pending finish branch branchTail
        altTail bodyBarrier callerBarrier
        (.unify left right :: bodyRest) bodyExecutables callerReferences
        callerExecutables outer current runtime qterm active resources
        callerScope outerScope context baseAlts source state payloadContext)
    (selected :
      AlphaCumulativeResidualVariantAgreesOnWith alpha support canonical
        referenceBase runtime representative)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote right))
    (_supportIncluded :
      ∀ pair, pair ∈ support → pair ∈ alpha)
    (safe : ReadyUnifyContinuationSafe support state)
    (resolved : UnifyResolution current left right result) :
    ∃ (spelling :
          NormalizedAlphaGoalsAgree.ExecutableUnifySpelling)
        (executableLeft executableRight : Atom)
        (bodyExecutableTail : List PLeaTTa.Goal)
        (sourceExtension executableExtension : TreeSubstitution)
        (generated installed : Subst),
      let executableTail :=
        bodyExecutableTail ++
          (callerExecutables ++ flattenExecutables outer)
      let executableAfter :=
        unifySuccessor state executableTail installed
      let nextSource :=
        ActiveProductContext.plug context
          (activeSourceProduct callerScope opened finish branch branchTail
            result bodyRest callerReferences)
      AlphaTermAgrees alpha left executableLeft ∧
        AlphaTermAgrees alpha right executableRight ∧
        state.control.cur =
          some
            (spelling.goal executableLeft executableRight ::
              executableTail,
              runtime) ∧
        SelectedUnifySuccessData alpha support canonical representative
          referenceBase current runtime left right left right executableLeft
          executableRight result sourceExtension executableExtension generated
          installed ∧
        RawStep session source [] .none session
          (.running nextSource) ∧
        DemandDrivenCallStep.Step prog gt (.ready state)
          (.ready executableAfter) ∧
        SpinedActiveProductPayloadResourceRelatesAt freshFrontier alpha support
          (sourceExtension ++ canonical) referenceBase opened session pending
          finish branch branchTail altTail bodyBarrier callerBarrier bodyRest
          bodyExecutableTail callerReferences callerExecutables outer result
          (PLeaTTa.trimFor executableTail qterm installed) qterm active
          resources callerScope outerScope context baseAlts nextSource
          executableAfter payloadContext ∧
        AlphaCumulativeResidualVariantAgreesOnWith alpha support
          (sourceExtension ++ canonical) referenceBase
          (PLeaTTa.trimFor executableTail qterm installed)
          (executableExtension ++ representative) :=
  PLeaTTa.PrologCurrentSessionUnifyTransitionBridge.SpinedActiveProductPayloadResourceRelatesAt.afterUnifySuccessWithLive
    agreement selected leftSupported rightSupported safe.live resolved

/-- Compatibility view which forgets the selected predecessor and successor
representatives.  Its proof is only a projection of
`afterUnifySuccessWith`; no independent unification argument remains. -/
theorem SpinedActiveProductPayloadResourceRelatesAt.afterUnifySuccess
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {session : Session}
    {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {bodyBarrier callerBarrier : Nat}
    {left right : Term} {result : Substitution}
    {bodyRest : List PeTTaSpec.PrologCore.Goal}
    {bodyExecutables : List PLeaTTa.Goal}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {current : Substitution} {runtime : Subst} {qterm : Atom}
    {active : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {source : Search} {state : OpenConf}
    {payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish branch
        branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context}
    (agreement :
      SpinedActiveProductPayloadResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened session pending finish branch branchTail
        altTail bodyBarrier callerBarrier
        (.unify left right :: bodyRest) bodyExecutables callerReferences
        callerExecutables outer current runtime qterm active resources
        callerScope outerScope context baseAlts source state payloadContext)
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote right))
    (supportIncluded :
      ∀ pair, pair ∈ support → pair ∈ alpha)
    (safe : ReadyUnifyContinuationSafe support state)
    (resolved : UnifyResolution current left right result) :
    ∃ (spelling :
          NormalizedAlphaGoalsAgree.ExecutableUnifySpelling)
        (executableLeft executableRight : Atom)
        (bodyExecutableTail : List PLeaTTa.Goal)
        (sourceExtension : TreeSubstitution) (installed : Subst),
      let executableTail :=
        bodyExecutableTail ++
          (callerExecutables ++ flattenExecutables outer)
      let executableAfter :=
        unifySuccessor state executableTail installed
      let nextSource :=
        ActiveProductContext.plug context
          (activeSourceProduct callerScope opened finish branch branchTail
            result bodyRest callerReferences)
      AlphaTermAgrees alpha left executableLeft ∧
        AlphaTermAgrees alpha right executableRight ∧
        state.control.cur =
          some
            (spelling.goal executableLeft executableRight ::
              executableTail,
              runtime) ∧
        RawStep session source [] .none session
          (.running nextSource) ∧
        DemandDrivenCallStep.Step prog gt (.ready state)
          (.ready executableAfter) ∧
        SpinedActiveProductPayloadResourceRelatesAt freshFrontier alpha support
          (sourceExtension ++ canonical) referenceBase opened session pending
          finish branch branchTail altTail bodyBarrier callerBarrier bodyRest
          bodyExecutableTail callerReferences callerExecutables outer result
          (PLeaTTa.trimFor executableTail qterm installed) qterm active
          resources callerScope outerScope context baseAlts nextSource
          executableAfter payloadContext := by
  rcases agreement.core.control.ready with
    ⟨_persistent, _currentControl, _queryTerm, spinePayload⟩
  have bodyPayload :
      TaskPayloadAgrees alpha support bodyBarrier canonical referenceBase
        current runtime (.unify left right :: bodyRest) bodyExecutables :=
    spinePayload.headPayload
  obtain ⟨representative, selected⟩ :=
    bodyPayload.valuation.existsWith
  obtain
    ⟨spelling, executableLeft, executableRight, bodyExecutableTail,
      sourceExtension, _executableExtension, _generated, installed,
      leftAgreement, rightAgreement, executableHead, _selectedSuccess,
      sourceStep, executableStep, nextAgreement, _nextSelected⟩ :=
    PLeaTTa.PrologCurrentSessionUnifyTransitionBridge.SpinedActiveProductPayloadResourceRelatesAt.afterUnifySuccessWith
      agreement selected leftSupported rightSupported supportIncluded safe
      resolved
  exact
    ⟨spelling, executableLeft, executableRight, bodyExecutableTail,
      sourceExtension, installed, leftAgreement, rightAgreement,
      executableHead, sourceStep, executableStep, nextAgreement⟩

end PLeaTTa.PrologCurrentSessionUnifyTransitionBridge
