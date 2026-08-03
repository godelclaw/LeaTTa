-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologPersistentFreeCommittedUnifyTransitionBridge
Purpose: Lift one successful primitive unification through the packet-free
  committed product/payload phase.
Trusted boundary: none
Main exports:
  PersistentFreeCommittedProductPayloadResourceRelatesAt.afterUnifySuccessWithLive,
  RepresentativePersistentFreeCommittedUnifySuccessorFacts,
  RepresentativePersistentFreeCommittedPayloadState.exists_afterUnifySuccessLive
-/
import PLeaTTa.Proofs.PrologCurrentSessionUnifyTransitionBridge
import PLeaTTa.Proofs.PrologPersistentFreeCommittedPayloadBridge

namespace PLeaTTa.PrologPersistentFreeCommittedUnifyTransitionBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologActivatedProductStepBridge
open PrologAlphaFreshFrontierBridge
open PrologControlSegmentSpineBridge
open PrologCurrentSessionPayloadBridge
open PrologCurrentSessionPayloadTransitionBridge
open PrologCurrentSessionUnifyTransitionBridge
open PrologGoalAlpha
open PrologMguBridge
open PrologMguComposition
open PrologNestedCallReadyBridge
open PrologOrdinaryStepBridge
open PrologPersistentFreeCommittedPayloadBridge
open PrologProductResourceContextBridge
open PrologProductResourceTransitionBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
open PrologSourceProductContextBridge
open PrologStateBridge

/-!
A clause-local cut destroys the activation packets and leaves a committed
task under the predicate's still-live cut boundary.  The active unification
bridge cannot be reused after that point: its type requires the already
consumed cursor and pending-call packets.

The theorem below performs the same selected MGU/install proof directly over
the packet-free committed carrier.  The source equality steps beneath the
surviving cut boundary, while persistent state, older retained resources,
typed scopes, frames, and control origins remain literal.  [SPEC
ISO:unification; metta.pl:251-256]
-/

/-- One successful primitive equality through an arbitrary packet-free
committed predicate stack.

The selected source and executable residual orientations are returned
together with both actual transitions and the exact successor relation.  No
caller can pair a source MGU from one run with an executable installation from
another. -/
theorem PersistentFreeCommittedProductPayloadResourceRelatesAt.afterUnifySuccessWithMaterializedLive
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical representative : TreeSubstitution}
    {referenceBase : Substitution}
    {predicateScope : CutScopeId} {session : Session}
    {bodyBarrier callerBarrier : Nat}
    {left right : Term} {result : Substitution}
    {bodyRest : List PeTTaSpec.PrologCore.Goal}
    {bodyExecutables : List PLeaTTa.Goal}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {current : Substitution} {runtime : Subst} {qterm : Atom}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {source : Search} {state : OpenConf}
    {payloadContext :
      CommittedProductPayloadContext alpha support qterm callerBarrier outer
        resources callerScope outerScope context}
    (agreement :
      PersistentFreeCommittedProductPayloadResourceRelatesAt freshFrontier
        alpha support canonical referenceBase predicateScope session
        bodyBarrier callerBarrier (.unify left right :: bodyRest)
        bodyExecutables callerReferences callerExecutables outer current
        runtime qterm resources callerScope outerScope context baseAlts source
        state payloadContext)
    (selected :
      AlphaCumulativeResidualVariantAgreesOnWith alpha support canonical
        referenceBase runtime representative)
    (headReady :
      MaterializedUnifyHeadReady alpha representative referenceBase runtime
        bodyBarrier left right bodyRest bodyExecutables)
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
          (cutSourceProductAt callerScope predicateScope result bodyRest
            callerReferences)
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
        PersistentFreeCommittedProductPayloadResourceRelatesAt freshFrontier
          alpha support (sourceExtension ++ canonical) referenceBase
          predicateScope session bodyBarrier callerBarrier bodyRest
          bodyExecutableTail callerReferences callerExecutables outer result
          (PLeaTTa.trimFor executableTail qterm installed) qterm resources
          callerScope outerScope context baseAlts nextSource executableAfter
          payloadContext ∧
        AlphaCumulativeResidualVariantAgreesOnWith alpha support
          (sourceExtension ++ canonical) referenceBase
          (PLeaTTa.trimFor executableTail qterm installed)
          (executableExtension ++ representative) := by
  rcases agreement.ready with
    ⟨persistent, currentControl, queryTerm, spinePayload⟩
  have bodyPayload :
      TaskPayloadAgrees alpha support bodyBarrier canonical referenceBase
        current runtime (.unify left right :: bodyRest) bodyExecutables :=
    spinePayload.headPayload
  rcases headReady with
    ⟨spelling, executableLeft, executableRight, bodyExecutableTail,
      bodyShape, leftAgreement, rightAgreement, bodyTailControl,
      materialized⟩
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
    bodyPayload.data.afterUnifySuccessDataWith_of_equivalentGeneral_materialized
      selected (by intro binding; rfl) materialized resolved
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
        (.task predicateScope (.unify left right :: bodyRest) current)
        [] .none session
        (.running (.task predicateScope bodyRest result)) :=
    .taskUnifySuccess predicateScope left right bodyRest current result session
      resolved
  have boundary :
      RawStep session
        (.cutBoundary predicateScope
          (.task predicateScope (.unify left right :: bodyRest) current))
        [] .none session
        (.running
          (.cutBoundary predicateScope
            (.task predicateScope bodyRest result))) :=
    .cutBoundaryProgress predicateScope _ _ [] session session child
  have product :
      RawStep session
        (cutSourceProductAt callerScope predicateScope current
          (.unify left right :: bodyRest) callerReferences)
        [] .none session
        (.running
          (cutSourceProductAt callerScope predicateScope result bodyRest
            callerReferences)) := by
    simpa [cutSourceProductAt] using
      (RawStep.productProgress callerScope _ _ callerReferences [] .none
        session session boundary (by simp [Trace.AnswerFree]))
  have sourceStep :
      RawStep session source [] .none session
        (.running
          (ActiveProductContext.plug context
            (cutSourceProductAt callerScope predicateScope result bodyRest
              callerReferences))) := by
    rw [agreement.sourceShape]
    exact
      ActiveProductContext.liftProgress context product
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
  let nextSource :=
    ActiveProductContext.plug context
      (cutSourceProductAt callerScope predicateScope result bodyRest
        callerReferences)
  have nextAgreement :
      PersistentFreeCommittedProductPayloadResourceRelatesAt freshFrontier
        alpha support (sourceExtension ++ canonical) referenceBase
        predicateScope session bodyBarrier callerBarrier bodyRest
        bodyExecutableTail callerReferences callerExecutables outer result
        (PLeaTTa.trimFor executableTail qterm installed) qterm resources
        callerScope outerScope context baseAlts nextSource executableAfter
        payloadContext := by
    refine
      { ready := nextReady
        actualAlts := ?_
        cacheCoherent := ?_
        sourceShape := rfl
        endpointsCurrent := ?_
        activationOrdered := agreement.activationOrdered
        activationOrigins := agreement.activationOrigins
        controlOrigins := ?_ }
    · simpa [executableAfter] using agreement.actualAlts
    · exact
        (executable_unify_sealed_step (prog := prog) (gt := gt) state spelling
          executableLeft executableRight executableTail runtime installed
          executableHead installedExact).preserves_barrierCacheCoherent
          agreement.cacheCoherent
    · simpa [executableAfter] using
        agreement.endpointsCurrent
    · simpa [executableAfter] using agreement.controlOrigins
  exact
    ⟨spelling, executableLeft, executableRight, bodyExecutableTail,
      sourceExtension, executableExtension, generated, installed,
      leftAgreement, rightAgreement, executableHead,
      by simpa [installed] using selectedSuccess, sourceStep, executableStep,
      nextAgreement, by simpa [executableTail] using nextSelected⟩

/-- Compatibility entry point for callers whose equality operands belong to
the immutable public support.  The support premises are used only to derive
the execution-local materialized readings; the transition itself is proved by
`afterUnifySuccessWithMaterializedLive`. -/
theorem PersistentFreeCommittedProductPayloadResourceRelatesAt.afterUnifySuccessWithLive
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical representative : TreeSubstitution}
    {referenceBase : Substitution}
    {predicateScope : CutScopeId} {session : Session}
    {bodyBarrier callerBarrier : Nat}
    {left right : Term} {result : Substitution}
    {bodyRest : List PeTTaSpec.PrologCore.Goal}
    {bodyExecutables : List PLeaTTa.Goal}
    {callerReferences : List PeTTaSpec.PrologCore.Goal}
    {callerExecutables : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {current : Substitution} {runtime : Subst} {qterm : Atom}
    {resources : List RetainedAlternativeSegment}
    {callerScope outerScope : CutScopeId}
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {source : Search} {state : OpenConf}
    {payloadContext :
      CommittedProductPayloadContext alpha support qterm callerBarrier outer
        resources callerScope outerScope context}
    (agreement :
      PersistentFreeCommittedProductPayloadResourceRelatesAt freshFrontier
        alpha support canonical referenceBase predicateScope session
        bodyBarrier callerBarrier (.unify left right :: bodyRest)
        bodyExecutables callerReferences callerExecutables outer current
        runtime qterm resources callerScope outerScope context baseAlts source
        state payloadContext)
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
          (cutSourceProductAt callerScope predicateScope result bodyRest
            callerReferences)
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
        PersistentFreeCommittedProductPayloadResourceRelatesAt freshFrontier
          alpha support (sourceExtension ++ canonical) referenceBase
          predicateScope session bodyBarrier callerBarrier bodyRest
          bodyExecutableTail callerReferences callerExecutables outer result
          (PLeaTTa.trimFor executableTail qterm installed) qterm resources
          callerScope outerScope context baseAlts nextSource executableAfter
          payloadContext ∧
        AlphaCumulativeResidualVariantAgreesOnWith alpha support
          (sourceExtension ++ canonical) referenceBase
          (PLeaTTa.trimFor executableTail qterm installed)
          (executableExtension ++ representative) := by
  have bodyPayload :
      TaskPayloadAgrees alpha support bodyBarrier canonical referenceBase
        current runtime (.unify left right :: bodyRest) bodyExecutables :=
    agreement.ready.2.2.2.headPayload
  have headReady :
      MaterializedUnifyHeadReady alpha representative referenceBase runtime
        bodyBarrier left right bodyRest bodyExecutables :=
    bodyPayload.materializedUnifyHeadReady_of_supported selected leftSupported
      rightSupported
  exact
    PersistentFreeCommittedProductPayloadResourceRelatesAt.afterUnifySuccessWithMaterializedLive
      agreement selected headReady continuationLive resolved

namespace RepresentativePersistentFreeCommittedPayloadState

/-- Exact flattened executable continuation after a committed equality. -/
def unifyExecutableTail
    (state : RepresentativePersistentFreeCommittedPayloadState)
    (bodyExecutableTail : List PLeaTTa.Goal) : List PLeaTTa.Goal :=
  bodyExecutableTail ++
    (state.carrier.index.callerExecutables ++
      flattenExecutables state.carrier.index.outer)

/-- Exact independent source focus after the committed equality succeeds. -/
def unifySource
    (state : RepresentativePersistentFreeCommittedPayloadState)
    (result : Substitution)
    (bodyRest : List PeTTaSpec.PrologCore.Goal) : Search :=
  ActiveProductContext.plug state.carrier.index.context
    (cutSourceProductAt state.carrier.index.callerScope
      state.carrier.index.predicateScope result bodyRest
      state.carrier.index.callerReferences)

/-- Exact fine successor after installing the selected executable MGU. -/
def unifyOpenConf
    (state : RepresentativePersistentFreeCommittedPayloadState)
    (bodyExecutableTail : List PLeaTTa.Goal) (installed : Subst) : OpenConf :=
  unifySuccessor state.carrier.index.openConf
    (unifyExecutableTail state bodyExecutableTail) installed

/-- Every index of the packet-free committed unification successor. -/
def unifyIndex
    (state : RepresentativePersistentFreeCommittedPayloadState)
    (bodyRest : List PeTTaSpec.PrologCore.Goal)
    (bodyExecutableTail : List PLeaTTa.Goal)
    (result : Substitution) (sourceExtension : TreeSubstitution)
    (installed : Subst) : PersistentFreeCommittedPayloadIndex :=
  { state.carrier.index with
    canonical := sourceExtension ++ state.carrier.index.canonical
    bodyReferences := bodyRest
    bodyExecutables := bodyExecutableTail
    current := result
    runtime :=
      PLeaTTa.trimFor (unifyExecutableTail state bodyExecutableTail)
        state.carrier.index.qterm installed
    source := unifySource state result bodyRest
    openConf := unifyOpenConf state bodyExecutableTail installed }

end RepresentativePersistentFreeCommittedPayloadState

/-- Closed producer facts for one selected committed primitive-unification
successor.  Every chosen MGU datum, both actual transitions, the literal
successor, and the payload identity inhabit one proposition. -/
structure RepresentativePersistentFreeCommittedUnifySuccessorFacts
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (before after : RepresentativePersistentFreeCommittedPayloadState)
    (left right : Term) (result : Substitution)
    (bodyRest : List PeTTaSpec.PrologCore.Goal)
    (bodyExecutableTail : List PLeaTTa.Goal)
    (sourceExtension executableExtension : TreeSubstitution)
    (generated installed : Subst) : Prop where
  referenceHead :
    before.carrier.index.bodyReferences = .unify left right :: bodyRest
  afterIndexExact :
    after.carrier.index =
      RepresentativePersistentFreeCommittedPayloadState.unifyIndex before
        bodyRest bodyExecutableTail result sourceExtension installed
  selectedExecution :
    ∃ (spelling : NormalizedAlphaGoalsAgree.ExecutableUnifySpelling)
        (executableLeft executableRight : Atom),
      AlphaTermAgrees before.carrier.index.alpha left executableLeft ∧
        AlphaTermAgrees before.carrier.index.alpha right executableRight ∧
        before.carrier.index.openConf.control.cur =
          some
            (spelling.goal executableLeft executableRight ::
              RepresentativePersistentFreeCommittedPayloadState.unifyExecutableTail
                before bodyExecutableTail,
              before.carrier.index.runtime) ∧
        SelectedUnifySuccessData before.carrier.index.alpha
          before.carrier.index.support before.carrier.index.canonical
          before.representative before.carrier.index.referenceBase
          before.carrier.index.current before.carrier.index.runtime left right
          left right executableLeft executableRight result sourceExtension
          executableExtension generated installed
  sourceStep :
    RawStep before.carrier.index.session before.carrier.index.source [] .none
      before.carrier.index.session (.running after.carrier.index.source)
  fineStep :
    DemandDrivenCallStep.Step prog gt
      (.ready before.carrier.index.openConf)
      (.ready after.carrier.index.openConf)
  representativeExact :
    after.representative = executableExtension ++ before.representative
  payloadCellsExact :
    after.carrier.cellIdentities = before.carrier.cellIdentities

namespace RepresentativePersistentFreeCommittedUnifySuccessorFacts

/-- A nonempty executable residual extension cannot be hidden behind literal
representative equality. -/
theorem executableExtension_eq_nil_of_representative_eq
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : RepresentativePersistentFreeCommittedPayloadState}
    {left right : Term} {result : Substitution}
    {bodyRest : List PeTTaSpec.PrologCore.Goal}
    {bodyExecutableTail : List PLeaTTa.Goal}
    {sourceExtension executableExtension : TreeSubstitution}
    {generated installed : Subst}
    (facts :
      RepresentativePersistentFreeCommittedUnifySuccessorFacts prog gt before
        after left right result bodyRest bodyExecutableTail sourceExtension
        executableExtension generated installed)
    (same : after.representative = before.representative) :
    executableExtension = [] := by
  have lengths := congrArg List.length facts.representativeExact
  rw [same] at lengths
  simp only [List.length_append] at lengths
  apply List.eq_nil_of_length_eq_zero
  omega

/-- A committed primitive-unification transition is one present fine step,
not an endpoint-compatible stutter.

The predecessor control has the selected equality consed onto the exact
flattened continuation; the successor control is exactly that continuation.
Their goal-list lengths therefore differ by one independently of the selected
MGU orientation or runtime substitution. -/
theorem fineState_ne
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : RepresentativePersistentFreeCommittedPayloadState}
    {left right : Term} {result : Substitution}
    {bodyRest : List PeTTaSpec.PrologCore.Goal}
    {bodyExecutableTail : List PLeaTTa.Goal}
    {sourceExtension executableExtension : TreeSubstitution}
    {generated installed : Subst}
    (facts :
      RepresentativePersistentFreeCommittedUnifySuccessorFacts prog gt before
        after left right result bodyRest bodyExecutableTail sourceExtension
        executableExtension generated installed) :
    before.carrier.fineState ≠ after.carrier.fineState := by
  intro same
  have openEq :
      before.carrier.index.openConf = after.carrier.index.openConf := by
    simpa [PersistentFreeCommittedPayloadState.fineState] using same
  obtain
    ⟨spelling, executableLeft, executableRight, _leftAgreement,
      _rightAgreement, beforeHead, _selected⟩ :=
    facts.selectedExecution
  have afterOpen :
      after.carrier.index.openConf =
        unifySuccessor before.carrier.index.openConf
          (RepresentativePersistentFreeCommittedPayloadState.unifyExecutableTail
            before bodyExecutableTail)
          installed := by
    have projected :=
      congrArg PersistentFreeCommittedPayloadIndex.openConf
        facts.afterIndexExact
    simpa [RepresentativePersistentFreeCommittedPayloadState.unifyIndex,
      RepresentativePersistentFreeCommittedPayloadState.unifyOpenConf] using
      projected
  have afterHead :
      after.carrier.index.openConf.control.cur =
        some
          (RepresentativePersistentFreeCommittedPayloadState.unifyExecutableTail
            before bodyExecutableTail,
            PLeaTTa.trimFor
              (RepresentativePersistentFreeCommittedPayloadState.unifyExecutableTail
                before bodyExecutableTail)
              before.carrier.index.openConf.control.qterm installed) := by
    rw [afterOpen]
    exact
      unifySuccessor_current before.carrier.index.openConf
        (RepresentativePersistentFreeCommittedPayloadState.unifyExecutableTail
          before bodyExecutableTail)
        installed
  rw [← openEq, beforeHead] at afterHead
  have pairEq :
      (spelling.goal executableLeft executableRight ::
          RepresentativePersistentFreeCommittedPayloadState.unifyExecutableTail
            before bodyExecutableTail,
        before.carrier.index.runtime) =
      (RepresentativePersistentFreeCommittedPayloadState.unifyExecutableTail
          before bodyExecutableTail,
        PLeaTTa.trimFor
          (RepresentativePersistentFreeCommittedPayloadState.unifyExecutableTail
            before bodyExecutableTail)
          before.carrier.index.openConf.control.qterm installed) :=
    Option.some.inj afterHead
  have goalsEq :
      spelling.goal executableLeft executableRight ::
          RepresentativePersistentFreeCommittedPayloadState.unifyExecutableTail
            before bodyExecutableTail =
        RepresentativePersistentFreeCommittedPayloadState.unifyExecutableTail
          before bodyExecutableTail :=
    congrArg Prod.fst pairEq
  have lengths := congrArg List.length goalsEq
  simp at lengths

end RepresentativePersistentFreeCommittedUnifySuccessorFacts

namespace RepresentativePersistentFreeCommittedPayloadState

/-- Produce the literal committed successor while retaining both selected
residual orientations in one proof package. -/
theorem exists_afterUnifySuccessWithMaterializedLive
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (before : RepresentativePersistentFreeCommittedPayloadState)
    {left right : Term} {result : Substitution}
    {bodyRest : List PeTTaSpec.PrologCore.Goal}
    (referenceHead :
      before.carrier.index.bodyReferences = .unify left right :: bodyRest)
    (headReady :
      MaterializedUnifyHeadReady before.carrier.index.alpha
        before.representative before.carrier.index.referenceBase
        before.carrier.index.runtime before.carrier.index.bodyBarrier left right
        bodyRest before.carrier.index.bodyExecutables)
    (continuationLive :
      ReadyUnifyContinuationLive before.carrier.index.support
        before.carrier.index.openConf)
    (resolved :
      UnifyResolution before.carrier.index.current left right result) :
    ∃ bodyExecutableTail : List PLeaTTa.Goal,
      ∃ sourceExtension executableExtension : TreeSubstitution,
      ∃ generated installed : Subst,
      ∃ after : RepresentativePersistentFreeCommittedPayloadState,
        RepresentativePersistentFreeCommittedUnifySuccessorFacts prog gt
          before after left right result bodyRest bodyExecutableTail
          sourceExtension executableExtension generated installed := by
  have committedAgreement :
      PersistentFreeCommittedProductPayloadResourceRelatesAt
        before.carrier.index.freshFrontier before.carrier.index.alpha
        before.carrier.index.support before.carrier.index.canonical
        before.carrier.index.referenceBase before.carrier.index.predicateScope
        before.carrier.index.session before.carrier.index.bodyBarrier
        before.carrier.index.callerBarrier (.unify left right :: bodyRest)
        before.carrier.index.bodyExecutables
        before.carrier.index.callerReferences
        before.carrier.index.callerExecutables before.carrier.index.outer
        before.carrier.index.current before.carrier.index.runtime
        before.carrier.index.qterm before.carrier.index.resources
        before.carrier.index.callerScope before.carrier.index.outerScope
        before.carrier.index.context before.carrier.index.baseAlts
        before.carrier.index.source before.carrier.index.openConf
        before.carrier.payloadContext := by
    simpa only [PersistentFreeCommittedPayloadIndex.Relates, referenceHead] using
      before.carrier.agreement
  obtain
    ⟨spelling, executableLeft, executableRight, bodyExecutableTail,
      sourceExtension, executableExtension, generated, installed,
      leftAgreement, rightAgreement, executableHead, selectedSuccess,
      sourceStep, fineStep, nextAgreement, nextSelected⟩ :=
    PersistentFreeCommittedProductPayloadResourceRelatesAt.afterUnifySuccessWithMaterializedLive
      committedAgreement before.cumulative headReady
      continuationLive resolved
  let nextCarrier := PersistentFreeCommittedPayloadState.ofAgreement nextAgreement
  let after : RepresentativePersistentFreeCommittedPayloadState :=
    { carrier := nextCarrier
      representative := executableExtension ++ before.representative
      cumulative := by
        simpa [nextCarrier, PersistentFreeCommittedPayloadState.ofAgreement]
          using nextSelected }
  refine
    ⟨bodyExecutableTail, sourceExtension, executableExtension, generated,
      installed, after, ?_⟩
  refine
    { referenceHead := referenceHead
      afterIndexExact := ?_
      selectedExecution :=
        ⟨spelling, executableLeft, executableRight, leftAgreement,
          rightAgreement, executableHead, selectedSuccess⟩
      sourceStep := ?_
      fineStep := ?_
      representativeExact := rfl
      payloadCellsExact := rfl }
  · rfl
  · simpa [after, nextCarrier, PersistentFreeCommittedPayloadState.ofAgreement]
      using sourceStep
  · simpa [after, nextCarrier, PersistentFreeCommittedPayloadState.ofAgreement]
      using fineStep

/-- Compatibility producer for callers whose equality operands are inside the
immutable public support.  New activation paths should preserve the
whole-body certificate and call
`exists_afterUnifySuccessWithMaterializedLive` directly. -/
theorem exists_afterUnifySuccessLive
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (before : RepresentativePersistentFreeCommittedPayloadState)
    {left right : Term} {result : Substitution}
    {bodyRest : List PeTTaSpec.PrologCore.Goal}
    (referenceHead :
      before.carrier.index.bodyReferences = .unify left right :: bodyRest)
    (leftSupported :
      AlphaTreeSupported before.carrier.index.alpha
        before.carrier.index.support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported before.carrier.index.alpha
        before.carrier.index.support (Term.denote right))
    (continuationLive :
      ReadyUnifyContinuationLive before.carrier.index.support
        before.carrier.index.openConf)
    (resolved :
      UnifyResolution before.carrier.index.current left right result) :
    ∃ bodyExecutableTail : List PLeaTTa.Goal,
      ∃ sourceExtension executableExtension : TreeSubstitution,
      ∃ generated installed : Subst,
      ∃ after : RepresentativePersistentFreeCommittedPayloadState,
        RepresentativePersistentFreeCommittedUnifySuccessorFacts prog gt
          before after left right result bodyRest bodyExecutableTail
          sourceExtension executableExtension generated installed := by
  have bodyPayload :
      TaskPayloadAgrees before.carrier.index.alpha before.carrier.index.support
        before.carrier.index.bodyBarrier before.carrier.index.canonical
        before.carrier.index.referenceBase before.carrier.index.current
        before.carrier.index.runtime before.carrier.index.bodyReferences
        before.carrier.index.bodyExecutables :=
    before.carrier.agreement.ready.2.2.2.headPayload
  have headReady :
      MaterializedUnifyHeadReady before.carrier.index.alpha
        before.representative before.carrier.index.referenceBase
        before.carrier.index.runtime before.carrier.index.bodyBarrier left right
        bodyRest before.carrier.index.bodyExecutables := by
    rw [referenceHead] at bodyPayload
    exact bodyPayload.materializedUnifyHeadReady_of_supported before.cumulative
      leftSupported rightSupported
  exact
    PLeaTTa.PrologPersistentFreeCommittedUnifyTransitionBridge.RepresentativePersistentFreeCommittedPayloadState.exists_afterUnifySuccessWithMaterializedLive
      before referenceHead headReady continuationLive resolved

end RepresentativePersistentFreeCommittedPayloadState

namespace MaterializedRepresentativePersistentFreeCommittedPayloadState

/-- Consume the current committed equality from the whole-body certificate,
without requiring the freshly standardized clause variables to occur in the
caller's immutable support. -/
theorem exists_afterUnifySuccess
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (before : MaterializedRepresentativePersistentFreeCommittedPayloadState)
    {left right : Term} {result : Substitution}
    {bodyRest : List PeTTaSpec.PrologCore.Goal}
    (referenceHead :
      before.carrier.carrier.index.bodyReferences =
        .unify left right :: bodyRest)
    (continuationLive :
      ReadyUnifyContinuationLive before.carrier.carrier.index.support
        before.carrier.carrier.index.openConf)
    (resolved :
      UnifyResolution before.carrier.carrier.index.current left right result) :
    ∃ bodyExecutableTail : List PLeaTTa.Goal,
      ∃ sourceExtension executableExtension : TreeSubstitution,
      ∃ generated installed : Subst,
      ∃ after : RepresentativePersistentFreeCommittedPayloadState,
        RepresentativePersistentFreeCommittedUnifySuccessorFacts prog gt
          before.carrier after left right result bodyRest bodyExecutableTail
          sourceExtension executableExtension generated installed := by
  have current := before.materializedUnifyGoals
  rw [referenceHead] at current
  have headReady := current.unifyHeadReady
  exact
    PLeaTTa.PrologPersistentFreeCommittedUnifyTransitionBridge.RepresentativePersistentFreeCommittedPayloadState.exists_afterUnifySuccessWithMaterializedLive
      before.carrier referenceHead headReady continuationLive resolved

end MaterializedRepresentativePersistentFreeCommittedPayloadState

end PLeaTTa.PrologPersistentFreeCommittedUnifyTransitionBridge
