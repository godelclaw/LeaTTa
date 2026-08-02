-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologCurrentSessionPayloadBridge
Purpose: Couple current-session product/resource correspondence to the exact
  immutable payload zipper owned by its retained alternatives.
Trusted boundary: none
Main exports:
  SpinedActiveProductPayloadResourceRelatesAt,
  SpinedActiveProductPayloadResourceRelatesAt.reindex,
  SpinedRepresentativeProductActivation.spinedProductPayloadResourceRelates
-/
import PLeaTTa.Proofs.PrologNestedRetainedPayloadBridge

namespace PLeaTTa.PrologCurrentSessionPayloadBridge

open Metta (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologAlphaFreshFrontierBridge
open PrologControlSegmentSpineBridge
open PrologNestedRetainedPayloadBridge
open PrologMguComposition
open PrologProductResourceContextBridge
open PrologProductResourceTransitionBridge
open PrologRecursiveCallPayloadBridge
open PrologRepresentativeCallFrontierBridge
open PrologRepresentativeProductActivationBridge
open PrologRepresentativeStepActivationBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
open PrologSourceProductContextBridge
open PrologStateBridge

/-- The unique payload-bearing zipper shape belonging to one active product
resource state.  Naming this dependent index keeps subsequent relations
readable without weakening any cursor/resource/scope equality. -/
abbrev ActiveProductPayloadContext
    (alpha support : List (LogicVar × String)) (qterm : Atom)
    (opened : OpenedCall) (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (bodyBarrier callerBarrier : Nat)
    (callerReferences : List PeTTaSpec.PrologCore.Goal)
    (callerExecutables : List PLeaTTa.Goal)
    (outer : List ControlSegment)
    (active : RetainedAlternativeSegment)
    (resources : List RetainedAlternativeSegment)
    (callerScope outerScope : CutScopeId)
    (context : ActiveProductContext) :=
  SourceControlResourcePayloadContextAgrees alpha support qterm bodyBarrier
    ({ barrier := callerBarrier
       references := callerReferences
       executables := callerExecutables } ::
     outer)
    (active :: resources) opened.scope
    ({ callerScope := callerScope
       predicateScope := opened.scope
       retained :=
         .clauses opened.scope (finish.advance branch branchTail)
       callerRest := callerReferences } ::
     context)
    outerScope

/-- One active local-product state with its complete retained logical payload.

The relation and its final payload-context index deliberately share all source
segments, resource descriptors, cursor scopes, and executable state.  Thus a
payload certificate
cannot be paired with a merely shape-compatible resource bank.  Persistent
world/database agreement comes from `core` at the *current* session, while
`endpointsCurrent` pins every immutable retained allocation to that same
source fresh high-water and executable counter.

The zipper remains Type-valued linear data; this relation is Prop-valued and
names that exact zipper as a dependent index, so existing activation theorems
can produce it without forbidden Prop-to-Type elimination. -/
structure SpinedActiveProductPayloadResourceRelatesAt
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String))
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (opened : OpenedCall) (session : Session)
    (pending : DemandDrivenCallStep.PendingCall)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (altTail : List PLeaTTa.Alt)
    (bodyBarrier callerBarrier : Nat)
    (bodyReferences : List PeTTaSpec.PrologCore.Goal)
    (bodyExecutables : List PLeaTTa.Goal)
    (callerReferences : List PeTTaSpec.PrologCore.Goal)
    (callerExecutables : List PLeaTTa.Goal)
    (outer : List ControlSegment)
    (current : Substitution) (runtime : Subst) (qterm : Atom)
    (active : RetainedAlternativeSegment)
    (resources : List RetainedAlternativeSegment)
    (callerScope outerScope : CutScopeId)
    (context : ActiveProductContext)
    (baseAlts : List PLeaTTa.Alt)
    (source : Search) (state : OpenConf)
    (payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish branch
        branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context) : Prop where
  core :
    SpinedActiveProductResourceRelatesAt freshFrontier alpha support canonical
      referenceBase opened session pending finish branch branchTail altTail
      bodyBarrier callerBarrier bodyReferences bodyExecutables
      callerReferences callerExecutables outer current runtime qterm active
      resources callerScope outerScope context baseAlts source state
  endpointsCurrent :
    endpointsBelow payloadContext session.resolver.nextFresh
      state.persistent.counter
  /-- Every payload cell recursively dominates its complete older tail at
  that cell's own allocation seeds.  Unlike a one-level head certificate,
  this survives arbitrary nested-call exhaustion and payload popping. -/
  activationOrdered : ActivationOrdered payloadContext
  /-- Every retained activation is indexed by its literal call-start
  generation and dominated by this relation's current persistent session. -/
  activationOrigins :
    LocalActivationOriginSpineRelates session payloadContext
  /-- Every retained occurrence owns the exact historical alternatives and
  barrier cache outside its call.  The separate frame conjunct explicitly
  states the current local-call build has no typed delimiter interleaved
  between cells. -/
  controlOrigins :
    LocalControlOriginSpineRelates baseAlts state.frames
      state.control.barriers payloadContext

namespace SpinedActiveProductPayloadResourceRelatesAt

/-- Recover the historical one-level API from the recursive chronology
invariant.  Consumers needing only the active head's older-tail bound do not
need to know how deeper pops are represented. -/
theorem outerActivationEndpoints
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
        altTail bodyBarrier callerBarrier bodyReferences bodyExecutables
        callerReferences callerExecutables outer current runtime qterm active
        resources callerScope outerScope context baseAlts source state
        payloadContext) :
    endpointsBelow
      (SourceControlResourcePayloadContextAgrees.tail payloadContext)
      (finish.advance branch branchTail).reservationStart active.counter :=
  ActivationOrdered.head payloadContext agreement.activationOrdered

/-- Erasing immutable payload evidence recovers the exact current-session
resource correspondence, without changing any state index. -/
def weak
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
        altTail bodyBarrier callerBarrier bodyReferences bodyExecutables
        callerReferences callerExecutables outer current runtime qterm active
        resources callerScope outerScope context baseAlts source state
        payloadContext) :
    SpinedActiveProductResourceRelatesAt freshFrontier alpha support canonical
      referenceBase opened session pending finish branch branchTail altTail
      bodyBarrier callerBarrier bodyReferences bodyExecutables
      callerReferences callerExecutables outer current runtime qterm active
      resources callerScope outerScope context baseAlts source state :=
  agreement.core

/-- Any singleton-cut older caller retained by the payload-coupled
current-session relation keeps its own executable barrier tag.

The active body and immediate caller already occupy the first two spine
regions.  Thus `segment ∈ outer` ranges over arbitrarily deep surrounding
callers; the theorem rules out silently retagging any of them while lifting a
local step through the complete control/resource/payload context. -/
theorem outerCutBarrier_eq
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
        altTail bodyBarrier callerBarrier bodyReferences bodyExecutables
        callerReferences callerExecutables outer current runtime qterm active
        resources callerScope outerScope context baseAlts source state
        payloadContext)
    {segment : ControlSegment} {actualBarrier : Nat}
    (present : segment ∈ outer)
    (sourceCut : segment.references = [.cut])
    (executableCut : segment.executables = [.cutAt actualBarrier]) :
    segment.barrier = actualBarrier := by
  exact
    agreement.core.control.ready.2.2.2.control.member_cutBarrier_eq
      (by simp [present]) sourceCut executableCut

/-- A differently tagged singleton-cut outer segment cannot inhabit the full
current-session payload/resource relation.  This is the arbitrary-depth
contradiction form of `outerCutBarrier_eq`. -/
theorem rejectsOuterCutRetag
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
        altTail bodyBarrier callerBarrier bodyReferences bodyExecutables
        callerReferences callerExecutables outer current runtime qterm active
        resources callerScope outerScope context baseAlts source state
        payloadContext)
    {segment : ControlSegment} {actualBarrier : Nat}
    (present : segment ∈ outer)
    (sourceCut : segment.references = [.cut])
    (executableCut : segment.executables = [.cutAt actualBarrier])
    (different : segment.barrier ≠ actualBarrier) : False :=
  different
    (agreement.outerCutBarrier_eq present sourceCut executableCut)

/-- The payload-bearing zipper erases to the same outer
source/control/resource alignment used by the core resource stack. -/
def payloadAlignment
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
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {source : Search} {state : OpenConf}
    {payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish branch
        branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context}
    (_agreement :
      SpinedActiveProductPayloadResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened session pending finish branch branchTail
        altTail bodyBarrier callerBarrier bodyReferences bodyExecutables
        callerReferences callerExecutables outer current runtime qterm active
        resources callerScope outerScope context baseAlts source state
        payloadContext) :
    SourceControlResourceContextAgrees alpha qterm bodyBarrier
      ({ barrier := callerBarrier
         references := callerReferences
         executables := callerExecutables } ::
       outer)
      (active :: resources) opened.scope
      ({ callerScope := callerScope
         predicateScope := opened.scope
         retained :=
           .clauses opened.scope (finish.advance branch branchTail)
         callerRest := callerReferences } ::
      context)
      outerScope :=
  payloadContext.alignment

/-- Reindex at a later source session while retaining the exact source focus,
resource bank, payload zipper, and executable state.

This is a chronology transport, not a reachability theorem: the caller must
supply current persistent database/fresh agreement and source high-water
advance. -/
def reindex
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {session nextSession : Session}
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
        altTail bodyBarrier callerBarrier bodyReferences bodyExecutables
        callerReferences callerExecutables outer current runtime qterm active
        resources callerScope outerScope context baseAlts source state
        payloadContext)
    (persistent :
      SessionRelatesPersistent freshFrontier nextSession state.persistent)
    (advanced : SessionHighWatersExtend session nextSession) :
    SpinedActiveProductPayloadResourceRelatesAt freshFrontier alpha support
      canonical referenceBase opened nextSession pending finish branch
      branchTail altTail bodyBarrier callerBarrier bodyReferences
      bodyExecutables callerReferences callerExecutables outer current runtime
      qterm active resources callerScope outerScope context baseAlts source
      state payloadContext :=
  ⟨agreement.core.reindex persistent advanced,
    endpointsBelow_mono payloadContext agreement.endpointsCurrent
      advanced.fresh (Nat.le_refl _),
    agreement.activationOrdered,
    agreement.activationOrigins.advance payloadContext advanced,
    agreement.controlOrigins⟩

/-- The payload-coupled relation genuinely admits a strictly later fresh
session when the frontier relates that high-water to the unchanged executable
counter.  Every cursor/resource/payload index remains literal. -/
theorem strictFreshReindex
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
        altTail bodyBarrier callerBarrier bodyReferences bodyExecutables
        callerReferences callerExecutables outer current runtime qterm active
        resources callerScope outerScope context baseAlts source state
        payloadContext)
    (freshAdvanced :
      freshFrontier (session.resolver.nextFresh + 1)
        state.persistent.counter) :
    ∃ nextSession : Session,
      session.resolver.nextFresh < nextSession.resolver.nextFresh ∧
      SpinedActiveProductPayloadResourceRelatesAt freshFrontier alpha support
        canonical referenceBase opened nextSession pending finish branch
        branchTail altTail bodyBarrier callerBarrier bodyReferences
        bodyExecutables callerReferences callerExecutables outer current runtime
        qterm active resources callerScope outerScope context baseAlts source
        state payloadContext := by
  let nextSession : Session :=
    { session with
      resolver :=
        { session.resolver with
          nextFresh := session.resolver.nextFresh + 1 } }
  have persistent :
      SessionRelatesPersistent freshFrontier nextSession state.persistent := by
    refine ⟨?_, ?_⟩
    · simpa [nextSession] using agreement.core.control.ready.1.database
    · simpa [nextSession] using freshAdvanced
  have chronology : SessionHighWatersExtend session nextSession := by
    simpa [nextSession] using
      (SessionHighWatersExtend.strict_fresh_witness session).1
  refine ⟨nextSession, ?_, agreement.reindex persistent chronology⟩
  simp [nextSession]

/-- A source fresh allocator below the historical opener cannot inhabit the
payload-coupled current-session relation. -/
theorem rejectsFreshRegression
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
    {context : ActiveProductContext}
    {baseAlts : List PLeaTTa.Alt}
    {source : Search} {state : OpenConf}
    {payloadContext :
      ActiveProductPayloadContext alpha support qterm opened finish branch
        branchTail bodyBarrier callerBarrier callerReferences
        callerExecutables outer active resources callerScope outerScope
        context}
    (regressed :
      session.resolver.nextFresh < opened.session.resolver.nextFresh) :
    SpinedActiveProductPayloadResourceRelatesAt freshFrontier alpha support
      canonical referenceBase opened session pending finish branch branchTail
      altTail bodyBarrier callerBarrier bodyReferences bodyExecutables
      callerReferences callerExecutables outer current runtime qterm active
      resources callerScope outerScope context baseAlts source state
      payloadContext → False := by
  intro agreement
  exact agreement.core.control.rejectsFreshRegression regressed

end SpinedActiveProductPayloadResourceRelatesAt

/-! ## Construction from one real nested local activation -/

/-- A real nested representative activation constructs the current-session
resource relation and its exact payload zipper in one existential package.

The endpoint certificate is returned at the actual post-activation source
session and executable counter.  No later caller chooses either floor. -/
theorem
    SpinedRepresentativeProductActivation.spinedProductPayloadResourceRelates
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
      pending.outer.alts = flattenOwnedAlts resources baseAlts)
    (outerControlOrigins :
      LocalControlOriginSpineRelates baseAlts pending.frames
        pending.outer.barriers outerPayloads) :
    ∃ active : RetainedAlternativeSegment,
      ∃ payloadContext :
          ActiveProductPayloadContext nextAlpha support qterm opened finish
            branch branchTail bodyBarrier callerBarrier segmentReferenceRest
            segmentExecutableRest outer active resources callerScope outerScope
            context,
        SpinedActiveProductPayloadResourceRelatesAt
            (AlphaFreshFrontier nextAlpha) nextAlpha support
            (sourceCanonical ++ canonical) referenceBase opened opened.session
            pending finish branch branchTail altTail bodyBarrier callerBarrier
            branch.body copied.body segmentReferenceRest segmentExecutableRest
            outer independentResult
            (PLeaTTa.trimFor
              (copied.body ++
                (segmentExecutableRest ++ flattenExecutables outer))
              qterm installed)
            qterm active resources callerScope outerScope context baseAlts
            (ActiveProductContext.plug context
              (activatedSourceProduct callerScope opened finish branch branchTail
                independentResult segmentReferenceRest))
            (activatedOpenSuccessor pending copied
              (segmentExecutableRest ++ flattenExecutables outer) qterm
              installed)
            payloadContext ∧
          ExtendsAboveAt branch.firstFresh startCounter
            activation.alphaExtension outerPayloads
            (SourceControlResourcePayloadContextAgrees.tail payloadContext) ∧
          (SourceControlResourcePayloadContextAgrees.headCell payloadContext).snapshot.residualRepresentative =
            representative := by
  obtain ⟨active, _snapshot, payloadContext, result⟩ :=
    _root_.PLeaTTa.PrologNestedRetainedPayloadBridge.SpinedRepresentativeProductActivation.activeResourceStackWithNestedSnapshots
      retainedPosition positioned frontier preHeadPayload oldCumulative
      materializedAtOpen openedArguments openedBindings queryReferenceBelow activation
      sourceFresh outerPayloads outerEndpoints outerOrdered
      outerActivationOrigins baseAlts outerAlts
  have endpoints := result.1
  have activationOrdered := result.2.1
  have activationOrigins := result.2.2.1
  have outerPayloadExact := result.2.2.2.1
  have _outerActivationEndpoints := result.2.2.2.2.1
  have resourceStack :
      ActiveProductResourceStackAgrees nextAlpha qterm bodyBarrier
        callerBarrier pending (finish.advance branch branchTail)
        (segmentExecutableRest ++ flattenExecutables outer)
        altTail active outer resources callerScope outerScope context
        baseAlts
        (activatedOpenSuccessor pending copied
          (segmentExecutableRest ++ flattenExecutables outer) qterm
          installed) := result.2.2.2.2.2.1
  have snapshotRepresentative :
      (SourceControlResourcePayloadContextAgrees.headCell payloadContext).snapshot.residualRepresentative =
      representative :=
    result.2.2.2.2.2.2.1
  have snapshotOrigin :
      (SourceControlResourcePayloadContextAgrees.headCell payloadContext).snapshot.controlOrigin.MatchesPendingControl
        pending :=
    result.2.2.2.2.2.2.2
  have counterExact :
      (activatedOpenSuccessor pending copied
        (segmentExecutableRest ++ flattenExecutables outer) qterm
        installed).persistent.counter =
        pending.persistent.counter := by
    unfold activatedOpenSuccessor OpenConf.stepOpen OpenConf.ofConfWith
      persistentOf
    exact activation.counterPreserved
  have endpointsCurrent :
      endpointsBelow payloadContext opened.session.resolver.nextFresh
        (activatedOpenSuccessor pending copied
          (segmentExecutableRest ++ flattenExecutables outer) qterm
          installed).persistent.counter := by
    rw [counterExact]
    exact endpoints
  have outerControlNext :
      LocalControlOriginSpineRelates baseAlts pending.frames
        pending.outer.barriers
        (SourceControlResourcePayloadContextAgrees.tail payloadContext) := by
    rw [outerPayloadExact.exact]
    exact
      outerControlOrigins.extendAbove activation.alphaExtension outerPayloads
        outerPayloadExact.below baseAlts pending.frames
        pending.outer.barriers
  have activeControl :
      SpinedActiveProductRelatesAt (AlphaFreshFrontier nextAlpha) nextAlpha
        support (sourceCanonical ++ canonical) referenceBase opened
        opened.session pending finish branch branchTail altTail bodyBarrier
        callerBarrier branch.body copied.body segmentReferenceRest
        segmentExecutableRest outer independentResult
        (PLeaTTa.trimFor
          (copied.body ++
            (segmentExecutableRest ++ flattenExecutables outer))
          qterm installed)
        qterm
        (activatedOpenSuccessor pending copied
          (segmentExecutableRest ++ flattenExecutables outer) qterm
          installed) :=
    _root_.PLeaTTa.PrologProductResourceTransitionBridge.SpinedRepresentativeProductActivation.spinedActiveProductRelates
      activation
  have core :
      SpinedActiveProductResourceRelatesAt (AlphaFreshFrontier nextAlpha)
        nextAlpha support (sourceCanonical ++ canonical) referenceBase opened
        opened.session pending finish branch branchTail altTail bodyBarrier
        callerBarrier branch.body copied.body segmentReferenceRest
        segmentExecutableRest outer independentResult
        (PLeaTTa.trimFor
          (copied.body ++
            (segmentExecutableRest ++ flattenExecutables outer))
          qterm installed)
        qterm active resources callerScope outerScope context baseAlts
        (ActiveProductContext.plug context
          (activatedSourceProduct callerScope opened finish branch branchTail
            independentResult segmentReferenceRest))
        (activatedOpenSuccessor pending copied
          (segmentExecutableRest ++ flattenExecutables outer) qterm installed) :=
    ⟨activeControl, resourceStack, rfl⟩
  have controlOriginsAtPending :
      LocalControlOriginSpineRelates baseAlts pending.frames
        (PLeaTTa.pushBarrierCache pending.outer.barriers) payloadContext :=
    LocalControlOriginSpineRelates.prepend payloadContext outerControlNext
      (snapshotOrigin.outerAlts.trans outerAlts)
      snapshotOrigin.outerBarriers snapshotOrigin.frames
  have controlOrigins :
      LocalControlOriginSpineRelates baseAlts
        (activatedOpenSuccessor pending copied
          (segmentExecutableRest ++ flattenExecutables outer) qterm
          installed).frames
        (activatedOpenSuccessor pending copied
          (segmentExecutableRest ++ flattenExecutables outer) qterm
          installed).control.barriers
        payloadContext := by
    simpa only [core.control.frames, core.control.retainedBarriers] using
      controlOriginsAtPending
  refine
    ⟨active, payloadContext, ?_, outerPayloadExact, snapshotRepresentative⟩
  exact
    ⟨core, endpointsCurrent, activationOrdered, activationOrigins,
      controlOrigins⟩

end PLeaTTa.PrologCurrentSessionPayloadBridge
