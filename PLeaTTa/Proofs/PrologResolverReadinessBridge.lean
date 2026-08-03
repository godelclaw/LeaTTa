-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologResolverReadinessBridge
Purpose: Couple exact resolver readiness packets to failure/rebase-aware
  source and fine-machine transitions.
Trusted boundary: none
Main exports:
  ResolverStepReady,
  ResolverStepReady.Produces,
  ResolverCertifiedCoupledStep,
  ResolverProgressPreservesReady
-/
import PLeaTTa.Proofs.PrologFailureRebasePrefixBridge

namespace PLeaTTa.PrologResolverReadinessBridge

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
open PrologFailureRebasePrefixBridge
open PrologHeterogeneousPrefixBridge
open PrologMguBridge
open PrologMguComposition
open PrologNestedCallChainBridge
open PrologNestedCallReadyBridge
open PrologOrdinaryStepBridge
open PrologPrefilterScanBridge
open PrologProductResourceContextBridge
open PrologProductResourceTransitionBridge
open PrologPersistentFreeActivePayloadBridge
open PrologRepresentativeProductActivationBridge
open PrologRetainedCursorOwnershipBridge
open PrologRetainedPayloadActivationBridge
open PrologRetainedPayloadSnapshotBridge
open PrologRetainedPayloadSnapshotBridge.SourceControlResourcePayloadContextAgrees
open PrologSourceProductContextBridge
open PrologStateBridge

/-!
`ActiveStepReady` couples successful forward work to exact successors, but it
cannot express the non-monotone logical representative change at
backtracking.  This additive readiness vocabulary embeds that forward lane
unchanged and adds precisely the two rollback phases already modeled by
`ResolverCertifiedTransition`.

The readiness packets contain only producer premises.  In particular, they
contain neither `RetainedFailureSuccessor` nor `RetainedActivationSuccessor`;
those proof-relevant successor packages are reconstructed by `produces`.
The transition relation is intentionally relational: a packet licenses any
independently valid successor package for its literal indexed state.  It does
not claim uniqueness of the retained-failure rejection count or endpoint.
Reactivation has a determining `HeadResolution` result in its readiness
packet, so that lane additionally requires the generated successor package to
carry exactly the same result; failure currently has no analogous determining
premise, and its cross-package uniqueness remains open.
-/

/-- Semantic and operational premises for one exact resolver step.

The index is the literal source phase.  Failure is ready only at an ordinary
active state, while reactivation is ready only at the exact post-failure
payload that owns the retained snapshot. -/
inductive ResolverStepReady : ResolverPhaseState → Type where
  | forward {state : ProductPhaseState}
      (ready : ActiveStepReady state) :
      ResolverStepReady (.ordinary state)
  | retainedFailure
      (state : RepresentativeActivePayloadState)
      {left right : Term}
      {bodyRest : List PeTTaSpec.PrologCore.Goal}
      (referenceHead :
        state.carrier.index.bodyReferences = .unify left right :: bodyRest)
      (leftSupported :
        AlphaTreeSupported state.carrier.index.alpha
          state.carrier.index.support (Term.denote left))
      (rightSupported :
        AlphaTreeSupported state.carrier.index.alpha
          state.carrier.index.support (Term.denote right))
      (currentSafe :
        Substitution.BooleanAliasSafe state.carrier.index.current)
      (leftAliasSafe : TermBooleanAliasSafe left)
      (rightAliasSafe : TermBooleanAliasSafe right)
      (clash :
        ¬ ∃ result,
          UnifyResolution state.carrier.index.current left right result)
      (exactFresh :
        state.carrier.index.freshFrontier =
          AlphaFreshFrontier state.carrier.index.alpha)
      (nonempty : state.carrier.index.active.alts ≠ []) :
      ResolverStepReady
        (.ordinary
          (.active
            (RepresentativePersistentFreeActivePayloadState.ofLegacy state)))
  | retainedActivation
      (state : PostFailurePayloadState)
      {resolvedResult : Substitution}
      (currentShared : SharedRuntimeAlpha state.index.alpha)
      (below : ConfBelowResolutionCounter state.index.openConf.toConf)
      (live :
        AlphaRuntimeNamesLive state.index.support
          (state.index.copied.body ++ state.index.resource.rest)
          state.index.resource.qterm)
      (resolved : HeadResolution state.index.branch resolvedResult) :
      ResolverStepReady (.postFailure state)

namespace ResolverStepReady

/-- An exact successor licensed by one resolver readiness packet.

Each constructor repeats the readiness packet's indices and adds only the
independently generated successor facts.  The failure target is definitionally
`facts.after`; the activation target is definitionally `facts.after`; neither
can be replaced by a merely endpoint-compatible state.  This relation does
not assert that two independently valid failure packages for the same state
are equal. -/
inductive Produces (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable) :
    {before : ResolverPhaseState} →
      ResolverStepReady before → ResolverPhaseState → Prop where
  | forward
      {state after : ProductPhaseState}
      (ready : ActiveStepReady state)
      (production : ready.Produces prog gt after) :
      Produces prog gt (.forward ready) (.ordinary after)
  | retainedFailure
      (state : RepresentativeActivePayloadState)
      {left right : Term}
      {bodyRest : List PeTTaSpec.PrologCore.Goal}
      (referenceHead :
        state.carrier.index.bodyReferences = .unify left right :: bodyRest)
      (leftSupported :
        AlphaTreeSupported state.carrier.index.alpha
          state.carrier.index.support (Term.denote left))
      (rightSupported :
        AlphaTreeSupported state.carrier.index.alpha
          state.carrier.index.support (Term.denote right))
      (currentSafe :
        Substitution.BooleanAliasSafe state.carrier.index.current)
      (leftAliasSafe : TermBooleanAliasSafe left)
      (rightAliasSafe : TermBooleanAliasSafe right)
      (clash :
        ¬ ∃ result,
          UnifyResolution state.carrier.index.current left right result)
      (exactFresh :
        state.carrier.index.freshFrontier =
          AlphaFreshFrontier state.carrier.index.alpha)
      (nonempty : state.carrier.index.active.alts ≠ [])
      (facts : RetainedFailureSuccessor prog gt state) :
      Produces prog gt
        (.retainedFailure state referenceHead leftSupported rightSupported
          currentSafe leftAliasSafe rightAliasSafe clash exactFresh nonempty)
        (.postFailure facts.after)
  | retainedActivation
      (state : PostFailurePayloadState)
      {resolvedResult : Substitution}
      (currentShared : SharedRuntimeAlpha state.index.alpha)
      (below : ConfBelowResolutionCounter state.index.openConf.toConf)
      (live :
        AlphaRuntimeNamesLive state.index.support
          (state.index.copied.body ++ state.index.resource.rest)
          state.index.resource.qterm)
      (resolved : HeadResolution state.index.branch resolvedResult)
      (facts : RetainedActivationSuccessor prog gt state)
      (resultExact : facts.independentResult = resolvedResult) :
      Produces prog gt
        (.retainedActivation state currentShared below live resolved)
        (.ordinary
          (.active
            (RepresentativePersistentFreeActivePayloadState.ofLegacy
              facts.after)))

end ResolverStepReady

/-- One non-stuttering resolver transition after hiding only its closed kind.

The proof-relevant transition remains under `Nonempty`; endpoints alone do
not license a step.  Positive cost prevents zero-length administrative
derivations from inflating a prefix. -/
def ResolverCertifiedCoupledStep (prog : PLeaTTa.Prog)
    (gt : Metta.GroundingTable)
    (before after : ResolverPhaseState) : Prop :=
  ∃ kind : ResolverTransitionKind,
    0 < kind.sourceCost + kind.fineCost ∧
      Nonempty (ResolverCertifiedTransition prog gt kind before after)

namespace ResolverCertifiedCoupledStep

/-- A hidden resolver label still determines both exact executions. -/
theorem exactExecutions
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : ResolverPhaseState}
    (step : ResolverCertifiedCoupledStep prog gt before after) :
    ∃ kind : ResolverTransitionKind,
      StepsN kind.sourceCost before.sourceState kind.sourceEvents
          after.sourceState ∧
        DemandDrivenCallStep.StepsN prog gt kind.fineCost before.fineState
          after.fineState := by
  obtain ⟨kind, _positive, ⟨transition⟩⟩ := step
  exact ⟨kind, transition.sourceSteps, transition.fineSteps⟩

/-- Persistent source allocators cannot rewind through rollback. -/
theorem sessionHighWaters
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : ResolverPhaseState}
    (step : ResolverCertifiedCoupledStep prog gt before after) :
    SessionHighWatersExtend before.session after.session := by
  obtain ⟨_kind, _positive, ⟨transition⟩⟩ := step
  exact transition.sessionHighWaters

/-- The executable allocation counter cannot rewind through rollback. -/
theorem executableCounter_mono
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : ResolverPhaseState}
    (step : ResolverCertifiedCoupledStep prog gt before after) :
    before.openConf.persistent.counter ≤ after.openConf.persistent.counter := by
  obtain ⟨_kind, _positive, ⟨transition⟩⟩ := step
  exact transition.executableCounter_mono

/-- Every alpha pair live before the hidden transition remains live after. -/
theorem alphaIncluded
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : ResolverPhaseState}
    (step : ResolverCertifiedCoupledStep prog gt before after) :
    ∀ pair, pair ∈ before.alpha → pair ∈ after.alpha := by
  obtain ⟨_kind, _positive, ⟨transition⟩⟩ := step
  exact transition.alphaIncluded

/-- Hiding the kind does not hide its exact alpha-allocation law. -/
theorem alphaEvolution
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : ResolverPhaseState}
    (step : ResolverCertifiedCoupledStep prog gt before after) :
    ∃ kind : ResolverTransitionKind, kind.AlphaEvolution before after := by
  obtain ⟨kind, _positive, ⟨transition⟩⟩ := step
  exact ⟨kind, transition.alphaEvolution⟩

/-- Hiding the kind retains extension/rebase/reactivation as distinct laws. -/
theorem representativeEvolution
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : ResolverPhaseState}
    (step : ResolverCertifiedCoupledStep prog gt before after) :
    ∃ kind : ResolverTransitionKind,
      kind.RepresentativeEvolution before after := by
  obtain ⟨kind, _positive, ⟨transition⟩⟩ := step
  exact ⟨kind, transition.representativeEvolution⟩

end ResolverCertifiedCoupledStep

namespace ResolverStepReady.Produces

/-- The outer target phase is fixed by the readiness constructor.  This
shape lemma avoids asking dependent elimination to recover injectivity from
the intentionally one-way legacy-to-persistent-free carrier embedding. -/
theorem target_shape
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : ResolverPhaseState}
    {ready : ResolverStepReady before}
    (production : ready.Produces prog gt after) :
    match ready with
    | .forward _ => ∃ state, after = .ordinary state
    | .retainedFailure _ _ _ _ _ _ _ _ _ _ =>
        ∃ state, after = .postFailure state
    | .retainedActivation _ _ _ _ _ =>
        ∃ state, after = .ordinary state := by
  cases production with
  | forward ready production => exact ⟨_, rfl⟩
  | retainedFailure state referenceHead leftSupported rightSupported
      currentSafe leftAliasSafe rightAliasSafe clash exactFresh nonempty
      facts =>
      exact ⟨_, rfl⟩
  | retainedActivation state currentShared below live resolved facts
      resultExact =>
      exact ⟨_, rfl⟩

/-- A retained-failure production exposes the independently certified
successor package carried by the transition.  The legacy source is returned
as data rather than recovered by pretending the one-way carrier embedding is
injective. -/
theorem retainedFailure_certificate
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : ResolverPhaseState}
    {ready : ResolverStepReady before}
    (production : ready.Produces prog gt after) :
    match ready with
    | .retainedFailure _ _ _ _ _ _ _ _ _ _ =>
        ∃ source : RepresentativeActivePayloadState,
          ∃ facts : RetainedFailureSuccessor prog gt source,
            before =
                .ordinary
                  (.active
                    (RepresentativePersistentFreeActivePayloadState.ofLegacy
                      source)) ∧
              after = .postFailure facts.after
    | _ => True := by
  cases production with
  | forward ready production => trivial
  | retainedFailure state referenceHead leftSupported rightSupported
      currentSafe leftAliasSafe rightAliasSafe clash exactFresh nonempty
      facts =>
      exact ⟨state, facts, rfl, rfl⟩
  | retainedActivation state currentShared below live resolved facts
      resultExact =>
      trivial

/-- Forgetting a readiness packet preserves the one exact resolver
transition that it generated. -/
theorem certifiedCoupledStep
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before after : ResolverPhaseState}
    {ready : ResolverStepReady before}
    (production : ready.Produces prog gt after) :
    ResolverCertifiedCoupledStep prog gt before after := by
  cases production with
  | forward ready forwardProduction =>
      obtain ⟨kind, positive, ⟨transition⟩⟩ :=
        forwardProduction.certifiedCoupledStep
      exact
        ⟨.forward kind,
          by simpa [ResolverTransitionKind.sourceCost,
            ResolverTransitionKind.fineCost] using positive,
          ⟨.forward transition⟩⟩
  | retainedFailure state referenceHead leftSupported rightSupported
      currentSafe leftAliasSafe rightAliasSafe clash exactFresh nonempty
      facts =>
      exact
        ⟨.retainedFailure facts.count,
          by simp [ResolverTransitionKind.sourceCost,
            ResolverTransitionKind.fineCost],
          ⟨.retainedFailure facts⟩⟩
  | retainedActivation state currentShared below live resolved facts
      resultExact =>
      exact
        ⟨.retainedActivation,
          by simp [ResolverTransitionKind.sourceCost,
            ResolverTransitionKind.fineCost],
          ⟨.retainedActivation facts⟩⟩

/-- A forward readiness packet cannot be laundered into a post-failure
successor. -/
theorem forward_not_postFailure
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {state : ProductPhaseState}
    (ready : ActiveStepReady state)
    (target : PostFailurePayloadState) :
    ¬ Produces prog gt (.forward ready) (.postFailure target) := by
  intro production
  cases production

/-- Failure readiness can only produce its exact post-failure phase, never
an ordinary endpoint. -/
theorem retainedFailure_not_ordinary
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (state : RepresentativeActivePayloadState)
    {left right : Term}
    {bodyRest : List PeTTaSpec.PrologCore.Goal}
    (referenceHead :
      state.carrier.index.bodyReferences = .unify left right :: bodyRest)
    (leftSupported :
      AlphaTreeSupported state.carrier.index.alpha
        state.carrier.index.support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported state.carrier.index.alpha
        state.carrier.index.support (Term.denote right))
    (currentSafe : Substitution.BooleanAliasSafe state.carrier.index.current)
    (leftAliasSafe : TermBooleanAliasSafe left)
    (rightAliasSafe : TermBooleanAliasSafe right)
    (clash :
      ¬ ∃ result,
        UnifyResolution state.carrier.index.current left right result)
    (exactFresh :
      state.carrier.index.freshFrontier =
        AlphaFreshFrontier state.carrier.index.alpha)
    (nonempty : state.carrier.index.active.alts ≠ [])
    (target : ProductPhaseState) :
    ¬ Produces prog gt
        (.retainedFailure state referenceHead leftSupported rightSupported
          currentSafe leftAliasSafe rightAliasSafe clash exactFresh nonempty)
        (.ordinary target) := by
  intro production
  simpa using production.target_shape

/-- Every post-failure endpoint licensed by a failure packet is the literal
`after` projection of a complete independently certified failure package.

This is exact endpoint provenance, not successor determinism: uniqueness of
two such packages remains a separate open theorem. -/
theorem retainedFailure_target_exact
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (state : RepresentativeActivePayloadState)
    {left right : Term}
    {bodyRest : List PeTTaSpec.PrologCore.Goal}
    (referenceHead :
      state.carrier.index.bodyReferences = .unify left right :: bodyRest)
    (leftSupported :
      AlphaTreeSupported state.carrier.index.alpha
        state.carrier.index.support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported state.carrier.index.alpha
        state.carrier.index.support (Term.denote right))
    (currentSafe : Substitution.BooleanAliasSafe state.carrier.index.current)
    (leftAliasSafe : TermBooleanAliasSafe left)
    (rightAliasSafe : TermBooleanAliasSafe right)
    (clash :
      ¬ ∃ result,
        UnifyResolution state.carrier.index.current left right result)
    (exactFresh :
      state.carrier.index.freshFrontier =
        AlphaFreshFrontier state.carrier.index.alpha)
    (nonempty : state.carrier.index.active.alts ≠ [])
    (target : PostFailurePayloadState)
    (production :
      Produces prog gt
        (.retainedFailure state referenceHead leftSupported rightSupported
          currentSafe leftAliasSafe rightAliasSafe clash exactFresh nonempty)
        (.postFailure target)) :
    ∃ source : RepresentativeActivePayloadState,
      ∃ facts : RetainedFailureSuccessor prog gt source,
        RepresentativePersistentFreeActivePayloadState.ofLegacy state =
            RepresentativePersistentFreeActivePayloadState.ofLegacy source ∧
          target = facts.after := by
  simpa using production.retainedFailure_certificate

/-- Reactivation readiness cannot be laundered into another post-failure
endpoint. -/
theorem retainedActivation_not_postFailure
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (state : PostFailurePayloadState)
    {resolvedResult : Substitution}
    (currentShared : SharedRuntimeAlpha state.index.alpha)
    (below : ConfBelowResolutionCounter state.index.openConf.toConf)
    (live :
      AlphaRuntimeNamesLive state.index.support
        (state.index.copied.body ++ state.index.resource.rest)
        state.index.resource.qterm)
    (resolved : HeadResolution state.index.branch resolvedResult)
    (target : PostFailurePayloadState) :
    ¬ Produces prog gt
        (.retainedActivation state currentShared below live resolved)
        (.postFailure target) := by
  intro production
  cases production

/-- Any ordinary target produced by a retained-activation packet exposes the
same independent head-resolution result named by readiness.  This is a data
equality, not proof irrelevance, and prevents mixing two MGU orientations at
the post-failure seam. -/
theorem retainedActivation_result_exact
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (state : PostFailurePayloadState)
    {resolvedResult : Substitution}
    (currentShared : SharedRuntimeAlpha state.index.alpha)
    (below : ConfBelowResolutionCounter state.index.openConf.toConf)
    (live :
      AlphaRuntimeNamesLive state.index.support
        (state.index.copied.body ++ state.index.resource.rest)
        state.index.resource.qterm)
    (resolved : HeadResolution state.index.branch resolvedResult)
    (target : ProductPhaseState)
    (production :
      Produces prog gt
        (.retainedActivation state currentShared below live resolved)
        (.ordinary target)) :
    ∃ facts : RetainedActivationSuccessor prog gt state,
      target =
          .active
            (RepresentativePersistentFreeActivePayloadState.ofLegacy
              facts.after) ∧
        facts.independentResult = resolvedResult := by
  cases production with
  | retainedActivation state currentShared below live resolved facts
      resultExact =>
      exact ⟨facts, rfl, resultExact⟩

end ResolverStepReady.Produces

namespace ResolverStepReady

/-- Every readiness packet reconstructs an exact successor package from its
producer premises. -/
theorem produces
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : ResolverPhaseState}
    (ready : ResolverStepReady before) :
    ∃ after : ResolverPhaseState, Produces prog gt ready after := by
  cases ready with
  | forward forwardReady =>
      obtain ⟨after, production⟩ :=
        forwardReady.produces (prog := prog) (gt := gt)
      exact ⟨.ordinary after, .forward forwardReady production⟩
  | retainedFailure state referenceHead leftSupported rightSupported
      currentSafe leftAliasSafe rightAliasSafe clash exactFresh nonempty =>
      obtain ⟨facts⟩ :=
        PrologFailureRebasePrefixBridge.RepresentativeActivePayloadState.retainedFailureSuccessor
          (prog := prog) (gt := gt) state referenceHead leftSupported
          rightSupported currentSafe leftAliasSafe rightAliasSafe clash
          exactFresh nonempty
      exact
        ⟨.postFailure facts.after,
          .retainedFailure state referenceHead leftSupported rightSupported
            currentSafe leftAliasSafe rightAliasSafe clash exactFresh nonempty
            facts⟩
  | retainedActivation state currentShared below live resolved =>
      obtain ⟨facts, resultExact⟩ :=
        PrologFailureRebasePrefixBridge.PostFailurePayloadState.retainedActivationSuccessor
          (prog := prog) (gt := gt) state currentShared below live resolved
      exact
        ⟨.ordinary
            (.active
              (RepresentativePersistentFreeActivePayloadState.ofLegacy
                facts.after)),
          .retainedActivation state currentShared below live resolved facts
            resultExact⟩

/-- Readiness produces one shared resolver label carrying both exact
executions and the transition-kind-specific alpha and representative laws.

No global representative-extension conclusion appears: retained failure is
a literal snapshot rebase, not monotone substitution growth. -/
theorem produces_exact_coupled_transition
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {before : ResolverPhaseState}
    (ready : ResolverStepReady before) :
    ∃ after : ResolverPhaseState, ∃ kind : ResolverTransitionKind,
      0 < kind.sourceCost + kind.fineCost ∧
        StepsN kind.sourceCost before.sourceState kind.sourceEvents
          after.sourceState ∧
        DemandDrivenCallStep.StepsN prog gt kind.fineCost before.fineState
          after.fineState ∧
        SessionHighWatersExtend before.session after.session ∧
        before.openConf.persistent.counter ≤
          after.openConf.persistent.counter ∧
        (∀ pair, pair ∈ before.alpha → pair ∈ after.alpha) ∧
        kind.AlphaEvolution before after ∧
        kind.RepresentativeEvolution before after := by
  obtain ⟨after, production⟩ := ready.produces (prog := prog) (gt := gt)
  have coupled := production.certifiedCoupledStep
  obtain ⟨kind, positive, ⟨transition⟩⟩ := coupled
  exact
    ⟨after, kind, positive, transition.sourceSteps, transition.fineSteps,
      transition.sessionHighWaters, transition.executableCounter_mono,
      transition.alphaIncluded, transition.alphaEvolution,
      transition.representativeEvolution⟩

end ResolverStepReady

/-- Readiness-indexed progress over the forward-plus-failure fragment.

This intentionally does not claim readiness after body-answer scheduling or
cut commitment; outgoing scheduled and committed transitions remain separate
open phase-closure obligations. -/
def ResolverProgressPreservesReady (prog : PLeaTTa.Prog)
    (gt : Metta.GroundingTable)
    (invariant : ResolverPhaseState → Prop) : Prop :=
  ∀ {state : ResolverPhaseState}, invariant state →
    ∃ ready : ResolverStepReady state, ∃ next : ResolverPhaseState,
      ready.Produces prog gt next ∧ invariant next

namespace ResolverStepReady

/-- Repeated resolver progress inhabits an exact failure-aware certified
prefix of every requested finite length, retaining literal dependent
midpoints between adjacent constructors. -/
theorem exists_prefix_of_ready
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {invariant : ResolverPhaseState → Prop}
    (progress : ResolverProgressPreservesReady prog gt invariant)
    {before : ResolverPhaseState} (ready : invariant before) :
    ∀ count : Nat,
      ∃ kinds : List ResolverTransitionKind, ∃ after : ResolverPhaseState,
        kinds.length = count ∧
          ∃ _run : ResolverCertifiedPrefix prog gt kinds before after,
            invariant after ∧ Nonempty (ResolverStepReady after) := by
  intro count
  induction count generalizing before with
  | zero =>
      obtain ⟨currentReady, _next, _production, _nextInvariant⟩ :=
        progress ready
      exact
        ⟨[], before, rfl, .nil before, ready, ⟨currentReady⟩⟩
  | succ count inductionHypothesis =>
      obtain ⟨_currentReady, middle, production, middleReady⟩ :=
        progress ready
      have coupled := production.certifiedCoupledStep
      obtain ⟨kind, _positive, ⟨step⟩⟩ := coupled
      obtain ⟨kinds, after, lengthExact, tail, afterInvariant,
          afterReady⟩ :=
        inductionHypothesis middleReady
      exact
        ⟨kind :: kinds, after, by simp [lengthExact],
          .cons step tail, afterInvariant, afterReady⟩

end ResolverStepReady

end PLeaTTa.PrologResolverReadinessBridge
