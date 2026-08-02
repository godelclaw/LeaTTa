-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologUnboundPublicAnswerRegression
Purpose: Exercise exact source-value/public-answer coupling on the reachable
  non-ground p(Z) :- q(Z) run
Trusted boundary: none
Main exports: ReachableUnboundPublicAnswerWitness,
  reachable_unbound_p_q_public_answer
-/
import PLeaTTa.Proofs.PrologScheduledAnswerValueBridge
import PLeaTTa.Proofs.PrologUnboundNestedCallRegression

namespace PLeaTTa.PrologUnboundPublicAnswerRegression

open Metta (Atom)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open DemandDrivenStep
open PrologAnswerValueBridge
open PrologFindallCopyBridge
open PrologHeterogeneousPrefixBridge
open PrologNestedCallReadyBridge
open PrologRecursiveCallPayloadBridge
open PrologRootClosedAnswerBridge
open PrologScheduledAnswerValueBridge
open PrologStateBridge
open PrologUnboundNestedCallRegression

/-- One literal reachable non-ground answer, coupled from the independent
source substitution to the exact executable public accumulator.

The active endpoint is reached by the real `p(Z) :- q(Z)` source and fine
prefixes.  The body-completion proofs are fields of the witness, so the
scheduled state, root-closure certificate, and public-answer relation cannot
refer to shape-compatible but different endpoints.  `sourceValueExact` and
`sourceValueNontrivial` make the fixture discriminate ordered substitution
composition rather than merely transport a ground constant. -/
structure ReachableUnboundPublicAnswerWitness
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (active : RepresentativeActivePayloadState)
    (bodyReferencesEmpty : active.carrier.index.bodyReferences = [])
    (bodyExecutablesEmpty : active.carrier.index.bodyExecutables = [])
    (ready :
      RootClosedAnswerReady
        (RepresentativeActivePayloadState.afterBodyAnswer prog gt active
          bodyReferencesEmpty bodyExecutablesEmpty)) : Prop where
  sourcePrefix :
    StepsN 4
      (.running initialSession
        (.task (0 : CutScopeId) [.call "p" [queryTerm]] []))
      [.opened (requestFor "p" [queryTerm] []),
        .opened
          (requestFor "q" [(.variable (.generated 0) : Term)]
            pSourceExtension)]
      active.carrier.sourceState
  finePrefix :
    DemandDrivenCallStep.StepsN prog gt 6
      (.ready initialOpenConf) active.carrier.fineState
  publicRelation :
    RootClosedPublicAnswerRelates queryTerm prog gt
      (RepresentativeActivePayloadState.afterBodyAnswer prog gt active
        bodyReferencesEmpty bodyExecutablesEmpty)
      ready
  sourceValueExact :
    active.carrier.index.current.applyTerm queryTerm =
      .variable (.generated 1)
  sourceValueNontrivial :
    active.carrier.index.current.applyTerm queryTerm ≠ queryTerm
  runtimeValueExact :
    PLeaTTa.subst
        (RepresentativeActivePayloadState.afterBodyAnswer prog gt active
          bodyReferencesEmpty bodyExecutablesEmpty).carrier.index.runtime
        (RepresentativeActivePayloadState.afterBodyAnswer prog gt active
          bodyReferencesEmpty bodyExecutablesEmpty).carrier.index.openConf.control.qterm =
      .var ("x" ++ PLeaTTa.resolutionCompactSuffix 1)
  runtimeValueNontrivial :
    PLeaTTa.subst
        (RepresentativeActivePayloadState.afterBodyAnswer prog gt active
          bodyReferencesEmpty bodyExecutablesEmpty).carrier.index.runtime
        (RepresentativeActivePayloadState.afterBodyAnswer prog gt active
          bodyReferencesEmpty bodyExecutablesEmpty).carrier.index.openConf.control.qterm ≠
      (RepresentativeActivePayloadState.afterBodyAnswer prog gt active
        bodyReferencesEmpty bodyExecutablesEmpty).carrier.index.openConf.control.qterm
  runtimeValue :
    RuntimeTermAgrees (.variable (.generated 1))
      (PLeaTTa.subst
        (RepresentativeActivePayloadState.afterBodyAnswer prog gt active
          bodyReferencesEmpty bodyExecutablesEmpty).carrier.index.runtime
        (RepresentativeActivePayloadState.afterBodyAnswer prog gt active
          bodyReferencesEmpty bodyExecutablesEmpty).carrier.index.openConf.control.qterm)
  publicAppend :
    publicAnswers
        (privateAnswerTarget
          (RepresentativeActivePayloadState.afterBodyAnswer prog gt active
            bodyReferencesEmpty bodyExecutablesEmpty).carrier.index.openConf
          (RepresentativeActivePayloadState.afterBodyAnswer prog gt active
            bodyReferencesEmpty bodyExecutablesEmpty).carrier.index.runtime) =
      publicAnswers
          (RepresentativeActivePayloadState.afterBodyAnswer prog gt active
            bodyReferencesEmpty bodyExecutablesEmpty).carrier.index.openConf ++
        [PLeaTTa.subst
          (RepresentativeActivePayloadState.afterBodyAnswer prog gt active
            bodyReferencesEmpty bodyExecutablesEmpty).carrier.index.runtime
          (RepresentativeActivePayloadState.afterBodyAnswer prog gt active
            bodyReferencesEmpty bodyExecutablesEmpty).carrier.index.openConf.control.qterm]

/-- The concrete non-ground `p(Z) :- q(Z)` execution inhabits the complete
root-public answer relation.

This theorem composes the exact four-source/six-fine-step call prefix, body
completion, root closure, source substitution observation, runtime query
materialization, and public append.  The source value is generated identity
one rather than the original source variable, so the value half is not the
ground-query tautology exercised by the smaller smoke regression. -/
theorem reachable_unbound_p_q_public_answer
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    ∃ active : RepresentativeActivePayloadState,
      ∃ bodyReferencesEmpty : active.carrier.index.bodyReferences = [],
        ∃ bodyExecutablesEmpty : active.carrier.index.bodyExecutables = [],
          ∃ ready :
            RootClosedAnswerReady
              (RepresentativeActivePayloadState.afterBodyAnswer prog gt active
                bodyReferencesEmpty bodyExecutablesEmpty),
            ReachableUnboundPublicAnswerWitness prog gt active
              bodyReferencesEmpty bodyExecutablesEmpty ready := by
  obtain ⟨_before, active, facts⟩ :=
    reachable_unbound_p_q_exact_prefix (prog := prog) (gt := gt)
  obtain ⟨_rootSource, facts⟩ := facts
  obtain ⟨_rootFine, facts⟩ := facts
  obtain ⟨_beforeNextFresh, facts⟩ := facts
  obtain ⟨_beforeFrontier, facts⟩ := facts
  obtain ⟨sourcePrefix, facts⟩ := facts
  obtain ⟨finePrefix, facts⟩ := facts
  obtain ⟨_currentExact, facts⟩ := facts
  obtain ⟨_afterNextFresh, facts⟩ := facts
  obtain ⟨_afterFrontier, facts⟩ := facts
  obtain ⟨_alphaExtension, facts⟩ := facts
  obtain ⟨_representativeExtension, facts⟩ := facts
  have nestedPush := facts.1
  have facts := facts.2
  obtain ⟨bodyReferencesEmpty, facts⟩ := facts
  obtain ⟨bodyExecutablesEmpty, facts⟩ := facts
  obtain ⟨callerReferencesEmpty, facts⟩ := facts
  obtain ⟨outerReferencesEmpty, facts⟩ := facts
  obtain ⟨baseAltsEmpty, facts⟩ := facts
  obtain ⟨framesEmpty, facts⟩ := facts
  obtain ⟨_qtermExact, facts⟩ := facts
  obtain ⟨openQtermExact, facts⟩ := facts
  obtain ⟨queryAgreement, facts⟩ := facts
  obtain ⟨querySupported, facts⟩ := facts
  obtain ⟨sourceValueExact, facts⟩ := facts
  obtain ⟨sourceValueNontrivial, facts⟩ := facts
  obtain ⟨runtimeValueExact, runtimeValueNontrivial⟩ := facts
  let scheduled :=
    RepresentativeActivePayloadState.afterBodyAnswer prog gt active
      bodyReferencesEmpty bodyExecutablesEmpty
  have scheduledCallerReferencesEmpty :
      scheduled.carrier.index.callerReferences = [] := by
    simpa [scheduled] using callerReferencesEmpty
  have scheduledOuterReferencesEmpty :
      ∀ segment, segment ∈ scheduled.carrier.index.outer →
        segment.references = [] := by
    simpa [scheduled] using outerReferencesEmpty
  have scheduledBaseAltsEmpty :
      scheduled.carrier.index.baseAlts = [] := by
    simpa [scheduled] using baseAltsEmpty
  let ready : RootClosedAnswerReady scheduled :=
    PLeaTTa.PrologRootClosedAnswerBridge.RepresentativeScheduledPayloadState.rootClosedAnswerReady
      scheduled scheduledCallerReferencesEmpty scheduledOuterReferencesEmpty
        scheduledBaseAltsEmpty
  have scheduledQueryAgreement :
      AlphaTermAgrees scheduled.carrier.index.alpha queryTerm
        scheduled.carrier.index.openConf.control.qterm := by
    change
      AlphaTermAgrees active.carrier.index.alpha queryTerm
        active.carrier.index.openConf.control.qterm
    rw [openQtermExact]
    exact queryAgreement
  have scheduledQuerySupported :
      AlphaTermsSupported scheduled.carrier.index.alpha
        scheduled.carrier.index.support [queryTerm] := by
    change
      AlphaTermsSupported active.carrier.index.alpha
        active.carrier.index.support [queryTerm]
    exact querySupported
  have scheduledFramesEmpty :
      scheduled.carrier.index.openConf.frames = [] := by
    simpa [scheduled] using framesEmpty
  have publicOwner :
      PublicAnswerOwner scheduled.carrier.index.openConf.frames := by
    rw [scheduledFramesEmpty]
    exact publicAnswerOwner_nil
  have publicRelation :
      RootClosedPublicAnswerRelates queryTerm prog gt scheduled ready :=
    PLeaTTa.PrologScheduledAnswerValueBridge.RootClosedAnswerReady.withPublicAnswer
      ready scheduledQueryAgreement scheduledQuerySupported publicOwner
  have scheduledSourceValueExact :
      scheduled.carrier.index.current.applyTerm queryTerm =
        .variable (.generated 1) := by
    simpa [scheduled] using sourceValueExact
  have scheduledRuntimeValueExact :
      PLeaTTa.subst scheduled.carrier.index.runtime
          scheduled.carrier.index.openConf.control.qterm =
        .var ("x" ++ PLeaTTa.resolutionCompactSuffix 1) := by
    simpa [scheduled] using runtimeValueExact
  have scheduledRuntimeValueNontrivial :
      PLeaTTa.subst scheduled.carrier.index.runtime
          scheduled.carrier.index.openConf.control.qterm ≠
        scheduled.carrier.index.openConf.control.qterm := by
    simpa [scheduled] using runtimeValueNontrivial
  have runtimeValue := publicRelation.valueAgreement
  rw [scheduledSourceValueExact] at runtimeValue
  refine ⟨active, bodyReferencesEmpty, bodyExecutablesEmpty, ready, ?_⟩
  exact
    { sourcePrefix := sourcePrefix
      finePrefix := finePrefix
      publicRelation := publicRelation
      sourceValueExact := sourceValueExact
      sourceValueNontrivial := sourceValueNontrivial
      runtimeValueExact := scheduledRuntimeValueExact
      runtimeValueNontrivial := scheduledRuntimeValueNontrivial
      runtimeValue := runtimeValue
      publicAppend := publicRelation.publicAnswer }

end PLeaTTa.PrologUnboundPublicAnswerRegression
