-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologRootClosedLocalLiveRegression
Purpose: Inhabit rooted local-live answer coupling with a literal retained
  sibling selected by the actual executable pull
Trusted boundary: none
-/
import PLeaTTa.Proofs.PrologRootRejectedPrefixRegression
import PLeaTTa.Proofs.PrologRootClosedLocalLiveBridge
import PLeaTTa.Proofs.PrologScheduledAnswerValueBridge

namespace PLeaTTa.PrologRootClosedLocalLiveRegression

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open DemandDrivenStep
open PrologHeterogeneousPrefixBridge
open PrologOrdinaryStepBridge
open PrologRecursiveCallPayloadBridge
open PrologRootClosedAnswerBridge
open PrologRootClosedLocalLiveBridge
open PrologScheduledAnswerValueBridge
open PrologScheduledPayloadResumeBridge
open PrologStateBridge

/-- The concrete source-ordered root fixture rejects two rigid clauses,
selects a clause whose singleton empty conjunction is compiler-erased, and
retains a second matching clause.  After the one real source administrative
step and body answer, the rooted classifier must choose the retained local
branch: its terminal arm contradicts the literal nonempty owned bank.

This theorem is the anti-vacuity witness for
`RootClosedLocalLiveAnswerRelates`; neither the scheduled carrier nor the
classifier landing is supplied independently of the executable resolver
path.  Its selected clause has a compiler-erased body; rejection-prefix
coverage combined with a selected nonempty compiled body remains separate.

[SPEC metta.pl:251-256, translator.pl:320-321] -/
theorem rejected_prefix_then_root_answer_is_genuinely_local_live
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    exists before : RepresentativeScheduledPayloadState,
      exists ready : RootClosedAnswerReady before,
        exists retainedGoals retainedBinding selectedGoals selectedBinding
            selectedTail count target,
          RootClosedLocalLiveAnswerRelates prog gt before ready selectedGoals
              selectedBinding selectedTail count target /\
            before.carrier.index.openConf.control.alts =
              [.br retainedGoals retainedBinding, .barrier] /\
            selectedGoals = retainedGoals /\
            selectedBinding = retainedBinding /\
            selectedTail = [.barrier] /\
            before.carrier.index.openConf.frames = [] /\
            before.carrier.index.openConf.control.qterm =
              PrologRootRejectedPrefixRegression.queryAtom := by
  obtain
    ⟨_finish, _representative, _nextAlpha, _sourceCanonical, _flattened,
      _installed, active, facts, _finishRemaining, bodyReferences,
      bodyExecutables, _sourceSteps, _fineSteps⟩ :=
    PrologRootRejectedPrefixRegression.two_rigid_rejections_then_selected_retained_exact
      (prog := prog) (gt := gt)
  have referenceConjunction :
      active.carrier.index.bodyReferences = [.conjunction []] := by
    simpa [PrologRootRejectedPrefixRegression.selectedReference] using
      bodyReferences
  have executableEmpty : active.carrier.index.bodyExecutables = [] := by
    exact bodyExecutables.trans
      PrologRootRejectedPrefixRegression.selectedCopied_body_empty
  have administration :
      AdministrativeStepsN 1 active.carrier.index.bodyReferences [] := by
    rw [referenceConjunction]
    exact .succ 0 _ _ _ (.conjunction [] []) (.zero [])
  let normalized :=
    RepresentativeActivePayloadState.afterAdministrative prog gt active
      administration
  have normalizedReferencesEmpty :
      normalized.carrier.index.bodyReferences = [] := by
    rfl
  have normalizedExecutablesEmpty :
      normalized.carrier.index.bodyExecutables = [] := by
    change active.carrier.index.bodyExecutables = []
    exact executableEmpty
  let before :=
    RepresentativeActivePayloadState.afterBodyAnswer prog gt normalized
      normalizedReferencesEmpty normalizedExecutablesEmpty
  have callerEmpty : before.carrier.index.callerReferences = [] := by
    simpa [before, normalized] using facts.callerReferencesEmpty
  have outerEmpty : before.carrier.index.outer = [] := by
    simpa [before, normalized] using facts.outerEmpty
  have baseEmpty : before.carrier.index.baseAlts = [] := by
    simpa [before, normalized] using facts.baseAltsEmpty
  have resourcesEmpty : before.carrier.index.resources = [] := by
    simpa [before, normalized] using facts.resourcesEmpty
  have framesEmpty : before.carrier.index.openConf.frames = [] := by
    simpa [before, normalized] using facts.framesEmpty
  have indexQterm :
      before.carrier.index.qterm =
        PrologRootRejectedPrefixRegression.queryAtom := by
    simpa [before, normalized,
      PrologRootRejectedPrefixRegression.initialOpenConf] using
        facts.qtermPreserved
  have qtermExact :
      before.carrier.index.openConf.control.qterm =
        PrologRootRejectedPrefixRegression.queryAtom :=
    before.carrier.agreement.core.control.ready.2.2.1.trans indexQterm
  have allOuterEmpty :
      forall segment, segment ∈ before.carrier.index.outer ->
        segment.references = [] := by
    rw [outerEmpty]
    simp
  let ready :=
    RepresentativeScheduledPayloadState.rootClosedAnswerReady before
      callerEmpty allOuterEmpty baseEmpty
  obtain ⟨retainedGoals, retainedBinding, retainedAltShape⟩ :=
    PrologRootRejectedPrefixRegression.retainedAlt_is_branch
  have activeAltsShape :
      before.carrier.index.active.alts =
        [.br retainedGoals retainedBinding] := by
    have raw := facts.activeAltsExact.trans
      (congrArg (fun alternative => [alternative]) retainedAltShape)
    simpa [before, normalized] using raw
  have historyResources :
      ready.result.history.resources = [before.carrier.index.active] := by
    rw [ready.result.resourcesExact, currentAnswerHistory_resources,
      resourcesEmpty]
    rfl
  have bankShape :
      before.carrier.index.openConf.control.alts =
        [.br retainedGoals retainedBinding, .barrier] := by
    rw [ready.bankExact, historyResources]
    simp only [PrologProductResourceContextBridge.flattenOwnedAlts_cons,
      PrologProductResourceContextBridge.flattenOwnedAlts_nil]
    rw [activeAltsShape]
    rfl
  have classified :=
    PLeaTTa.PrologRootClosedLocalLiveBridge.RootClosedAnswerReady.classifyPullAndRelate
      (prog := prog) (gt := gt) ready
  rcases classified with relates | falls
  · rcases relates with
      ⟨selectedGoals, selectedBinding, selectedTail, count, target, exact⟩
    have selectedPull :
        PLeaTTa.pullAux before.carrier.index.openConf.control.alts =
          some ((selectedGoals, selectedBinding), selectedTail) := by
      rw [ready.bankExact]
      exact exact.landing.pullAux_exact
    have retainedPull :
        PLeaTTa.pullAux before.carrier.index.openConf.control.alts =
          some ((retainedGoals, retainedBinding), [.barrier]) := by
      rw [bankShape]
      rfl
    rw [retainedPull] at selectedPull
    simp only [Option.some.injEq, Prod.mk.injEq] at selectedPull
    refine
      ⟨before, ready, retainedGoals, retainedBinding, selectedGoals,
        selectedBinding, selectedTail, count, target, exact, bankShape,
        selectedPull.1.1.symm, selectedPull.1.2.symm,
        selectedPull.2.symm, framesEmpty, qtermExact⟩
  · have impossible := falls.pullAux_eq
    change
      PLeaTTa.pullAux
          (PrologProductResourceContextBridge.flattenOwnedAlts
            ready.result.history.resources []) =
        PLeaTTa.pullAux [] at impossible
    rw [historyResources] at impossible
    simp only [PrologProductResourceContextBridge.flattenOwnedAlts_cons,
      PrologProductResourceContextBridge.flattenOwnedAlts_nil] at impossible
    rw [activeAltsShape] at impossible
    simp [PLeaTTa.pullAux] at impossible

/-- The same concrete source-ordered fixture smoke-checks the public-answer
plumbing: source integer zero and executable integer zero are runtime-alpha
equivalent, and the real root answer step appends that value exactly once to
the public accumulator.

Because both query spellings are ground, this theorem does not discriminate
cumulative substitution correspondence.  The separate non-ground witness is
load-bearing for that content.  Producing arbitrary query spellings from
source/compiler input remains a global composition obligation. -/
theorem rejected_prefix_then_root_answer_ground_public_append_smoke
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable} :
    exists before : RepresentativeScheduledPayloadState,
      exists ready : RootClosedAnswerReady before,
        exists retainedGoals retainedBinding selectedGoals selectedBinding
            selectedTail count target,
          RootClosedLocalLivePublicAnswerRelates
              PrologRootRejectedPrefixRegression.queryTerm prog gt before
              ready selectedGoals selectedBinding selectedTail count target /\
            before.carrier.index.openConf.control.alts =
              [.br retainedGoals retainedBinding, .barrier] /\
            selectedGoals = retainedGoals /\
            selectedBinding = retainedBinding /\
            selectedTail = [.barrier] /\
            before.carrier.index.current.applyTerm
                PrologRootRejectedPrefixRegression.queryTerm =
              .integer 0 /\
            PLeaTTa.subst before.carrier.index.runtime
                before.carrier.index.openConf.control.qterm =
              PrologRootRejectedPrefixRegression.queryAtom /\
            publicAnswers
                (privateAnswerTarget before.carrier.index.openConf
                  before.carrier.index.runtime) =
              publicAnswers before.carrier.index.openConf ++
                [PrologRootRejectedPrefixRegression.queryAtom] := by
  obtain
    ⟨before, ready, retainedGoals, retainedBinding, selectedGoals,
      selectedBinding, selectedTail, count, target, control, bankShape,
      selectedGoalsExact, selectedBindingExact, selectedTailExact,
      framesEmpty, qtermExact⟩ :=
    rejected_prefix_then_root_answer_is_genuinely_local_live
      (prog := prog) (gt := gt)
  have queryAgreement :
      AlphaTermAgrees before.carrier.index.alpha
        PrologRootRejectedPrefixRegression.queryTerm
        before.carrier.index.openConf.control.qterm := by
    rw [qtermExact]
    exact AlphaTermAgrees.integer 0
  have querySupported :
      AlphaTermsSupported before.carrier.index.alpha
        before.carrier.index.support
        [PrologRootRejectedPrefixRegression.queryTerm] := by
    intro term member
    simp only [List.mem_singleton] at member
    subst term
    simp [PrologRootRejectedPrefixRegression.queryTerm, AlphaTreeSupported,
      Term.denote, PrologMguOpenAgreement.TreeVariablesSatisfy,
      PrologMguOpenAgreement.TreesVariablesSatisfy]
  have publicRelation :=
    PLeaTTa.PrologScheduledAnswerValueBridge.RootClosedLocalLiveAnswerRelates.withPublicAnswer
      control queryAgreement querySupported framesEmpty
  have sourceValue :
      before.carrier.index.current.applyTerm
          PrologRootRejectedPrefixRegression.queryTerm = .integer 0 := by
    simp [PrologRootRejectedPrefixRegression.queryTerm]
  have runtimeValue :
      PLeaTTa.subst before.carrier.index.runtime
          before.carrier.index.openConf.control.qterm =
        PrologRootRejectedPrefixRegression.queryAtom := by
    rw [qtermExact]
    simp [PrologRootRejectedPrefixRegression.queryAtom]
  have publicValue :
      publicAnswers
          (privateAnswerTarget before.carrier.index.openConf
            before.carrier.index.runtime) =
        publicAnswers before.carrier.index.openConf ++
          [PrologRootRejectedPrefixRegression.queryAtom] := by
    rw [publicRelation.rootAnswer.publicAnswer, runtimeValue]
  exact
    ⟨before, ready, retainedGoals, retainedBinding, selectedGoals,
      selectedBinding, selectedTail, count, target, publicRelation, bankShape,
      selectedGoalsExact, selectedBindingExact, selectedTailExact,
      sourceValue, runtimeValue, publicValue⟩

end PLeaTTa.PrologRootClosedLocalLiveRegression
