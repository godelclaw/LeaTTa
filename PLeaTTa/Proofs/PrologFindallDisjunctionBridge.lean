-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologFindallDisjunctionBridge
Purpose: Compose real contextual findall entry with exact literal-disjunction
  scheduling and selected-branch unification
Trusted boundary: none
Main exports: ContextualLiteralFindallEntryRelates,
  contextual_literal_findall_entry_correspondence,
  contextual_literal_findall_selected_unify_three_steps
-/
import PLeaTTa.Proofs.PrologActiveControlContextBridge
import PLeaTTa.Proofs.PrologDisjunctionStepBridge

namespace PLeaTTa.PrologFindallDisjunctionBridge

open Metta (Atom Subst GroundingTable)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PrologActiveControlContextBridge
open PrologDisjunctionStepBridge
open PrologFindallEntryBridge
open PrologFindallFrameZipperBridge
open PrologGoalAlpha
open PrologOrdinaryStepBridge
open PrologStateBridge
open DemandDrivenStep

/-!
# A reachable literal disjunction inside `findall/3`

The disjunction bridge starts at an exact ready task.  This module proves that
such a task is reached by one real contextual source `taskFindall` transition
and one real fine `findallEnter` transition, under an explicit compiler
payload certificate.  The source active path is represented only by
`ActiveControlContext`; executable alternatives remain discontinuous across
the collection frame and are never stored in that context.
-/

/-- Compiler payload needed after the control-only `findall/3` entry.

The relation is deliberately explicit: the control-entry theorem alone says
nothing about terms, substitutions, or generated goals. -/
structure LiteralFindallGeneratorPayloadAgrees
    (alpha support : List (LogicVar × String)) (barrier : Nat)
    (canonical : TreeSubstitution) (referenceBase current : Substitution)
    (referenceAmbOutput : Term)
    (referenceBranches : List PeTTaSpec.PrologCore.Goal)
    (runtime : Metta.Subst) (executableAmbOutput : Metta.Atom)
    (executableBranches : List (Metta.Atom × List PLeaTTa.Goal))
    (executableTail : List PLeaTTa.Goal) : Prop where
  data :
    TaskDataAgrees alpha support canonical referenceBase current runtime
  branches :
    AlphaLiteralAmbBranchesAgree alpha referenceAmbOutput executableAmbOutput
      referenceBranches executableBranches
  tail : NormalizedAlphaGoalsAgree alpha barrier [] executableTail
  nonempty : referenceBranches ≠ []

/-- Source state immediately before the active `findall/3` entry. -/
def sourceLiteralFindallBefore
    (context : ActiveControlContext) (callerScope : CutScopeId)
    (template : Term) (branches : List PeTTaSpec.PrologCore.Goal)
    (result : Term) (rest : List PeTTaSpec.PrologCore.Goal)
    (bindings : Substitution) : Search :=
  ActiveControlContext.plug context
    (.task callerScope (.findall template (.disjunction branches) result :: rest)
      bindings)

/-- The new collection frame prepended to the old active source context. -/
def enteredLiteralFindallContext
    (context : ActiveControlContext) (session : Session)
    (callerScope : CutScopeId) (template result : Term)
    (rest : List PeTTaSpec.PrologCore.Goal) (bindings : Substitution) :
    ActiveControlContext :=
  .collection (openFindall session).collectionScope callerScope
      (openFindall session).cutScope template result bindings rest [] ::
    context

/-- Source generator focus immediately after entry. -/
def sourceLiteralFindallFocus
    (session : Session) (branches : List PeTTaSpec.PrologCore.Goal)
    (bindings : Substitution) : Search :=
  .task (openFindall session).cutScope [.disjunction branches] bindings

/-- Fine state immediately after `findallEnter`. -/
def executableLiteralFindallEntered
    (before : OpenConf) (template : Metta.Atom)
    (branches : List (Metta.Atom × List PLeaTTa.Goal))
    (ambOutput result : Metta.Atom) (tail rest : List PLeaTTa.Goal)
    (binding : Metta.Subst) : OpenConf :=
  enterFindall before template (.amb branches ambOutput :: tail) result rest
    binding

@[simp] theorem activeCollectionCells_sourceLiteralFindallFocus
    (session : Session) (branches : List PeTTaSpec.PrologCore.Goal)
    (bindings : Substitution) :
    activeCollectionCells
        (sourceLiteralFindallFocus session branches bindings) =
      some [] := by
  rfl

/-- Disjunction scheduling leaves the focus itself collection-free.  This is
the premise that lets the occurrence zipper survive the first generator
step; it is proved from the actual recursive `Search.disjoin`. -/
@[simp] theorem activeCollectionCells_disjoin
    (scope : CutScopeId) (branches tail : List PeTTaSpec.PrologCore.Goal)
    (bindings : Substitution) :
    activeCollectionCells (Search.disjoin scope branches tail bindings) =
      some [] := by
  cases branches with
  | nil => rfl
  | cons branch rest =>
      cases rest <;> rfl

/-- Exact contextual entry packet.  `control` contains both real entry steps
and the one-cell/one-frame occurrence update.  `ready` is the independently
typed compiler payload at the active generator focus. -/
structure ContextualLiteralFindallEntryRelates
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String)) (barrier : Nat)
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (prog : PLeaTTa.Prog) (gt : Metta.GroundingTable)
    (context : ActiveControlContext) (session : Session)
    (callerScope : CutScopeId)
    (referenceTemplate referenceAmbOutput referenceResult : Term)
    (referenceBranches : List PeTTaSpec.PrologCore.Goal)
    (referenceRest : List PeTTaSpec.PrologCore.Goal)
    (referenceBindings : Substitution)
    (executableTemplate executableAmbOutput executableResult : Metta.Atom)
    (executableBranches : List (Metta.Atom × List PLeaTTa.Goal))
    (executableTail executableRest : List PLeaTTa.Goal)
    (executableBinding : Metta.Subst) (before : OpenConf) : Prop where
  control :
    ContextualFindallEntryRelates freshFrontier prog gt session
      (sourceLiteralFindallBefore context callerScope referenceTemplate
        referenceBranches referenceResult referenceRest referenceBindings)
      before
      (ActiveControlContext.enterFindallResult context session callerScope
        referenceTemplate (.disjunction referenceBranches) referenceResult
        referenceRest referenceBindings)
      executableTemplate (.amb executableBranches executableAmbOutput ::
        executableTail) executableResult executableRest executableBinding
      (executableLiteralFindallEntered before executableTemplate
        executableBranches executableAmbOutput executableResult executableTail
        executableRest executableBinding)
  sourceTarget :
    (ActiveControlContext.enterFindallResult context session callerScope
      referenceTemplate (.disjunction referenceBranches) referenceResult
      referenceRest referenceBindings).afterSearch =
      ActiveControlContext.plug
        (enteredLiteralFindallContext context session callerScope
          referenceTemplate referenceResult referenceRest referenceBindings)
        (sourceLiteralFindallFocus session referenceBranches referenceBindings)
  ready :
    ReadyLiteralDisjunctionRelates freshFrontier alpha support barrier canonical
      referenceBase (openFindall session).session referenceBindings
      referenceAmbOutput referenceBranches [] executableBinding
      executableAmbOutput executableBranches executableTail
      (executableLiteralFindallEntered before executableTemplate
        executableBranches executableAmbOutput executableResult executableTail
        executableRest executableBinding)

/-- One real contextual source entry plus one real fine frame push produces
the exact ready literal-disjunction focus.  All term/goal payload facts are
supplied by `payload`, never inferred from the control-only entry theorem.

[SPEC translator.pl:112-116] -/
theorem contextual_literal_findall_entry_correspondence
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {context : ActiveControlContext} {session : Session}
    {callerScope : CutScopeId}
    {referenceTemplate referenceAmbOutput referenceResult : Term}
    {referenceBranches : List PeTTaSpec.PrologCore.Goal}
    {referenceRest : List PeTTaSpec.PrologCore.Goal}
    {referenceBindings : Substitution}
    {executableTemplate executableAmbOutput executableResult : Metta.Atom}
    {executableBranches : List (Metta.Atom × List PLeaTTa.Goal)}
    {executableTail executableRest : List PLeaTTa.Goal}
    {executableBinding : Metta.Subst} {before : OpenConf}
    (beforeAgreement :
      SessionRelatesOpenConf freshFrontier ExactControlFrontiers session before)
    (beforeOccurrences :
      CollectionOccurrenceAgrees
        (sourceLiteralFindallBefore context callerScope referenceTemplate
          referenceBranches referenceResult referenceRest referenceBindings)
        before.frames)
    (head :
      before.toConf.cur =
        some
          (PLeaTTa.Goal.findall executableTemplate
              (.amb executableBranches executableAmbOutput :: executableTail)
              executableResult :: executableRest,
            executableBinding))
    (payload :
      LiteralFindallGeneratorPayloadAgrees alpha support barrier canonical
        referenceBase referenceBindings referenceAmbOutput referenceBranches
        executableBinding executableAmbOutput executableBranches
        executableTail) :
    ContextualLiteralFindallEntryRelates freshFrontier alpha support barrier
      canonical referenceBase prog gt context session callerScope
      referenceTemplate referenceAmbOutput referenceResult referenceBranches
      referenceRest referenceBindings executableTemplate executableAmbOutput
      executableResult executableBranches executableTail executableRest
      executableBinding before := by
  let entered :=
    ActiveControlContext.enterFindallResult context session callerScope
      referenceTemplate (.disjunction referenceBranches) referenceResult
      referenceRest referenceBindings
  let after :=
    executableLiteralFindallEntered before executableTemplate
      executableBranches executableAmbOutput executableResult executableTail
      executableRest executableBinding
  have control :
      ContextualFindallEntryRelates freshFrontier prog gt session
        (sourceLiteralFindallBefore context callerScope referenceTemplate
          referenceBranches referenceResult referenceRest referenceBindings)
        before entered executableTemplate
        (.amb executableBranches executableAmbOutput :: executableTail)
        executableResult executableRest executableBinding after :=
    enterActiveFindall_findallEnter_occurrence_prepend entered beforeAgreement
      beforeOccurrences executableTemplate
      (.amb executableBranches executableAmbOutput :: executableTail)
      executableResult executableRest executableBinding head
  have ready :
      ReadyLiteralDisjunctionRelates freshFrontier alpha support barrier
        canonical referenceBase (openFindall session).session referenceBindings
        referenceAmbOutput referenceBranches [] executableBinding
        executableAmbOutput executableBranches executableTail after := by
    exact
      { persistent := control.afterAgreement.persistent
        current_exact := rfl
        data := payload.data
        branches := payload.branches
        tail := payload.tail
        nonempty := payload.nonempty }
  exact
    { control := control
      sourceTarget :=
        ActiveControlContext.enterFindallResult_afterSearch context session
          callerScope referenceTemplate (.disjunction referenceBranches)
          referenceResult referenceRest referenceBindings
      ready := ready }

/-! ## Exact reachable three-step prefix -/

/-- Whole source state immediately after the contextual entry. -/
def sourceLiteralFindallEntered
    (context : ActiveControlContext) (session : Session)
    (callerScope : CutScopeId) (template result : Term)
    (branches : List PeTTaSpec.PrologCore.Goal)
    (rest : List PeTTaSpec.PrologCore.Goal) (bindings : Substitution) : Search :=
  ActiveControlContext.plug
    (enteredLiteralFindallContext context session callerScope template result
      rest bindings)
    (sourceLiteralFindallFocus session branches bindings)

/-- Whole source state after the generator's literal disjunction is exposed. -/
def sourceLiteralFindallBranched
    (context : ActiveControlContext) (session : Session)
    (callerScope : CutScopeId) (template result : Term)
    (branches : List PeTTaSpec.PrologCore.Goal)
    (rest : List PeTTaSpec.PrologCore.Goal) (bindings : Substitution) : Search :=
  ActiveControlContext.plug
    (enteredLiteralFindallContext context session callerScope template result
      rest bindings)
    (Search.disjoin (openFindall session).cutScope branches [] bindings)

/-- Whole source state after the selected literal branch unifies. -/
def sourceLiteralFindallAfterSelectedUnify
    (context : ActiveControlContext) (session : Session)
    (callerScope : CutScopeId) (template result : Term)
    (remainingBranches : List PeTTaSpec.PrologCore.Goal)
    (rest : List PeTTaSpec.PrologCore.Goal)
    (beforeBindings afterBindings : Substitution) : Search :=
  ActiveControlContext.plug
    (enteredLiteralFindallContext context session callerScope template result
      rest beforeBindings)
    (selectedUnifySourceSuccessor (openFindall session).cutScope
      remainingBranches [] beforeBindings afterBindings)

/-- Selected-unification control remains collection-free at the focus, both
with and without residual siblings. -/
@[simp] theorem activeCollectionCells_selectedUnifySourceSuccessor
    (scope : CutScopeId)
    (remainingBranches tail : List PeTTaSpec.PrologCore.Goal)
    (beforeBindings afterBindings : Substitution) :
    activeCollectionCells
        (selectedUnifySourceSuccessor scope remainingBranches tail
          beforeBindings afterBindings) =
      some [] := by
  cases remainingBranches <;> rfl

/-- The exact reachable prefix for a successful first literal branch inside
an active `findall/3` generator.

Step 1 enters the collector and pushes its fine frame.  Step 2 exposes and
selects the leftmost amb branch.  Step 3 performs its equality.  The source
steps are lifted through the same typed active context; the executable steps
retain the literal frame stack.  Collector occurrences agree after all three
steps, while the MGU result is stated up to the proved cumulative variant
relation rather than raw association-list equality.

[SPEC translator.pl:112-116; metta.pl:251-256] -/
theorem contextual_literal_findall_selected_unify_three_steps
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {context : ActiveControlContext} {session : Session}
    {callerScope : CutScopeId}
    {referenceTemplate referenceAmbOutput referenceResult referenceValue : Term}
    {remainingReferences : List PeTTaSpec.PrologCore.Goal}
    {referenceRest : List PeTTaSpec.PrologCore.Goal}
    {referenceBindings resolvedBindings : Substitution}
    {executableTemplate executableAmbOutput executableResult executableValue :
      Metta.Atom}
    {remainingExecutables : List (Metta.Atom × List PLeaTTa.Goal)}
    {executableTail executableRest : List PLeaTTa.Goal}
    {executableBinding : Metta.Subst} {before : OpenConf}
    (entry :
      ContextualLiteralFindallEntryRelates freshFrontier alpha support barrier
        canonical referenceBase prog gt context session callerScope
        referenceTemplate referenceAmbOutput referenceResult
        (.unify referenceValue referenceAmbOutput :: remainingReferences)
        referenceRest referenceBindings executableTemplate executableAmbOutput
        executableResult ((executableValue, []) :: remainingExecutables)
        executableTail executableRest executableBinding before)
    (valueSupported :
      AlphaTreeSupported alpha support (Term.denote referenceValue))
    (outputSupported :
      AlphaTreeSupported alpha support (Term.denote referenceAmbOutput))
    (supportIncluded : ∀ pair, pair ∈ support → pair ∈ alpha)
    (runtimeAvoids :
      PrologMguComposition.AlphaRuntimeNamesAvoid support executableBinding)
    (live :
      PrologMguBridge.AlphaRuntimeNamesLive support executableTail
        (executableLiteralFindallEntered before executableTemplate
          ((executableValue, []) :: remainingExecutables) executableAmbOutput
          executableResult executableTail executableRest
          executableBinding).control.qterm)
    (resolved :
      UnifyResolution referenceBindings referenceValue referenceAmbOutput
        resolvedBindings) :
    ∃ sourceExtension : TreeSubstitution,
      ∃ installed : Metta.Subst,
        let sourceBefore :=
          sourceLiteralFindallBefore context callerScope referenceTemplate
            (.unify referenceValue referenceAmbOutput :: remainingReferences)
            referenceResult referenceRest referenceBindings
        let sourceEntered :=
          sourceLiteralFindallEntered context session callerScope
            referenceTemplate referenceResult
            (.unify referenceValue referenceAmbOutput :: remainingReferences)
            referenceRest referenceBindings
        let sourceBranched :=
          sourceLiteralFindallBranched context session callerScope
            referenceTemplate referenceResult
            (.unify referenceValue referenceAmbOutput :: remainingReferences)
            referenceRest referenceBindings
        let sourceAfter :=
          sourceLiteralFindallAfterSelectedUnify context session callerScope
            referenceTemplate referenceResult remainingReferences referenceRest
            referenceBindings resolvedBindings
        let fineEntered :=
          executableLiteralFindallEntered before executableTemplate
            ((executableValue, []) :: remainingExecutables) executableAmbOutput
            executableResult executableTail executableRest executableBinding
        let fineSelected :=
          literalAmbPulledSuccessor fineEntered executableAmbOutput
            executableValue remainingExecutables executableTail
            executableBinding
        let fineAfter :=
          PrologOrdinaryStepBridge.unifySuccessor fineSelected executableTail
            installed
        PLeaTTa.unifyB executableBinding executableAmbOutput executableValue =
            some installed ∧
          RawStep session sourceBefore [] .none (openFindall session).session
            (.running sourceEntered) ∧
          DemandDrivenStep.Step prog gt before fineEntered ∧
          RawStep (openFindall session).session sourceEntered [] .none
            (openFindall session).session (.running sourceBranched) ∧
          DemandDrivenCallStep.Step prog gt (.ready fineEntered)
            (.ready fineSelected) ∧
          RawStep (openFindall session).session sourceBranched [] .none
            (openFindall session).session (.running sourceAfter) ∧
          DemandDrivenCallStep.Step prog gt (.ready fineSelected)
            (.ready fineAfter) ∧
          CollectionOccurrenceAgrees sourceEntered fineEntered.frames ∧
          CollectionOccurrenceAgrees sourceBranched fineSelected.frames ∧
          CollectionOccurrenceAgrees sourceAfter fineAfter.frames ∧
          TaskPayloadAgrees alpha support barrier
            (sourceExtension ++ canonical) referenceBase resolvedBindings
            (PLeaTTa.trimFor executableTail fineEntered.control.qterm installed)
            [] executableTail ∧
          PrologAnswerResourceBridge.OrderedTaskChoicePayloadsAgree
            alpha support barrier canonical
            referenceBase referenceBindings executableBinding []
            remainingReferences
            (remainingExecutables.map fun branch =>
              PLeaTTa.ambBranchGoals executableAmbOutput branch ++
                executableTail) ∧
          fineAfter.control.alts =
            remainingExecutables.map (fun branch =>
              PLeaTTa.Alt.br
                (PLeaTTa.ambBranchGoals executableAmbOutput branch ++
                  executableTail)
                executableBinding) ++ fineEntered.control.alts ∧
          SessionRelatesPersistent freshFrontier
            (openFindall session).session fineAfter.persistent ∧
          fineAfter.frames = fineEntered.frames ∧
          fineAfter.scopes = fineEntered.scopes := by
  obtain
    ⟨sourceExtension, installed, installedExact, sourceSchedule, fineSchedule,
      sourceUnify, fineUnify, payloadAfter, residualPayloads, altsAfter,
      persistentAfter, framesAfter, scopesAfter⟩ :=
    literal_selected_unify_two_step_correspondence entry.ready valueSupported
      outputSupported supportIncluded runtimeAvoids live resolved
  let enteredContext :=
    enteredLiteralFindallContext context session callerScope referenceTemplate
      referenceResult referenceRest referenceBindings
  have sourceEntry :
      RawStep session
        (sourceLiteralFindallBefore context callerScope referenceTemplate
          (.unify referenceValue referenceAmbOutput :: remainingReferences)
          referenceResult referenceRest referenceBindings)
        [] .none (openFindall session).session
        (.running
          (sourceLiteralFindallEntered context session callerScope
            referenceTemplate referenceResult
            (.unify referenceValue referenceAmbOutput :: remainingReferences)
            referenceRest referenceBindings)) := by
    have raw :=
      (ActiveControlContext.enterFindallResult context session callerScope
        referenceTemplate
        (.disjunction
          (.unify referenceValue referenceAmbOutput :: remainingReferences))
        referenceResult referenceRest referenceBindings).sourceStep
    rw [entry.sourceTarget] at raw
    exact raw
  have contextualSchedule :
      RawStep (openFindall session).session
        (sourceLiteralFindallEntered context session callerScope
          referenceTemplate referenceResult
          (.unify referenceValue referenceAmbOutput :: remainingReferences)
          referenceRest referenceBindings)
        [] .none (openFindall session).session
        (.running
          (sourceLiteralFindallBranched context session callerScope
            referenceTemplate referenceResult
            (.unify referenceValue referenceAmbOutput :: remainingReferences)
            referenceRest referenceBindings)) := by
    exact
      ActiveControlContext.liftProgress enteredContext sourceSchedule
        (by simp [Trace.AnswerFree])
  have contextualUnify :
      RawStep (openFindall session).session
        (sourceLiteralFindallBranched context session callerScope
          referenceTemplate referenceResult
          (.unify referenceValue referenceAmbOutput :: remainingReferences)
          referenceRest referenceBindings)
        [] .none (openFindall session).session
        (.running
          (sourceLiteralFindallAfterSelectedUnify context session callerScope
            referenceTemplate referenceResult remainingReferences referenceRest
            referenceBindings resolvedBindings)) := by
    exact
      ActiveControlContext.liftProgress enteredContext sourceUnify
        (by simp [Trace.AnswerFree])
  have enteredOccurrences :
      CollectionOccurrenceAgrees
        (sourceLiteralFindallEntered context session callerScope
          referenceTemplate referenceResult
          (.unify referenceValue referenceAmbOutput :: remainingReferences)
          referenceRest referenceBindings)
        (executableLiteralFindallEntered before executableTemplate
          ((executableValue, []) :: remainingExecutables) executableAmbOutput
          executableResult executableTail executableRest
          executableBinding).frames := by
    have occurrences := entry.control.occurrences
    rw [entry.sourceTarget] at occurrences
    exact occurrences
  have branchedOccurrencesAtEntryFrames :
      CollectionOccurrenceAgrees
        (sourceLiteralFindallBranched context session callerScope
          referenceTemplate referenceResult
          (.unify referenceValue referenceAmbOutput :: remainingReferences)
          referenceRest referenceBindings)
        (executableLiteralFindallEntered before executableTemplate
          ((executableValue, []) :: remainingExecutables) executableAmbOutput
          executableResult executableTail executableRest
          executableBinding).frames := by
    apply ActiveControlContext.preserve_occurrences enteredContext
      (focus := sourceLiteralFindallFocus session
        (.unify referenceValue referenceAmbOutput :: remainingReferences)
        referenceBindings)
      (next := Search.disjoin (openFindall session).cutScope
        (.unify referenceValue referenceAmbOutput :: remainingReferences) []
        referenceBindings)
    · simp
    · exact enteredOccurrences
  have branchedOccurrences :
      CollectionOccurrenceAgrees
        (sourceLiteralFindallBranched context session callerScope
          referenceTemplate referenceResult
          (.unify referenceValue referenceAmbOutput :: remainingReferences)
          referenceRest referenceBindings)
        (literalAmbPulledSuccessor
          (executableLiteralFindallEntered before executableTemplate
            ((executableValue, []) :: remainingExecutables)
            executableAmbOutput executableResult executableTail executableRest
            executableBinding)
          executableAmbOutput executableValue remainingExecutables
          executableTail executableBinding).frames := by
    simpa using branchedOccurrencesAtEntryFrames
  have afterOccurrencesAtEntryFrames :
      CollectionOccurrenceAgrees
        (sourceLiteralFindallAfterSelectedUnify context session callerScope
          referenceTemplate referenceResult remainingReferences referenceRest
          referenceBindings resolvedBindings)
        (executableLiteralFindallEntered before executableTemplate
          ((executableValue, []) :: remainingExecutables) executableAmbOutput
          executableResult executableTail executableRest
          executableBinding).frames := by
    apply ActiveControlContext.preserve_occurrences enteredContext
      (focus := Search.disjoin (openFindall session).cutScope
        (.unify referenceValue referenceAmbOutput :: remainingReferences) []
        referenceBindings)
      (next := selectedUnifySourceSuccessor
        (openFindall session).cutScope remainingReferences []
        referenceBindings resolvedBindings)
    · simp
    · exact branchedOccurrencesAtEntryFrames
  have afterOccurrences :
      CollectionOccurrenceAgrees
        (sourceLiteralFindallAfterSelectedUnify context session callerScope
          referenceTemplate referenceResult remainingReferences referenceRest
          referenceBindings resolvedBindings)
        (PrologOrdinaryStepBridge.unifySuccessor
          (literalAmbPulledSuccessor
            (executableLiteralFindallEntered before executableTemplate
              ((executableValue, []) :: remainingExecutables)
              executableAmbOutput executableResult executableTail
              executableRest executableBinding)
            executableAmbOutput executableValue remainingExecutables
            executableTail executableBinding)
          executableTail installed).frames := by
    rw [framesAfter]
    exact afterOccurrencesAtEntryFrames
  refine
    ⟨sourceExtension, installed, installedExact, sourceEntry,
      entry.control.fineStep, contextualSchedule, fineSchedule,
      contextualUnify, fineUnify, enteredOccurrences, branchedOccurrences,
      afterOccurrences, payloadAfter, residualPayloads, altsAfter,
      persistentAfter, framesAfter, scopesAfter⟩

end PLeaTTa.PrologFindallDisjunctionBridge
