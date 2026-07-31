-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologFindallDisjunctionExitBridge
Purpose: Close a singleton literal-disjunction failure through one active
  findall and the additive certified copy lane.
Trusted boundary: none
Main exports: contextual_singleton_literal_findall_failure_exit,
  contextual_singleton_literal_findall_failure_exit_correspondence
-/
import PLeaTTa.Proofs.PrologFindallDisjunctionBridge
import PLeaTTa.Proofs.PrologFindallExitPayloadBridge

namespace PLeaTTa.PrologFindallDisjunctionExitBridge

open Metta (Atom GroundingTable Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PrologActiveControlContextBridge
open PrologAnswerResourceBridge
open PrologDisjunctionStepBridge
open PrologFindallCopyBridge
open PrologFindallDisjunctionBridge
open PrologFindallEntryBridge
open PrologFindallExitBridge
open PrologFindallExitPayloadBridge
open PrologFindallFrameZipperBridge
open PrologGoalAlpha
open PrologOrdinaryStepBridge
open PrologStateBridge
open DemandDrivenStep

/-! ## Occurrence-aware exit lifting -/

/-- One typed outer frame transports an actual active collector exit.  Unlike
`ActiveControlFrame.liftProgress`, this retains the identity of the consumed
source collection occurrence. -/
theorem ActiveControlFrame.liftFindallExit
    (frame : ActiveControlFrame)
    {before after : Session} {focus next : Search}
    {cell : SourceCollectionCell}
    (inside : ActiveFindallExit before focus after next cell) :
    ActiveFindallExit before (frame.wrap focus) after (frame.wrap next) cell := by
  cases frame with
  | choiceLeft scope right =>
      exact .underChoice scope right inside
  | cut outerScope innerScope =>
      exact .underCut innerScope inside
  | catchBoundary handlerScope scope catcher handler entryBindings =>
      exact .underCatch handlerScope scope catcher handler entryBindings inside
  | collection collectionScope callerScope generatorScope template output
      entryBindings tail reversed =>
      exact
        .underCollection collectionScope callerScope generatorScope template
          output entryBindings tail reversed inside
  | productHead scope tail =>
      exact .underProduct scope tail inside

/-- Any typed active outer context transports the same positional exit. -/
theorem ActiveControlContext.liftFindallExit
    (context : ActiveControlContext)
    {before after : Session} {focus next : Search}
    {cell : SourceCollectionCell}
    (inside : ActiveFindallExit before focus after next cell) :
    ActiveFindallExit before (context.plug focus) after (context.plug next)
      cell := by
  induction context generalizing focus next with
  | nil => exact inside
  | cons frame outer inductionHypothesis =>
      exact
        inductionHypothesis
          (PLeaTTa.PrologFindallDisjunctionExitBridge.ActiveControlFrame.liftFindallExit
            frame inside)

/-! ## Exact singleton source exit -/

/-- The source collection occurrence created by this literal `findall`. -/
def singletonLiteralFindallCell
    (session : Session) (callerScope : CutScopeId)
    (template result : Term) (rest : List PeTTaSpec.PrologCore.Goal)
    (bindings : Substitution) : SourceCollectionCell :=
  sourceCollectionCell (openFindall session).cutScope
    (openFindall session).collectionScope callerScope template result bindings
    rest []

/-- Source caller immediately after an exhausted empty collection rejoins. -/
def sourceLiteralFindallEmptyRejoined
    (context : ActiveControlContext) (callerScope : CutScopeId)
    (result : Term) (rest : List PeTTaSpec.PrologCore.Goal)
    (bindings : Substitution) : Search :=
  context.plug
    (.task callerScope (.unify result (.list [] none) :: rest) bindings)

/-- A singleton selected equality clash is the real child completion consumed
by the active collection boundary.  The outer context is transported with the
occurrence identity intact; no standalone terminal source state is invented. -/
theorem contextual_singleton_literal_findall_failure_exit
    {context : ActiveControlContext} {session : Session}
    {callerScope : CutScopeId}
    {template result value output : Term}
    {rest : List PeTTaSpec.PrologCore.Goal}
    {bindings : Substitution}
    (clash : ¬ ∃ resolved, UnifyResolution bindings value output resolved) :
    ActiveFindallExit (openFindall session).session
      (sourceLiteralFindallBranched context session callerScope template result
        [.unify value output] rest bindings)
      (openFindall session).session
      (sourceLiteralFindallEmptyRejoined context callerScope result rest
        bindings)
      (singletonLiteralFindallCell session callerScope template result rest
        bindings) := by
  have leaf :
      RawStep (openFindall session).session
        (.task (openFindall session).cutScope [.unify value output] bindings)
        [.completed] .none (openFindall session).session
        (.terminal .completed) := by
    exact
      .taskUnifyFailure (openFindall session).cutScope value output [] bindings
        (openFindall session).session clash
  have child :
      RawStep (openFindall session).session
        (.cutBoundary (openFindall session).cutScope
          (.task (openFindall session).cutScope [.unify value output]
            bindings))
        [.completed] .none (openFindall session).session
        (.terminal .completed) := by
    exact
      .cutBoundaryComplete (openFindall session).cutScope
        (.task (openFindall session).cutScope [.unify value output] bindings)
        (openFindall session).session (openFindall session).session leaf
  have inner :
      ActiveFindallExit (openFindall session).session
        (.collectionBoundary (openFindall session).collectionScope callerScope
          (.cutBoundary (openFindall session).cutScope
            (.task (openFindall session).cutScope [.unify value output]
              bindings))
          template result bindings rest [])
        (openFindall session).session
        (.task callerScope (.unify result (.list [] none) :: rest) bindings)
        (singletonLiteralFindallCell session callerScope template result rest
          bindings) := by
    exact
      .here (openFindall session).session (openFindall session).session
        callerScope (openFindall session).cutScope
        (openFindall session).collectionScope
        (.task (openFindall session).cutScope [.unify value output] bindings)
        template result bindings rest [] child
  simpa [sourceLiteralFindallBranched, enteredLiteralFindallContext,
    sourceLiteralFindallEmptyRejoined, ActiveControlFrame.wrap,
    Search.disjoin] using
    ActiveControlContext.liftFindallExit context inner

/-! ## Additive-lane ordinary steps -/

/-- The actual sealed literal-`amb` transition is admissible in the additive
copy lane.  This direct constructor excludes the atomic collector-exit case
that a generic lift from the established fine lane would accidentally permit. -/
theorem executable_literal_amb_copy_step
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (state : OpenConf) (output value : Atom)
    (remaining : List (Atom × List PLeaTTa.Goal))
    (tail : List PLeaTTa.Goal) (runtime : Subst)
    (head :
      state.control.cur =
        some (.amb ((value, []) :: remaining) output :: tail, runtime)) :
    let next :=
      literalAmbPulledSuccessor state output value remaining tail runtime
    CopyStep prog gt (.open state) (.open next) := by
  let next :=
    literalAmbPulledSuccessor state output value remaining tail runtime
  have sealedHead :
      state.toConf.cur =
        some (.amb ((value, []) :: remaining) output :: tail, runtime) := by
    simpa [OpenConf.toConf, Control.toConf] using head
  have notFindall : ¬ PLeaTTa.findallRunHead state.toConf := by
    simp [PLeaTTa.findallRunHead, sealedHead]
  have sealedStep : PLeaTTa.Step prog gt state.toConf next.toConf := by
    simpa [next, literalAmbPulledSuccessor] using
      (PLeaTTa.Step.amb state.toConf ((value, []) :: remaining) output tail
        runtime sealedHead)
  simpa [next, literalAmbPulledSuccessor] using
    (CopyStep.ordinary state next.toConf notFindall sealedStep)

/-- Either sealed primitive-equality spelling takes its real failed pull in
the additive copy lane, without enabling the atomic collector exit. -/
theorem executable_unify_failure_copy_step
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    (state : OpenConf)
    (spelling : NormalizedAlphaGoalsAgree.ExecutableUnifySpelling)
    (left right : Atom) (rest : List PLeaTTa.Goal) (runtime : Subst)
    (head :
      state.control.cur =
        some (spelling.goal left right :: rest, runtime))
    (failed : PLeaTTa.unifyB runtime left right = none) :
    CopyStep prog gt (.open state)
      (.open (unifyFailureSuccessor state)) := by
  have sealedHead :
      state.toConf.cur =
        some (spelling.goal left right :: rest, runtime) := by
    simpa [OpenConf.toConf, Control.toConf] using head
  have notFindall : ¬ PLeaTTa.findallRunHead state.toConf := by
    cases spelling <;>
      simp [PLeaTTa.findallRunHead,
        NormalizedAlphaGoalsAgree.ExecutableUnifySpelling.goal, sealedHead]
  apply CopyStep.ordinary state (unifyFailureSuccessor state).toConf notFindall
  cases spelling with
  | equality =>
      simpa [unifyFailureSuccessor,
        NormalizedAlphaGoalsAgree.ExecutableUnifySpelling.goal] using
        (PLeaTTa.Step.eq_fail state.toConf left right rest runtime sealedHead
          failed)
  | compilerAlias =>
      simpa [unifyFailureSuccessor,
        NormalizedAlphaGoalsAgree.ExecutableUnifySpelling.goal] using
        (PLeaTTa.Step.compileAlias_fail state.toConf left right rest runtime
          sealedHead failed)

/-- Collector entry starts with an empty private answer accumulator. -/
@[simp] theorem executableLiteralFindallEntered_answers
    (before : OpenConf) (template : Atom)
    (branches : List (Atom × List PLeaTTa.Goal))
    (ambOutput result : Atom) (tail rest : List PLeaTTa.Goal)
    (binding : Subst) :
    (executableLiteralFindallEntered before template branches ambOutput result
      tail rest binding).control.answers = [] := by
  rfl

/-- A newly entered private generator owns no active alternative yet. -/
@[simp] theorem executableLiteralFindallEntered_alts
    (before : OpenConf) (template : Atom)
    (branches : List (Atom × List PLeaTTa.Goal))
    (ambOutput result : Atom) (tail rest : List PLeaTTa.Goal)
    (binding : Subst) :
    (executableLiteralFindallEntered before template branches ambOutput result
      tail rest binding).control.alts = [] := by
  rfl

/-- The exact frame installed by the literal collector entry. -/
@[simp] theorem executableLiteralFindallEntered_frames
    (before : OpenConf) (template : Atom)
    (branches : List (Atom × List PLeaTTa.Goal))
    (ambOutput result : Atom) (tail rest : List PLeaTTa.Goal)
    (binding : Subst) :
    (executableLiteralFindallEntered before template branches ambOutput result
      tail rest binding).frames =
      .findall (executableFindallFrame before template result rest binding) ::
        before.frames := by
  rfl

/-! ## Reachable empty-exit composition -/

/-- Exact control correspondence for a singleton literal failure that
exhausts its active collector.

The source collector consumes the selected leaf's completion in its third
transition.  The additive fine lane reaches a terminal generator in its third
transition, then takes the mandatory transfer and finish transitions even for
an empty bag.  The `3` versus `5` count is therefore proof-relevant rather
than an observation-list quotient. -/
structure ContextualEmptyFindallExitRelates
    (prog : PLeaTTa.Prog) (gt : GroundingTable)
    (runtime : Subst) (output value : Atom)
    (beforeSession afterSession : Session)
    (beforeSearch enteredSearch branchedSearch afterSearch : Search)
    (before entered selected terminal after : OpenConf)
    (cell : SourceCollectionCell) (frame : FindallFrame)
    (remaining : List Frame) : Prop where
  runtimeFailure : PLeaTTa.unifyB runtime output value = none
  sourceEntry :
    RawStep beforeSession beforeSearch [] .none afterSession
      (.running enteredSearch)
  sourceSchedule :
    RawStep afterSession enteredSearch [] .none afterSession
      (.running branchedSearch)
  sourceExit :
    ActiveFindallExit afterSession branchedSearch afterSession afterSearch cell
  fineEntry : CopyStep prog gt (.open before) (.open entered)
  fineSchedule : CopyStep prog gt (.open entered) (.open selected)
  fineFailure : CopyStep prog gt (.open selected) (.open terminal)
  fineTerminal : PLeaTTa.Terminal terminal.toConf
  emptyAnswers : terminal.control.answers = []
  frameHead : terminal.frames = .findall frame :: remaining
  occurrencesBeforeExit :
    CollectionOccurrenceAgrees branchedSearch terminal.frames
  atomicExit :
    ContextualFindallExitRelates prog gt afterSession branchedSearch
      afterSession afterSearch cell terminal after frame remaining
  additiveExit :
    CopyStepsN prog gt 2 (.open terminal) (.open after)
  sourceRun :
    PeTTaSpec.PrologCore.GoalSemantics.StepsN 3
      (.running beforeSession beforeSearch) []
      (.running afterSession afterSearch)
  fineRun : CopyStepsN prog gt 5 (.open before) (.open after)

/-- One exact singleton literal clash closes the active source collector and
the additive fine collector on the same positional occurrence.

The compiler payload premise remains the independently typed literal entry
certificate.  Runtime failure is reflected from its strict operand relation;
it is not supplied separately.  The fine frame is the one pushed by that
entry, not an arbitrary head-frame hypothesis.

[SPEC translator.pl:112-116; metta.pl:251-256] -/
theorem contextual_singleton_literal_findall_failure_exit_correspondence
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {prog : PLeaTTa.Prog} {gt : GroundingTable}
    {context : ActiveControlContext} {session : Session}
    {callerScope : CutScopeId}
    {referenceTemplate referenceAmbOutput referenceResult referenceValue : Term}
    {referenceRest : List PeTTaSpec.PrologCore.Goal}
    {referenceBindings : Substitution}
    {executableTemplate executableAmbOutput executableResult executableValue :
      Atom}
    {executableTail executableRest : List PLeaTTa.Goal}
    {executableBinding : Subst} {before : OpenConf}
    (entry :
      ContextualLiteralFindallEntryRelates freshFrontier alpha support barrier
        canonical referenceBase prog gt context session callerScope
        referenceTemplate referenceAmbOutput referenceResult
        [.unify referenceValue referenceAmbOutput]
        referenceRest referenceBindings executableTemplate executableAmbOutput
        executableResult [(executableValue, [])] executableTail executableRest
        executableBinding before)
    (valueSupported :
      AlphaTreeSupported alpha support (Term.denote referenceValue))
    (outputSupported :
      AlphaTreeSupported alpha support (Term.denote referenceAmbOutput))
    (aliasSafe :
      CurrentUnifyOperandsAliasSafe referenceBindings referenceValue
        referenceAmbOutput)
    (clash :
      ¬ ∃ resolved,
        UnifyResolution referenceBindings referenceValue referenceAmbOutput
          resolved) :
    let sourceBefore :=
      sourceLiteralFindallBefore context callerScope referenceTemplate
        [.unify referenceValue referenceAmbOutput] referenceResult
        referenceRest referenceBindings
    let sourceEntered :=
      sourceLiteralFindallEntered context session callerScope referenceTemplate
        referenceResult [.unify referenceValue referenceAmbOutput]
        referenceRest referenceBindings
    let sourceBranched :=
      sourceLiteralFindallBranched context session callerScope referenceTemplate
        referenceResult [.unify referenceValue referenceAmbOutput]
        referenceRest referenceBindings
    let sourceAfter :=
      sourceLiteralFindallEmptyRejoined context callerScope referenceResult
        referenceRest referenceBindings
    let fineEntered :=
      executableLiteralFindallEntered before executableTemplate
        [(executableValue, [])] executableAmbOutput executableResult
        executableTail executableRest executableBinding
    let fineSelected :=
      literalAmbPulledSuccessor fineEntered executableAmbOutput executableValue
        [] executableTail executableBinding
    let fineTerminal := unifyFailureSuccessor fineSelected
    let frame :=
      executableFindallFrame before executableTemplate executableResult
        executableRest executableBinding
    let fineAfter := resumeFindall fineTerminal frame before.frames
    let cell :=
      singletonLiteralFindallCell session callerScope referenceTemplate
        referenceResult referenceRest referenceBindings
    ContextualEmptyFindallExitRelates prog gt executableBinding
      executableAmbOutput executableValue session (openFindall session).session
      sourceBefore sourceEntered sourceBranched sourceAfter before fineEntered
      fineSelected fineTerminal fineAfter cell frame before.frames := by
  rcases entry.ready.literal_cons_components with
    ⟨valueAgreement, outputAgreement, residualAgreement⟩
  let fineEntered :=
    executableLiteralFindallEntered before executableTemplate
      [(executableValue, [])] executableAmbOutput executableResult
      executableTail executableRest executableBinding
  let fineSelected :=
    literalAmbPulledSuccessor fineEntered executableAmbOutput executableValue
      [] executableTail executableBinding
  let fineTerminal := unifyFailureSuccessor fineSelected
  let frame :=
    executableFindallFrame before executableTemplate executableResult
      executableRest executableBinding
  let fineAfter := resumeFindall fineTerminal frame before.frames
  let enteredContext :=
    enteredLiteralFindallContext context session callerScope referenceTemplate
      referenceResult referenceRest referenceBindings
  let cell :=
    singletonLiteralFindallCell session callerScope referenceTemplate
      referenceResult referenceRest referenceBindings
  let selectedPayload :
      TaskChoicePayloadAgrees alpha support barrier canonical referenceBase
        referenceBindings executableBinding
        [.unify referenceValue referenceAmbOutput]
        (.eq executableAmbOutput executableValue :: executableTail) :=
    .symmetricUnify entry.ready.data valueAgreement outputAgreement
      entry.ready.tail
  have failed :
      PLeaTTa.unifyB executableBinding executableAmbOutput executableValue =
        none :=
    selectedPayload.unifyB_eq_none_of_no_resolution
      valueSupported outputSupported aliasSafe clash
  have sourceEntry :
      RawStep session
        (sourceLiteralFindallBefore context callerScope referenceTemplate
          [.unify referenceValue referenceAmbOutput] referenceResult
          referenceRest referenceBindings)
        [] .none (openFindall session).session
        (.running
          (sourceLiteralFindallEntered context session callerScope
            referenceTemplate referenceResult
            [.unify referenceValue referenceAmbOutput] referenceRest
            referenceBindings)) := by
    have raw :=
      (ActiveControlContext.enterFindallResult context session callerScope
        referenceTemplate (.disjunction [.unify referenceValue referenceAmbOutput])
        referenceResult referenceRest referenceBindings).sourceStep
    rw [entry.sourceTarget] at raw
    exact raw
  have fineEntry : CopyStep prog gt (.open before) (.open fineEntered) := by
    exact
      .findallEnter before executableTemplate
        (.amb [(executableValue, [])] executableAmbOutput :: executableTail)
        executableResult executableRest executableBinding
        entry.control.fineHead
  have sourceScheduleFocus :=
    (literal_disjunction_step_correspondence_cons
      (prog := prog) (gt := gt) (scope := (openFindall session).cutScope)
      entry.ready).1
  have sourceSchedule :
      RawStep (openFindall session).session
        (sourceLiteralFindallEntered context session callerScope
          referenceTemplate referenceResult
          [.unify referenceValue referenceAmbOutput] referenceRest
          referenceBindings)
        [] .none (openFindall session).session
        (.running
          (sourceLiteralFindallBranched context session callerScope
            referenceTemplate referenceResult
            [.unify referenceValue referenceAmbOutput] referenceRest
            referenceBindings)) := by
    exact
      ActiveControlContext.liftProgress enteredContext sourceScheduleFocus
        (by simp [Trace.AnswerFree])
  have fineSchedule :
      CopyStep prog gt (.open fineEntered) (.open fineSelected) := by
    exact
      executable_literal_amb_copy_step fineEntered executableAmbOutput
        executableValue [] executableTail executableBinding
        entry.ready.current_exact
  have selectedHead :
      fineSelected.control.cur =
        some (.eq executableAmbOutput executableValue :: executableTail,
          executableBinding) := by
    simp [fineSelected, PLeaTTa.ambBranchGoals]
  have fineFailure :
      CopyStep prog gt (.open fineSelected) (.open fineTerminal) := by
    exact
      executable_unify_failure_copy_step fineSelected .equality
        executableAmbOutput executableValue executableTail executableBinding
        selectedHead failed
  have selectedAlts : fineSelected.control.alts = [] := by
    simp [fineSelected, fineEntered]
  have fineTerminalProof : PLeaTTa.Terminal fineTerminal.toConf := by
    exact unifyFailureSuccessor_terminal_of_alts_empty fineSelected selectedAlts
  have emptyAnswers : fineTerminal.control.answers = [] := by
    simp [fineTerminal, fineSelected, fineEntered]
  have sourceExit :
      ActiveFindallExit (openFindall session).session
        (sourceLiteralFindallBranched context session callerScope
          referenceTemplate referenceResult
          [.unify referenceValue referenceAmbOutput] referenceRest
          referenceBindings)
        (openFindall session).session
        (sourceLiteralFindallEmptyRejoined context callerScope referenceResult
          referenceRest referenceBindings)
        cell := by
    simpa [cell] using
      (contextual_singleton_literal_findall_failure_exit
        (context := context) (session := session) (callerScope := callerScope)
        (template := referenceTemplate) (result := referenceResult)
        (value := referenceValue) (output := referenceAmbOutput)
        (rest := referenceRest) (bindings := referenceBindings) clash)
  have enteredOccurrences :
      CollectionOccurrenceAgrees
        (sourceLiteralFindallEntered context session callerScope
          referenceTemplate referenceResult
          [.unify referenceValue referenceAmbOutput] referenceRest
          referenceBindings)
        fineEntered.frames := by
    have occurrences := entry.control.occurrences
    rw [entry.sourceTarget] at occurrences
    exact occurrences
  have branchedOccurrencesAtEntryFrames :
      CollectionOccurrenceAgrees
        (sourceLiteralFindallBranched context session callerScope
          referenceTemplate referenceResult
          [.unify referenceValue referenceAmbOutput] referenceRest
          referenceBindings)
        fineEntered.frames := by
    apply ActiveControlContext.preserve_occurrences enteredContext
      (focus := sourceLiteralFindallFocus session
        [.unify referenceValue referenceAmbOutput] referenceBindings)
      (next := Search.disjoin (openFindall session).cutScope
        [.unify referenceValue referenceAmbOutput] [] referenceBindings)
    · simp
    · exact enteredOccurrences
  have occurrencesBeforeExit :
      CollectionOccurrenceAgrees
        (sourceLiteralFindallBranched context session callerScope
          referenceTemplate referenceResult
          [.unify referenceValue referenceAmbOutput] referenceRest
          referenceBindings)
        fineTerminal.frames := by
    simpa [fineTerminal, fineSelected] using branchedOccurrencesAtEntryFrames
  have frameHead : fineTerminal.frames = .findall frame :: before.frames := by
    simp [fineTerminal, fineSelected, fineEntered, frame]
  have atomicExit :
      ContextualFindallExitRelates prog gt (openFindall session).session
        (sourceLiteralFindallBranched context session callerScope
          referenceTemplate referenceResult
          [.unify referenceValue referenceAmbOutput] referenceRest
          referenceBindings)
        (openFindall session).session
        (sourceLiteralFindallEmptyRejoined context callerScope referenceResult
          referenceRest referenceBindings)
        cell fineTerminal fineAfter frame before.frames := by
    simpa [fineAfter] using
      sourceExit.findallExit_occurrence_pop frameHead fineTerminalProof
        occurrencesBeforeExit
  have additiveExit :
      CopyStepsN prog gt 2 (.open fineTerminal) (.open fineAfter) := by
    have expanded :=
      findallExit_copy_expands prog gt fineTerminal frame before.frames
        frameHead fineTerminalProof
    simpa [fineAfter, Control.answerValues, emptyAnswers] using expanded
  have sourceRun :
      PeTTaSpec.PrologCore.GoalSemantics.StepsN 3
        (.running session
          (sourceLiteralFindallBefore context callerScope referenceTemplate
            [.unify referenceValue referenceAmbOutput] referenceResult
            referenceRest referenceBindings))
        []
        (.running (openFindall session).session
          (sourceLiteralFindallEmptyRejoined context callerScope
            referenceResult referenceRest referenceBindings)) := by
    have first :
        Transition
          (.running session
            (sourceLiteralFindallBefore context callerScope referenceTemplate
              [.unify referenceValue referenceAmbOutput] referenceResult
              referenceRest referenceBindings))
          []
          (.running (openFindall session).session
            (sourceLiteralFindallEntered context session callerScope
              referenceTemplate referenceResult
              [.unify referenceValue referenceAmbOutput] referenceRest
              referenceBindings)) :=
      .ordinary _ [] _ _ _ sourceEntry
    have second :
        Transition
          (.running (openFindall session).session
            (sourceLiteralFindallEntered context session callerScope
              referenceTemplate referenceResult
              [.unify referenceValue referenceAmbOutput] referenceRest
              referenceBindings))
          []
          (.running (openFindall session).session
            (sourceLiteralFindallBranched context session callerScope
              referenceTemplate referenceResult
              [.unify referenceValue referenceAmbOutput] referenceRest
              referenceBindings)) :=
      .ordinary _ [] _ _ _ sourceSchedule
    have third :
        Transition
          (.running (openFindall session).session
            (sourceLiteralFindallBranched context session callerScope
              referenceTemplate referenceResult
              [.unify referenceValue referenceAmbOutput] referenceRest
              referenceBindings))
          []
          (.running (openFindall session).session
            (sourceLiteralFindallEmptyRejoined context callerScope
              referenceResult referenceRest referenceBindings)) :=
      .ordinary _ [] _ _ _ sourceExit.sourceStep
    simpa using
      (PeTTaSpec.PrologCore.GoalSemantics.StepsN.succ 2 _ _ _ [] [] first
        (PeTTaSpec.PrologCore.GoalSemantics.StepsN.succ 1 _ _ _ [] [] second
          (PeTTaSpec.PrologCore.GoalSemantics.StepsN.succ 0 _ _ _ [] [] third
            (.zero _))))
  have oneFineEntry :
      CopyStepsN prog gt 1 (.open before) (.open fineEntered) := by
    simpa using CopyStepsN.succ 0 _ _ _ fineEntry (.zero _)
  have oneFineSchedule :
      CopyStepsN prog gt 1 (.open fineEntered) (.open fineSelected) := by
    simpa using CopyStepsN.succ 0 _ _ _ fineSchedule (.zero _)
  have oneFineFailure :
      CopyStepsN prog gt 1 (.open fineSelected) (.open fineTerminal) := by
    simpa using CopyStepsN.succ 0 _ _ _ fineFailure (.zero _)
  have fineRun : CopyStepsN prog gt 5 (.open before) (.open fineAfter) := by
    have combined :=
      oneFineEntry.trans
        (oneFineSchedule.trans (oneFineFailure.trans additiveExit))
    norm_num at combined ⊢
    exact combined
  exact
    { runtimeFailure := failed
      sourceEntry := sourceEntry
      sourceSchedule := sourceSchedule
      sourceExit := sourceExit
      fineEntry := fineEntry
      fineSchedule := fineSchedule
      fineFailure := fineFailure
      fineTerminal := fineTerminalProof
      emptyAnswers := emptyAnswers
      frameHead := frameHead
      occurrencesBeforeExit := occurrencesBeforeExit
      atomicExit := atomicExit
      additiveExit := additiveExit
      sourceRun := sourceRun
      fineRun := fineRun }

/-- Payload-complete specialization of the reachable empty exit.

The generic entry certificate remains parameterized in its definition; this
theorem instantiates its persistent relation with the empty copy-debt frontier
because the concrete entry/schedule/failure prefix proves that no generator
answer was accumulated.  Static template/result/tail agreement and their
entry-materialized forms remain the explicit `framePayload` compiler premise.
They are not inferred from control alignment.

[SPEC translator.pl:112-116; metta.pl:251-256] -/
theorem contextual_singleton_literal_findall_failure_exit_payload
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {prog : PLeaTTa.Prog} {gt : GroundingTable}
    {context : ActiveControlContext} {session : Session}
    {callerScope : CutScopeId}
    {referenceTemplate referenceAmbOutput referenceResult referenceValue : Term}
    {referenceRest : List PeTTaSpec.PrologCore.Goal}
    {referenceBindings : Substitution}
    {executableTemplate executableAmbOutput executableResult executableValue :
      Atom}
    {executableTail executableRest : List PLeaTTa.Goal}
    {executableBinding : Subst} {before : OpenConf}
    (entry :
      ContextualLiteralFindallEntryRelates (CopyDebtFrontier [] []) alpha
        support barrier canonical referenceBase prog gt context session
        callerScope referenceTemplate referenceAmbOutput referenceResult
        [.unify referenceValue referenceAmbOutput]
        referenceRest referenceBindings executableTemplate executableAmbOutput
        executableResult [(executableValue, [])] executableTail executableRest
        executableBinding before)
    (valueSupported :
      AlphaTreeSupported alpha support (Term.denote referenceValue))
    (outputSupported :
      AlphaTreeSupported alpha support (Term.denote referenceAmbOutput))
    (aliasSafe :
      CurrentUnifyOperandsAliasSafe referenceBindings referenceValue
        referenceAmbOutput)
    (clash :
      ¬ ∃ resolved,
        UnifyResolution referenceBindings referenceValue referenceAmbOutput
          resolved)
    (framePayload :
      FindallFramePayloadAgrees
        (singletonLiteralFindallCell session callerScope referenceTemplate
          referenceResult referenceRest referenceBindings)
        (executableFindallFrame before executableTemplate executableResult
          executableRest executableBinding)) :
    let sourceBefore :=
      sourceLiteralFindallBefore context callerScope referenceTemplate
        [.unify referenceValue referenceAmbOutput] referenceResult
        referenceRest referenceBindings
    let sourceEntered :=
      sourceLiteralFindallEntered context session callerScope referenceTemplate
        referenceResult [.unify referenceValue referenceAmbOutput]
        referenceRest referenceBindings
    let sourceBranched :=
      sourceLiteralFindallBranched context session callerScope referenceTemplate
        referenceResult [.unify referenceValue referenceAmbOutput]
        referenceRest referenceBindings
    let sourceAfter :=
      sourceLiteralFindallEmptyRejoined context callerScope referenceResult
        referenceRest referenceBindings
    let fineEntered :=
      executableLiteralFindallEntered before executableTemplate
        [(executableValue, [])] executableAmbOutput executableResult
        executableTail executableRest executableBinding
    let fineSelected :=
      literalAmbPulledSuccessor fineEntered executableAmbOutput executableValue
        [] executableTail executableBinding
    let fineTerminal := unifyFailureSuccessor fineSelected
    let frame :=
      executableFindallFrame before executableTemplate executableResult
        executableRest executableBinding
    let fineAfter := resumeFindall fineTerminal frame before.frames
    let cell :=
      singletonLiteralFindallCell session callerScope referenceTemplate
        referenceResult referenceRest referenceBindings
    ContextualEmptyFindallExitRelates prog gt executableBinding
        executableAmbOutput executableValue session
        (openFindall session).session sourceBefore sourceEntered sourceBranched
        sourceAfter before fineEntered fineSelected fineTerminal fineAfter cell
        frame before.frames ∧
      ContextualFindallExitPayloadRelates prog gt
        (openFindall session).session sourceBranched
        (openFindall session).session sourceAfter cell fineTerminal fineAfter
        frame before.frames := by
  let fineEntered :=
    executableLiteralFindallEntered before executableTemplate
      [(executableValue, [])] executableAmbOutput executableResult
      executableTail executableRest executableBinding
  let fineSelected :=
    literalAmbPulledSuccessor fineEntered executableAmbOutput executableValue
      [] executableTail executableBinding
  let fineTerminal := unifyFailureSuccessor fineSelected
  let frame :=
    executableFindallFrame before executableTemplate executableResult
      executableRest executableBinding
  let fineAfter := resumeFindall fineTerminal frame before.frames
  let cell :=
    singletonLiteralFindallCell session callerScope referenceTemplate
      referenceResult referenceRest referenceBindings
  have control :=
    contextual_singleton_literal_findall_failure_exit_correspondence
      (entry := entry) valueSupported outputSupported aliasSafe clash
  have sessionAtExit :
      CollectionSessionRelates [] [] (openFindall session).session
        fineTerminal.persistent := by
    simpa [fineTerminal, fineSelected, fineEntered] using entry.ready.persistent
  have payload :
      FindallExitPayloadAgrees (openFindall session).session cell fineTerminal
        frame := by
    exact
      { framePayload := by simpa [cell, frame] using framePayload
        session := by
          change
            CollectionSessionRelates [] fineTerminal.control.answers
              (openFindall session).session fineTerminal.persistent
          rw [control.emptyAnswers]
          exact sessionAtExit }
  exact
    ⟨control,
      { control := control.atomicExit
        payload := payload }⟩

/-- The exact runs cannot be mistaken for a lockstep correspondence: the
additive collector owns two certified local transitions that have no source
counterpart even when the bag is empty. -/
theorem ContextualEmptyFindallExitRelates.not_lockstep
    {prog : PLeaTTa.Prog} {gt : GroundingTable}
    {runtime : Subst} {output value : Atom}
    {beforeSession afterSession : Session}
    {beforeSearch enteredSearch branchedSearch afterSearch : Search}
    {before entered selected terminal after : OpenConf}
    {cell : SourceCollectionCell} {frame : FindallFrame}
    {remaining : List Frame}
    (_related :
      ContextualEmptyFindallExitRelates prog gt runtime output value
        beforeSession afterSession beforeSearch enteredSearch branchedSearch
        afterSearch before entered selected terminal after cell frame
        remaining) :
    (3 : Nat) ≠ 5 := by
  omega

end PLeaTTa.PrologFindallDisjunctionExitBridge
