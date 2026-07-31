-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologFindallAnswerBridge
Purpose: Relate one actual source findall generator answer to one private
  fine-machine answer step and the resulting ordered copy-debt frontier.
Trusted boundary: none
Main exports: ActiveFindallAnswer, ContextualFindallAnswerRelates
-/
import PLeaTTa.Proofs.PrologFindallExitPayloadBridge

namespace PLeaTTa.PrologFindallAnswerBridge

open Metta (Atom GroundingTable Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Copy
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open CompilerAdequacy
open CompilerSubstitutionAdequacy
open OpenBindingAgreement
open PrologStateBridge
open PrologFindallCopyBridge
open PrologFindallFrameZipperBridge
open PrologFindallExitPayloadBridge
open DemandDrivenStep

/-!
# One private generator answer

`RawStep.collectionAnswer` performs the generator child transition and then
copies the materialized template at the child's *post-step* source session.
The fine machine reaches the corresponding answer-ready configuration and
uses one ordinary private answer step to prepend the materialized raw value;
the residual-variable copy remains explicit debt until the bounded local copy
phase.

The child-post/source versus fine-pre relation below is deliberate.  It does
not claim the still-open child simulation that must establish that phase
alignment in the eventual finite-prefix bisimulation.
-/

/-- Exact source-cell successor after collecting one generator solution.
Only the reverse-discovery payload changes; all typed occurrence identities
and suspended caller fields remain literal. -/
def afterAnswer (cell : SourceCollectionCell) (childAfter : Session)
    (answerBindings : Substitution) : SourceCollectionCell :=
  { cell with
    reversed :=
      (collectTemplate childAfter cell.template
        answerBindings).prepared.copied :: cell.reversed }

@[simp] theorem afterAnswer_cutScope (cell : SourceCollectionCell)
    (childAfter : Session) (answerBindings : Substitution) :
    (afterAnswer cell childAfter answerBindings).cutScope = cell.cutScope :=
  rfl

@[simp] theorem afterAnswer_collectionScope (cell : SourceCollectionCell)
    (childAfter : Session) (answerBindings : Substitution) :
    (afterAnswer cell childAfter answerBindings).collectionScope =
      cell.collectionScope :=
  rfl

@[simp] theorem afterAnswer_callerScope (cell : SourceCollectionCell)
    (childAfter : Session) (answerBindings : Substitution) :
    (afterAnswer cell childAfter answerBindings).callerScope =
      cell.callerScope :=
  rfl

@[simp] theorem afterAnswer_template (cell : SourceCollectionCell)
    (childAfter : Session) (answerBindings : Substitution) :
    (afterAnswer cell childAfter answerBindings).template = cell.template :=
  rfl

@[simp] theorem afterAnswer_output (cell : SourceCollectionCell)
    (childAfter : Session) (answerBindings : Substitution) :
    (afterAnswer cell childAfter answerBindings).output = cell.output :=
  rfl

@[simp] theorem afterAnswer_entryBindings (cell : SourceCollectionCell)
    (childAfter : Session) (answerBindings : Substitution) :
    (afterAnswer cell childAfter answerBindings).entryBindings =
      cell.entryBindings :=
  rfl

@[simp] theorem afterAnswer_tail (cell : SourceCollectionCell)
    (childAfter : Session) (answerBindings : Substitution) :
    (afterAnswer cell childAfter answerBindings).tail = cell.tail :=
  rfl

@[simp] theorem afterAnswer_reversed (cell : SourceCollectionCell)
    (childAfter : Session) (answerBindings : Substitution) :
    (afterAnswer cell childAfter answerBindings).reversed =
      (collectTemplate childAfter cell.template
        answerBindings).prepared.copied :: cell.reversed :=
  rfl

@[simp] theorem afterAnswer_agreesFrame
    (cell : SourceCollectionCell) (childAfter : Session)
    (answerBindings : Substitution) (frame : Frame) :
    (afterAnswer cell childAfter answerBindings).AgreesFrame frame ↔
      cell.AgreesFrame frame := by
  cases frame
  rfl

/-- One actual active `findall/3` answer, closed under exactly the wrappers
that can lie on the leftmost source control path.  Crossing an outer
collection uses `collectionProgress`, never `collectionAnswer`: the inner
solution is consumed exactly once.

The direct constructor is fail-closed about nested collectors: until the raw
event-shape classifier is exported, it requires exact empty active-collection
proofs on both child endpoints rather than inferring them from an unconstrained
cleanup batch. -/
inductive ActiveFindallAnswer :
    Session → Search → Session → Search → SourceCollectionCell →
      Substitution → Prop where
  | here (before childAfter : Session)
      (callerScope cutScope : CutScopeId)
      (collectionScope : CollectionScopeId)
      (body next : Search) (template output : Term)
      (entryBindings : Substitution)
      (tail : List PeTTaSpec.PrologCore.Goal)
      (reversed : List Term) (answerBindings : Substitution)
      (child :
        RawStep before (.cutBoundary cutScope body)
          [.answer answerBindings] .none childAfter
          (.running (.cutBoundary cutScope next)))
      (beforeEmpty : activeCollectionCells body = some [])
      (afterEmpty : activeCollectionCells next = some []) :
      ActiveFindallAnswer before
        (.collectionBoundary collectionScope callerScope
          (.cutBoundary cutScope body) template output entryBindings tail
          reversed)
        childAfter
        (.collectionBoundary collectionScope callerScope
          (.cutBoundary cutScope next) template output entryBindings tail
          ((collectTemplate childAfter template
            answerBindings).prepared.copied :: reversed))
        (sourceCollectionCell cutScope collectionScope callerScope template
          output entryBindings tail reversed)
        answerBindings
  | underChoice (scope : CutScopeId) (right : Search)
      {before childAfter : Session} {left next : Search}
      {cell : SourceCollectionCell} {answerBindings : Substitution}
      (inside :
        ActiveFindallAnswer before left childAfter next cell
          answerBindings) :
      ActiveFindallAnswer before (.choice scope left right) childAfter
        (.choice scope next right) cell answerBindings
  | underCut (scope : CutScopeId)
      {before childAfter : Session} {body next : Search}
      {cell : SourceCollectionCell} {answerBindings : Substitution}
      (inside :
        ActiveFindallAnswer before body childAfter next cell
          answerBindings) :
      ActiveFindallAnswer before (.cutBoundary scope body) childAfter
        (.cutBoundary scope next) cell answerBindings
  | underCatch (handlerScope : ExceptionScopeId) (scope : CutScopeId)
      (catcher : Term) (handler : PeTTaSpec.PrologCore.Goal)
      (entryBindings : Substitution)
      {before childAfter : Session} {body next : Search}
      {cell : SourceCollectionCell} {answerBindings : Substitution}
      (inside :
        ActiveFindallAnswer before body childAfter next cell
          answerBindings) :
      ActiveFindallAnswer before
        (.catchBoundary handlerScope scope body catcher handler entryBindings)
        childAfter
        (.catchBoundary handlerScope scope next catcher handler entryBindings)
        cell answerBindings
  | underCollection (collectionScope : CollectionScopeId)
      (callerScope outerCutScope : CutScopeId)
      (template output : Term) (entryBindings : Substitution)
      (tail : List PeTTaSpec.PrologCore.Goal) (reversed : List Term)
      {before childAfter : Session} {body next : Search}
      {cell : SourceCollectionCell} {answerBindings : Substitution}
      (inside :
        ActiveFindallAnswer before body childAfter next cell
          answerBindings) :
      ActiveFindallAnswer before
        (.collectionBoundary collectionScope callerScope
          (.cutBoundary outerCutScope body) template output entryBindings tail
          reversed)
        childAfter
        (.collectionBoundary collectionScope callerScope
          (.cutBoundary outerCutScope next) template output entryBindings tail
          reversed)
        cell answerBindings
  | underProduct (scope : CutScopeId)
      (tail : List PeTTaSpec.PrologCore.Goal)
      {before childAfter : Session} {head next : Search}
      {cell : SourceCollectionCell} {answerBindings : Substitution}
      (inside :
        ActiveFindallAnswer before head childAfter next cell
          answerBindings) :
      ActiveFindallAnswer before (.product scope head tail) childAfter
        (.product scope next tail) cell answerBindings

namespace ActiveFindallAnswer

/-- Every contextual answer is one actual source transition with no public
observation and no escaping cut signal.  The final source session is the
answer-time copy successor of the generator child's post-session. -/
theorem sourceStep
    {before childAfter : Session} {search next : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    (answer :
      ActiveFindallAnswer before search childAfter next cell answerBindings) :
    RawStep before search [] .none
      (collectTemplate childAfter cell.template answerBindings).session
      (.running next) := by
  induction answer with
  | here before childAfter callerScope cutScope collectionScope body next
      template output entryBindings tail reversed answerBindings child
      beforeEmpty afterEmpty =>
      exact
        .collectionAnswer collectionScope callerScope
          (.cutBoundary cutScope body) (.cutBoundary cutScope next)
          template output entryBindings tail reversed answerBindings before
          childAfter child
  | underChoice scope right inside inductionHypothesis =>
      exact
        .choiceProgress scope _ right _ [] _ _ inductionHypothesis
  | underCut scope inside inductionHypothesis =>
      exact
        .cutBoundaryProgress scope _ _ [] _ _ inductionHypothesis
  | underCatch handlerScope scope catcher handler entryBindings inside
      inductionHypothesis =>
      exact
        .catchProgress handlerScope scope _ _ catcher handler entryBindings
          [] .none _ _ inductionHypothesis
  | underCollection collectionScope callerScope outerCutScope template output
      entryBindings tail reversed inside inductionHypothesis =>
      have boundaryStep :
          RawStep _ (.cutBoundary outerCutScope _) [] .none _
            (.running (.cutBoundary outerCutScope _)) :=
        .cutBoundaryProgress outerCutScope _ _ [] _ _ inductionHypothesis
      exact
        .collectionProgress collectionScope callerScope
          (.cutBoundary outerCutScope _) (.cutBoundary outerCutScope _)
          template output entryBindings tail reversed [] .none _ _
          boundaryStep (by simp [Trace.AnswerFree])
  | underProduct scope tail inside inductionHypothesis =>
      exact
        .productProgress scope _ _ tail [] .none _ _ inductionHypothesis
          (by simp [Trace.AnswerFree])

/-- Exact occurrence-stack effect of one contextual answer: only the
innermost payload is extended, and the same older-cell tail appears literally
on both sides. -/
theorem cells_replace
    {before childAfter : Session} {search next : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    (answer :
      ActiveFindallAnswer before search childAfter next cell answerBindings) :
    ∃ cells,
      activeCollectionCells search = some (cell :: cells) ∧
        activeCollectionCells next =
          some (afterAnswer cell childAfter answerBindings :: cells) := by
  induction answer with
  | here before childAfter callerScope cutScope collectionScope body next
      template output entryBindings tail reversed answerBindings child
      beforeEmpty afterEmpty =>
      refine ⟨[], ?_, ?_⟩
      · simp [activeCollectionCells, beforeEmpty]
      · simp [activeCollectionCells, afterEmpty, afterAnswer,
          sourceCollectionCell]
  | underChoice scope right inside inductionHypothesis =>
      rcases inductionHypothesis with ⟨cells, beforeCells, afterCells⟩
      exact
        ⟨cells, by simpa [activeCollectionCells] using beforeCells,
          by simpa [activeCollectionCells] using afterCells⟩
  | underCut scope inside inductionHypothesis =>
      rcases inductionHypothesis with ⟨cells, beforeCells, afterCells⟩
      exact
        ⟨cells, by simpa [activeCollectionCells] using beforeCells,
          by simpa [activeCollectionCells] using afterCells⟩
  | underCatch handlerScope scope catcher handler entryBindings inside
      inductionHypothesis =>
      rcases inductionHypothesis with ⟨cells, beforeCells, afterCells⟩
      exact
        ⟨cells, by simpa [activeCollectionCells] using beforeCells,
          by simpa [activeCollectionCells] using afterCells⟩
  | underCollection collectionScope callerScope outerCutScope template output
      entryBindings tail reversed inside inductionHypothesis =>
      rcases inductionHypothesis with ⟨cells, beforeCells, afterCells⟩
      let outerCell :=
        sourceCollectionCell outerCutScope collectionScope callerScope
          template output entryBindings tail reversed
      refine ⟨cells ++ [outerCell], ?_, ?_⟩
      · simp [activeCollectionCells, beforeCells, outerCell]
      · simp [activeCollectionCells, afterCells, outerCell]
  | underProduct scope tail inside inductionHypothesis =>
      rcases inductionHypothesis with ⟨cells, beforeCells, afterCells⟩
      exact
        ⟨cells, by simpa [activeCollectionCells] using beforeCells,
          by simpa [activeCollectionCells] using afterCells⟩

/-- Positional occurrence agreement pins the exact head frame and remains
true after the payload-only source update; no older occurrence may change. -/
theorem occurrences_after
    {before childAfter : Session} {search next : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    (answer :
      ActiveFindallAnswer before search childAfter next cell answerBindings)
    {frame : FindallFrame} {remaining : List Frame}
    (agreement :
      CollectionOccurrenceAgrees search (.findall frame :: remaining)) :
    cell.AgreesFrame (.findall frame) ∧
      CollectionOccurrenceAgrees next (.findall frame :: remaining) := by
  rcases answer.cells_replace with ⟨cells, beforeCells, afterCells⟩
  rw [CollectionOccurrenceAgrees, beforeCells] at agreement
  cases agreement with
  | cons head tail =>
      constructor
      · exact head
      · rw [CollectionOccurrenceAgrees, afterCells]
        exact .cons
          ((afterAnswer_agreesFrame
            cell childAfter answerBindings (.findall frame)).mpr head)
          tail

end ActiveFindallAnswer

/-- Full open-state agreement for one live collector frontier.  Database/world
agreement and the ordered copy debt occupy the persistent component; the
three typed scope allocators remain exact and distinct. -/
abbrev CollectionOpenStateRelates
    (referenceCopiedRev : List Term) (executableRawRev : List Atom)
    (session : Session) (state : OpenConf) : Prop :=
  SessionRelatesOpenConf
    (CopyDebtFrontier referenceCopiedRev executableRawRev)
    ExactControlFrontiers session state

/-- Payload premises at the phase seam between the completed source child
answer and the answer-ready fine state.

`queryTemplate` prevents the executable query term and suspended frame
template from floating independently.  The state relation is intentionally at
`childAfter`, matching the literal `collectTemplate after` in
`RawStep.collectionAnswer`; the earlier child simulation remains open. -/
structure FindallAnswerPayloadAgrees
    (childAfter : Session) (cell : SourceCollectionCell)
    (before : OpenConf) (frame : FindallFrame)
    (answerBindings : Substitution) (binding : Subst) : Prop where
  framePayload : FindallFramePayloadAgrees cell frame
  queryTemplate : before.control.qterm = frame.template
  state :
    CollectionOpenStateRelates cell.reversed before.control.answers
      childAfter before
  materialized :
    TermAgrees (answerBindings.applyTerm cell.template)
      (PLeaTTa.subst binding before.control.qterm)
  encoding :
    EncodingInjectiveOn
      (copyVariables (answerBindings.applyTerm cell.template))
  rawBound :
    resolutionSeedHighWaterNames
        (PLeaTTa.subst binding before.control.qterm).vars ≤
      before.persistent.counter

namespace FindallAnswerPayloadAgrees

/-- One actual private answer successor extends the persistent copy debt and
preserves all three typed allocator relations. -/
theorem afterOpenState
    {childAfter : Session} {cell : SourceCollectionCell}
    {before : OpenConf} {frame : FindallFrame}
    {answerBindings : Substitution} {binding : Subst}
    (agreement :
      FindallAnswerPayloadAgrees childAfter cell before frame answerBindings
        binding) :
    CollectionOpenStateRelates
      (afterAnswer cell childAfter answerBindings).reversed
      (privateAnswerTarget before binding).control.answers
      (collectTemplate childAfter cell.template answerBindings).session
      (privateAnswerTarget before binding) := by
  have persistent :
      CollectionSessionRelates
        ((collectTemplate childAfter cell.template
          answerBindings).prepared.copied :: cell.reversed)
        (PLeaTTa.subst binding before.control.qterm ::
          before.control.answers)
        (collectTemplate childAfter cell.template answerBindings).session
        (privateAnswerTarget before binding).persistent := by
    apply CollectionSessionRelates.collect agreement.state.persistent
      cell.template answerBindings
      (PLeaTTa.subst binding before.control.qterm)
    · exact agreement.materialized
    · exact agreement.encoding
    · simp
    · simp
    · simpa using agreement.rawBound
  exact
    { persistent := by
        simpa [afterAnswer] using persistent
      cut := by
        simpa using agreement.state.cut
      exception := by
        simpa using agreement.state.exception
      collection := by
        simpa using agreement.state.collection }

/-- The source payload update cannot alter the suspended compiler payload. -/
theorem afterFramePayload
    {childAfter : Session} {cell : SourceCollectionCell}
    {before : OpenConf} {frame : FindallFrame}
    {answerBindings : Substitution} {binding : Subst}
    (agreement :
      FindallAnswerPayloadAgrees childAfter cell before frame answerBindings
        binding) :
    FindallFramePayloadAgrees
      (afterAnswer cell childAfter answerBindings) frame := by
  exact
    { template := by
        simpa [afterAnswer] using agreement.framePayload.template
      output := by
        simpa [afterAnswer] using agreement.framePayload.output
      tail := by
        simpa [afterAnswer] using agreement.framePayload.tail
      entryOutput := by
        simpa [afterAnswer] using agreement.framePayload.entryOutput
      entryTail := by
        simpa [afterAnswer] using agreement.framePayload.entryTail }

/-- The exact successor is immediately eligible for the already-proved exit
payload theorem.  This is the producer/rejoin seam, not an exit claim: the
generator may continue with more answers or diverge. -/
theorem afterExitPayload
    {childAfter : Session} {cell : SourceCollectionCell}
    {before : OpenConf} {frame : FindallFrame}
    {answerBindings : Substitution} {binding : Subst}
    (agreement :
      FindallAnswerPayloadAgrees childAfter cell before frame answerBindings
        binding) :
    FindallExitPayloadAgrees
      (collectTemplate childAfter cell.template answerBindings).session
      (afterAnswer cell childAfter answerBindings)
      (privateAnswerTarget before binding) frame := by
  exact
    { framePayload := agreement.afterFramePayload
      session := agreement.afterOpenState.persistent }

/-- Query-template identity survives the private answer step literally. -/
theorem afterQueryTemplate
    {childAfter : Session} {cell : SourceCollectionCell}
    {before : OpenConf} {frame : FindallFrame}
    {answerBindings : Substitution} {binding : Subst}
    (agreement :
      FindallAnswerPayloadAgrees childAfter cell before frame answerBindings
        binding) :
    (privateAnswerTarget before binding).control.qterm = frame.template := by
  simpa using
    (privateAnswerTarget_qterm before binding).trans agreement.queryTemplate

end FindallAnswerPayloadAgrees

/-- Exact one-answer source/fine correspondence at an active collector.

The source outer step and fine private step are both real constructors.  The
source child-step/fine-answer-ready correspondence is deliberately a premise
through `payload.state`; this theorem does not launder that earlier phase into
the oracle. -/
structure ContextualFindallAnswerRelates
    (prog : Prog) (gt : GroundingTable)
    (beforeSession : Session) (beforeSearch : Search)
    (childAfter : Session) (afterSearch : Search)
    (cell : SourceCollectionCell) (answerBindings : Substitution)
    (before after : OpenConf) (frame : FindallFrame)
    (remaining : List Frame) (binding : Subst) : Prop where
  sourceAnswer :
    ActiveFindallAnswer beforeSession beforeSearch childAfter afterSearch
      cell answerBindings
  sourceStep :
    RawStep beforeSession beforeSearch [] .none
      (collectTemplate childAfter cell.template answerBindings).session
      (.running afterSearch)
  frameHead : before.frames = .findall frame :: remaining
  fineHead : before.toConf.cur = some ([], binding)
  fineStep : DemandDrivenStep.Step prog gt before after
  fineTarget : after = privateAnswerTarget before binding
  frameIdentity : cell.AgreesFrame (.findall frame)
  occurrences :
    CollectionOccurrenceAgrees afterSearch after.frames
  framesPreserved : after.frames = before.frames
  scopesPreserved : after.scopes = before.scopes
  persistentPreserved : after.persistent = before.persistent
  queryTemplateBefore : before.control.qterm = frame.template
  queryTemplateAfter : after.control.qterm = frame.template
  rawPrepended :
    after.control.answers =
      PLeaTTa.subst binding before.control.qterm ::
        before.control.answers
  publicAnswersPreserved :
    publicAnswers after = publicAnswers before
  payloadBefore :
    FindallAnswerPayloadAgrees childAfter cell before frame answerBindings
      binding
  stateAfter :
    CollectionOpenStateRelates
      (afterAnswer cell childAfter answerBindings).reversed
      after.control.answers
      (collectTemplate childAfter cell.template answerBindings).session
      after
  exitPayloadAfter :
    FindallExitPayloadAgrees
      (collectTemplate childAfter cell.template answerBindings).session
      (afterAnswer cell childAfter answerBindings) after frame

/-- One contextual source `collectionAnswer` and one arbitrary-frontier fine
private answer step preserve the exact occurrence stack and produce the next
copy-debt/exit-payload relation. -/
theorem ActiveFindallAnswer.privateAnswer_correspondence
    {prog : Prog} {gt : GroundingTable}
    {beforeSession childAfter : Session}
    {beforeSearch afterSearch : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    (answer :
      ActiveFindallAnswer beforeSession beforeSearch childAfter afterSearch
        cell answerBindings)
    {before : OpenConf} {frame : FindallFrame}
    {remaining : List Frame} {binding : Subst}
    (frameHead : before.frames = .findall frame :: remaining)
    (fineHead : before.toConf.cur = some ([], binding))
    (beforeOccurrences :
      CollectionOccurrenceAgrees beforeSearch before.frames)
    (payload :
      FindallAnswerPayloadAgrees childAfter cell before frame answerBindings
        binding) :
    ContextualFindallAnswerRelates prog gt
      beforeSession beforeSearch childAfter afterSearch cell answerBindings
      before (privateAnswerTarget before binding) frame remaining binding := by
  have fine :=
    answer_is_one_private_step prog gt before frame remaining binding
      frameHead fineHead
  have aligned :
      cell.AgreesFrame (.findall frame) ∧
        CollectionOccurrenceAgrees afterSearch
          (.findall frame :: remaining) := by
    apply answer.occurrences_after
    simpa [frameHead] using beforeOccurrences
  exact
    { sourceAnswer := answer
      sourceStep := answer.sourceStep
      frameHead := frameHead
      fineHead := fineHead
      fineStep := fine.1
      fineTarget := rfl
      frameIdentity := aligned.1
      occurrences := by
        simpa [frameHead] using aligned.2
      framesPreserved := fine.2.1
      scopesPreserved := fine.2.2.1
      persistentPreserved := fine.2.2.2.1
      queryTemplateBefore := payload.queryTemplate
      queryTemplateAfter := payload.afterQueryTemplate
      rawPrepended := fine.2.2.2.2.2.1
      publicAnswersPreserved := fine.2.2.2.2.2.2
      payloadBefore := payload
      stateAfter := payload.afterOpenState
      exitPayloadAfter := payload.afterExitPayload }

/-- A mismatched live query term and suspended frame template cannot inhabit
the answer-payload relation, even if every other field were supplied. -/
theorem mismatched_query_template_rejected
    {childAfter : Session} {cell : SourceCollectionCell}
    {before : OpenConf} {frame : FindallFrame}
    {answerBindings : Substitution} {binding : Subst}
    (different : before.control.qterm ≠ frame.template) :
    ¬ FindallAnswerPayloadAgrees childAfter cell before frame answerBindings
      binding := by
  intro agreement
  exact different agreement.queryTemplate

/-- One private answer prepends to the reverse-discovery accumulator.  The
same two closed values in append order are rejected, so a count-only or
commutative reading cannot satisfy the fine transition. -/
theorem wrong_raw_append_rejected :
    let control : Control :=
      { cur := some ([], [])
        alts := []
        qterm := .gnd (.int 2)
        answers := [.gnd (.int 1)] }
    let state : OpenConf :=
      { persistent := { world := {}, counter := 0 }
        control := control }
    (privateAnswerTarget state []).control.answers =
        [.gnd (.int 2), .gnd (.int 1)] ∧
      (privateAnswerTarget state []).control.answers ≠
        [.gnd (.int 1), .gnd (.int 2)] := by
  dsimp
  constructor
  · simp [PLeaTTa.subst, PLeaTTa.substN]
  · intro equality
    have := congrArg List.head? equality
    simp at this

/-- Using the frame-entry high-water after the generator has allocated a
fresh variable changes the actual copied payload.  The real child-post
session starts at `1` and produces generated `1`; a stale session starts at
`0` and collides at generated `0`. -/
theorem stale_pre_session_copy_rejected :
    let stale : Session := {}
    let childAfter : Session :=
      { resolver := { database := .empty, nextFresh := 1 } }
    let template : Term := .variable (.source "y")
    (collectTemplate stale template []).prepared.copied =
        .variable (.generated 0) ∧
      (collectTemplate childAfter template []).prepared.copied =
        .variable (.generated 1) ∧
      (collectTemplate stale template []).prepared.copied ≠
        (collectTemplate childAfter template []).prepared.copied := by
  simp [collectTemplate, prepareTermCopy, Copy.copyTerm, Copy.copyRename,
    Copy.copyVariables, termVariables, variablesGeneratedCeiling,
    logicVarGeneratedCeiling, substitutionVariables,
    Substitution.applyTerm, Term.renameVariables, List.eraseDups_cons,
    List.idxOf, List.findIdx_cons]

/-- A concrete depth-two collector consumes one inner generator answer
without touching the outer reverse-discovery payload.  The final inequality
shows that applying the same collection update to the outer cell would be a
genuine, observable second collection rather than a harmless restatement. -/
theorem nested_answer_only_updates_innermost_cell :
    let session : Session := {}
    let answerBindings : Substitution :=
      [(.source "x", .integer 1)]
    let innerCell :=
      sourceCollectionCell 2 ⟨2⟩ 1 (.variable (.source "x"))
        (.integer 8) [] [] []
    let outerCell :=
      sourceCollectionCell 1 ⟨1⟩ 0 (.integer 2)
        (.integer 9) [] [] [.integer 7]
    let beforeSearch : Search :=
      .collectionBoundary ⟨1⟩ 0
        (.cutBoundary 1
          (.collectionBoundary ⟨2⟩ 1
            (.cutBoundary 2 (.task 2 [] answerBindings))
            (.variable (.source "x")) (.integer 8) [] [] []))
        (.integer 2) (.integer 9) [] [] [.integer 7]
    let afterSearch : Search :=
      .collectionBoundary ⟨1⟩ 0
        (.cutBoundary 1
          (.collectionBoundary ⟨2⟩ 1
            (.cutBoundary 2 .done)
            (.variable (.source "x")) (.integer 8) [] []
            [(collectTemplate session (.variable (.source "x"))
              answerBindings).prepared.copied]))
        (.integer 2) (.integer 9) [] [] [.integer 7]
    ActiveFindallAnswer session beforeSearch session afterSearch innerCell
        answerBindings ∧
      activeCollectionCells beforeSearch =
        some [innerCell, outerCell] ∧
      activeCollectionCells afterSearch =
        some [afterAnswer innerCell session answerBindings, outerCell] ∧
      (afterAnswer outerCell session answerBindings).reversed ≠
        outerCell.reversed := by
  dsimp
  have inner :
      ActiveFindallAnswer ({} : Session)
        (.collectionBoundary ⟨2⟩ 1
          (.cutBoundary 2
            (.task 2 [] [(.source "x", .integer 1)]))
          (.variable (.source "x")) (.integer 8) [] [] [])
        ({} : Session)
        (.collectionBoundary ⟨2⟩ 1 (.cutBoundary 2 .done)
          (.variable (.source "x")) (.integer 8) [] []
          [(collectTemplate ({} : Session) (.variable (.source "x"))
            [(.source "x", .integer 1)]).prepared.copied])
        (sourceCollectionCell 2 ⟨2⟩ 1 (.variable (.source "x"))
          (.integer 8) [] [] [])
        [(.source "x", .integer 1)] := by
    apply ActiveFindallAnswer.here
    · exact
        .cutBoundaryProgress 2 _ _ [.answer
          [(.source "x", .integer 1)]] _ _
          (.taskAnswer 2 [(.source "x", .integer 1)] ({} : Session))
    · rfl
    · rfl
  have nested :
      ActiveFindallAnswer ({} : Session)
        (.collectionBoundary ⟨1⟩ 0
          (.cutBoundary 1
            (.collectionBoundary ⟨2⟩ 1
              (.cutBoundary 2
                (.task 2 [] [(.source "x", .integer 1)]))
              (.variable (.source "x")) (.integer 8) [] [] []))
          (.integer 2) (.integer 9) [] [] [.integer 7])
        ({} : Session)
        (.collectionBoundary ⟨1⟩ 0
          (.cutBoundary 1
            (.collectionBoundary ⟨2⟩ 1 (.cutBoundary 2 .done)
              (.variable (.source "x")) (.integer 8) [] []
              [(collectTemplate ({} : Session)
                (.variable (.source "x"))
                [(.source "x", .integer 1)]).prepared.copied]))
          (.integer 2) (.integer 9) [] [] [.integer 7])
        (sourceCollectionCell 2 ⟨2⟩ 1 (.variable (.source "x"))
          (.integer 8) [] [] [])
        [(.source "x", .integer 1)] := by
    exact
      .underCollection ⟨1⟩ 0 1 (.integer 2) (.integer 9) [] []
        [.integer 7] inner
  refine ⟨nested, rfl, rfl, ?_⟩
  intro changed
  have lengths := congrArg List.length changed
  simp [sourceCollectionCell] at lengths

/-- Fully closed inhabitance of the actual producer path:

* source `taskAnswer` is propagated through the generator cut boundary and
  consumed by one real `collectionAnswer`;
* fine `Step.answer` runs under the exact live `FindallFrame`;
* the variable template is materialized as integer `1`;
* the post-state carries one ordered copy debt and the proved exit payload.
-/
theorem ground_direct_answer_correspondence_inhabited
    (prog : Prog) (gt : GroundingTable) :
    let sourceBindings : Substitution :=
      [(.source "x", .integer 1)]
    let fineBinding : Subst := [("x", .gnd (.int 1))]
    let session : Session := {}
    let cell :=
      sourceCollectionCell 1 ⟨1⟩ 0 (.variable (.source "x"))
        (.integer 9) [] [] []
    let beforeSearch : Search :=
      .collectionBoundary ⟨1⟩ 0
        (.cutBoundary 1 (.task 1 [] sourceBindings))
        (.variable (.source "x")) (.integer 9) [] [] []
    let afterSearch : Search :=
      .collectionBoundary ⟨1⟩ 0 (.cutBoundary 1 .done)
        (.variable (.source "x")) (.integer 9) [] []
        [(collectTemplate session (.variable (.source "x"))
          sourceBindings).prepared.copied]
    let control : Control :=
      { cur := some ([], fineBinding)
        alts := []
        qterm := .var "x"
        answers := [] }
    let frame : FindallFrame :=
      { preCut := 1
        preCollection := 1
        outer := control
        template := .var "x"
        result := .gnd (.int 9)
        rest := []
        binding := [] }
    let before : OpenConf :=
      { persistent := { world := {}, counter := 0 }
        control := control
        frames := [.findall frame]
        scopes := {} }
    ContextualFindallAnswerRelates prog gt
      session beforeSearch session afterSearch cell sourceBindings
      before (privateAnswerTarget before fineBinding) frame [] fineBinding := by
  dsimp
  have sourceAnswer :
      ActiveFindallAnswer ({} : Session)
        (.collectionBoundary ⟨1⟩ 0
          (.cutBoundary 1
            (.task 1 [] [(.source "x", .integer 1)]))
          (.variable (.source "x")) (.integer 9) [] [] [])
        ({} : Session)
        (.collectionBoundary ⟨1⟩ 0 (.cutBoundary 1 .done)
          (.variable (.source "x")) (.integer 9) [] []
          [(collectTemplate ({} : Session) (.variable (.source "x"))
            [(.source "x", .integer 1)]).prepared.copied])
        (sourceCollectionCell 1 ⟨1⟩ 0 (.variable (.source "x"))
          (.integer 9) [] [] [])
        [(.source "x", .integer 1)] := by
    apply ActiveFindallAnswer.here
    · exact
        .cutBoundaryProgress 1 _ _ [.answer
          [(.source "x", .integer 1)]] _ _
          (.taskAnswer 1 [(.source "x", .integer 1)] ({} : Session))
    · rfl
    · rfl
  have occurrences :
      CollectionOccurrenceAgrees
        (.collectionBoundary ⟨1⟩ 0
          (.cutBoundary 1
            (.task 1 [] [(.source "x", .integer 1)]))
          (.variable (.source "x")) (.integer 9) [] [] [])
        [.findall
          { preCut := 1
            preCollection := 1
            outer :=
              { cur := some ([], [("x", .gnd (.int 1))])
                alts := []
                qterm := .var "x"
                answers := [] }
            template := .var "x"
            result := .gnd (.int 9)
            rest := []
            binding := [] }] := by
    simp [CollectionOccurrenceAgrees, activeCollectionCells,
      SourceCollectionCell.AgreesFrame, sourceCollectionCell]
  have payload :
      FindallAnswerPayloadAgrees ({} : Session)
        (sourceCollectionCell 1 ⟨1⟩ 0 (.variable (.source "x"))
          (.integer 9) [] [] [])
        { persistent := { world := {}, counter := 0 }
          control :=
            { cur := some ([], [("x", .gnd (.int 1))])
              alts := []
              qterm := .var "x"
              answers := [] }
          frames :=
            [.findall
              { preCut := 1
                preCollection := 1
                outer :=
                  { cur := some ([], [("x", .gnd (.int 1))])
                    alts := []
                    qterm := .var "x"
                    answers := [] }
                template := .var "x"
                result := .gnd (.int 9)
                rest := []
                binding := [] }]
          scopes := {} }
        { preCut := 1
          preCollection := 1
          outer :=
            { cur := some ([], [("x", .gnd (.int 1))])
              alts := []
              qterm := .var "x"
              answers := [] }
          template := .var "x"
          result := .gnd (.int 9)
          rest := []
          binding := [] }
        [(.source "x", .integer 1)]
        [("x", .gnd (.int 1))] := by
    exact
      { framePayload :=
          { template := TermAgrees.sourceVariable "x"
            output := TermAgrees.integer 9
            tail := GoalsAgree.nil
            entryOutput := by
              simpa [sourceCollectionCell] using (TermAgrees.integer 9)
            entryTail := by
              simpa [sourceCollectionCell, substCompiledGoals] using
                (GoalsAgree.nil : GoalsAgree [] []) }
        queryTemplate := rfl
        state :=
          { persistent :=
              PrologStateBridge.empty_session_relates
                (CopyDebtFrontier [] [])
                (CollectionCopyFrontier.empty 0 0)
            cut := rfl
            exception := rfl
            collection := rfl }
        materialized := by
          simpa [sourceCollectionCell, Substitution.applyTerm,
            Term.instantiateOne, PLeaTTa.subst, PLeaTTa.substN,
            Metta.Subst.lookup] using
            (TermAgrees.integer 1)
        encoding := by
          intro left right leftMember rightMember same
          simp [sourceCollectionCell, copyVariables, termVariables,
            Substitution.applyTerm, Term.instantiateOne] at leftMember
        rawBound := by
          simp [PLeaTTa.subst, PLeaTTa.substN, Metta.Subst.lookup,
            Metta.Atom.vars, resolutionSeedHighWaterNames] }
  exact
    sourceAnswer.privateAnswer_correspondence rfl rfl occurrences payload

end PLeaTTa.PrologFindallAnswerBridge
