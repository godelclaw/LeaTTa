-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologFindallAnswerExitBridge
Purpose: Compose one terminal local findall answer with certified bounded
  collection copying and the exact source/fine rejoin.
Trusted boundary: none
Main exports: ActiveFindallTerminalAnswerResourceAgrees,
  ContextualTerminalFindallAnswerExitRelates,
  ContextualFindallAnswerRelates.terminalExit
-/
import PLeaTTa.Proofs.PrologAnswerPullClassificationBridge

namespace PLeaTTa.PrologFindallAnswerExitBridge

open Metta (Atom GroundingTable Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PrologFindallCopyBridge
open PrologFindallFrameZipperBridge
open PrologFindallExitBridge
open PrologFindallExitPayloadBridge
open PrologFindallAnswerBridge
open PrologFindallAnswerResourceBridge
open PrologAnswerPullClassificationBridge
open PrologAnswerResourceBridge
open PrologProductResourceContextBridge
open DemandDrivenStep

/-!
The fine answer rule records one private generator answer and eagerly pulls
the next executable alternative in the same sealed step.  The general case
therefore still needs the source catch-up relation tracked by
`BISIM.answer_backtrack_phase`.

This module closes the exact terminal subcase: the eager pull exhausts the
fine alternative bank, while one joint source certificate couples the answer
to the actual `ActiveFindallExit` of that answer's literal successor.  No
terminality or exhaustion is inferred from an answer list; both follow from
the real source control relation and the exact machine pull classifier.
-/

/-- Two consecutive source steps at one and the same resource-certified local
collector: first one private generator answer, then exhaustion of the literal
post-answer generator search.

The direct constructor shares `next` between the answer producer and the
completion premise.  Every contextual constructor transports both steps
together through one wrapper.  Hence a nested collector with extensionally
equal metadata cannot supply the exit for a different answered collector. -/
inductive ActiveFindallTerminalAnswerResourceAgrees
    (alpha : List (LogicVar × String)) :
    Session -> Search -> Session -> Search -> Session -> Search ->
      SourceCollectionCell -> Substitution ->
      List RetainedAlternativeSegment ->
      List RetainedAlternativeSegment ->
      List PLeaTTa.Alt -> List PLeaTTa.Alt -> Prop where
  | here (before childAfter finalSession : Session)
      (callerScope cutScope : CutScopeId)
      (collectionScope : CollectionScopeId)
      (body next : Search) (template output : Term)
      (entryBindings : Substitution)
      (tail : List PeTTaSpec.PrologCore.Goal)
      (reversed : List Term) (answerBindings : Substitution)
      {beforeResources afterResources : List RetainedAlternativeSegment}
      {beforeAlts afterAlts : List PLeaTTa.Alt}
      (answerChild :
        ExactFindallBodyAnswerProducerResourceAgrees alpha before childAfter
          body next
          answerBindings beforeResources afterResources beforeAlts afterAlts)
      (exitChild :
        RawStep
          (collectTemplate childAfter template answerBindings).session
          (.cutBoundary cutScope next) [.completed] .none finalSession
          (.terminal .completed)) :
      ActiveFindallTerminalAnswerResourceAgrees alpha before
        (.collectionBoundary collectionScope callerScope
          (.cutBoundary cutScope body) template output entryBindings tail
          reversed)
        childAfter
        (.collectionBoundary collectionScope callerScope
          (.cutBoundary cutScope next) template output entryBindings tail
          ((collectTemplate childAfter template
            answerBindings).prepared.copied :: reversed))
        finalSession
        (.task callerScope
          (.unify output
            (.list
              ((collectTemplate childAfter template
                answerBindings).prepared.copied :: reversed).reverse none) ::
              tail)
          entryBindings)
        (sourceCollectionCell cutScope collectionScope callerScope template
          output entryBindings tail reversed)
        answerBindings beforeResources afterResources beforeAlts afterAlts
  | underChoice (scope : CutScopeId) (right : Search)
      {before childAfter finalSession : Session}
      {left answered rejoined : Search}
      {cell : SourceCollectionCell} {answerBindings : Substitution}
      {beforeResources afterResources : List RetainedAlternativeSegment}
      {beforeAlts afterAlts : List PLeaTTa.Alt}
      (inside :
        ActiveFindallTerminalAnswerResourceAgrees alpha before left childAfter
          answered finalSession rejoined cell answerBindings beforeResources
          afterResources beforeAlts afterAlts) :
      ActiveFindallTerminalAnswerResourceAgrees alpha before
        (.choice scope left right) childAfter (.choice scope answered right)
        finalSession (.choice scope rejoined right) cell answerBindings
        beforeResources afterResources beforeAlts afterAlts
  | underCut (scope : CutScopeId)
      {before childAfter finalSession : Session}
      {body answered rejoined : Search}
      {cell : SourceCollectionCell} {answerBindings : Substitution}
      {beforeResources afterResources : List RetainedAlternativeSegment}
      {beforeAlts afterAlts : List PLeaTTa.Alt}
      (inside :
        ActiveFindallTerminalAnswerResourceAgrees alpha before body childAfter
          answered finalSession rejoined cell answerBindings beforeResources
          afterResources beforeAlts afterAlts) :
      ActiveFindallTerminalAnswerResourceAgrees alpha before
        (.cutBoundary scope body) childAfter (.cutBoundary scope answered)
        finalSession (.cutBoundary scope rejoined) cell answerBindings
        beforeResources afterResources beforeAlts afterAlts
  | underCatch (handlerScope : ExceptionScopeId) (scope : CutScopeId)
      (catcher : Term) (handler : PeTTaSpec.PrologCore.Goal)
      (entryBindings : Substitution)
      {before childAfter finalSession : Session}
      {body answered rejoined : Search}
      {cell : SourceCollectionCell} {answerBindings : Substitution}
      {beforeResources afterResources : List RetainedAlternativeSegment}
      {beforeAlts afterAlts : List PLeaTTa.Alt}
      (inside :
        ActiveFindallTerminalAnswerResourceAgrees alpha before body childAfter
          answered finalSession rejoined cell answerBindings beforeResources
          afterResources beforeAlts afterAlts) :
      ActiveFindallTerminalAnswerResourceAgrees alpha before
        (.catchBoundary handlerScope scope body catcher handler entryBindings)
        childAfter
        (.catchBoundary handlerScope scope answered catcher handler
          entryBindings)
        finalSession
        (.catchBoundary handlerScope scope rejoined catcher handler
          entryBindings)
        cell answerBindings beforeResources afterResources beforeAlts afterAlts
  | underCollection (collectionScope : CollectionScopeId)
      (callerScope outerCutScope : CutScopeId)
      (template output : Term) (entryBindings : Substitution)
      (tail : List PeTTaSpec.PrologCore.Goal) (reversed : List Term)
      {before childAfter finalSession : Session}
      {body answered rejoined : Search}
      {cell : SourceCollectionCell} {answerBindings : Substitution}
      {beforeResources afterResources : List RetainedAlternativeSegment}
      {beforeAlts afterAlts : List PLeaTTa.Alt}
      (inside :
        ActiveFindallTerminalAnswerResourceAgrees alpha before body childAfter
          answered finalSession rejoined cell answerBindings beforeResources
          afterResources beforeAlts afterAlts) :
      ActiveFindallTerminalAnswerResourceAgrees alpha before
        (.collectionBoundary collectionScope callerScope
          (.cutBoundary outerCutScope body) template output entryBindings tail
          reversed)
        childAfter
        (.collectionBoundary collectionScope callerScope
          (.cutBoundary outerCutScope answered) template output entryBindings
          tail reversed)
        finalSession
        (.collectionBoundary collectionScope callerScope
          (.cutBoundary outerCutScope rejoined) template output entryBindings
          tail reversed)
        cell answerBindings beforeResources afterResources beforeAlts afterAlts
  | underProduct (scope : CutScopeId)
      (tail : List PeTTaSpec.PrologCore.Goal)
      {before childAfter finalSession : Session}
      {head answered rejoined : Search}
      {cell : SourceCollectionCell} {answerBindings : Substitution}
      {beforeResources afterResources : List RetainedAlternativeSegment}
      {beforeAlts afterAlts : List PLeaTTa.Alt}
      (inside :
        ActiveFindallTerminalAnswerResourceAgrees alpha before head childAfter
          answered finalSession rejoined cell answerBindings beforeResources
          afterResources beforeAlts afterAlts) :
      ActiveFindallTerminalAnswerResourceAgrees alpha before
        (.product scope head tail) childAfter (.product scope answered tail)
        finalSession (.product scope rejoined tail) cell answerBindings
        beforeResources afterResources beforeAlts afterAlts

namespace ActiveFindallTerminalAnswerResourceAgrees

/-- Forget only the following completion step. -/
theorem toAnswer
    {alpha : List (LogicVar × String)}
    {before childAfter finalSession : Session}
    {search answered rejoined : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (pair :
      ActiveFindallTerminalAnswerResourceAgrees alpha before search childAfter
        answered finalSession rejoined cell answerBindings beforeResources
        afterResources beforeAlts afterAlts) :
    ActiveFindallAnswerResourceAgrees alpha before search childAfter answered
      cell answerBindings beforeResources afterResources beforeAlts
      afterAlts := by
  induction pair with
  | here before childAfter finalSession callerScope cutScope collectionScope
      body next template output entryBindings tail reversed answerBindings
      answerChild exitChild =>
      exact ActiveFindallAnswerResourceAgrees.here before childAfter
        callerScope cutScope collectionScope body next template output
        entryBindings tail reversed answerBindings answerChild
  | underChoice scope right _ ih => exact .underChoice scope right ih
  | underCut scope _ ih => exact .underCut scope ih
  | underCatch handlerScope scope catcher handler entryBindings _ ih =>
      exact .underCatch handlerScope scope catcher handler entryBindings ih
  | underCollection collectionScope callerScope outerCutScope template output
      entryBindings tail reversed _ ih =>
      exact .underCollection collectionScope callerScope outerCutScope template
        output entryBindings tail reversed ih
  | underProduct scope tail _ ih => exact .underProduct scope tail ih

/-- Forget only the preceding answer proof.  The resulting exit is indexed by
the exact post-answer cell produced by `toAnswer`. -/
theorem toExit
    {alpha : List (LogicVar × String)}
    {before childAfter finalSession : Session}
    {search answered rejoined : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (pair :
      ActiveFindallTerminalAnswerResourceAgrees alpha before search childAfter
        answered finalSession rejoined cell answerBindings beforeResources
        afterResources beforeAlts afterAlts) :
    ActiveFindallExit
      (collectTemplate childAfter cell.template answerBindings).session
      answered finalSession rejoined
      (afterAnswer cell childAfter answerBindings) := by
  induction pair with
  | here before childAfter finalSession callerScope cutScope collectionScope
      body next template output entryBindings tail reversed answerBindings
      answerChild exitChild =>
      simpa [afterAnswer, sourceCollectionCell] using
        (ActiveFindallExit.here
          (collectTemplate childAfter template answerBindings).session
          finalSession callerScope cutScope collectionScope next template
          output entryBindings tail
          ((collectTemplate childAfter template
            answerBindings).prepared.copied :: reversed)
          exitChild)
  | underChoice scope right _ ih => exact .underChoice scope right ih
  | underCut scope _ ih => exact .underCut scope ih
  | underCatch handlerScope scope catcher handler entryBindings _ ih =>
      exact .underCatch handlerScope scope catcher handler entryBindings ih
  | underCollection collectionScope callerScope outerCutScope template output
      entryBindings tail reversed _ ih =>
      exact .underCollection collectionScope callerScope outerCutScope template
        output entryBindings tail reversed ih
  | underProduct scope tail _ ih => exact .underProduct scope tail ih

/-- Immediate completion of the shared literal successor forces every region
owned by the answer origin to fall through to the supplied older bank. -/
theorem pull_eq_base
    {alpha : List (LogicVar × String)}
    {before childAfter finalSession : Session}
    {search answered rejoined : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (pair :
      ActiveFindallTerminalAnswerResourceAgrees alpha before search childAfter
        answered finalSession rejoined cell answerBindings beforeResources
        afterResources beforeAlts afterAlts) :
    PLeaTTa.pullAux beforeAlts = PLeaTTa.pullAux afterAlts := by
  induction pair with
  | here before childAfter finalSession callerScope cutScope collectionScope
      body next template output entryBindings tail reversed answerBindings
      answerChild exitChild =>
      rcases answerChild.bodyProducer.originAgreement with
        ⟨_, _, agreement⟩
      cases exitChild with
      | cutBoundaryComplete _ _ _ _ child =>
          exact
            (PrologAnswerPullClassificationBridge.AnswerOriginResourceAgrees.fallsThrough_of_next_completed
              agreement child).pullAux_eq
  | underChoice _ _ _ ih => exact ih
  | underCut _ _ ih => exact ih
  | underCatch _ _ _ _ _ _ ih => exact ih
  | underCollection _ _ _ _ _ _ _ _ _ ih => exact ih
  | underProduct _ _ _ ih => exact ih

/-- The coupled certificate always denotes two distinct source transitions:
one private answer followed by one completion of that answer's literal
successor.  Contextual wrappers lift both transitions separately. -/
theorem toStepsN
    {alpha : List (LogicVar × String)}
    {before childAfter finalSession : Session}
    {search answered rejoined : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (pair :
      ActiveFindallTerminalAnswerResourceAgrees alpha before search childAfter
        answered finalSession rejoined cell answerBindings beforeResources
        afterResources beforeAlts afterAlts) :
    PeTTaSpec.PrologCore.GoalSemantics.StepsN 2
      (.running before search) [] (.running finalSession rejoined) := by
  have first :
      Transition (.running before search) []
        (.running
          (collectTemplate childAfter cell.template answerBindings).session
          answered) :=
    .ordinary _ [] _ _ _ pair.toAnswer.weak.sourceStep
  have second :
      Transition
        (.running
          (collectTemplate childAfter cell.template answerBindings).session
          answered)
        [] (.running finalSession rejoined) :=
    .ordinary _ [] _ _ _ pair.toExit.sourceStep
  simpa using
    (PeTTaSpec.PrologCore.GoalSemantics.StepsN.succ 1 _ _ _ [] [] first
      (PeTTaSpec.PrologCore.GoalSemantics.StepsN.succ 0 _ _ _ [] [] second
        (.zero _)))

end ActiveFindallTerminalAnswerResourceAgrees

/-- Replace only the live executable alternative bank of an open state. -/
def replaceAlternativeBank (state : OpenConf) (alts : List PLeaTTa.Alt) :
    OpenConf :=
  { state with control := { state.control with alts := alts } }

namespace FindallAnswerPayloadAgrees

/-- The answer payload seam is independent of the scheduler's alternative
bank.  Persistent state, all typed scope frontiers, the ready head, query,
valuation, and copy bound are retained literally; only `control.alts` changes.

This transport does not describe an answer step and makes no claim about the
post-pull bank. -/
theorem replaceAlternativeBank
    {childAfter : Session} {cell : SourceCollectionCell}
    {before : OpenConf} {frame : FindallFrame}
    {answerBindings : Substitution} {binding : Subst}
    (agreement :
      FindallAnswerPayloadAgrees childAfter cell before frame answerBindings
        binding)
    (alts : List PLeaTTa.Alt) :
    FindallAnswerPayloadAgrees childAfter cell
      (PLeaTTa.PrologFindallAnswerExitBridge.replaceAlternativeBank before alts)
      frame answerBindings binding := by
  rcases agreement with
    ⟨framePayload, queryTemplate, state, answerReady, encoding, rawBound⟩
  rcases answerReady with
    ⟨alpha, support, canonical, referenceBase, readyPersistent, fineHead,
      data, template, templateSupported⟩
  exact
    { framePayload := framePayload
      queryTemplate := queryTemplate
      state :=
        { persistent := state.persistent
          cut := state.cut
          exception := state.exception
          collection := state.collection }
      answerReady :=
        ⟨alpha, support, canonical, referenceBase, readyPersistent, fineHead,
          data, template, templateSupported⟩
      encoding := encoding
      rawBound := rawBound }

end FindallAnswerPayloadAgrees

/-- The established private-answer step is also one direct transition in the
additive copy lane.  It cannot use the atomic collector-exit constructor:
the source state has an empty goal head, not a `findall` head. -/
theorem answer_is_one_private_copy_step
    (prog : Prog) (gt : GroundingTable) (state : OpenConf)
    (binding : Subst)
    (head : state.toConf.cur = some ([], binding)) :
    CopyStep prog gt (.open state)
      (.open (privateAnswerTarget state binding)) := by
  have notFindall : ¬ findallRunHead state.toConf := by
    intro findallHead
    rcases findallHead with
      ⟨template, sub, result, rest, otherBinding, conflict⟩
    rw [head] at conflict
    cases conflict
  simpa [privateAnswerTarget] using
    (CopyStep.ordinary state (answerSuccessor state.toConf binding)
      notFindall (PLeaTTa.Step.answer state.toConf binding head))

/-- Exact source and additive-fine segment for a private answer that is the
last answer of its active local collector.

The post-answer source cell and fine state occur literally in every field.
The source takes two transitions: collect the answer, then complete the
collector.  The fine lane takes one answer transition, one transfer, exactly
one copy transition per accumulated answer, and one finish transition. -/
structure ContextualTerminalFindallAnswerExitRelates
    (alpha : List (LogicVar × String))
    (prog : Prog) (gt : GroundingTable)
    (beforeSession childAfter finalSession : Session)
    (beforeSearch answeredSearch rejoinedSearch : Search)
    (cell : SourceCollectionCell) (answerBindings : Substitution)
    (before answered rejoined : OpenConf)
    (frame : FindallFrame) (remaining : List Frame)
    (binding : Subst)
    (beforeResources afterResources : List RetainedAlternativeSegment) :
    Prop where
  source :
    ActiveFindallTerminalAnswerResourceAgrees alpha beforeSession beforeSearch
      childAfter answeredSearch finalSession rejoinedSearch cell answerBindings
      beforeResources afterResources before.control.alts []
  answer :
    ContextualFindallAnswerResourceRelates alpha prog gt beforeSession
      beforeSearch childAfter answeredSearch cell answerBindings before answered
      frame remaining binding beforeResources afterResources []
  fineTerminal : PLeaTTa.Terminal answered.toConf
  exit :
    ContextualFindallExitPayloadRelates prog gt
      (collectTemplate childAfter cell.template answerBindings).session
      answeredSearch finalSession rejoinedSearch
      (afterAnswer cell childAfter answerBindings)
      answered rejoined frame remaining
  answerCopyStep :
    CopyStep prog gt (.open before) (.open answered)
  additiveExit :
    CopyStepsN prog gt
      ((afterAnswer cell childAfter answerBindings).reversed.length + 2)
      (.open answered) (.open rejoined)
  sourceRun :
    PeTTaSpec.PrologCore.GoalSemantics.StepsN 2
      (.running beforeSession beforeSearch) []
      (.running finalSession rejoinedSearch)
  fineRun :
    CopyStepsN prog gt
      ((afterAnswer cell childAfter answerBindings).reversed.length + 3)
      (.open before) (.open rejoined)

namespace PullOutcomeAgrees

/-- If the bank supplying an exact pull outcome is exhausted, the indexed
post-pull control is terminal.  A selected outcome contradicts the same
literal `pullAux` equation. -/
theorem terminal_fields_of_pull_none
    {beforeAlts : List PLeaTTa.Alt}
    {cur : Option (List PLeaTTa.Goal × Subst)}
    {afterAlts : List PLeaTTa.Alt}
    (outcome : PullOutcomeAgrees beforeAlts cur afterAlts)
    (empty : PLeaTTa.pullAux beforeAlts = none) :
    cur = none ∧ afterAlts = [] := by
  cases outcome with
  | exhausted _ => exact ⟨rfl, rfl⟩
  | selected goals binding rest selected =>
      rw [empty] at selected
      cases selected

end PullOutcomeAgrees

namespace ContextualFindallCollectionAnswerRelates

/-- The collection-only state relation already determines the exact
post-answer bag length used by the additive exit.  No suspended caller payload
or exit-ready packet is needed for this ordered-copy invariant. -/
theorem postAnswerBagLength
    {prog : Prog} {gt : GroundingTable}
    {beforeSession childAfter : Session}
    {beforeSearch answeredSearch : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {before answered : OpenConf} {frame : FindallFrame}
    {remaining : List Frame} {binding : Subst}
    (related :
      ContextualFindallCollectionAnswerRelates prog gt beforeSession
        beforeSearch childAfter answeredSearch cell answerBindings before
        answered frame remaining binding) :
    (afterAnswer cell childAfter answerBindings).reversed.length =
      answered.control.answerValues.length := by
  have debtLength :
      (afterAnswer cell childAfter answerBindings).reversed.length =
        answered.control.answers.length :=
    List.Forall₂.length_eq related.stateAfter.persistent.fresh.debt
  have reverseLength :
      answered.control.answers.length =
        answered.control.answerValues.length := by
    calc
      answered.control.answers.length =
          answered.control.answers.reverse.length :=
        (@List.length_reverse _ answered.control.answers).symm
      _ = answered.control.answerValues.length :=
        congrArg List.length
          (rawAnswerAccumulator_sourceOrder answered.control)
  exact debtLength.trans reverseLength

end ContextualFindallCollectionAnswerRelates

namespace ContextualFindallAnswerRelates

/-- The copy-debt relation determines the exact post-answer bag length used
by the additive exit.  This is derived from pointwise ordered agreement, not
an independently supplied counter. -/
theorem postAnswerBagLength
    {prog : Prog} {gt : GroundingTable}
    {beforeSession childAfter : Session}
    {beforeSearch answeredSearch : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {before answered : OpenConf} {frame : FindallFrame}
    {remaining : List Frame} {binding : Subst}
    (related :
      ContextualFindallAnswerRelates prog gt beforeSession beforeSearch
        childAfter answeredSearch cell answerBindings before answered frame
        remaining binding) :
    (afterAnswer cell childAfter answerBindings).reversed.length =
      answered.control.answerValues.length :=
  PLeaTTa.PrologFindallAnswerExitBridge.ContextualFindallCollectionAnswerRelates.postAnswerBagLength
    related.collection

/-- Compose one jointly certified terminal private answer with the bounded
certified copy phase.

The source certificate shares the literal post-answer child between answer
and exit.  `exhaustedOlderAlts` names the still-narrow empty older-bank premise
explicitly.  Given it, the fine terminal state is derived from source
exhaustion and the exact machine pull classifier; it is never supplied
independently.  A nonempty older bank still belongs to
`BISIM.answer_backtrack_phase`.

[SPEC metta.pl:251-256; SWI:findall/3] -/
theorem terminalExit
    {alpha : List (LogicVar × String)}
    {prog : Prog} {gt : GroundingTable}
    {beforeSession childAfter finalSession : Session}
    {beforeSearch answeredSearch rejoinedSearch : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {before : OpenConf} {frame : FindallFrame}
    {remaining : List Frame} {binding : Subst}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {afterAlts : List PLeaTTa.Alt}
    (source :
      ActiveFindallTerminalAnswerResourceAgrees alpha beforeSession
        beforeSearch childAfter answeredSearch finalSession rejoinedSearch cell
        answerBindings beforeResources afterResources before.control.alts
        afterAlts)
    (exhaustedOlderAlts : afterAlts = [])
    (beforeFrameHead : before.frames = .findall frame :: remaining)
    (beforeOccurrences :
      CollectionOccurrenceAgrees beforeSearch before.frames)
    (payloadBefore :
      FindallAnswerPayloadAgrees childAfter cell before frame answerBindings
        binding) :
    ContextualTerminalFindallAnswerExitRelates alpha prog gt beforeSession
      childAfter finalSession beforeSearch answeredSearch rejoinedSearch cell
      answerBindings before (privateAnswerTarget before binding)
      (resumeFindall (privateAnswerTarget before binding) frame remaining)
      frame remaining binding beforeResources afterResources := by
  subst afterAlts
  let answered := privateAnswerTarget before binding
  have answer :
      ContextualFindallAnswerResourceRelates alpha prog gt beforeSession
        beforeSearch childAfter answeredSearch cell answerBindings before
        answered frame remaining binding beforeResources afterResources [] :=
    source.toAnswer.privateAnswer_correspondence beforeFrameHead
      beforeOccurrences payloadBefore
  have sourceExit := source.toExit
  have pullNone : PLeaTTa.pullAux before.control.alts = none := by
    simpa [PLeaTTa.pullAux] using source.pull_eq_base
  have terminalFields :
      answered.control.cur = none ∧ answered.control.alts = [] :=
    PLeaTTa.PrologFindallAnswerExitBridge.PullOutcomeAgrees.terminal_fields_of_pull_none
      answer.finePullOutcome pullNone
  have done : PLeaTTa.Terminal answered.toConf := terminalFields
  have frameHead : answered.frames = .findall frame :: remaining :=
    answer.base.framesPreserved.trans answer.base.frameHead
  have control :=
    sourceExit.findallExit_occurrence_pop (prog := prog) (gt := gt)
      frameHead done answer.base.occurrences
  have payload :
      ContextualFindallExitPayloadRelates prog gt
        (collectTemplate childAfter cell.template answerBindings).session
        answeredSearch finalSession rejoinedSearch
        (afterAnswer cell childAfter answerBindings) answered
        (resumeFindall answered frame remaining) frame remaining :=
    { control := control
      payload := by
        rw [sourceExit.session_exact]
        exact answer.base.exitPayloadAfter }
  have answerCopy :
      CopyStep prog gt (.open before) (.open answered) := by
    rw [answer.base.fineTarget]
    exact answer_is_one_private_copy_step prog gt before binding
      answer.base.fineHead
  have additiveRaw :=
    findallExit_copy_expands prog gt answered frame remaining frameHead done
  have bagLength := postAnswerBagLength answer.base
  have additive :
      CopyStepsN prog gt
      ((afterAnswer cell childAfter answerBindings).reversed.length + 2)
        (.open answered)
        (.open (resumeFindall answered frame remaining)) := by
    rw [bagLength]
    exact additiveRaw
  have sourceRun :
      PeTTaSpec.PrologCore.GoalSemantics.StepsN 2
        (.running beforeSession beforeSearch) []
        (.running finalSession rejoinedSearch) :=
    source.toStepsN
  have oneAnswer :
      CopyStepsN prog gt 1 (.open before) (.open answered) := by
    simpa using CopyStepsN.succ 0 _ _ _ answerCopy (.zero _)
  have fineRun :
      CopyStepsN prog gt
        ((afterAnswer cell childAfter answerBindings).reversed.length + 3)
        (.open before)
        (.open (resumeFindall answered frame remaining)) := by
    have combined := oneAnswer.trans additive
    have countEq :
        1 +
            ((afterAnswer cell childAfter answerBindings).reversed.length + 2) =
          (afterAnswer cell childAfter answerBindings).reversed.length + 3 := by
      omega
    rw [countEq] at combined
    exact combined
  exact
    { source := source
      answer := answer
      fineTerminal := done
      exit := payload
      answerCopyStep := answerCopy
      additiveExit := additive
      sourceRun := sourceRun
      fineRun := by simpa [answered] using fineRun }

end ContextualFindallAnswerRelates

/-- A direct one-answer generator inhabits the joint source certificate with
the real marker-free private generator bank.  The following completion runs at
the post-copy session and shares the literal `.cutBoundary 1 .done` successor
with the answer origin. -/
theorem ground_one_answer_source_pair_inhabited :
    let sourceBindings : Substitution := [(.source "x", .integer 1)]
    let session : Session := {}
    let template : Term := .variable (.source "x")
    let copied := collectTemplate session template sourceBindings
    let cell :=
      sourceCollectionCell 1 ⟨1⟩ 0 template (.integer 9) [] [] []
    let beforeSearch : Search :=
      .collectionBoundary ⟨1⟩ 0
        (.cutBoundary 1 (.task 1 [] sourceBindings))
        template (.integer 9) [] [] []
    let answeredSearch : Search :=
      .collectionBoundary ⟨1⟩ 0 (.cutBoundary 1 .done)
        template (.integer 9) [] [] [copied.prepared.copied]
    let rejoinedSearch : Search :=
      .task 0
        [.unify (.integer 9) (.list [copied.prepared.copied] none)] []
    ActiveFindallTerminalAnswerResourceAgrees [] session beforeSearch session
      answeredSearch copied.session rejoinedSearch cell sourceBindings [] []
      [] [] := by
  dsimp
  let origin :
      PrologAnswerOriginBridge.AnswerOrigin 1
        [(.source "x", .integer 1)]
        (.task 1 [] [(.source "x", .integer 1)]) .done :=
    .task
  have resources :
      AnswerOriginResourceAgrees [] origin [] [] [] [] := by
    exact .task 1 [(.source "x", .integer 1)] [] []
  have producer :=
    ExactFindallBodyAnswerProducerResourceAgrees.ofOrigin ({} : Session)
      origin resources
  have exit :
      RawStep
        (collectTemplate ({} : Session) (.variable (.source "x"))
          [(.source "x", .integer 1)]).session
        (.cutBoundary 1 .done) [.completed] .none
        (collectTemplate ({} : Session) (.variable (.source "x"))
          [(.source "x", .integer 1)]).session
        (.terminal .completed) :=
    .cutBoundaryComplete 1 .done _ _ (.done _)
  simpa using
    (ActiveFindallTerminalAnswerResourceAgrees.here
      (alpha := ([] : List (LogicVar × String)))
      ({} : Session) ({} : Session)
      (collectTemplate ({} : Session) (.variable (.source "x"))
        [(.source "x", .integer 1)]).session
      0 1 ⟨1⟩
      (.task 1 [] [(.source "x", .integer 1)]) .done
      (.variable (.source "x")) (.integer 9) [] [] []
      [(.source "x", .integer 1)] producer exit)

/-- A depth-one cut wrapper cannot collapse the answer and completion lifts
into one transition.  Both steps remain present under real source context. -/
theorem ground_one_answer_under_cut_source_pair_inhabited :
    let sourceBindings : Substitution := [(.source "x", .integer 1)]
    let session : Session := {}
    let template : Term := .variable (.source "x")
    let copied := collectTemplate session template sourceBindings
    let cell :=
      sourceCollectionCell 1 ⟨1⟩ 0 template (.integer 9) [] [] []
    let beforeSearch : Search :=
      .collectionBoundary ⟨1⟩ 0
        (.cutBoundary 1 (.task 1 [] sourceBindings))
        template (.integer 9) [] [] []
    let answeredSearch : Search :=
      .collectionBoundary ⟨1⟩ 0 (.cutBoundary 1 .done)
        template (.integer 9) [] [] [copied.prepared.copied]
    let rejoinedSearch : Search :=
      .task 0
        [.unify (.integer 9) (.list [copied.prepared.copied] none)] []
    ActiveFindallTerminalAnswerResourceAgrees [] session
      (.cutBoundary 7 beforeSearch) session (.cutBoundary 7 answeredSearch)
      copied.session (.cutBoundary 7 rejoinedSearch) cell sourceBindings [] []
      [] [] := by
  dsimp
  exact .underCut 7 (by simpa using ground_one_answer_source_pair_inhabited)

/-- The depth-one contextual witness has exactly two source steps, rejecting
any implementation that shares one lift between answer and completion. -/
theorem ground_one_answer_under_cut_source_exact_two_steps :
    let sourceBindings : Substitution := [(.source "x", .integer 1)]
    let session : Session := {}
    let template : Term := .variable (.source "x")
    let copied := collectTemplate session template sourceBindings
    let beforeSearch : Search :=
      .collectionBoundary ⟨1⟩ 0
        (.cutBoundary 1 (.task 1 [] sourceBindings))
        template (.integer 9) [] [] []
    let rejoinedSearch : Search :=
      .task 0
        [.unify (.integer 9) (.list [copied.prepared.copied] none)] []
    PeTTaSpec.PrologCore.GoalSemantics.StepsN 2
      (.running session (.cutBoundary 7 beforeSearch)) []
      (.running copied.session (.cutBoundary 7 rejoinedSearch)) := by
  dsimp
  have pair := ground_one_answer_under_cut_source_pair_inhabited
  dsimp only at pair
  exact pair.toStepsN

/-- The complete one-answer terminal seam is inhabited.  Its source run has
exactly two steps, while its certified additive fine run has exactly four:
one private answer, one transfer, one local copy, and one finish. -/
theorem ground_one_answer_terminal_exit_inhabited
    (prog : Prog) (gt : GroundingTable) :
    let sourceBindings : Substitution := [(.source "x", .integer 1)]
    let fineBinding : Subst := [("x", .gnd (.int 1))]
    let session : Session := {}
    let template : Term := .variable (.source "x")
    let copied := collectTemplate session template sourceBindings
    let cell :=
      sourceCollectionCell 1 ⟨1⟩ 0 template (.integer 9) [] [] []
    let beforeSearch : Search :=
      .collectionBoundary ⟨1⟩ 0
        (.cutBoundary 1 (.task 1 [] sourceBindings))
        template (.integer 9) [] [] []
    let answeredSearch : Search :=
      .collectionBoundary ⟨1⟩ 0 (.cutBoundary 1 .done)
        template (.integer 9) [] [] [copied.prepared.copied]
    let rejoinedSearch : Search :=
      .task 0
        [.unify (.integer 9) (.list [copied.prepared.copied] none)] []
    let outerControl : Control :=
      { cur := some ([], fineBinding)
        alts := []
        qterm := .var "x"
        answers := [] }
    let frame : FindallFrame :=
      { preCut := 1
        preCollection := 1
        outer := outerControl
        template := .var "x"
        result := .gnd (.int 9)
        rest := []
        binding := [] }
    let baseBefore : OpenConf :=
      { persistent := { world := {}, counter := 0 }
        control := outerControl
        frames := [.findall frame]
        scopes := {} }
    let before := baseBefore
    ContextualTerminalFindallAnswerExitRelates [] prog gt session session
      copied.session beforeSearch answeredSearch rejoinedSearch cell
      sourceBindings before (privateAnswerTarget before fineBinding)
      (resumeFindall (privateAnswerTarget before fineBinding) frame []) frame []
      fineBinding [] [] := by
  dsimp only
  have base := ground_direct_answer_correspondence_inhabited prog gt
  dsimp only at base
  have source := ground_one_answer_source_pair_inhabited
  dsimp only at source
  have payload := base.payloadBefore
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
  simpa using
    (ContextualFindallAnswerRelates.terminalExit (prog := prog) (gt := gt)
      source rfl rfl occurrences payload)

/-- Every terminal answer/exit segment is genuinely non-lockstep.  The newly
collected head makes the post-answer bag nonempty, hence the fine run has at
least four transitions while the source run has exactly two. -/
theorem ContextualTerminalFindallAnswerExitRelates.not_lockstep
    {alpha : List (LogicVar × String)}
    {prog : Prog} {gt : GroundingTable}
    {beforeSession childAfter finalSession : Session}
    {beforeSearch answeredSearch rejoinedSearch : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {before answered rejoined : OpenConf}
    {frame : FindallFrame} {remaining : List Frame} {binding : Subst}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    (_related :
      ContextualTerminalFindallAnswerExitRelates alpha prog gt beforeSession
        childAfter finalSession beforeSearch answeredSearch rejoinedSearch
        cell answerBindings before answered rejoined frame remaining binding
        beforeResources afterResources) :
    (2 : Nat) ≠
      (afterAnswer cell childAfter answerBindings).reversed.length + 3 := by
  simp [afterAnswer]

/-- At post-answer bag length one, the source/fine segment is exactly `2/4`.
The ground witness above inhabits this specialization. -/
theorem ContextualTerminalFindallAnswerExitRelates.one_answer_exact_counts
    {alpha : List (LogicVar × String)}
    {prog : Prog} {gt : GroundingTable}
    {beforeSession childAfter finalSession : Session}
    {beforeSearch answeredSearch rejoinedSearch : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {before answered rejoined : OpenConf}
    {frame : FindallFrame} {remaining : List Frame} {binding : Subst}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    (related :
      ContextualTerminalFindallAnswerExitRelates alpha prog gt beforeSession
        childAfter finalSession beforeSearch answeredSearch rejoinedSearch
        cell answerBindings before answered rejoined frame remaining binding
        beforeResources afterResources)
    (one : (afterAnswer cell childAfter answerBindings).reversed.length = 1) :
    PeTTaSpec.PrologCore.GoalSemantics.StepsN 2
        (.running beforeSession beforeSearch) []
        (.running finalSession rejoinedSearch) ∧
      CopyStepsN prog gt 4 (.open before) (.open rejoined) := by
  constructor
  · exact related.sourceRun
  · have fine := related.fineRun
    rw [one] at fine
    norm_num at fine ⊢
    exact fine

/-- At post-answer bag length two, the same source segment still costs two
steps while certified local copying makes the fine segment exactly five. -/
theorem ContextualTerminalFindallAnswerExitRelates.two_answer_exact_counts
    {alpha : List (LogicVar × String)}
    {prog : Prog} {gt : GroundingTable}
    {beforeSession childAfter finalSession : Session}
    {beforeSearch answeredSearch rejoinedSearch : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {before answered rejoined : OpenConf}
    {frame : FindallFrame} {remaining : List Frame} {binding : Subst}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    (related :
      ContextualTerminalFindallAnswerExitRelates alpha prog gt beforeSession
        childAfter finalSession beforeSearch answeredSearch rejoinedSearch
        cell answerBindings before answered rejoined frame remaining binding
        beforeResources afterResources)
    (two : (afterAnswer cell childAfter answerBindings).reversed.length = 2) :
    PeTTaSpec.PrologCore.GoalSemantics.StepsN 2
        (.running beforeSession beforeSearch) []
        (.running finalSession rejoinedSearch) ∧
      CopyStepsN prog gt 5 (.open before) (.open rejoined) := by
  constructor
  · exact related.sourceRun
  · have fine := related.fineRun
    rw [two] at fine
    norm_num at fine ⊢
    exact fine

end PLeaTTa.PrologFindallAnswerExitBridge
