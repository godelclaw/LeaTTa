-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologFindallLocalLiveCatchupBridge
Purpose: Compose one active local findall answer with the exact independent
  source catch-up to the same eagerly selected local alternative
Trusted boundary: none
Main exports: ActiveFindallLocalLiveAnswerResourceAgrees,
  ContextualFindallCollectionLocalLiveCatchupRelates,
  ContextualFindallLocalLiveCatchupRelates
-/
import PLeaTTa.Proofs.PrologFindallAnswerExitBridge
import PLeaTTa.Proofs.PrologAnswerSourceCatchupBridge

namespace PLeaTTa.PrologFindallLocalLiveCatchupBridge

open Metta (GroundingTable Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PrologAnswerOriginBridge
open PrologAnswerPullClassificationBridge
open PrologAnswerResourceBridge
open PrologAnswerSourceCatchupBridge
open PrologFindallAnswerBridge
open PrologFindallAnswerExitBridge
open PrologFindallAnswerResourceBridge
open PrologFindallFrameZipperBridge
open PrologProductResourceContextBridge
open DemandDrivenStep

/-!
The executable answer step records the private answer and eagerly pulls one
alternative.  The independent source answer step leaves the answer leaf at
`done`; later silent source steps walk the exact origin/resource zipper to the
same selected local occurrence.

The carrier below makes that phase gap structurally expressible.  Its direct
constructor has one `AnswerOrigin`; that same proof generates the answer
step, indexes the resource agreement, and indexes `OriginPrefixLanding`.
Every contextual constructor transports the answer and its later catch-up
together.  Hence neither a same-shaped origin nor a different wrapper depth
can be paired by coincident existential witnesses.
-/

/-- One active local `findall` answer whose eager executable pull selects a
branch owned by that answer's exact source origin.

`selectedTail` is the complete executable tail returned by `pullAux`, while
the eventual source frontier records its locally owned prefix and ordered
older suffix separately through `ConservativeReadyPullTarget`. -/
inductive ActiveFindallLocalLiveAnswerResourceAgrees
    (alpha : List (LogicVar × String)) :
    Session -> Search -> Session -> Search -> SourceCollectionCell ->
      Substitution ->
      List RetainedAlternativeSegment ->
      List RetainedAlternativeSegment ->
      List PLeaTTa.Alt -> List PLeaTTa.Alt ->
      List PLeaTTa.Goal -> Subst -> List PLeaTTa.Alt -> Prop where
  | here (session : Session)
      (callerScope cutScope : CutScopeId)
      (collectionScope : CollectionScopeId)
      (body next : Search) (template output : Term)
      (entryBindings : Substitution)
      (tail : List PeTTaSpec.PrologCore.Goal)
      (reversed : List Term) (answerBindings : Substitution)
      {leafScope : CutScopeId}
      {beforeResources afterResources : List RetainedAlternativeSegment}
      {beforeAlts afterAlts : List PLeaTTa.Alt}
      {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
      {selectedTail : List PLeaTTa.Alt}
      (origin :
        AnswerOrigin leafScope answerBindings
          body next)
      (agreement :
        AnswerOriginResourceAgrees alpha origin beforeResources afterResources
          beforeAlts afterAlts)
      (landing :
        OriginPrefixLanding alpha agreement selectedGoals selectedBinding
          selectedTail) :
      ActiveFindallLocalLiveAnswerResourceAgrees alpha session
        (.collectionBoundary collectionScope callerScope
          (.cutBoundary cutScope body) template output entryBindings tail
          reversed)
        session
        (.collectionBoundary collectionScope callerScope
          (.cutBoundary cutScope next) template output entryBindings tail
          ((collectTemplate session template
            answerBindings).prepared.copied :: reversed))
        (sourceCollectionCell cutScope collectionScope callerScope template
          output entryBindings tail reversed)
        answerBindings beforeResources afterResources beforeAlts afterAlts
        selectedGoals selectedBinding selectedTail
  | underChoice (scope : CutScopeId) (right : Search)
      {before childAfter : Session} {left answered : Search}
      {cell : SourceCollectionCell} {answerBindings : Substitution}
      {beforeResources afterResources : List RetainedAlternativeSegment}
      {beforeAlts afterAlts : List PLeaTTa.Alt}
      {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
      {selectedTail : List PLeaTTa.Alt}
      (inside :
        ActiveFindallLocalLiveAnswerResourceAgrees alpha before left childAfter
          answered cell answerBindings beforeResources afterResources
          beforeAlts afterAlts selectedGoals selectedBinding selectedTail) :
      ActiveFindallLocalLiveAnswerResourceAgrees alpha before
        (.choice scope left right) childAfter (.choice scope answered right)
        cell answerBindings beforeResources afterResources beforeAlts afterAlts
        selectedGoals selectedBinding selectedTail
  | underCut (scope : CutScopeId)
      {before childAfter : Session} {body answered : Search}
      {cell : SourceCollectionCell} {answerBindings : Substitution}
      {beforeResources afterResources : List RetainedAlternativeSegment}
      {beforeAlts afterAlts : List PLeaTTa.Alt}
      {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
      {selectedTail : List PLeaTTa.Alt}
      (inside :
        ActiveFindallLocalLiveAnswerResourceAgrees alpha before body childAfter
          answered cell answerBindings beforeResources afterResources
          beforeAlts afterAlts selectedGoals selectedBinding selectedTail) :
      ActiveFindallLocalLiveAnswerResourceAgrees alpha before
        (.cutBoundary scope body) childAfter (.cutBoundary scope answered)
        cell answerBindings beforeResources afterResources beforeAlts afterAlts
        selectedGoals selectedBinding selectedTail
  | underCatch (handlerScope : ExceptionScopeId) (scope : CutScopeId)
      (catcher : Term) (handler : PeTTaSpec.PrologCore.Goal)
      (entryBindings : Substitution)
      {before childAfter : Session} {body answered : Search}
      {cell : SourceCollectionCell} {answerBindings : Substitution}
      {beforeResources afterResources : List RetainedAlternativeSegment}
      {beforeAlts afterAlts : List PLeaTTa.Alt}
      {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
      {selectedTail : List PLeaTTa.Alt}
      (inside :
        ActiveFindallLocalLiveAnswerResourceAgrees alpha before body childAfter
          answered cell answerBindings beforeResources afterResources
          beforeAlts afterAlts selectedGoals selectedBinding selectedTail) :
      ActiveFindallLocalLiveAnswerResourceAgrees alpha before
        (.catchBoundary handlerScope scope body catcher handler entryBindings)
        childAfter
        (.catchBoundary handlerScope scope answered catcher handler
          entryBindings)
        cell answerBindings beforeResources afterResources beforeAlts afterAlts
        selectedGoals selectedBinding selectedTail
  | underCollection (collectionScope : CollectionScopeId)
      (callerScope outerCutScope : CutScopeId)
      (template output : Term) (entryBindings : Substitution)
      (tail : List PeTTaSpec.PrologCore.Goal) (reversed : List Term)
      {before childAfter : Session} {body answered : Search}
      {cell : SourceCollectionCell} {answerBindings : Substitution}
      {beforeResources afterResources : List RetainedAlternativeSegment}
      {beforeAlts afterAlts : List PLeaTTa.Alt}
      {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
      {selectedTail : List PLeaTTa.Alt}
      (inside :
        ActiveFindallLocalLiveAnswerResourceAgrees alpha before body childAfter
          answered cell answerBindings beforeResources afterResources
          beforeAlts afterAlts selectedGoals selectedBinding selectedTail) :
      ActiveFindallLocalLiveAnswerResourceAgrees alpha before
        (.collectionBoundary collectionScope callerScope
          (.cutBoundary outerCutScope body) template output entryBindings tail
          reversed)
        childAfter
        (.collectionBoundary collectionScope callerScope
          (.cutBoundary outerCutScope answered) template output entryBindings
          tail reversed)
        cell answerBindings beforeResources afterResources beforeAlts afterAlts
        selectedGoals selectedBinding selectedTail
  | underProduct (scope : CutScopeId)
      (tail : List PeTTaSpec.PrologCore.Goal)
      {before childAfter : Session} {head answered : Search}
      {cell : SourceCollectionCell} {answerBindings : Substitution}
      {beforeResources afterResources : List RetainedAlternativeSegment}
      {beforeAlts afterAlts : List PLeaTTa.Alt}
      {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
      {selectedTail : List PLeaTTa.Alt}
      (inside :
        ActiveFindallLocalLiveAnswerResourceAgrees alpha before head childAfter
          answered cell answerBindings beforeResources afterResources
          beforeAlts afterAlts selectedGoals selectedBinding selectedTail) :
      ActiveFindallLocalLiveAnswerResourceAgrees alpha before
        (.product scope head tail) childAfter (.product scope answered tail)
        cell answerBindings beforeResources afterResources beforeAlts afterAlts
        selectedGoals selectedBinding selectedTail

namespace ActiveFindallLocalLiveAnswerResourceAgrees

/-- Erase only the local-live landing.  The answer relation is reconstructed
from the very same origin and resource agreement. -/
theorem toAnswer
    {alpha : List (LogicVar × String)}
    {before childAfter : Session} {search answered : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
    {selectedTail : List PLeaTTa.Alt}
    (live :
      ActiveFindallLocalLiveAnswerResourceAgrees alpha before search childAfter
        answered cell answerBindings beforeResources afterResources beforeAlts
        afterAlts selectedGoals selectedBinding selectedTail) :
    ActiveFindallAnswerResourceAgrees alpha before search childAfter answered
      cell answerBindings beforeResources afterResources beforeAlts
      afterAlts := by
  induction live with
  | here session callerScope cutScope collectionScope body next template output
      entryBindings tail reversed answerBindings origin agreement landing =>
      exact .here session session callerScope cutScope collectionScope body next
        template output entryBindings tail reversed answerBindings
        (ExactFindallBodyAnswerProducerResourceAgrees.ofOrigin session origin
          agreement)
  | underChoice scope right _ ih => exact .underChoice scope right ih
  | underCut scope _ ih => exact .underCut scope ih
  | underCatch handlerScope scope catcher handler entryBindings _ ih =>
      exact .underCatch handlerScope scope catcher handler entryBindings ih
  | underCollection collectionScope callerScope outerCutScope template output
      entryBindings tail reversed _ ih =>
      exact .underCollection collectionScope callerScope outerCutScope template
        output entryBindings tail reversed ih
  | underProduct scope tail _ ih => exact .underProduct scope tail ih

/-- The local-live carrier fixes the literal eager-pull equation at the exact
incoming alternative bank. -/
theorem pullExact
    {alpha : List (LogicVar × String)}
    {before childAfter : Session} {search answered : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
    {selectedTail : List PLeaTTa.Alt}
    (live :
      ActiveFindallLocalLiveAnswerResourceAgrees alpha before search childAfter
        answered cell answerBindings beforeResources afterResources beforeAlts
        afterAlts selectedGoals selectedBinding selectedTail) :
    PLeaTTa.pullAux beforeAlts =
      some ((selectedGoals, selectedBinding), selectedTail) := by
  induction live with
  | here _ _ _ _ _ _ _ _ _ _ _ _ _ _ landing =>
      exact landing.pullAux_exact
  | underChoice _ _ _ ih => exact ih
  | underCut _ _ ih => exact ih
  | underCatch _ _ _ _ _ _ ih => exact ih
  | underCollection _ _ _ _ _ _ _ _ _ ih => exact ih
  | underProduct _ _ _ ih => exact ih

/-- Exact silent source catch-up after the answer-produced template copy.
The transition count is computed by `OriginPrefixLanding.sourceCatchup` and
preserved literally through every contextual wrapper. -/
theorem sourceCatchup
    {alpha : List (LogicVar × String)}
    {before childAfter : Session} {search answered : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
    {selectedTail : List PLeaTTa.Alt}
    (live :
      ActiveFindallLocalLiveAnswerResourceAgrees alpha before search childAfter
        answered cell answerBindings beforeResources afterResources beforeAlts
        afterAlts selectedGoals selectedBinding selectedTail) :
    exists count target,
      SilentStepsN
          (collectTemplate childAfter cell.template answerBindings).session
          count answered target /\
        ConservativeReadyPullTarget alpha selectedGoals selectedBinding
          selectedTail target := by
  induction live with
  | here session callerScope cutScope collectionScope body next template output
      entryBindings tail reversed answerBindings origin agreement landing =>
      let copied := collectTemplate session template answerBindings
      obtain ⟨count, target, steps, ready⟩ :=
        PLeaTTa.PrologAnswerSourceCatchupBridge.OriginPrefixLanding.sourceCatchup
          landing copied.session
      exact
        ⟨count,
          .collectionBoundary collectionScope callerScope
            (.cutBoundary cutScope target) template output entryBindings tail
            (copied.prepared.copied :: reversed),
          (steps.underCutBoundary cutScope).underCollectionBoundary
            collectionScope callerScope template output entryBindings tail
            (copied.prepared.copied :: reversed),
          (ready.underCutBoundary cutScope).underCollectionBoundary
            collectionScope callerScope template output entryBindings tail
            (copied.prepared.copied :: reversed)⟩
  | underChoice scope right inside ih =>
      obtain ⟨count, target, steps, ready⟩ := ih
      exact
        ⟨count, .choice scope target right, steps.underChoice scope,
          ready.underChoice scope⟩
  | underCut scope inside ih =>
      obtain ⟨count, target, steps, ready⟩ := ih
      exact
        ⟨count, .cutBoundary scope target, steps.underCutBoundary scope,
          ready.underCutBoundary scope⟩
  | underCatch handlerScope scope catcher handler entryBindings inside ih =>
      obtain ⟨count, target, steps, ready⟩ := ih
      exact
        ⟨count,
          .catchBoundary handlerScope scope target catcher handler
            entryBindings,
          steps.underCatchBoundary handlerScope scope catcher handler
            entryBindings,
          ready.underCatchBoundary handlerScope scope catcher handler
            entryBindings⟩
  | underCollection collectionScope callerScope outerCutScope template output
      entryBindings tail reversed inside ih =>
      obtain ⟨count, target, steps, ready⟩ := ih
      exact
        ⟨count,
          .collectionBoundary collectionScope callerScope
            (.cutBoundary outerCutScope target) template output entryBindings
            tail reversed,
          (steps.underCutBoundary outerCutScope).underCollectionBoundary
            collectionScope callerScope template output entryBindings tail
            reversed,
          (ready.underCutBoundary outerCutScope).underCollectionBoundary
            collectionScope callerScope template output entryBindings tail
            reversed⟩
  | underProduct scope tail inside ih =>
      obtain ⟨count, target, steps, ready⟩ := ih
      exact
        ⟨count, .product scope target tail, steps.underProduct scope tail,
          ready.underProduct scope tail⟩

end ActiveFindallLocalLiveAnswerResourceAgrees

/-- General contextual correspondence for one active local collector answer
whose eager executable pull selects another locally owned occurrence.

This variant carries only the collection-step payload.  It therefore applies
across residual-alias orientations that are semantically valid during
collection but do not yet support exact-name caller exit packaging.

The independent source emits the private answer in one transition and then
takes `count` silent DFS transitions to the same branch-indexed frontier.  The
fine additive lane performs the answer and eager pull in exactly one step. -/
structure ContextualFindallCollectionLocalLiveCatchupRelates
    (alpha : List (LogicVar × String))
    (prog : Prog) (gt : GroundingTable)
    (beforeSession childAfter : Session)
    (beforeSearch answeredSearch : Search)
    (cell : SourceCollectionCell) (answerBindings : Substitution)
    (before answered : OpenConf) (frame : FindallFrame)
    (remaining : List Frame) (binding : Subst)
    (beforeResources afterResources : List RetainedAlternativeSegment)
    (afterAlts : List PLeaTTa.Alt)
    (selectedGoals : List PLeaTTa.Goal) (selectedBinding : Subst)
    (selectedTail : List PLeaTTa.Alt)
    (count : Nat) (target : Search) : Prop where
  source :
    ActiveFindallLocalLiveAnswerResourceAgrees alpha beforeSession beforeSearch
      childAfter answeredSearch cell answerBindings beforeResources
      afterResources before.control.alts afterAlts selectedGoals
      selectedBinding selectedTail
  answer :
    ContextualFindallCollectionAnswerResourceRelates alpha prog gt
      beforeSession beforeSearch childAfter answeredSearch cell answerBindings
      before answered frame remaining binding beforeResources afterResources
      afterAlts
  catchup :
    SilentStepsN
      (collectTemplate childAfter cell.template answerBindings).session count
      answeredSearch target
  ready :
    ConservativeReadyPullTarget alpha selectedGoals selectedBinding
      selectedTail target
  fineSelected :
    answered.control.cur = some (selectedGoals, selectedBinding) ∧
      answered.control.alts = selectedTail
  answerCopyStep :
    CopyStep prog gt (.open before) (.open answered)
  sourceRun :
    PeTTaSpec.PrologCore.GoalSemantics.StepsN (count + 1)
      (.running beforeSession beforeSearch) []
      (.running
        (collectTemplate childAfter cell.template answerBindings).session
        target)
  fineRun :
    CopyStepsN prog gt 1 (.open before) (.open answered)

/-- Exit-enriched contextual correspondence for one active local collector
answer whose eager executable pull selects another locally owned occurrence.

The independent source emits the private answer in one transition and then
takes `count` silent DFS transitions to the same branch-indexed frontier.  The
fine additive lane performs the answer and eager pull in exactly one step.
The single `source` carrier owns the answer origin, resource zipper, selected
branch, and catch-up proof, so none can be paired by independent existential
witnesses.

[SPEC metta.pl:251-256; SWI:findall/3] -/
structure ContextualFindallLocalLiveCatchupRelates
    (alpha : List (LogicVar × String))
    (prog : Prog) (gt : GroundingTable)
    (beforeSession childAfter : Session)
    (beforeSearch answeredSearch : Search)
    (cell : SourceCollectionCell) (answerBindings : Substitution)
    (before answered : OpenConf) (frame : FindallFrame)
    (remaining : List Frame) (binding : Subst)
    (beforeResources afterResources : List RetainedAlternativeSegment)
    (afterAlts : List PLeaTTa.Alt)
    (selectedGoals : List PLeaTTa.Goal) (selectedBinding : Subst)
    (selectedTail : List PLeaTTa.Alt)
    (count : Nat) (target : Search) : Prop where
  source :
    ActiveFindallLocalLiveAnswerResourceAgrees alpha beforeSession beforeSearch
      childAfter answeredSearch cell answerBindings beforeResources
      afterResources before.control.alts afterAlts selectedGoals
      selectedBinding selectedTail
  answer :
    ContextualFindallAnswerResourceRelates alpha prog gt beforeSession
      beforeSearch childAfter answeredSearch cell answerBindings before answered
      frame remaining binding beforeResources afterResources afterAlts
  catchup :
    SilentStepsN
      (collectTemplate childAfter cell.template answerBindings).session count
      answeredSearch target
  ready :
    ConservativeReadyPullTarget alpha selectedGoals selectedBinding
      selectedTail target
  fineSelected :
    answered.control.cur = some (selectedGoals, selectedBinding) ∧
      answered.control.alts = selectedTail
  answerCopyStep :
    CopyStep prog gt (.open before) (.open answered)
  sourceRun :
    PeTTaSpec.PrologCore.GoalSemantics.StepsN (count + 1)
      (.running beforeSession beforeSearch) []
      (.running
        (collectTemplate childAfter cell.template answerBindings).session
        target)
  fineRun :
    CopyStepsN prog gt 1 (.open before) (.open answered)

namespace ContextualFindallLocalLiveCatchupRelates

/-- Forget only the strict exit-ready answer packet. -/
theorem collection
    {alpha : List (LogicVar × String)}
    {prog : Prog} {gt : GroundingTable}
    {beforeSession childAfter : Session}
    {beforeSearch answeredSearch : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {before answered : OpenConf} {frame : FindallFrame}
    {remaining : List Frame} {binding : Subst}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {afterAlts : List PLeaTTa.Alt}
    {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
    {selectedTail : List PLeaTTa.Alt}
    {count : Nat} {target : Search}
    (agreement :
      ContextualFindallLocalLiveCatchupRelates alpha prog gt beforeSession
        childAfter beforeSearch answeredSearch cell answerBindings before
        answered frame remaining binding beforeResources afterResources
        afterAlts selectedGoals selectedBinding selectedTail count target) :
    ContextualFindallCollectionLocalLiveCatchupRelates alpha prog gt
      beforeSession childAfter beforeSearch answeredSearch cell answerBindings
      before answered frame remaining binding beforeResources afterResources
      afterAlts selectedGoals selectedBinding selectedTail count target :=
  { source := agreement.source
    answer := agreement.answer.collection
    catchup := agreement.catchup
    ready := agreement.ready
    fineSelected := agreement.fineSelected
    answerCopyStep := agreement.answerCopyStep
    sourceRun := agreement.sourceRun
    fineRun := agreement.fineRun }

end ContextualFindallLocalLiveCatchupRelates

namespace ContextualFindallCollectionAnswerRelates

/-- Compose one jointly certified local-live private answer with its exact
independent-source catch-up and bounded fine answer step, requiring no
exit-ready suspended-caller payload.

[SPEC metta.pl:251-256; SWI:findall/3] -/
theorem localLiveCatchup
    {alpha : List (LogicVar × String)}
    {prog : Prog} {gt : GroundingTable}
    {beforeSession childAfter : Session}
    {beforeSearch answeredSearch : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {before : OpenConf} {frame : FindallFrame}
    {remaining : List Frame} {binding : Subst}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {afterAlts : List PLeaTTa.Alt}
    {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
    {selectedTail : List PLeaTTa.Alt}
    (source :
      ActiveFindallLocalLiveAnswerResourceAgrees alpha beforeSession
        beforeSearch childAfter answeredSearch cell answerBindings
        beforeResources afterResources before.control.alts afterAlts
        selectedGoals selectedBinding selectedTail)
    (beforeFrameHead : before.frames = .findall frame :: remaining)
    (beforeOccurrences :
      CollectionOccurrenceAgrees beforeSearch before.frames)
    (payloadBefore :
      FindallCollectionAnswerPayloadAgrees childAfter cell before frame
        answerBindings binding) :
    exists count target,
      ContextualFindallCollectionLocalLiveCatchupRelates alpha prog gt
        beforeSession childAfter beforeSearch answeredSearch cell
        answerBindings before (privateAnswerTarget before binding) frame
        remaining binding beforeResources afterResources afterAlts selectedGoals
        selectedBinding selectedTail count target := by
  let answered := privateAnswerTarget before binding
  have answer :
      ContextualFindallCollectionAnswerResourceRelates alpha prog gt
        beforeSession beforeSearch childAfter answeredSearch cell
        answerBindings before answered frame remaining binding beforeResources
        afterResources afterAlts :=
    source.toAnswer.privateCollectionAnswer_correspondence
      (prog := prog) (gt := gt) beforeFrameHead beforeOccurrences payloadBefore
  obtain ⟨count, target, catchup, ready⟩ := source.sourceCatchup
  have fineSelected :
      answered.control.cur = some (selectedGoals, selectedBinding) ∧
        answered.control.alts = selectedTail :=
    PLeaTTa.PrologFindallAnswerResourceBridge.PullOutcomeAgrees.fields_of_pull_some
      answer.finePullOutcome source.pullExact
  have answerCopy :
      CopyStep prog gt (.open before) (.open answered) := by
    rw [answer.base.fineTarget]
    exact answer_is_one_private_copy_step prog gt before binding
      answer.base.fineHead
  have first :
      PeTTaSpec.PrologCore.GoalSemantics.Transition
        (.running beforeSession beforeSearch) []
        (.running
          (collectTemplate childAfter cell.template answerBindings).session
          answeredSearch) :=
    .ordinary _ [] _ _ _ answer.base.sourceStep
  have firstRun :
      PeTTaSpec.PrologCore.GoalSemantics.StepsN 1
        (.running beforeSession beforeSearch) []
        (.running
          (collectTemplate childAfter cell.template answerBindings).session
          answeredSearch) := by
    simpa using
      (PeTTaSpec.PrologCore.GoalSemantics.StepsN.succ 0 _ _ _ [] [] first
        (.zero _))
  have sourceRun :
      PeTTaSpec.PrologCore.GoalSemantics.StepsN (count + 1)
        (.running beforeSession beforeSearch) []
        (.running
          (collectTemplate childAfter cell.template answerBindings).session
          target) := by
    simpa [Nat.add_comm] using
      PeTTaSpec.PrologCore.GoalSemantics.StepsN.trans firstRun
        catchup.toStepsN
  have fineRun :
      CopyStepsN prog gt 1 (.open before) (.open answered) := by
    simpa using CopyStepsN.succ 0 _ _ _ answerCopy (.zero _)
  exact
    ⟨count, target,
      { source := source
        answer := by simpa [answered] using answer
        catchup := catchup
        ready := ready
        fineSelected := by simpa [answered] using fineSelected
        answerCopyStep := by simpa [answered] using answerCopy
        sourceRun := sourceRun
        fineRun := by simpa [answered] using fineRun }⟩

end ContextualFindallCollectionAnswerRelates

namespace ContextualFindallAnswerRelates

/-- Compose one jointly certified local-live private answer with its exact
independent-source catch-up and the bounded fine answer step.

The catch-up count and target are derived from `OriginPrefixLanding`; the
caller supplies neither.  The fine selected fields are then forced by the
same literal `pullAux` equation carried by that landing.

[SPEC metta.pl:251-256; SWI:findall/3] -/
theorem localLiveCatchup
    {alpha : List (LogicVar × String)}
    {prog : Prog} {gt : GroundingTable}
    {beforeSession childAfter : Session}
    {beforeSearch answeredSearch : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {before : OpenConf} {frame : FindallFrame}
    {remaining : List Frame} {binding : Subst}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {afterAlts : List PLeaTTa.Alt}
    {selectedGoals : List PLeaTTa.Goal} {selectedBinding : Subst}
    {selectedTail : List PLeaTTa.Alt}
    (source :
      ActiveFindallLocalLiveAnswerResourceAgrees alpha beforeSession
        beforeSearch childAfter answeredSearch cell answerBindings
        beforeResources afterResources before.control.alts afterAlts
        selectedGoals selectedBinding selectedTail)
    (beforeFrameHead : before.frames = .findall frame :: remaining)
    (beforeOccurrences :
      CollectionOccurrenceAgrees beforeSearch before.frames)
    (payloadBefore :
      FindallAnswerPayloadAgrees childAfter cell before frame answerBindings
        binding) :
    exists count target,
      ContextualFindallLocalLiveCatchupRelates alpha prog gt beforeSession
        childAfter beforeSearch answeredSearch cell answerBindings before
        (privateAnswerTarget before binding) frame remaining binding
        beforeResources afterResources afterAlts selectedGoals selectedBinding
        selectedTail count target := by
  let answered := privateAnswerTarget before binding
  have answer :
      ContextualFindallAnswerResourceRelates alpha prog gt beforeSession
        beforeSearch childAfter answeredSearch cell answerBindings before
        answered frame remaining binding beforeResources afterResources
        afterAlts :=
    source.toAnswer.privateAnswer_correspondence beforeFrameHead
      beforeOccurrences payloadBefore
  obtain ⟨count, target, catchup, ready⟩ := source.sourceCatchup
  have fineSelected :
      answered.control.cur = some (selectedGoals, selectedBinding) ∧
        answered.control.alts = selectedTail :=
    PLeaTTa.PrologFindallAnswerResourceBridge.PullOutcomeAgrees.fields_of_pull_some
      answer.finePullOutcome source.pullExact
  have answerCopy :
      CopyStep prog gt (.open before) (.open answered) := by
    rw [answer.base.fineTarget]
    exact answer_is_one_private_copy_step prog gt before binding
      answer.base.fineHead
  have first :
      PeTTaSpec.PrologCore.GoalSemantics.Transition
        (.running beforeSession beforeSearch) []
        (.running
          (collectTemplate childAfter cell.template answerBindings).session
          answeredSearch) :=
    .ordinary _ [] _ _ _ answer.base.sourceStep
  have firstRun :
      PeTTaSpec.PrologCore.GoalSemantics.StepsN 1
        (.running beforeSession beforeSearch) []
        (.running
          (collectTemplate childAfter cell.template answerBindings).session
          answeredSearch) := by
    simpa using
      (PeTTaSpec.PrologCore.GoalSemantics.StepsN.succ 0 _ _ _ [] [] first
        (.zero _))
  have sourceRun :
      PeTTaSpec.PrologCore.GoalSemantics.StepsN (count + 1)
        (.running beforeSession beforeSearch) []
        (.running
          (collectTemplate childAfter cell.template answerBindings).session
          target) := by
    simpa [Nat.add_comm] using
      PeTTaSpec.PrologCore.GoalSemantics.StepsN.trans firstRun
        catchup.toStepsN
  have fineRun :
      CopyStepsN prog gt 1 (.open before) (.open answered) := by
    simpa using CopyStepsN.succ 0 _ _ _ answerCopy (.zero _)
  exact
    ⟨count, target,
      { source := source
        answer := by simpa [answered] using answer
        catchup := catchup
        ready := ready
        fineSelected := by simpa [answered] using fineSelected
        answerCopyStep := by simpa [answered] using answerCopy
        sourceRun := sourceRun
        fineRun := by simpa [answered] using fineRun }⟩

end ContextualFindallAnswerRelates

private theorem wrapped_nested_done_choices_are_not_ready
    {alpha : List (LogicVar × String)}
    {goals : List PLeaTTa.Goal} {binding : Subst}
    {selectedTail : List PLeaTTa.Alt}
    (outerScope callerScope generatorScope innerScope branchScope : CutScopeId)
    (collectionScope : CollectionScopeId)
    (emptyRight liveRight : Search) (template output : Term)
    (entryBindings : Substitution)
    (tail : List PeTTaSpec.PrologCore.Goal) (reversed : List Term) :
    ¬ ConservativeReadyPullTarget alpha goals binding selectedTail
      (.cutBoundary outerScope
        (.collectionBoundary collectionScope callerScope
          (.cutBoundary generatorScope
            (.choice branchScope (.choice innerScope .done emptyRight)
              liveRight))
          template output entryBindings tail reversed)) := by
  intro ready
  rcases ready with ⟨localTail, suffix, tailEq, localReady⟩
  cases localReady with
  | taskChoices _ _ _ _ _ _ _ _ choices => cases choices
  | underCutBoundary _ _ insideOuter =>
      cases insideOuter with
      | taskChoices _ _ _ _ _ _ _ _ choices => cases choices
      | underCollectionBoundary _ _ _ _ _ _ _ _ insideCollection =>
          cases insideCollection with
          | taskChoices _ _ _ _ _ _ _ _ choices => cases choices
          | underCutBoundary _ _ insideGenerator =>
              cases insideGenerator with
              | taskChoices _ _ _ _ _ _ _ _ choices => cases choices
              | underChoice _ _ _ insideBranch =>
                  cases insideBranch with
                  | taskChoices _ _ _ _ _ _ _ _ choices => cases choices
                  | underChoice _ _ _ insideInner =>
                      cases insideInner with
                      | taskChoices _ _ _ _ _ _ _ _ choices => cases choices

/-- The local-live composition is inhabited by a genuinely nested source
origin.  Its first owned region is conservatively empty, its second is live,
the generator cut contributes the literal executable barrier, and an outer
cut boundary exercises contextual lifting.

The post-answer catch-up is provably non-reflexive.  Consequently the exact
source segment has at least two transitions (one answer plus positive silent
catch-up), whereas the additive fine answer segment has the fixed one-step
shape proved by `localLiveCatchup`. -/
theorem nested_wrapped_local_live_source_run_is_inhabited :
    exists (emptyCursor liveCursor : Resolver.PreparedCursor)
        (emptyResource liveResource : RetainedAlternativeSegment)
        (selectedGoals : List PLeaTTa.Goal) (selectedBinding : Subst)
        (selectedTail : List PLeaTTa.Alt) (count : Nat) (target : Search),
      let session : Session := {}
      let template : Term := .integer 7
      let output : Term := .integer 9
      let copied := collectTemplate session template []
      let body : Search :=
        .choice 2
          (.choice 1 (.task 1 [] []) (.clauses 1 emptyCursor))
          (.clauses 2 liveCursor)
      let next : Search :=
        .choice 2 (.choice 1 .done (.clauses 1 emptyCursor))
          (.clauses 2 liveCursor)
      let beforeSearch : Search :=
        .cutBoundary 9
          (.collectionBoundary ⟨1⟩ 0 (.cutBoundary 3 body) template output
            [] [] [])
      let answeredSearch : Search :=
        .cutBoundary 9
          (.collectionBoundary ⟨1⟩ 0 (.cutBoundary 3 next) template output
            [] [] [copied.prepared.copied])
      let cell := sourceCollectionCell 3 ⟨1⟩ 0 template output [] [] []
      exists _source :
          ActiveFindallLocalLiveAnswerResourceAgrees [] session beforeSearch
            session answeredSearch cell [] [emptyResource, liveResource] []
            (emptyResource.alts ++ liveResource.alts) []
            selectedGoals selectedBinding selectedTail,
        emptyResource.alts = [] ∧
        liveResource.alts ≠ [] ∧
        0 < count ∧
        SilentStepsN copied.session count answeredSearch target ∧
        ConservativeReadyPullTarget [] selectedGoals selectedBinding
          selectedTail target ∧
        PeTTaSpec.PrologCore.GoalSemantics.StepsN (count + 1)
          (.running session beforeSearch) [] (.running copied.session target) := by
  obtain ⟨emptyResource, emptyCursor, emptyOwnership, emptyHead⟩ :=
    PLeaTTa.PrologAnswerPullClassificationBridge.empty_owned_region_is_inhabited
  obtain
      ⟨liveResource, liveCursor, goals, binding, localTail, liveOwnership,
        liveHead⟩ :=
    PLeaTTa.PrologAnswerPullClassificationBridge.live_owned_region_is_inhabited
  rcases emptyOwnership with
    ⟨emptyCallStart, emptyPosition, emptyExactOwnership⟩
  rcases liveOwnership with
    ⟨liveCallStart, livePosition, liveExactOwnership⟩
  let leaf :
      AnswerOrigin 1 ([] : Substitution) (.task 1 [] []) .done := .task
  let innerOrigin :
      AnswerOrigin 1 ([] : Substitution)
        (.choice 1 (.task 1 [] []) (.clauses 1 emptyCursor))
        (.choice 1 .done (.clauses 1 emptyCursor)) :=
    .choice 1 (.clauses 1 emptyCursor) leaf
  let origin :
      AnswerOrigin 1 ([] : Substitution)
        (.choice 2
          (.choice 1 (.task 1 [] []) (.clauses 1 emptyCursor))
          (.clauses 2 liveCursor))
        (.choice 2 (.choice 1 .done (.clauses 1 emptyCursor))
          (.clauses 2 liveCursor)) :=
    .choice 2 (.clauses 2 liveCursor) innerOrigin
  have leafAgreement :
      AnswerOriginResourceAgrees [] leaf [emptyResource, liveResource]
        [emptyResource, liveResource]
        (emptyResource.alts ++ liveResource.alts)
        (emptyResource.alts ++ liveResource.alts) :=
    .task 1 [] [emptyResource, liveResource]
      (emptyResource.alts ++ liveResource.alts)
  have emptyRegion :
    RightAlternativeRegionAgrees [] (.clauses 1 emptyCursor)
        [emptyResource] emptyResource.alts :=
    .clauses 1 emptyCallStart emptyCursor emptyPosition
      emptyResource emptyExactOwnership
  have innerAgreement :
      AnswerOriginResourceAgrees [] innerOrigin [emptyResource, liveResource]
        [liveResource]
        (emptyResource.alts ++ liveResource.alts)
        liveResource.alts := by
    apply AnswerOriginResourceAgrees.choice 1 (.clauses 1 emptyCursor) leaf
      (regionResources := [emptyResource])
      (regionAlts := emptyResource.alts)
    · simpa [List.append_assoc] using leafAgreement
    · exact emptyRegion
  have liveRegion :
    RightAlternativeRegionAgrees [] (.clauses 2 liveCursor)
        [liveResource] liveResource.alts :=
    .clauses 2 liveCallStart liveCursor livePosition
      liveResource liveExactOwnership
  have originAgreement :
      AnswerOriginResourceAgrees [] origin [emptyResource, liveResource] []
        (emptyResource.alts ++ liveResource.alts) [] := by
    apply AnswerOriginResourceAgrees.choice 2 (.clauses 2 liveCursor)
      innerOrigin (regionResources := [liveResource])
      (regionAlts := liveResource.alts)
    · simpa only [List.append_nil] using innerAgreement
    · exact liveRegion
  have selected :
      PLeaTTa.pullAux
          (emptyResource.alts ++ liveResource.alts) =
        some ((goals, binding), localTail) := by
    rw [emptyHead, liveHead]
    simp [PLeaTTa.pullAux]
  rcases AnswerOriginResourceAgrees.classifyPrefix originAgreement with
      ⟨selectedGoals, selectedBinding, selectedTail, landing⟩ | falls
  · let direct :
        ActiveFindallLocalLiveAnswerResourceAgrees [] ({} : Session)
          (.collectionBoundary ⟨1⟩ 0
            (.cutBoundary 3
              (.choice 2
                (.choice 1 (.task 1 [] []) (.clauses 1 emptyCursor))
                (.clauses 2 liveCursor)))
            (.integer 7) (.integer 9) [] [] [])
          ({} : Session)
          (.collectionBoundary ⟨1⟩ 0
            (.cutBoundary 3
              (.choice 2 (.choice 1 .done (.clauses 1 emptyCursor))
                (.clauses 2 liveCursor)))
            (.integer 7) (.integer 9) [] []
            [(collectTemplate ({} : Session) (.integer 7) []).prepared.copied])
          (sourceCollectionCell 3 ⟨1⟩ 0 (.integer 7) (.integer 9) [] [] [])
          [] [emptyResource, liveResource] []
          (emptyResource.alts ++ liveResource.alts) []
          selectedGoals selectedBinding selectedTail :=
      .here ({} : Session) 0 3 ⟨1⟩ _ _ (.integer 7) (.integer 9) [] []
        [] [] origin originAgreement landing
    let source :=
      ActiveFindallLocalLiveAnswerResourceAgrees.underCut 9 direct
    obtain ⟨count, target, steps, ready⟩ := source.sourceCatchup
    have countPositive : 0 < count := by
      apply Nat.pos_of_ne_zero
      intro countZero
      subst count
      cases steps
      exact wrapped_nested_done_choices_are_not_ready 9 0 3 1 2 ⟨1⟩
        (.clauses 1 emptyCursor) (.clauses 2 liveCursor) (.integer 7)
        (.integer 9) [] []
        [(collectTemplate ({} : Session) (.integer 7) []).prepared.copied]
        ready
    have first :
        PeTTaSpec.PrologCore.GoalSemantics.Transition
          (.running ({} : Session)
            (.cutBoundary 9
              (.collectionBoundary ⟨1⟩ 0
                (.cutBoundary 3
                  (.choice 2
                    (.choice 1 (.task 1 [] []) (.clauses 1 emptyCursor))
                    (.clauses 2 liveCursor)))
                (.integer 7) (.integer 9) [] [] []))) []
          (.running
            (collectTemplate ({} : Session) (.integer 7) []).session
            (.cutBoundary 9
              (.collectionBoundary ⟨1⟩ 0
                (.cutBoundary 3
                  (.choice 2 (.choice 1 .done (.clauses 1 emptyCursor))
                    (.clauses 2 liveCursor)))
                (.integer 7) (.integer 9) [] []
                [(collectTemplate ({} : Session) (.integer 7) []).prepared.copied]))) :=
      .ordinary _ [] _ _ _ source.toAnswer.weak.sourceStep
    have firstRun :
        PeTTaSpec.PrologCore.GoalSemantics.StepsN 1
          (.running ({} : Session)
            (.cutBoundary 9
              (.collectionBoundary ⟨1⟩ 0
                (.cutBoundary 3
                  (.choice 2
                    (.choice 1 (.task 1 [] []) (.clauses 1 emptyCursor))
                    (.clauses 2 liveCursor)))
                (.integer 7) (.integer 9) [] [] []))) []
          (.running
            (collectTemplate ({} : Session) (.integer 7) []).session
            (.cutBoundary 9
              (.collectionBoundary ⟨1⟩ 0
                (.cutBoundary 3
                  (.choice 2 (.choice 1 .done (.clauses 1 emptyCursor))
                    (.clauses 2 liveCursor)))
                (.integer 7) (.integer 9) [] []
                [(collectTemplate ({} : Session) (.integer 7) []).prepared.copied]))) := by
      simpa using
        (PeTTaSpec.PrologCore.GoalSemantics.StepsN.succ 0 _ _ _ [] [] first
          (.zero _))
    have sourceRun :=
      PeTTaSpec.PrologCore.GoalSemantics.StepsN.trans firstRun steps.toStepsN
    refine
      ⟨emptyCursor, liveCursor, emptyResource, liveResource, selectedGoals,
        selectedBinding, selectedTail, count, target, ?_⟩
    dsimp only
    refine ⟨source, emptyHead, ?_, countPositive, steps, ready, ?_⟩
    · rw [liveHead]
      simp
    · simpa [sourceCollectionCell, Nat.add_comm] using sourceRun
  · have impossible := falls.pullAux_eq
    rw [selected] at impossible
    simp [PLeaTTa.pullAux] at impossible

end PLeaTTa.PrologFindallLocalLiveCatchupBridge
