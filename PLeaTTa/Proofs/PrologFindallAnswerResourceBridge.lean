-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologFindallAnswerResourceBridge
Purpose: Compose one active local findall answer with the exact retained
  resource and executable-alternative zipper at its source answer leaf
Trusted boundary: none
Main exports: ActiveFindallAnswerResourceAgrees,
  ContextualFindallAnswerResourceRelates
-/
import PLeaTTa.Proofs.PrologFindallAnswerBridge
import PLeaTTa.Proofs.PrologAnswerResourceBridge

namespace PLeaTTa.PrologFindallAnswerResourceBridge

open Metta (Atom GroundingTable Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PrologAnswerOriginBridge
open PrologAnswerResourceBridge
open PrologFindallAnswerBridge
open PrologFindallFrameZipperBridge
open PrologProductResourceContextBridge
open DemandDrivenStep

/-!
# Active findall answers with exact resource provenance

`ActiveFindallAnswer` identifies the actual answer-producing source leaf and
the innermost collector that consumes it.  `ExactAnswerProducerResourceAgrees`
independently accounts for the retained source cursors and executable
alternative regions along that leaf's origin.  This module joins the two
without changing either relation.

The four resource/alternative endpoints belong to the generator's active
bank.  Every outer wrapper below reuses those endpoint variables literally:
its inactive choice, product tail, handler, or enclosing collector lives in
the suspended outer findall frame and therefore owns no part of this bank.

The cut boundary installed by `findall/3` is deliberately *not* part of the
resource zipper.  `subConfOf` starts the private generator with `alts := []`;
only a locally entered predicate call contributes an anonymous executable
marker.  The direct certificate therefore indexes resource ownership on the
collection body and derives the surrounding cut step separately.  This keeps
the typed collection cut from consuming a nonexistent predicate marker.  The
same boundary explains the apparent catch asymmetry: generator-internal catch
fails closed in `AnswerOriginResourceAgrees`, while `underCatch` is an outer
wrapper above the collector's `subConfOf` state.

The terminal zipper endpoint is *not* the executable answer successor's
alternative bank.  `PLeaTTa.answerSuccessor` records the answer and immediately
calls `pull`, which skips leading markers and consumes at most the first live
branch.  The source takes separate backtracking/control steps.  Consequently
the contextual relation anchors the exact pre-bank and exposes the literal
machine pull equation, but deliberately makes no `postAlts = afterAlts` claim.
-/

namespace AnswerOriginResourceAgrees

/-- An older executable-bank suffix may be threaded through an exact origin
zipper without changing any resource ownership or consumption order.  This
generic operation is not used for the marker-free collection cut. -/
theorem append_alts
    {alpha : List (LogicVar × String)}
    {leafScope : CutScopeId} {bindings : Substitution}
    {source next : Search}
    {origin : AnswerOrigin leafScope bindings source next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (agreement :
      AnswerOriginResourceAgrees alpha origin beforeResources afterResources
        beforeAlts afterAlts)
    (suffix : List PLeaTTa.Alt) :
    AnswerOriginResourceAgrees alpha origin beforeResources afterResources
      (beforeAlts ++ suffix) (afterAlts ++ suffix) := by
  exact AnswerOriginResourceAgrees.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun origin beforeResources afterResources beforeAlts
        afterAlts _ =>
      AnswerOriginResourceAgrees alpha origin beforeResources afterResources
        (beforeAlts ++ suffix) (afterAlts ++ suffix))
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (fun leafScope bindings resources alts =>
      .task leafScope bindings resources (alts ++ suffix))
    (by
      intro scope right leafScope bindings left next inside
        beforeResources afterResources regionResources
        beforeAlts afterAlts regionAlts insideAgrees regionAgrees
        insideIH regionIH
      apply AnswerOriginResourceAgrees.choice scope right inside
        (insideAgrees := ?_) (regionAgrees := regionAgrees)
      simpa only [List.append_assoc] using insideIH)
    (by
      intro scope leafScope bindings body next inside
        beforeResources afterResources beforeAlts afterAlts insideAgrees
        insideIH
      apply AnswerOriginResourceAgrees.cutBoundary scope inside
      simpa only [List.cons_append] using insideIH)
    agreement

end AnswerOriginResourceAgrees

/-- Exact resource provenance for the answer-producing body of one active
`findall/3` collector.

The body origin owns precisely the generator's executable alternative bank.
The collection-owned cut boundary is absent from this structure because the
fine `subConfOf` entry does not allocate an `Alt.barrier` for it. -/
structure ExactFindallBodyAnswerProducerResourceAgrees
    (alpha : List (LogicVar × String))
    (before after : Session) (body next : Search)
    (bindings : Substitution)
    (beforeResources afterResources : List RetainedAlternativeSegment)
    (beforeAlts afterAlts : List PLeaTTa.Alt) : Prop where
  bodyProducer :
    ExactAnswerProducerResourceAgrees alpha before after body next bindings
      beforeResources afterResources beforeAlts afterAlts

namespace ExactFindallBodyAnswerProducerResourceAgrees

/-- Wrap source control through the collection cut without consuming or
creating an executable alternative marker. -/
theorem cutWrappedProducer
    {alpha : List (LogicVar × String)}
    {before after : Session} {body next : Search}
    {bindings : Substitution}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (child :
      ExactFindallBodyAnswerProducerResourceAgrees alpha before after body next
        bindings beforeResources afterResources beforeAlts afterAlts)
    (cutScope : CutScopeId) :
    ExactAnswerProducer before after (.cutBoundary cutScope body)
      (.cutBoundary cutScope next) bindings := by
  exact
    ExactAnswerProducer.ofRawStep
      (.cutBoundaryProgress cutScope body next [.answer bindings] before after
        child.bodyProducer.producer.step)

/-- Any exact body origin and its resource zipper construct the marker-free
findall-body certificate directly. -/
theorem ofOrigin
    {alpha : List (LogicVar × String)}
    {leafScope : CutScopeId} {bindings : Substitution}
    {body next : Search}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (session : Session)
    (origin : AnswerOrigin leafScope bindings body next)
    (agreement :
      AnswerOriginResourceAgrees alpha origin beforeResources afterResources
        beforeAlts afterAlts) :
    ExactFindallBodyAnswerProducerResourceAgrees alpha session session body next
      bindings beforeResources afterResources beforeAlts afterAlts := by
  exact
    ⟨ExactAnswerProducerResourceAgrees.ofOrigin session origin agreement⟩

end ExactFindallBodyAnswerProducerResourceAgrees

/-- One active source `findall/3` answer whose exact direct child producer
also carries the body-origin-indexed resource and alternative zipper.

All transparent outer constructors keep the four endpoints definitionally
unchanged.  This makes accidental outer-resource consumption unrepresentable
rather than merely prohibited by a side condition. -/
inductive ActiveFindallAnswerResourceAgrees
    (alpha : List (LogicVar × String)) :
    Session -> Search -> Session -> Search -> SourceCollectionCell ->
      Substitution ->
      List RetainedAlternativeSegment ->
      List RetainedAlternativeSegment ->
      List PLeaTTa.Alt -> List PLeaTTa.Alt -> Prop where
  | here (before childAfter : Session)
      (callerScope cutScope : CutScopeId)
      (collectionScope : CollectionScopeId)
      (body next : Search) (template output : Term)
      (entryBindings : Substitution)
      (tail : List PeTTaSpec.PrologCore.Goal)
      (reversed : List Term) (answerBindings : Substitution)
      {beforeResources afterResources : List RetainedAlternativeSegment}
      {beforeAlts afterAlts : List PLeaTTa.Alt}
      (child :
        ExactFindallBodyAnswerProducerResourceAgrees alpha before childAfter
          body next
          answerBindings beforeResources afterResources beforeAlts afterAlts) :
      ActiveFindallAnswerResourceAgrees alpha before
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
        answerBindings beforeResources afterResources beforeAlts afterAlts
  | underChoice (scope : CutScopeId) (right : Search)
      {before childAfter : Session} {left next : Search}
      {cell : SourceCollectionCell} {answerBindings : Substitution}
      {beforeResources afterResources : List RetainedAlternativeSegment}
      {beforeAlts afterAlts : List PLeaTTa.Alt}
      (inside :
        ActiveFindallAnswerResourceAgrees alpha before left childAfter next
          cell answerBindings beforeResources afterResources beforeAlts
          afterAlts) :
      ActiveFindallAnswerResourceAgrees alpha before (.choice scope left right)
        childAfter (.choice scope next right) cell answerBindings
        beforeResources afterResources beforeAlts afterAlts
  | underCut (scope : CutScopeId)
      {before childAfter : Session} {body next : Search}
      {cell : SourceCollectionCell} {answerBindings : Substitution}
      {beforeResources afterResources : List RetainedAlternativeSegment}
      {beforeAlts afterAlts : List PLeaTTa.Alt}
      (inside :
        ActiveFindallAnswerResourceAgrees alpha before body childAfter next
          cell answerBindings beforeResources afterResources beforeAlts
          afterAlts) :
      ActiveFindallAnswerResourceAgrees alpha before
        (.cutBoundary scope body) childAfter (.cutBoundary scope next) cell
        answerBindings beforeResources afterResources beforeAlts afterAlts
  | underCatch (handlerScope : ExceptionScopeId) (scope : CutScopeId)
      (catcher : Term) (handler : PeTTaSpec.PrologCore.Goal)
      (entryBindings : Substitution)
      {before childAfter : Session} {body next : Search}
      {cell : SourceCollectionCell} {answerBindings : Substitution}
      {beforeResources afterResources : List RetainedAlternativeSegment}
      {beforeAlts afterAlts : List PLeaTTa.Alt}
      (inside :
        ActiveFindallAnswerResourceAgrees alpha before body childAfter next
          cell answerBindings beforeResources afterResources beforeAlts
          afterAlts) :
      ActiveFindallAnswerResourceAgrees alpha before
        (.catchBoundary handlerScope scope body catcher handler entryBindings)
        childAfter
        (.catchBoundary handlerScope scope next catcher handler entryBindings)
        cell answerBindings beforeResources afterResources beforeAlts afterAlts
  | underCollection (collectionScope : CollectionScopeId)
      (callerScope outerCutScope : CutScopeId)
      (template output : Term) (entryBindings : Substitution)
      (tail : List PeTTaSpec.PrologCore.Goal) (reversed : List Term)
      {before childAfter : Session} {body next : Search}
      {cell : SourceCollectionCell} {answerBindings : Substitution}
      {beforeResources afterResources : List RetainedAlternativeSegment}
      {beforeAlts afterAlts : List PLeaTTa.Alt}
      (inside :
        ActiveFindallAnswerResourceAgrees alpha before body childAfter next
          cell answerBindings beforeResources afterResources beforeAlts
          afterAlts) :
      ActiveFindallAnswerResourceAgrees alpha before
        (.collectionBoundary collectionScope callerScope
          (.cutBoundary outerCutScope body) template output entryBindings tail
          reversed)
        childAfter
        (.collectionBoundary collectionScope callerScope
          (.cutBoundary outerCutScope next) template output entryBindings tail
          reversed)
        cell answerBindings beforeResources afterResources beforeAlts afterAlts
  | underProduct (scope : CutScopeId)
      (tail : List PeTTaSpec.PrologCore.Goal)
      {before childAfter : Session} {head next : Search}
      {cell : SourceCollectionCell} {answerBindings : Substitution}
      {beforeResources afterResources : List RetainedAlternativeSegment}
      {beforeAlts afterAlts : List PLeaTTa.Alt}
      (inside :
        ActiveFindallAnswerResourceAgrees alpha before head childAfter next
          cell answerBindings beforeResources afterResources beforeAlts
          afterAlts) :
      ActiveFindallAnswerResourceAgrees alpha before (.product scope head tail)
        childAfter (.product scope next tail) cell answerBindings
        beforeResources afterResources beforeAlts afterAlts

namespace ActiveFindallAnswerResourceAgrees

/-- Erase only resource evidence.  The exact source leaf, collector update,
wrapper path, and answer binding remain the established active-answer proof. -/
theorem weak
    {alpha : List (LogicVar × String)}
    {before childAfter : Session} {search next : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (answer :
      ActiveFindallAnswerResourceAgrees alpha before search childAfter next
        cell answerBindings beforeResources afterResources beforeAlts
        afterAlts) :
    ActiveFindallAnswer before search childAfter next cell answerBindings := by
  induction answer with
  | here before childAfter callerScope cutScope collectionScope body next
      template output entryBindings tail reversed answerBindings child =>
      exact .here before childAfter callerScope cutScope collectionScope body
        next template output entryBindings tail reversed answerBindings
        (child.cutWrappedProducer cutScope)
  | underChoice scope right inside inductionHypothesis =>
      exact .underChoice scope right inductionHypothesis
  | underCut scope inside inductionHypothesis =>
      exact .underCut scope inductionHypothesis
  | underCatch handlerScope scope catcher handler entryBindings inside
      inductionHypothesis =>
      exact .underCatch handlerScope scope catcher handler entryBindings
        inductionHypothesis
  | underCollection collectionScope callerScope outerCutScope template output
      entryBindings tail reversed inside inductionHypothesis =>
      exact .underCollection collectionScope callerScope outerCutScope template
        output entryBindings tail reversed inductionHypothesis
  | underProduct scope tail inside inductionHypothesis =>
      exact .underProduct scope tail inductionHypothesis

/-- The exact resource-bearing direct producer remains structurally present
under every contextual wrapper. -/
theorem has_exactProducerResource
    {alpha : List (LogicVar × String)}
    {before childAfter : Session} {search next : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (answer :
      ActiveFindallAnswerResourceAgrees alpha before search childAfter next
        cell answerBindings beforeResources afterResources beforeAlts
        afterAlts) :
    exists childSource childNext,
      ExactAnswerProducerResourceAgrees alpha before childAfter childSource
        childNext answerBindings beforeResources afterResources beforeAlts
        afterAlts := by
  induction answer with
  | here _ _ _ _ _ body childNext _ _ _ _ _ _ child =>
      exact ⟨body, childNext, child.bodyProducer⟩
  | underChoice _ _ _ inductionHypothesis => exact inductionHypothesis
  | underCut _ _ inductionHypothesis => exact inductionHypothesis
  | underCatch _ _ _ _ _ _ inductionHypothesis => exact inductionHypothesis
  | underCollection _ _ _ _ _ _ _ _ _ inductionHypothesis =>
      exact inductionHypothesis
  | underProduct _ _ _ inductionHypothesis => exact inductionHypothesis

/-- Resource consumption is a literal ordered prefix removal, inherited from
the exact direct producer rather than separately postulated at the wrapper. -/
theorem resources_suffix
    {alpha : List (LogicVar × String)}
    {before childAfter : Session} {search next : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (answer :
      ActiveFindallAnswerResourceAgrees alpha before search childAfter next
        cell answerBindings beforeResources afterResources beforeAlts
        afterAlts) :
    exists consumed, beforeResources = consumed ++ afterResources := by
  rcases answer.has_exactProducerResource with ⟨_, _, producer⟩
  rcases producer.originAgreement with ⟨_, _, agreement⟩
  exact agreement.resources_suffix

/-- Executable alternatives are decomposed by the same ordered source-origin
zipper.  This is a pre-state decomposition, not a fine post-state equation. -/
theorem alts_suffix
    {alpha : List (LogicVar × String)}
    {before childAfter : Session} {search next : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (answer :
      ActiveFindallAnswerResourceAgrees alpha before search childAfter next
        cell answerBindings beforeResources afterResources beforeAlts
        afterAlts) :
    exists consumed, beforeAlts = consumed ++ afterAlts := by
  rcases answer.has_exactProducerResource with ⟨_, _, producer⟩
  rcases producer.originAgreement with ⟨_, _, agreement⟩
  exact agreement.alts_suffix

/-- Crossing an outer cut wrapper is endpoint-neutral by construction. -/
theorem underCut_endpoints
    {alpha : List (LogicVar × String)} (scope : CutScopeId)
    {before childAfter : Session} {body next : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (inside :
      ActiveFindallAnswerResourceAgrees alpha before body childAfter next cell
        answerBindings beforeResources afterResources beforeAlts afterAlts) :
    ActiveFindallAnswerResourceAgrees alpha before (.cutBoundary scope body)
      childAfter (.cutBoundary scope next) cell answerBindings beforeResources
      afterResources beforeAlts afterAlts :=
  .underCut scope inside

/-- Crossing an outer choice wrapper is likewise endpoint-neutral; its right
branch belongs to suspended outer control, not the generator bank. -/
theorem underChoice_endpoints
    {alpha : List (LogicVar × String)} (scope : CutScopeId) (right : Search)
    {before childAfter : Session} {left next : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (inside :
      ActiveFindallAnswerResourceAgrees alpha before left childAfter next cell
        answerBindings beforeResources afterResources beforeAlts afterAlts) :
    ActiveFindallAnswerResourceAgrees alpha before (.choice scope left right)
      childAfter (.choice scope next right) cell answerBindings beforeResources
      afterResources beforeAlts afterAlts :=
  .underChoice scope right inside

end ActiveFindallAnswerResourceAgrees

/-- Total, exact control projection of one executable `pull`.  The exhausted
case and the selected-branch case remain distinct, and the selected case
retains the literal alternative tail returned by `pullAux`. -/
inductive PullOutcomeAgrees :
    List PLeaTTa.Alt -> Option (List PLeaTTa.Goal × Subst) ->
      List PLeaTTa.Alt -> Prop where
  | exhausted {beforeAlts : List PLeaTTa.Alt}
      (outcome : PLeaTTa.pullAux beforeAlts = none) :
      PullOutcomeAgrees beforeAlts none []
  | selected {beforeAlts : List PLeaTTa.Alt}
      (goals : List PLeaTTa.Goal) (binding : Subst)
      (rest : List PLeaTTa.Alt)
      (outcome :
        PLeaTTa.pullAux beforeAlts = some ((goals, binding), rest)) :
      PullOutcomeAgrees beforeAlts (some (goals, binding)) rest

namespace PullOutcomeAgrees

/-- The concrete machine `pull` always produces exactly one of the two
outcomes above.  Cached barrier metadata cannot change the chosen branch or
remaining bank because `pullAuxTracked_fst` pins its first projection. -/
theorem of_pull (conf : PLeaTTa.Conf) :
    PullOutcomeAgrees conf.alts (PLeaTTa.pull conf).cur
      (PLeaTTa.pull conf).alts := by
  unfold PLeaTTa.pull
  generalize trackedEq :
    PLeaTTa.pullAuxTracked conf.barriers conf.alts = tracked
  rcases tracked with ⟨outcome, cache⟩
  have sameOutcome :=
    PLeaTTa.pullAuxTracked_fst conf.barriers conf.alts
  rw [trackedEq] at sameOutcome
  cases outcome with
  | none =>
      exact .exhausted sameOutcome.symm
  | some result =>
      rcases result with ⟨⟨goals, binding⟩, rest⟩
      exact .selected goals binding rest sameOutcome.symm

end PullOutcomeAgrees

/-- The private-answer successor exposes the total result of the same real
`pull` that appears in `answerSuccessor`; no resource endpoint is substituted
for it. -/
theorem privateAnswerTarget_pullOutcome
    (state : OpenConf) (answerBinding : Subst) :
    PullOutcomeAgrees state.control.alts
      (privateAnswerTarget state answerBinding).control.cur
      (privateAnswerTarget state answerBinding).control.alts := by
  let seed : PLeaTTa.Conf :=
    { state.toConf with
      cur := none
      answers := PLeaTTa.subst answerBinding state.toConf.qterm ::
        state.toConf.answers
      answerKeys :=
        PLeaTTa.PersistentSubst.atomExactKey
            (PLeaTTa.subst answerBinding state.toConf.qterm) ::
          state.toConf.answerKeys
      answerKeys_sound := by
        simp only [List.map_cons]
        rw [state.toConf.answerKeys_sound] }
  have outcome := PullOutcomeAgrees.of_pull seed
  simpa [seed, privateAnswerTarget, answerSuccessor, OpenConf.stepOpen,
    OpenConf.ofConfWith, OpenConf.toConf, Control.toConf, controlOf] using
      outcome

/-- Exact contextual private-answer correspondence with the source origin's
resource zipper anchored to the literal incoming executable alternative bank.

`afterAlts` is the zipper remainder beyond the complete source answer origin;
it is intentionally not equated with `after.control.alts`. -/
structure ContextualFindallAnswerResourceRelates
    (alpha : List (LogicVar × String))
    (prog : Prog) (gt : GroundingTable)
    (beforeSession : Session) (beforeSearch : Search)
    (childAfter : Session) (afterSearch : Search)
    (cell : SourceCollectionCell) (answerBindings : Substitution)
    (before after : OpenConf) (frame : FindallFrame)
    (remaining : List Frame) (binding : Subst)
    (beforeResources afterResources : List RetainedAlternativeSegment)
    (afterAlts : List PLeaTTa.Alt) : Prop where
  base :
    ContextualFindallAnswerRelates prog gt beforeSession beforeSearch
      childAfter afterSearch cell answerBindings before after frame remaining
      binding
  sourceResources :
    ActiveFindallAnswerResourceAgrees alpha beforeSession beforeSearch
      childAfter afterSearch cell answerBindings beforeResources afterResources
      before.control.alts afterAlts

namespace ContextualFindallAnswerResourceRelates

/-- The fine successor is exactly the real answer-plus-pull machine result.
This is the honest post-bank statement; no zipper endpoint is substituted for
the result of `pull`. -/
theorem finePullExact
    {alpha : List (LogicVar × String)}
    {prog : Prog} {gt : GroundingTable}
    {beforeSession childAfter : Session}
    {beforeSearch afterSearch : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {before after : OpenConf} {frame : FindallFrame}
    {remaining : List Frame} {binding : Subst}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {afterAlts : List PLeaTTa.Alt}
    (agreement :
      ContextualFindallAnswerResourceRelates alpha prog gt beforeSession
        beforeSearch childAfter afterSearch cell answerBindings before after
        frame remaining binding beforeResources afterResources afterAlts) :
    after.toConf = answerSuccessor before.toConf binding := by
  rw [agreement.base.fineTarget]
  simp [privateAnswerTarget]

/-- The contextual fine successor is classified by the real total pull
result over the zipper-anchored incoming bank. -/
theorem finePullOutcome
    {alpha : List (LogicVar × String)}
    {prog : Prog} {gt : GroundingTable}
    {beforeSession childAfter : Session}
    {beforeSearch afterSearch : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {before after : OpenConf} {frame : FindallFrame}
    {remaining : List Frame} {binding : Subst}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {afterAlts : List PLeaTTa.Alt}
    (agreement :
      ContextualFindallAnswerResourceRelates alpha prog gt beforeSession
        beforeSearch childAfter afterSearch cell answerBindings before after
        frame remaining binding beforeResources afterResources afterAlts) :
    PullOutcomeAgrees before.control.alts after.control.cur
      after.control.alts := by
  rw [agreement.base.fineTarget]
  exact privateAnswerTarget_pullOutcome before binding

/-- The anchored executable pre-bank has the exact ordered suffix exposed by
the resource zipper. -/
theorem sourceBank_suffix
    {alpha : List (LogicVar × String)}
    {prog : Prog} {gt : GroundingTable}
    {beforeSession childAfter : Session}
    {beforeSearch afterSearch : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {before after : OpenConf} {frame : FindallFrame}
    {remaining : List Frame} {binding : Subst}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {afterAlts : List PLeaTTa.Alt}
    (agreement :
      ContextualFindallAnswerResourceRelates alpha prog gt beforeSession
        beforeSearch childAfter afterSearch cell answerBindings before after
        frame remaining binding beforeResources afterResources afterAlts) :
    exists consumed, before.control.alts = consumed ++ afterAlts :=
  agreement.sourceResources.alts_suffix

end ContextualFindallAnswerResourceRelates

/-- The enriched source proof composes with the existing occurrence/payload
correspondence without adding a second source step or a second fine step. -/
theorem ActiveFindallAnswerResourceAgrees.privateAnswer_correspondence
    {alpha : List (LogicVar × String)}
    {prog : Prog} {gt : GroundingTable}
    {beforeSession childAfter : Session}
    {beforeSearch afterSearch : Search}
    {cell : SourceCollectionCell} {answerBindings : Substitution}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {afterAlts : List PLeaTTa.Alt}
    {before : OpenConf} {frame : FindallFrame}
    {remaining : List Frame} {binding : Subst}
    (answer :
      ActiveFindallAnswerResourceAgrees alpha beforeSession beforeSearch
        childAfter afterSearch cell answerBindings beforeResources
        afterResources before.control.alts afterAlts)
    (frameHead : before.frames = .findall frame :: remaining)
    (beforeOccurrences :
      CollectionOccurrenceAgrees beforeSearch before.frames)
    (payload :
      FindallAnswerPayloadAgrees childAfter cell before frame answerBindings
        binding) :
    ContextualFindallAnswerResourceRelates alpha prog gt beforeSession
      beforeSearch childAfter afterSearch cell answerBindings before
      (privateAnswerTarget before binding) frame remaining binding
      beforeResources afterResources afterAlts := by
  exact
    { base :=
        answer.weak.privateAnswer_correspondence frameHead beforeOccurrences
          payload
      sourceResources := answer }

/-- A private answer with two live alternatives consumes exactly the first
branch and leaves the second.  Therefore its post-bank cannot in general be
identified with a resource zipper's terminal suffix. -/
theorem private_answer_pull_is_not_terminal_suffix :
    let first : PLeaTTa.Alt := .br [] []
    let second : PLeaTTa.Alt := .br [] [("x", .gnd (.int 1))]
    let state : OpenConf :=
      { persistent := { world := {}, counter := 0 }
        control :=
          { cur := some ([], [])
            alts := [first, second]
            qterm := .gnd (.int 0)
            answers := [] } }
    (privateAnswerTarget state []).control.alts = [second] /\
      (privateAnswerTarget state []).control.alts ≠ [] := by
  dsimp
  constructor
  · rfl
  · intro impossible
    cases impossible

/-- A direct generator task answer is resource-certified on the exact empty
bank produced by `enterFindall`; no synthetic collection marker is needed. -/
theorem marker_free_body_answer_is_inhabited :
    ExactFindallBodyAnswerProducerResourceAgrees
      ([] : List (LogicVar × String)) ({} : Session) ({} : Session)
      (.task 1 [] []) .done [] [] [] [] [] := by
  exact
    ExactFindallBodyAnswerProducerResourceAgrees.ofOrigin ({} : Session)
      (AnswerOrigin.task (leafScope := 1) (bindings := []))
      (.task 1 [] [] [])

/-- The former model, in which the collection cut consumed an executable
marker, cannot describe the real empty generator bank.  Its inner task would
have to preserve `[]` as `[Alt.barrier]`. -/
theorem cut_wrapped_resource_origin_rejects_empty_generator_bank :
    let origin : AnswerOrigin 1 ([] : Substitution)
        (.cutBoundary 1 (.task 1 [] [])) (.cutBoundary 1 .done) :=
      .cutBoundary 1 (.task)
    ¬ AnswerOriginResourceAgrees ([] : List (LogicVar × String)) origin
        [] [] [] [] := by
  dsimp only
  intro agreement
  cases agreement with
  | cutBoundary _ _ inside => cases inside

/-- A real direct collector answer carries the previously certified
inner-active-under-outer-scheduled two-resource path.  Its literal pre-bank
has exactly the two historical predicate markers; the active collector cut is
marker-free, matching the executable `subConfOf` entry. -/
theorem two_resource_direct_answer_is_inhabited :
    exists innerCursor outerCursor :
        PeTTaSpec.PrologCore.Resolver.PreparedCursor,
      exists innerResource outerResource : RetainedAlternativeSegment,
        let outerRight : Search :=
          .product 3
            (.cutBoundary 2
              (.choice 2 .done (.clauses 2 outerCursor)))
            []
        let body : Search :=
          .choice 3
            (.cutBoundary 1
              (.choice 1 (.task 1 [] []) (.clauses 1 innerCursor)))
            outerRight
        let next : Search :=
          .choice 3
            (.cutBoundary 1
              (.choice 1 .done (.clauses 1 innerCursor)))
            outerRight
        let cell : SourceCollectionCell :=
          sourceCollectionCell 9 ⟨20⟩ 0 (.integer 0) (.integer 9) [] [] []
        ActiveFindallAnswerResourceAgrees [] ({} : Session)
          (.collectionBoundary ⟨20⟩ 0 (.cutBoundary 9 body)
            (.integer 0) (.integer 9) [] [] [])
          ({} : Session)
          (.collectionBoundary ⟨20⟩ 0 (.cutBoundary 9 next)
            (.integer 0) (.integer 9) [] []
            [(collectTemplate ({} : Session) (.integer 0) []).prepared.copied])
          cell [] [innerResource, outerResource] []
          (innerResource.alts ++
            (PLeaTTa.Alt.barrier ::
              (outerResource.alts ++ [PLeaTTa.Alt.barrier])))
          [] := by
  obtain
      ⟨innerCursor, outerCursor, innerResource, outerResource, nested⟩ :=
    PLeaTTa.PrologAnswerResourceBridge.AnswerOriginResourceAgrees.nested_answer_resource_path_is_inhabited
  refine ⟨innerCursor, outerCursor, innerResource, outerResource, ?_⟩
  dsimp only
  let outerRight : Search :=
    .product 3
      (.cutBoundary 2 (.choice 2 .done (.clauses 2 outerCursor))) []
  let origin : AnswerOrigin 1 ([] : Substitution)
      (.choice 3
        (.cutBoundary 1
          (.choice 1 (.task 1 [] []) (.clauses 1 innerCursor)))
        outerRight)
      (.choice 3
        (.cutBoundary 1
          (.choice 1 .done (.clauses 1 innerCursor)))
        outerRight) :=
    .choice 3 outerRight
      (.cutBoundary 1
        (.choice 1 (.clauses 1 innerCursor)
          (AnswerOrigin.task (leafScope := 1) (bindings := []))))
  apply ActiveFindallAnswerResourceAgrees.here
  exact
    ExactFindallBodyAnswerProducerResourceAgrees.ofOrigin ({} : Session)
      origin (by simpa [origin, outerRight] using nested)

/-- The same two-resource direct answer survives two different outer wrapper
kinds with literally identical endpoints.  This exercises endpoint-neutral
propagation at depth rather than only restating a one-wrapper constructor. -/
theorem two_resource_answer_survives_outer_choice_and_product :
    exists beforeSearch afterSearch : Search,
      exists cell : SourceCollectionCell,
        exists innerResource outerResource : RetainedAlternativeSegment,
          exists beforeAlts : List PLeaTTa.Alt,
            ActiveFindallAnswerResourceAgrees [] ({} : Session) beforeSearch
                ({} : Session) afterSearch cell []
                [innerResource, outerResource] [] beforeAlts [] /\
              ActiveFindallAnswerResourceAgrees [] ({} : Session)
                (.product 11 (.choice 10 beforeSearch .done) [])
                ({} : Session)
                (.product 11 (.choice 10 afterSearch .done) [])
                cell [] [innerResource, outerResource] [] beforeAlts [] := by
  obtain
      ⟨innerCursor, outerCursor, innerResource, outerResource, direct⟩ :=
    two_resource_direct_answer_is_inhabited
  let outerRight : Search :=
    .product 3
      (.cutBoundary 2 (.choice 2 .done (.clauses 2 outerCursor))) []
  let beforeSearch : Search :=
    .collectionBoundary ⟨20⟩ 0
      (.cutBoundary 9
        (.choice 3
          (.cutBoundary 1
            (.choice 1 (.task 1 [] []) (.clauses 1 innerCursor)))
          outerRight))
      (.integer 0) (.integer 9) [] [] []
  let afterSearch : Search :=
    .collectionBoundary ⟨20⟩ 0
      (.cutBoundary 9
        (.choice 3
          (.cutBoundary 1
            (.choice 1 .done (.clauses 1 innerCursor)))
          outerRight))
      (.integer 0) (.integer 9) [] []
      [(collectTemplate ({} : Session) (.integer 0) []).prepared.copied]
  let cell : SourceCollectionCell :=
    sourceCollectionCell 9 ⟨20⟩ 0 (.integer 0) (.integer 9) [] [] []
  let beforeAlts : List PLeaTTa.Alt :=
    innerResource.alts ++
      (PLeaTTa.Alt.barrier ::
        (outerResource.alts ++ [PLeaTTa.Alt.barrier]))
  have directTyped :
      ActiveFindallAnswerResourceAgrees [] ({} : Session) beforeSearch
        ({} : Session) afterSearch cell [] [innerResource, outerResource] []
        beforeAlts [] := by
    simpa [beforeSearch, afterSearch, cell, beforeAlts, outerRight] using direct
  refine ⟨beforeSearch, afterSearch, cell, innerResource, outerResource,
    beforeAlts, directTyped, ?_⟩
  exact
    .underProduct 11 []
      (.underChoice 10 .done directTyped)

end PLeaTTa.PrologFindallAnswerResourceBridge
