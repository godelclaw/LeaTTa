-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologFindallFrameZipperBridge
Purpose: Pair every active source findall occurrence with the corresponding
  fine executable frame in exact innermost-to-outermost order.
Trusted boundary: none
Main exports: activeCollectionCells, CollectionOccurrenceAgrees,
  enterActiveFindall_findallEnter_occurrence_prepend
-/
import PLeaTTa.Proofs.PrologFindallEntryBridge

namespace PLeaTTa.PrologFindallFrameZipperBridge

open Metta (Atom GroundingTable Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.GoalSemantics
open PrologStateBridge
open PrologFindallEntryBridge
open DemandDrivenStep

/-!
The source search tree stores active collectors outermost-to-innermost, while
the fine machine stores suspended callers in LIFO order.  The extractor below
therefore returns source cells innermost-to-outermost.  It is a function of the
source state alone and fails closed when a collection boundary has lost its
mandatory generator cut boundary.

The correspondence matches the applied extractor directly against the actual
frame list.  There is no existentially supplied cell list, no value search,
and no reconstruction from a post-entry high-water.
-/

/-- Source-owned, immutable fields of one active `findall/3` occurrence.
`reversed` is included because it is part of the live collector, although the
control-only frame relation below deliberately makes no payload claim. -/
structure SourceCollectionCell where
  cutScope : CutScopeId
  collectionScope : CollectionScopeId
  callerScope : CutScopeId
  template : Term
  output : Term
  entryBindings : Substitution
  tail : List PeTTaSpec.PrologCore.Goal
  reversed : List Term
deriving Repr

/-- Build one cell from the exact source boundary fields. -/
def sourceCollectionCell (cutScope : CutScopeId)
    (collectionScope : CollectionScopeId) (callerScope : CutScopeId)
    (template output : Term) (entryBindings : Substitution)
    (tail : List PeTTaSpec.PrologCore.Goal) (reversed : List Term) :
    SourceCollectionCell :=
  { cutScope := cutScope
    collectionScope := collectionScope
    callerScope := callerScope
    template := template
    output := output
    entryBindings := entryBindings
    tail := tail
    reversed := reversed }

/-- Active source collection occurrences, innermost first.

Only the left branch of a choice is executing.  A collection is accepted only
when its body is the cut boundary installed by `taskFindall`; malformed states
return `none` instead of inventing or omitting an identity. -/
def activeCollectionCells : Search → Option (List SourceCollectionCell)
  | .done => some []
  | .task _ _ _ => some []
  | .clauses _ _ => some []
  | .raise _ => some []
  | .choice _ left _ => activeCollectionCells left
  | .cutBoundary _ body => activeCollectionCells body
  | .catchBoundary _ _ body _ _ _ => activeCollectionCells body
  | .collectionBoundary collectionScope callerScope body template output
      entryBindings tail reversed =>
      match body with
      | .cutBoundary cutScope inner =>
          (activeCollectionCells inner).map fun innerCells =>
            innerCells ++
              [sourceCollectionCell cutScope collectionScope callerScope
                template output entryBindings tail reversed]
      | _ => none
  | .product _ head _ => activeCollectionCells head

/-- A source cell agrees with one executable frame exactly when the frame
records the same pre-entry cut and collection indices.  Payload agreement is
intentionally a separate later relation. -/
def SourceCollectionCell.AgreesFrame
    (cell : SourceCollectionCell) : Frame → Prop
  | .findall frame =>
      frame.preCut = cell.cutScope ∧
        frame.preCollection = cell.collectionScope.index

/-- Fail-closed, positional occurrence correspondence.  The source state
alone determines the cell list; executable frames cannot influence extraction
depth or order. -/
def CollectionOccurrenceAgrees (search : Search)
    (frames : List Frame) : Prop :=
  match activeCollectionCells search with
  | none => False
  | some cells => List.Forall₂ SourceCollectionCell.AgreesFrame cells frames

/-- Reachable progress through a source cut boundary retains that exact
boundary.  This justifies the extractor's expected collection-body shape on
running states; malformed forged states are still rejected independently. -/
theorem cutBoundary_running_shape
    {before after : Session} {scope : CutScopeId} {body next : Search}
    {events : List Observation} {signal : Trace.CutSignal}
    (step :
      RawStep before (.cutBoundary scope body) events signal after
        (.running next)) :
    ∃ nextBody, next = .cutBoundary scope nextBody := by
  cases step <;> simp_all

@[simp] theorem activeCollectionCells_collection
    (collectionScope : CollectionScopeId) (callerScope cutScope : CutScopeId)
    (inner : Search) (template output : Term)
    (entryBindings : Substitution) (tail : List PeTTaSpec.PrologCore.Goal)
    (reversed : List Term) :
    activeCollectionCells
        (.collectionBoundary collectionScope callerScope
          (.cutBoundary cutScope inner) template output entryBindings tail
          reversed) =
      (activeCollectionCells inner).map fun innerCells =>
        innerCells ++
          [sourceCollectionCell cutScope collectionScope callerScope template
            output entryBindings tail reversed] := rfl

/-- Exact target shape forced by an emitted answer.  An answer-producing raw
step remains running and exposes no live collection occurrence; a terminal
target is impossible in that same transition. -/
def AnswerSuccessorCollectionFree : RawTarget → Prop
  | .terminal _ => False
  | .running next => activeCollectionCells next = some []

/-- Any emitted source answer is outside every live collection boundary:
the innermost `collectionAnswer` consumes such an observation.  Both the
source and its raw target are therefore collection-free.

This is an event-membership inversion over the complete `RawStep` grammar,
not a reachability assumption supplied by a later bisimulation. -/
theorem RawStep.answer_mem_activeCollectionFree
    {before after : Session} {search : Search}
    {events : List Observation} {signal : Trace.CutSignal}
    {target : RawTarget}
    (step : RawStep before search events signal after target)
    {bindings : Substitution}
    (present : .answer bindings ∈ events) :
    activeCollectionCells search = some [] ∧
      AnswerSuccessorCollectionFree target := by
  induction step generalizing bindings
  case clausesPull pulled =>
    cases pulled <;>
      simp_all [localPullEvents]
  all_goals
    simp_all [AnswerSuccessorCollectionFree, activeCollectionCells,
      Trace.AnswerFree]
  -- The remaining goals are transparent left-path wrappers: choice
  -- progress/commit, cut-boundary progress/catch/pass, and catch progress.
  -- Each conclusion is exactly the corresponding child induction hypothesis.
  all_goals solve_by_elim

/-- Exact one-answer/running specialization used by the active-collector
producer. -/
theorem RawStep.answer_activeCollectionCells_empty
    {before after : Session} {search next : Search}
    {bindings : Substitution}
    (step :
      RawStep before search [.answer bindings] .none after
        (.running next)) :
    activeCollectionCells search = some [] ∧
      activeCollectionCells next = some [] := by
  simpa [AnswerSuccessorCollectionFree] using
    answer_mem_activeCollectionFree step (bindings := bindings) (by simp)

/-- One raw transition cannot both emit an answer and terminate (successfully
or exceptionally). -/
theorem RawStep.answer_mem_not_terminal
    {before after : Session} {search : Search}
    {events : List Observation} {signal : Trace.CutSignal}
    {target : RawTarget}
    (step : RawStep before search events signal after target)
    {bindings : Substitution}
    (present : .answer bindings ∈ events)
    (tag : RawTerminal) :
    target ≠ .terminal tag := by
  intro terminal
  subst target
  exact (answer_mem_activeCollectionFree step present).2

/-- A live collection consumes every child answer; no collection-boundary
transition can expose one to its enclosing context. -/
theorem RawStep.collectionBoundary_answerFree
    {before after : Session} {collectionScope : CollectionScopeId}
    {callerScope : CutScopeId} {body : Search} {template output : Term}
    {entryBindings : Substitution} {tail : List PeTTaSpec.PrologCore.Goal}
    {reversed : List Term} {events : List Observation}
    {signal : Trace.CutSignal} {target : RawTarget}
    (step :
      RawStep before
        (.collectionBoundary collectionScope callerScope body template output
          entryBindings tail reversed)
        events signal after target) :
    Trace.AnswerFree events := by
  intro bindings present
  have empty := (answer_mem_activeCollectionFree step present).1
  cases body <;> simp [activeCollectionCells] at empty

/-- Exact aligned length; no source occurrence or executable frame may be
inserted, dropped, or duplicated independently. -/
theorem CollectionOccurrenceAgrees.length_eq
    {search : Search} {frames : List Frame}
    (agreement : CollectionOccurrenceAgrees search frames)
    {cells : List SourceCollectionCell}
    (cellsExact : activeCollectionCells search = some cells) :
    cells.length = frames.length := by
  rw [CollectionOccurrenceAgrees, cellsExact] at agreement
  exact List.Forall₂.length_eq agreement

/-- A collection without its generator cut boundary is rejected rather than
silently shortened to an empty source list. -/
theorem missing_cut_boundary_rejected
    (collectionScope : CollectionScopeId) (callerScope : CutScopeId)
    (template output : Term) (entryBindings : Substitution)
    (tail : List PeTTaSpec.PrologCore.Goal) (reversed : List Term)
    (frames : List Frame) :
    ¬ CollectionOccurrenceAgrees
      (.collectionBoundary collectionScope callerScope .done template output
        entryBindings tail reversed)
      frames := by
  simp [CollectionOccurrenceAgrees, activeCollectionCells]

/-- A dormant right choice cannot manufacture an active frame. -/
theorem right_choice_collection_cannot_supply_frame
    (scope callerScope cutScope : CutScopeId)
    (collectionScope : CollectionScopeId)
    (template output : Term) (entryBindings : Substitution)
    (tail : List PeTTaSpec.PrologCore.Goal) (reversed : List Term)
    (frame : FindallFrame) :
    ¬ CollectionOccurrenceAgrees
      (.choice scope .done
        (.collectionBoundary collectionScope callerScope
          (.cutBoundary cutScope .done) template output entryBindings tail
          reversed))
      [.findall frame] := by
  simp [CollectionOccurrenceAgrees, activeCollectionCells]

/-- Source cell created by the actual `taskFindall` entry constructor. -/
def sourceEntryCell (session : Session) (callerScope : CutScopeId)
    (template output : Term) (entryBindings : Substitution)
    (tail : List PeTTaSpec.PrologCore.Goal) : SourceCollectionCell :=
  sourceCollectionCell (openFindall session).cutScope
    (openFindall session).collectionScope callerScope template output
    entryBindings tail []

/-- Certified result of locating and entering the unique active `findall`
head.  Besides the actual source transition, the result proves that extraction
gains exactly one innermost cell and that its IDs came from the incoming source
frontiers. -/
structure ActiveFindallEntryResult
    (beforeSession : Session) (beforeSearch : Search) where
  afterSession : Session
  afterSearch : Search
  cell : SourceCollectionCell
  sourceStep :
    RawStep beforeSession beforeSearch [] .none afterSession
      (.running afterSearch)
  afterSessionExact :
    afterSession = (openFindall beforeSession).session
  cutExact :
    cell.cutScope = beforeSession.nextCutScope
  collectionExact :
    cell.collectionScope.index = beforeSession.nextCollectionScope
  cellsPrepend :
    ∀ cells,
      activeCollectionCells beforeSearch = some cells →
        activeCollectionCells afterSearch = some (cell :: cells)

/-- Enter the active leftmost `findall` occurrence, if one exists.

This is a verified source-side algorithm, not a search guided by executable
frames.  Every successful result carries its exact `RawStep` and occurrence
update; malformed collection boundaries and non-active right branches are
rejected. -/
def enterActiveFindall (session : Session) :
    (search : Search) → Option (ActiveFindallEntryResult session search)
  | .task scope (.findall template generator output :: rest) bindings =>
      some
        { afterSession := (openFindall session).session
          afterSearch :=
            sourceFindallTarget session scope template generator output rest
              bindings
          cell := sourceEntryCell session scope template output bindings rest
          sourceStep :=
            .taskFindall scope template generator output rest bindings session
          afterSessionExact := rfl
          cutExact := rfl
          collectionExact := rfl
          cellsPrepend := by
            intro cells beforeCells
            simp [activeCollectionCells] at beforeCells
            subst cells
            rfl }
  | .choice scope left right =>
      match enterActiveFindall session left with
      | none => none
      | some entered =>
          some
            { afterSession := entered.afterSession
              afterSearch := .choice scope entered.afterSearch right
              cell := entered.cell
              sourceStep :=
                .choiceProgress scope left right entered.afterSearch []
                  session entered.afterSession entered.sourceStep
              afterSessionExact := entered.afterSessionExact
              cutExact := entered.cutExact
              collectionExact := entered.collectionExact
              cellsPrepend := by
                intro cells beforeCells
                simpa [activeCollectionCells] using
                  entered.cellsPrepend cells beforeCells }
  | .cutBoundary scope body =>
      match enterActiveFindall session body with
      | none => none
      | some entered =>
          some
            { afterSession := entered.afterSession
              afterSearch := .cutBoundary scope entered.afterSearch
              cell := entered.cell
              sourceStep :=
                .cutBoundaryProgress scope body entered.afterSearch []
                  session entered.afterSession entered.sourceStep
              afterSessionExact := entered.afterSessionExact
              cutExact := entered.cutExact
              collectionExact := entered.collectionExact
              cellsPrepend := by
                intro cells beforeCells
                simpa [activeCollectionCells] using
                  entered.cellsPrepend cells beforeCells }
  | .catchBoundary handlerScope scope body catcher handler entryBindings =>
      match enterActiveFindall session body with
      | none => none
      | some entered =>
          some
            { afterSession := entered.afterSession
              afterSearch :=
                .catchBoundary handlerScope scope entered.afterSearch catcher
                  handler entryBindings
              cell := entered.cell
              sourceStep :=
                .catchProgress handlerScope scope body entered.afterSearch
                  catcher handler entryBindings [] .none session
                  entered.afterSession entered.sourceStep
              afterSessionExact := entered.afterSessionExact
              cutExact := entered.cutExact
              collectionExact := entered.collectionExact
              cellsPrepend := by
                intro cells beforeCells
                simpa [activeCollectionCells] using
                  entered.cellsPrepend cells beforeCells }
  | .collectionBoundary collectionScope callerScope
      (.cutBoundary cutScope inner) template output entryBindings tail
      reversed =>
      match enterActiveFindall session inner with
      | none => none
      | some entered =>
          let nextBody := .cutBoundary cutScope entered.afterSearch
          let next :=
            .collectionBoundary collectionScope callerScope nextBody template
              output entryBindings tail reversed
          have boundaryStep :
              RawStep session (.cutBoundary cutScope inner) [] .none
                entered.afterSession (.running nextBody) :=
            .cutBoundaryProgress cutScope inner entered.afterSearch []
              session entered.afterSession entered.sourceStep
          some
            { afterSession := entered.afterSession
              afterSearch := next
              cell := entered.cell
              sourceStep :=
                .collectionProgress collectionScope callerScope
                  (.cutBoundary cutScope inner) nextBody template output
                  entryBindings tail reversed [] .none session
                  entered.afterSession boundaryStep (by
                    simp [Trace.AnswerFree])
              afterSessionExact := entered.afterSessionExact
              cutExact := entered.cutExact
              collectionExact := entered.collectionExact
              cellsPrepend := by
                intro cells beforeCells
                cases innerCellsExact :
                    activeCollectionCells inner with
                | none =>
                    simp [activeCollectionCells, innerCellsExact]
                      at beforeCells
                | some innerCells =>
                    simp [activeCollectionCells, innerCellsExact]
                      at beforeCells
                    subst cells
                    have enteredCells :=
                      entered.cellsPrepend innerCells innerCellsExact
                    simp [next, nextBody, activeCollectionCells,
                      enteredCells] }
  | .product scope head tail =>
      match enterActiveFindall session head with
      | none => none
      | some entered =>
          some
            { afterSession := entered.afterSession
              afterSearch := .product scope entered.afterSearch tail
              cell := entered.cell
              sourceStep :=
                .productProgress scope head entered.afterSearch tail []
                  .none session entered.afterSession entered.sourceStep (by
                    simp [Trace.AnswerFree])
              afterSessionExact := entered.afterSessionExact
              cutExact := entered.cutExact
              collectionExact := entered.collectionExact
              cellsPrepend := by
                intro cells beforeCells
                simpa [activeCollectionCells] using
                  entered.cellsPrepend cells beforeCells }
  | _ => none

/-- The source cell produced by contextual entry agrees with the fine frame
produced from the same pre-state.  The proof uses the executable frame's own
recorded frontiers and the exact pre-state relation; it never reads a source
identity while constructing the frame. -/
theorem ActiveFindallEntryResult.agrees_executableFrame
    {freshFrontier : FreshFrontierRelation}
    {session : Session} {search : Search} {before : OpenConf}
    (entered : ActiveFindallEntryResult session search)
    (agreement :
      SessionRelatesOpenConf freshFrontier ExactControlFrontiers
        session before)
    (template result : Atom) (rest : List PLeaTTa.Goal)
    (binding : Subst) :
    entered.cell.AgreesFrame
      (.findall
        (executableFindallFrame before template result rest binding)) := by
  constructor
  · exact agreement.cut.symm.trans entered.cutExact.symm
  · exact agreement.collection.symm.trans entered.collectionExact.symm

/-- One certified contextual source entry and one fine frame push preserve the
entire positional occurrence relation. -/
theorem CollectionOccurrenceAgrees.prepend
    {beforeSearch afterSearch : Search}
    {beforeFrames : List Frame} {cell : SourceCollectionCell}
    {frame : FindallFrame}
    (beforeAgreement :
      CollectionOccurrenceAgrees beforeSearch beforeFrames)
    (cellsPrepend :
      ∀ cells,
        activeCollectionCells beforeSearch = some cells →
          activeCollectionCells afterSearch = some (cell :: cells))
    (headAgreement : cell.AgreesFrame (.findall frame)) :
    CollectionOccurrenceAgrees afterSearch
      (.findall frame :: beforeFrames) := by
  cases cellsExact : activeCollectionCells beforeSearch with
  | none =>
      simp [CollectionOccurrenceAgrees, cellsExact] at beforeAgreement
  | some cells =>
      have afterCells := cellsPrepend cells cellsExact
      rw [CollectionOccurrenceAgrees, afterCells]
      rw [CollectionOccurrenceAgrees, cellsExact] at beforeAgreement
      exact .cons headAgreement beforeAgreement

/-- Exact nested source-entry/fine-entry control correspondence.

The source transition comes from the proof-producing active-path algorithm.
The fine transition is the real `findallEnter` constructor.  The persistent
and typed allocator relation advances in lockstep, and the new occurrence is
prepended to the already-related inner-to-outer cells/frames.  Payload and
observation agreement remain separate obligations. -/
structure ContextualFindallEntryRelates
    (freshFrontier : FreshFrontierRelation)
    (prog : Prog) (gt : GroundingTable)
    (session : Session) (search : Search)
    (before : OpenConf)
    (entered : ActiveFindallEntryResult session search)
    (template : Atom) (sub : List PLeaTTa.Goal) (result : Atom)
    (rest : List PLeaTTa.Goal) (binding : Subst)
    (after : OpenConf) : Prop where
  fineStep : DemandDrivenStep.Step prog gt before after
  target :
    after = enterFindall before template sub result rest binding
  afterAgreement :
    SessionRelatesOpenConf freshFrontier ExactControlFrontiers
      entered.afterSession after
  occurrences :
    CollectionOccurrenceAgrees entered.afterSearch after.frames

/-- Contextual entry consumes the previously proved single-entry theorem at
arbitrary active source depth: one source cell and one executable frame are
added at the innermost end, while every older occurrence stays aligned.

[SPEC translator.pl:112-116] -/
theorem enterActiveFindall_findallEnter_occurrence_prepend
    {freshFrontier : FreshFrontierRelation}
    {prog : Prog} {gt : GroundingTable}
    {session : Session} {search : Search} {before : OpenConf}
    (entered : ActiveFindallEntryResult session search)
    (persistent :
      SessionRelatesOpenConf freshFrontier ExactControlFrontiers
        session before)
    (beforeOccurrences :
      CollectionOccurrenceAgrees search before.frames)
    (template : Atom) (sub : List PLeaTTa.Goal) (result : Atom)
    (rest : List PLeaTTa.Goal) (binding : Subst)
    (head :
      before.toConf.cur =
        some (PLeaTTa.Goal.findall template sub result :: rest, binding)) :
    ContextualFindallEntryRelates freshFrontier prog gt session search before
      entered template sub result rest binding
      (enterFindall before template sub result rest binding) := by
  let after := enterFindall before template sub result rest binding
  have afterPersistent :
      SessionRelatesPersistent freshFrontier
        (openFindall session).session after.persistent := by
    rw [enterFindall_persistent]
    exact
      openFindall_preserves_persistent_relation freshFrontier session
        before.persistent persistent.persistent
  have afterAgreement :
      SessionRelatesOpenConf freshFrontier ExactControlFrontiers
        (openFindall session).session after := by
    exact
      SessionRelatesOpenConf.exact_afterFindall persistent afterPersistent rfl
  have afterAgreement' :
      SessionRelatesOpenConf freshFrontier ExactControlFrontiers
        entered.afterSession after := by
    rw [entered.afterSessionExact]
    exact afterAgreement
  have headAgreement :
      entered.cell.AgreesFrame
        (.findall
          (executableFindallFrame before template result rest binding)) :=
    entered.agrees_executableFrame persistent template result rest binding
  have occurrences :
      CollectionOccurrenceAgrees entered.afterSearch after.frames := by
    change
      CollectionOccurrenceAgrees entered.afterSearch
        (.findall
          (executableFindallFrame before template result rest binding) ::
          before.frames)
    exact
      beforeOccurrences.prepend entered.cellsPrepend headAgreement
  exact
    { fineStep :=
        .findallEnter before template sub result rest binding head
      target := rfl
      afterAgreement := afterAgreement'
      occurrences := occurrences }

/-- Minimal two-level active collector state used to discriminate positional
occurrence pairing.  The payload is intentionally fixed: only delimiter order
is under test. -/
def twoCollectionSearch
    (outerCut innerCut : CutScopeId)
    (outerCollection innerCollection : CollectionScopeId) : Search :=
  .collectionBoundary outerCollection 0
    (.cutBoundary outerCut
      (.collectionBoundary innerCollection outerCut
        (.cutBoundary innerCut .done)
        (.atom "inner-template") (.atom "inner-output") [] [] []))
    (.atom "outer-template") (.atom "outer-output") [] [] []

/-- Correct innermost-to-outermost frame order is inhabited for two distinct
active collectors. -/
theorem two_collection_occurrences_inhabited
    (outerCut innerCut : CutScopeId)
    (outerCollection innerCollection : CollectionScopeId)
    (innerFrame outerFrame : FindallFrame)
    (innerCutExact : innerFrame.preCut = innerCut)
    (innerCollectionExact :
      innerFrame.preCollection = innerCollection.index)
    (outerCutExact : outerFrame.preCut = outerCut)
    (outerCollectionExact :
      outerFrame.preCollection = outerCollection.index) :
    CollectionOccurrenceAgrees
      (twoCollectionSearch outerCut innerCut outerCollection innerCollection)
      [.findall innerFrame, .findall outerFrame] := by
  simp [twoCollectionSearch, CollectionOccurrenceAgrees,
    activeCollectionCells, SourceCollectionCell.AgreesFrame,
    sourceCollectionCell, innerCutExact, innerCollectionExact, outerCutExact,
    outerCollectionExact]

/-- Swapping two nested frames with distinct cut occurrence IDs is rejected.
The explicit inequality keeps the witness non-vacuous. -/
theorem swapped_distinct_collection_frames_rejected
    (outerCut innerCut : CutScopeId)
    (outerCollection innerCollection : CollectionScopeId)
    (innerFrame outerFrame : FindallFrame)
    (different : innerCut ≠ outerCut)
    (outerCutExact : outerFrame.preCut = outerCut) :
    ¬ CollectionOccurrenceAgrees
      (twoCollectionSearch outerCut innerCut outerCollection innerCollection)
      [.findall outerFrame, .findall innerFrame] := by
  intro agreement
  change
    List.Forall₂ SourceCollectionCell.AgreesFrame
      [sourceCollectionCell innerCut innerCollection outerCut
        (.atom "inner-template") (.atom "inner-output") [] [] [],
       sourceCollectionCell outerCut outerCollection 0
        (.atom "outer-template") (.atom "outer-output") [] [] []]
      [.findall outerFrame, .findall innerFrame] at agreement
  cases agreement with
  | cons firstCutAndCollection remaining =>
      exact
        different
          (firstCutAndCollection.1.symm.trans outerCutExact)

/-- A third executable frame cannot be hidden behind two source occurrences. -/
theorem duplicated_collection_frame_rejected
    (outerCut innerCut : CutScopeId)
    (outerCollection innerCollection : CollectionScopeId)
    (innerFrame outerFrame duplicate : FindallFrame) :
    ¬ CollectionOccurrenceAgrees
      (twoCollectionSearch outerCut innerCut outerCollection innerCollection)
      [.findall innerFrame, .findall outerFrame, .findall duplicate] := by
  intro agreement
  have lengths :=
    agreement.length_eq
      (show
        activeCollectionCells
            (twoCollectionSearch outerCut innerCut outerCollection
              innerCollection) =
          some
            [sourceCollectionCell innerCut innerCollection outerCut
              (.atom "inner-template") (.atom "inner-output") [] [] [],
             sourceCollectionCell outerCut outerCollection 0
              (.atom "outer-template") (.atom "outer-output") [] [] []] by
        rfl)
  simp at lengths

end PLeaTTa.PrologFindallFrameZipperBridge
