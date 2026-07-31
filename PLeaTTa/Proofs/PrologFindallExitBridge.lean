-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologFindallExitBridge
Purpose: Pop the same active source findall occurrence and fine executable
  frame when a local generator completes.
Trusted boundary: none
Main exports: ActiveFindallExit, ContextualFindallExitRelates,
  ActiveFindallExit.findallExit_occurrence_pop
-/
import PLeaTTa.Proofs.PrologFindallFrameZipperBridge

namespace PLeaTTa.PrologFindallExitBridge

open Metta (Atom GroundingTable Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.GoalSemantics
open PrologFindallFrameZipperBridge
open DemandDrivenStep

/-!
The source collector consumes its generator's final completion transition,
whereas the fine lane exits from the resulting terminal generator state.  The
relation below identifies that one source collection-completion event through
the same active leftmost wrapper grammar used by `activeCollectionCells`.

This tranche is deliberately control-only.  It proves that the matching source
occurrence and fine frame are removed together.  Relating the source
duplicate-sensitive bag and entry substitution to the fine copied bag remains
the subsequent payload theorem.
-/

/-- A source step that publicly completes cannot still contain an active
collection occurrence.  In particular, a nested collector must first exit to
a running caller task before an enclosing generator can complete. -/
theorem completed_target_has_no_active_collections
    {before after : Session} {search : Search}
    {events : List Observation} {signal : Trace.CutSignal}
    {target : RawTarget}
    (step : RawStep before search events signal after target)
    (targetExact : target = .terminal .completed) :
    activeCollectionCells search = some [] := by
  induction step <;> simp_all [activeCollectionCells]

theorem completed_step_has_no_active_collections
    {before after : Session} {search : Search}
    (step :
      RawStep before search [.completed] .none after
        (.terminal .completed)) :
    activeCollectionCells search = some [] :=
  completed_target_has_no_active_collections step rfl

set_option maxRecDepth 10000 in
/-- A raw transition that reaches ordinary completion cannot change the
persistent source session.  Session-changing primitive rules always produce
a running continuation; completion itself and every wrapper that propagates
it merely thread the child's endpoints. -/
theorem RawStep.completed_session_exact
    {before after : Session} {search : Search}
    {events : List Observation} {signal : Trace.CutSignal}
    {target : RawTarget}
    (step : RawStep before search events signal after target)
    (eventsExact : events = [.completed])
    (signalExact : signal = .none)
    (targetExact : target = .terminal .completed) :
    after = before := by
  induction step <;>
    try { cases targetExact } <;>
    try { cases signalExact } <;>
    try { cases eventsExact } <;>
    try rfl
  all_goals solve_by_elim

/-- One actual active `findall/3` exit, closed under exactly the wrappers that
can lie on the leftmost source control path.

The `here` constructor requires the real child completion transition through
the generator's cut boundary.  Every contextual constructor retains that
transition structurally; no executable frame or post-state is consulted to
locate the source occurrence. -/
inductive ActiveFindallExit :
    Session → Search → Session → Search → SourceCollectionCell → Prop where
  | here (before after : Session)
      (callerScope cutScope : CutScopeId)
      (collectionScope : CollectionScopeId)
      (body : Search) (template output : Term)
      (entryBindings : Substitution)
      (tail : List PeTTaSpec.PrologCore.Goal)
      (reversed : List Term)
      (child :
        RawStep before (.cutBoundary cutScope body) [.completed] .none after
          (.terminal .completed)) :
      ActiveFindallExit before
        (.collectionBoundary collectionScope callerScope
          (.cutBoundary cutScope body) template output entryBindings tail
          reversed)
        after
        (.task callerScope
          (.unify output (.list reversed.reverse none) :: tail)
          entryBindings)
        (sourceCollectionCell cutScope collectionScope callerScope template
          output entryBindings tail reversed)
  | underChoice (scope : CutScopeId) (right : Search)
      {before after : Session} {left next : Search}
      {cell : SourceCollectionCell}
      (inside : ActiveFindallExit before left after next cell) :
      ActiveFindallExit before (.choice scope left right) after
        (.choice scope next right) cell
  | underCut (scope : CutScopeId)
      {before after : Session} {body next : Search}
      {cell : SourceCollectionCell}
      (inside : ActiveFindallExit before body after next cell) :
      ActiveFindallExit before (.cutBoundary scope body) after
        (.cutBoundary scope next) cell
  | underCatch (handlerScope : ExceptionScopeId) (scope : CutScopeId)
      (catcher : Term) (handler : PeTTaSpec.PrologCore.Goal)
      (entryBindings : Substitution)
      {before after : Session} {body next : Search}
      {cell : SourceCollectionCell}
      (inside : ActiveFindallExit before body after next cell) :
      ActiveFindallExit before
        (.catchBoundary handlerScope scope body catcher handler entryBindings)
        after
        (.catchBoundary handlerScope scope next catcher handler entryBindings)
        cell
  | underCollection (collectionScope : CollectionScopeId)
      (callerScope outerCutScope : CutScopeId)
      (template output : Term) (entryBindings : Substitution)
      (tail : List PeTTaSpec.PrologCore.Goal) (reversed : List Term)
      {before after : Session} {body next : Search}
      {cell : SourceCollectionCell}
      (inside : ActiveFindallExit before body after next cell) :
      ActiveFindallExit before
        (.collectionBoundary collectionScope callerScope
          (.cutBoundary outerCutScope body) template output entryBindings tail
          reversed)
        after
        (.collectionBoundary collectionScope callerScope
          (.cutBoundary outerCutScope next) template output entryBindings tail
          reversed)
        cell
  | underProduct (scope : CutScopeId)
      (tail : List PeTTaSpec.PrologCore.Goal)
      {before after : Session} {head next : Search}
      {cell : SourceCollectionCell}
      (inside : ActiveFindallExit before head after next cell) :
      ActiveFindallExit before (.product scope head tail) after
        (.product scope next tail) cell

namespace ActiveFindallExit

/-- Exiting an active collector preserves the source session exactly.  This
is inherited from the real child-completion transition and remains true
under every allowed leftmost control wrapper. -/
theorem session_exact
    {before after : Session} {search next : Search}
    {cell : SourceCollectionCell}
    (exit : ActiveFindallExit before search after next cell) :
    after = before := by
  induction exit with
  | here _ _ _ _ _ _ _ _ _ _ _ child =>
      exact
        PLeaTTa.PrologFindallExitBridge.RawStep.completed_session_exact
          child rfl rfl rfl
  | underChoice _ _ inside inductionHypothesis =>
      exact inductionHypothesis
  | underCut _ inside inductionHypothesis =>
      exact inductionHypothesis
  | underCatch _ _ _ _ _ inside inductionHypothesis =>
      exact inductionHypothesis
  | underCollection _ _ _ _ _ _ _ _ inside inductionHypothesis =>
      exact inductionHypothesis
  | underProduct _ _ inside inductionHypothesis =>
      exact inductionHypothesis

/-- Every contextual exit is an actual source transition with no public
observation and no escaping cut signal. -/
theorem sourceStep
    {before after : Session} {search next : Search}
    {cell : SourceCollectionCell}
    (exit : ActiveFindallExit before search after next cell) :
    RawStep before search [] .none after (.running next) := by
  induction exit with
  | here before after callerScope cutScope collectionScope body template
      output entryBindings tail reversed child =>
      exact
        .collectionComplete collectionScope callerScope
          (.cutBoundary cutScope body) template output entryBindings tail
          reversed before after child
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

/-- Exact occurrence-stack effect of one contextual exit: the innermost active
source cell is removed and every older occurrence remains in the same order. -/
theorem cells_pop
    {before after : Session} {search next : Search}
    {cell : SourceCollectionCell}
    (exit : ActiveFindallExit before search after next cell) :
    ∃ cells,
      activeCollectionCells search = some (cell :: cells) ∧
        activeCollectionCells next = some cells := by
  induction exit with
  | here before after callerScope cutScope collectionScope body template
      output entryBindings tail reversed child =>
      have bodyEmpty :=
        completed_step_has_no_active_collections child
      have innerEmpty : activeCollectionCells body = some [] := by
        simpa [activeCollectionCells] using bodyEmpty
      refine ⟨[], ?_, rfl⟩
      simp [activeCollectionCells, innerEmpty]
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

/-- Positional occurrence agreement determines both the exact frame being
popped and the unchanged agreement for all remaining source cells/frames. -/
theorem occurrences_after
    {before after : Session} {search next : Search}
    {cell : SourceCollectionCell}
    (exit : ActiveFindallExit before search after next cell)
    {frame : FindallFrame} {remaining : List Frame}
    (agreement :
      CollectionOccurrenceAgrees search (.findall frame :: remaining)) :
    cell.AgreesFrame (.findall frame) ∧
      CollectionOccurrenceAgrees next remaining := by
  rcases exit.cells_pop with ⟨cells, beforeCells, afterCells⟩
  rw [CollectionOccurrenceAgrees, beforeCells] at agreement
  cases agreement with
  | cons head tail =>
      constructor
      · exact head
      · rw [CollectionOccurrenceAgrees, afterCells]
        exact tail

end ActiveFindallExit

/-- Exact control-only source/fine exit correspondence.

The source transition removes its innermost active collection occurrence.  The
fine transition pops the exact frame paired with that occurrence, retains the
generator's world and current scope frontiers, advances the executable fresh
counter by exactly its certified bag-copy operation, and leaves every older
occurrence/frame aligned.  Source/fine bag, substitution, and fresh-copy
agreement are intentionally not fields of this structure. -/
structure ContextualFindallExitRelates
    (prog : Prog) (gt : GroundingTable)
    (beforeSession : Session) (beforeSearch : Search)
    (afterSession : Session) (afterSearch : Search)
    (cell : SourceCollectionCell)
    (before after : OpenConf)
    (frame : FindallFrame) (remaining : List Frame) : Prop where
  sourceExit :
    ActiveFindallExit beforeSession beforeSearch afterSession afterSearch cell
  sourceStep :
    RawStep beforeSession beforeSearch [] .none afterSession
      (.running afterSearch)
  frameHead : before.frames = .findall frame :: remaining
  fineStep : DemandDrivenStep.Step prog gt before after
  fineTarget : after = resumeFindall before frame remaining
  frameIdentity : cell.AgreesFrame (.findall frame)
  occurrences : CollectionOccurrenceAgrees afterSearch after.frames
  framesPopped : after.frames = remaining
  scopesPreserved : after.scopes = before.scopes
  persistentAfterCopy :
    after.persistent =
      { before.persistent with
        counter :=
          (copyFindallBag before.persistent.counter
            before.control.answerValues).counter }

/-- One actual contextual source exit and one actual fine `findallExit` remove
the same occurrence and preserve the complete older occurrence stack. -/
theorem ActiveFindallExit.findallExit_occurrence_pop
    {prog : Prog} {gt : GroundingTable}
    {beforeSession afterSession : Session}
    {beforeSearch afterSearch : Search}
    {cell : SourceCollectionCell}
    (exit :
      ActiveFindallExit beforeSession beforeSearch afterSession afterSearch
        cell)
    {before : OpenConf} {frame : FindallFrame}
    {remaining : List Frame}
    (frameHead : before.frames = .findall frame :: remaining)
    (done : PLeaTTa.Terminal before.toConf)
    (beforeOccurrences :
      CollectionOccurrenceAgrees beforeSearch before.frames) :
    ContextualFindallExitRelates prog gt beforeSession beforeSearch
      afterSession afterSearch cell before
      (resumeFindall before frame remaining) frame remaining := by
  have aligned :
      cell.AgreesFrame (.findall frame) ∧
        CollectionOccurrenceAgrees afterSearch remaining := by
    apply exit.occurrences_after
    simpa [frameHead] using beforeOccurrences
  exact
    { sourceExit := exit
      sourceStep := exit.sourceStep
      frameHead := frameHead
      fineStep := .findallExit before frame remaining frameHead done
      fineTarget := rfl
      frameIdentity := aligned.1
      occurrences := by
        simpa [resumeFindall] using aligned.2
      framesPopped := rfl
      scopesPreserved := rfl
      persistentAfterCopy := rfl }

/-- Exit consumes exactly one executable frame; the claim follows from the
literal pre-state head equation and post-state frame list, not from a count
stored independently. -/
theorem ContextualFindallExitRelates.frames_length_exact
    {prog : Prog} {gt : GroundingTable}
    {beforeSession afterSession : Session}
    {beforeSearch afterSearch : Search}
    {cell : SourceCollectionCell} {before after : OpenConf}
    {frame : FindallFrame} {remaining : List Frame}
    (related :
      ContextualFindallExitRelates prog gt beforeSession beforeSearch
        afterSession afterSearch cell before after frame remaining) :
    after.frames.length + 1 = before.frames.length := by
  rw [related.framesPopped, related.frameHead]
  simp

/-- If nested execution advanced beyond the frame's historical collection
frontier, exit retains that distinction instead of rolling the allocator back
to the entry value. -/
theorem ContextualFindallExitRelates.collection_frontier_not_rolled_back
    {prog : Prog} {gt : GroundingTable}
    {beforeSession afterSession : Session}
    {beforeSearch afterSearch : Search}
    {cell : SourceCollectionCell} {before after : OpenConf}
    {frame : FindallFrame} {remaining : List Frame}
    (related :
      ContextualFindallExitRelates prog gt beforeSession beforeSearch
        afterSession afterSearch cell before after frame remaining)
    (advanced :
      before.scopes.nextCollectionScope ≠ frame.preCollection) :
    after.scopes.nextCollectionScope ≠ frame.preCollection := by
  rw [related.scopesPreserved]
  exact advanced

/-- Exit retains the generator's current world rather than restoring the
world stored in the suspended outer continuation. -/
theorem ContextualFindallExitRelates.world_preserved
    {prog : Prog} {gt : GroundingTable}
    {beforeSession afterSession : Session}
    {beforeSearch afterSearch : Search}
    {cell : SourceCollectionCell} {before after : OpenConf}
    {frame : FindallFrame} {remaining : List Frame}
    (related :
      ContextualFindallExitRelates prog gt beforeSession beforeSearch
        afterSession afterSearch cell before after frame remaining) :
    after.persistent.world = before.persistent.world := by
  rw [related.persistentAfterCopy]

/-- Exit advances the executable fresh high-water by exactly the local
machine's bag-copy operation; it neither restores the frame-entry counter nor
permits an unrelated counter change. -/
theorem ContextualFindallExitRelates.counter_after_copy
    {prog : Prog} {gt : GroundingTable}
    {beforeSession afterSession : Session}
    {beforeSearch afterSearch : Search}
    {cell : SourceCollectionCell} {before after : OpenConf}
    {frame : FindallFrame} {remaining : List Frame}
    (related :
      ContextualFindallExitRelates prog gt beforeSession beforeSearch
        afterSession afterSearch cell before after frame remaining) :
    after.persistent.counter =
      (copyFindallBag before.persistent.counter
        before.control.answerValues).counter := by
  rw [related.persistentAfterCopy]

/-- A frame with a different pre-entry cut identity cannot be popped from an
occurrence-aligned state.  This is the exit-specific anti-laundering guard. -/
theorem ActiveFindallExit.wrong_head_frame_rejected
    {before after : Session} {search next : Search}
    {cell : SourceCollectionCell}
    (exit : ActiveFindallExit before search after next cell)
    (frame : FindallFrame) (remaining : List Frame)
    (different : frame.preCut ≠ cell.cutScope) :
    ¬ CollectionOccurrenceAgrees search (.findall frame :: remaining) := by
  intro agreement
  exact different (exit.occurrences_after agreement).1.1

/-- The direct empty-generator exit is inhabited by the actual source
completion constructors. -/
theorem direct_empty_generator_exit_inhabited
    (session : Session) (callerScope cutScope : CutScopeId)
    (collectionScope : CollectionScopeId)
    (template output : Term) (entryBindings : Substitution)
    (tail : List PeTTaSpec.PrologCore.Goal) (reversed : List Term) :
    ActiveFindallExit session
      (.collectionBoundary collectionScope callerScope
        (.cutBoundary cutScope .done) template output entryBindings tail
        reversed)
      session
      (.task callerScope
        (.unify output (.list reversed.reverse none) :: tail)
        entryBindings)
      (sourceCollectionCell cutScope collectionScope callerScope template
        output entryBindings tail reversed) := by
  apply ActiveFindallExit.here
  exact .cutBoundaryComplete cutScope .done session session (.done session)

end PLeaTTa.PrologFindallExitBridge
