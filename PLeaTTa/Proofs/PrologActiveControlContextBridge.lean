-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologActiveControlContextBridge
Purpose: Lift answer-free, noncommitting local source progress through the
  exact active leftmost control path while preserving collector occurrences
Trusted boundary: none
Main exports: ActiveControlFrame, ActiveControlContext,
  ActiveControlContext.liftProgress,
  ActiveControlContext.plug_activeCollectionCells,
  ActiveControlContext.enterFindallResult
-/
import PLeaTTa.Proofs.PrologFindallFrameZipperBridge

namespace PLeaTTa.PrologActiveControlContextBridge

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PrologFindallEntryBridge
open PrologFindallFrameZipperBridge

/-!
# Control-only active contexts

This zipper records only the source constructors on the active leftmost path.
It deliberately contains no executable alternative bank, retained-cursor
descriptor, or machine resource.  In particular, a `findall/3` frame is a
control discontinuity: its executable generator starts with an empty
alternative bank while the outer bank lives in `FindallFrame.outer`.

The collection constructor owns its generator cut boundary structurally.
Consequently malformed collection states without that boundary cannot be
represented, and a separate adjacent `cut` constructor denotes a genuinely
second boundary.
-/

/-- One transparent source-control frame surrounding the active focus.

`cut` stores the outer active scope as proof-relevant typing data even though
the `Search.cutBoundary` syntax stores only the inner cut identity.  Collection
stores both its caller scope and its distinct owned generator-cut scope. -/
inductive ActiveControlFrame where
  | choiceLeft (scope : CutScopeId) (right : Search)
  | cut (outerScope innerScope : CutScopeId)
  | catchBoundary (handlerScope : ExceptionScopeId) (scope : CutScopeId)
      (catcher : Term) (handler : PeTTaSpec.PrologCore.Goal)
      (entryBindings : Substitution)
  | collection (collectionScope : CollectionScopeId)
      (callerScope generatorScope : CutScopeId)
      (template output : Term) (entryBindings : Substitution)
      (tail : List PeTTaSpec.PrologCore.Goal) (reversed : List Term)
  | productHead (scope : CutScopeId)
      (tail : List PeTTaSpec.PrologCore.Goal)
deriving Repr

namespace ActiveControlFrame

/-- Scope expected of the active focus before this frame is installed. -/
def innerScope : ActiveControlFrame → CutScopeId
  | .choiceLeft scope _ => scope
  | .cut _ innerScope => innerScope
  | .catchBoundary _ scope _ _ _ => scope
  | .collection _ _ generatorScope _ _ _ _ _ => generatorScope
  | .productHead scope _ => scope

/-- Scope exposed to the next outer frame. -/
def outerScope : ActiveControlFrame → CutScopeId
  | .choiceLeft scope _ => scope
  | .cut outerScope _ => outerScope
  | .catchBoundary _ scope _ _ _ => scope
  | .collection _ callerScope _ _ _ _ _ _ => callerScope
  | .productHead scope _ => scope

/-- Install the active focus into one source-control frame. -/
def wrap : ActiveControlFrame → Search → Search
  | .choiceLeft scope right, focus => .choice scope focus right
  | .cut _ innerScope, focus => .cutBoundary innerScope focus
  | .catchBoundary handlerScope scope catcher handler entryBindings, focus =>
      .catchBoundary handlerScope scope focus catcher handler entryBindings
  | .collection collectionScope callerScope generatorScope template output
      entryBindings tail reversed, focus =>
      .collectionBoundary collectionScope callerScope
        (.cutBoundary generatorScope focus) template output entryBindings tail
        reversed
  | .productHead scope tail, focus => .product scope focus tail

/-- The inactive cursors structurally owned by this control frame.

Only a choice contributes cursors.  This is source ownership, not an
executable alternative-bank relation. -/
def retainedCursors : ActiveControlFrame → List CursorToken
  | .choiceLeft _ right => right.liveCursors
  | _ => []

/-- The active collection occurrence contributed by this frame, if any. -/
def collectionCells : ActiveControlFrame → List SourceCollectionCell
  | .collection collectionScope callerScope generatorScope template output
      entryBindings tail reversed =>
      [sourceCollectionCell generatorScope collectionScope callerScope
        template output entryBindings tail reversed]
  | _ => []

/-- The only additional scope premise is the inactive branch of a choice.
Every other frame is structurally well-typed once its focus has the declared
inner scope. -/
def Valid : ActiveControlFrame → Prop
  | .choiceLeft scope right => right.WellScoped scope
  | _ => True

@[simp] theorem wrap_liveCursors
    (frame : ActiveControlFrame) (focus : Search) :
    (frame.wrap focus).liveCursors =
      focus.liveCursors ++ frame.retainedCursors := by
  cases frame <;> simp [wrap, retainedCursors, Search.liveCursors]

/-- Collector extraction crosses each frame compositionally.  The focus's
innermost cells remain first; a collection frame appends its own cell.  A
malformed focus remains `none` rather than being repaired by the context. -/
@[simp] theorem wrap_activeCollectionCells
    (frame : ActiveControlFrame) (focus : Search) :
    activeCollectionCells (frame.wrap focus) =
      (activeCollectionCells focus).map fun cells =>
        cells ++ frame.collectionCells := by
  cases frame <;> simp [wrap, collectionCells, activeCollectionCells]

/-- One frame preserves structural cut-scope discipline.  A collection's
owned generator cut maps `generatorScope` to `callerScope`; an adjacent `cut`
frame therefore remains a separate boundary. -/
theorem wrap_wellScoped
    (frame : ActiveControlFrame) {focus : Search}
    (valid : frame.Valid)
    (focusScoped : focus.WellScoped frame.innerScope) :
    (frame.wrap focus).WellScoped frame.outerScope := by
  cases frame with
  | choiceLeft scope right =>
      exact .choice scope focus right focusScoped valid
  | cut outerScope innerScope =>
      exact .cutBoundary outerScope innerScope focus focusScoped
  | catchBoundary handlerScope scope catcher handler entryBindings =>
      exact .catchBoundary scope handlerScope focus catcher handler
        entryBindings focusScoped
  | collection collectionScope callerScope generatorScope template output
      entryBindings tail reversed =>
      exact
        .collectionBoundary callerScope collectionScope
          (.cutBoundary generatorScope focus) template output entryBindings
          tail reversed
          (.cutBoundary callerScope generatorScope focus focusScoped)
  | productHead scope tail =>
      exact .product scope focus tail focusScoped

/-- Lift one answer-free, noncommitting running child transition through one
frame.  The restriction is load-bearing: answers must be consumed by
`collectionAnswer`, and commits require scope-sensitive catch/pass rules. -/
theorem liftProgress
    (frame : ActiveControlFrame)
    {before after : Session} {focus next : Search}
    {events : List Observation}
    (child : RawStep before focus events .none after (.running next))
    (answerFree : Trace.AnswerFree events) :
    RawStep before (frame.wrap focus) events .none after
      (.running (frame.wrap next)) := by
  cases frame with
  | choiceLeft scope right =>
      exact .choiceProgress scope focus right next events before after child
  | cut outerScope innerScope =>
      exact .cutBoundaryProgress innerScope focus next events before after child
  | catchBoundary handlerScope scope catcher handler entryBindings =>
      exact
        .catchProgress handlerScope scope focus next catcher handler
          entryBindings events .none before after child
  | collection collectionScope callerScope generatorScope template output
      entryBindings tail reversed =>
      have boundary :
          RawStep before (.cutBoundary generatorScope focus) events .none after
            (.running (.cutBoundary generatorScope next)) :=
        .cutBoundaryProgress generatorScope focus next events before after child
      exact
        .collectionProgress collectionScope callerScope
          (.cutBoundary generatorScope focus)
          (.cutBoundary generatorScope next) template output entryBindings tail
          reversed events .none before after boundary answerFree
  | productHead scope tail =>
      exact
        .productProgress scope focus next tail events .none before after child
          answerFree

end ActiveControlFrame

/-- Active frames in nearest-to-farthest order. -/
abbrev ActiveControlContext := List ActiveControlFrame

namespace ActiveControlContext

/-- Plug a focus through the active path, nearest frame first. -/
def plug : ActiveControlContext → Search → Search
  | [], focus => focus
  | frame :: outer, focus => plug outer (frame.wrap focus)

/-- Collection cells contributed by the context in inner-to-outer order. -/
def collectionCells (context : ActiveControlContext) :
    List SourceCollectionCell :=
  context.flatMap ActiveControlFrame.collectionCells

/-- Inactive choice cursors contributed by the context in inner-to-outer
order. -/
def retainedCursors (context : ActiveControlContext) : List CursorToken :=
  context.flatMap ActiveControlFrame.retainedCursors

@[simp] theorem plug_nil (focus : Search) : plug [] focus = focus := rfl

@[simp] theorem plug_cons (frame : ActiveControlFrame)
    (outer : ActiveControlContext) (focus : Search) :
    plug (frame :: outer) focus = plug outer (frame.wrap focus) := rfl

/-- Plugging neither loses nor duplicates inactive choice cursors. -/
theorem plug_liveCursors (context : ActiveControlContext) (focus : Search) :
    (plug context focus).liveCursors =
      focus.liveCursors ++ context.retainedCursors := by
  induction context generalizing focus with
  | nil => simp [plug, retainedCursors]
  | cons frame outer inductionHypothesis =>
      rw [plug_cons, inductionHypothesis,
        ActiveControlFrame.wrap_liveCursors]
      simp [retainedCursors, List.append_assoc]

/-- Exact collector-cell extraction through an arbitrary heterogeneous active
path.  This is the occurrence-zipper composition law; it makes no statement
about executable alternatives across a collection frame. -/
theorem plug_activeCollectionCells
    (context : ActiveControlContext) (focus : Search) :
    activeCollectionCells (plug context focus) =
      (activeCollectionCells focus).map fun cells =>
        cells ++ context.collectionCells := by
  induction context generalizing focus with
  | nil =>
      simp [plug, collectionCells]
  | cons frame outer inductionHypothesis =>
      rw [plug_cons, inductionHypothesis,
        ActiveControlFrame.wrap_activeCollectionCells]
      simp [collectionCells, Option.map_map, Function.comp_def,
        List.append_assoc]

/-- Equality of the focus-level collector extraction is sufficient to
preserve an existing positional source-cell/executable-frame relation. -/
theorem preserve_occurrences
    (context : ActiveControlContext) {focus next : Search}
    {frames : List DemandDrivenStep.Frame}
    (focusCells :
      activeCollectionCells focus = activeCollectionCells next)
    (before : CollectionOccurrenceAgrees (plug context focus) frames) :
    CollectionOccurrenceAgrees (plug context next) frames := by
  rw [CollectionOccurrenceAgrees,
    plug_activeCollectionCells context focus] at before
  rw [CollectionOccurrenceAgrees,
    plug_activeCollectionCells context next, ← focusCells]
  exact before

/-- Every answer-free, noncommitting child step lifts through any number of
active control frames with exactly the same events and session endpoints. -/
theorem liftProgress
    (context : ActiveControlContext)
    {before after : Session} {focus next : Search}
    {events : List Observation}
    (child : RawStep before focus events .none after (.running next))
    (answerFree : Trace.AnswerFree events) :
    RawStep before (plug context focus) events .none after
      (.running (plug context next)) := by
  induction context generalizing focus next with
  | nil => exact child
  | cons frame outer inductionHypothesis =>
      exact inductionHypothesis (frame.liftProgress child answerFree)

/-- Typed scope chain across an active context. -/
inductive WellScoped :
    CutScopeId → ActiveControlContext → CutScopeId → Prop where
  | nil (scope : CutScopeId) : WellScoped scope [] scope
  | cons (frame : ActiveControlFrame) (outer : ActiveControlContext)
      (outermost : CutScopeId)
      (valid : frame.Valid)
      (tail : WellScoped frame.outerScope outer outermost) :
      WellScoped frame.innerScope (frame :: outer) outermost

/-- A typed context turns a well-scoped focus into a well-scoped complete
search at the outermost scope. -/
theorem plug_wellScoped
    {inner outer : CutScopeId} {context : ActiveControlContext}
    {focus : Search}
    (contextScoped : WellScoped inner context outer)
    (focusScoped : focus.WellScoped inner) :
    (plug context focus).WellScoped outer := by
  induction contextScoped generalizing focus with
  | nil scope => exact focusScoped
  | cons frame context outermost valid tail inductionHypothesis =>
      exact inductionHypothesis (frame.wrap_wellScoped valid focusScoped)

/-- Contextual source entry for one active `findall/3` head.

The result is built from the real `taskFindall` constructor and the generic
answer-free progress lift.  Its occurrence theorem is derived from the exact
cell-extraction homomorphism, not by consulting executable frames. -/
def enterFindallResult
    (context : ActiveControlContext) (session : Session)
    (callerScope : CutScopeId) (template : Term)
    (generator : PeTTaSpec.PrologCore.Goal) (output : Term)
    (rest : List PeTTaSpec.PrologCore.Goal) (bindings : Substitution) :
    ActiveFindallEntryResult session
      (plug context
        (.task callerScope (.findall template generator output :: rest)
          bindings)) :=
  { afterSession := (openFindall session).session
    afterSearch :=
      plug context
        (sourceFindallTarget session callerScope template generator output rest
          bindings)
    cell := sourceEntryCell session callerScope template output bindings rest
    sourceStep :=
      liftProgress context
        (.taskFindall callerScope template generator output rest bindings
          session)
        (by simp [Trace.AnswerFree])
    afterSessionExact := rfl
    cutExact := rfl
    collectionExact := rfl
    cellsPrepend := by
      intro cells beforeCells
      rw [plug_activeCollectionCells] at beforeCells ⊢
      simp [activeCollectionCells, sourceFindallTarget, sourceEntryCell]
        at beforeCells ⊢
      subst cells
      rfl }

/-- After contextual entry, the new collection frame is literally the
nearest frame around the generator focus.  Existing outer frames retain
their order. -/
theorem enterFindallResult_afterSearch
    (context : ActiveControlContext) (session : Session)
    (callerScope : CutScopeId) (template : Term)
    (generator : PeTTaSpec.PrologCore.Goal) (output : Term)
    (rest : List PeTTaSpec.PrologCore.Goal) (bindings : Substitution) :
    (enterFindallResult context session callerScope template generator output
      rest bindings).afterSearch =
      plug
        (.collection (openFindall session).collectionScope callerScope
            (openFindall session).cutScope template output bindings rest [] ::
          context)
        (.task (openFindall session).cutScope [generator] bindings) :=
  rfl

end ActiveControlContext

/-! ## Structural anti-vacuity witnesses -/

/-- A collection in the middle of a heterogeneous choice/collection/product
path contributes exactly one cell, even though the inactive choice owns an
arbitrary separate search. -/
theorem heterogeneous_collection_cell_exact
    (inner middle : CutScopeId) (collectionScope : CollectionScopeId)
    (inactive : Search) :
    activeCollectionCells
        (ActiveControlContext.plug
          [.choiceLeft inner inactive,
           .collection collectionScope middle inner (.integer 1) (.integer 2)
             [] [] [],
           .productHead middle []]
          (.task inner [] [])) =
      some
        [sourceCollectionCell inner collectionScope middle
          (.integer 1) (.integer 2) [] [] []] := by
  rfl

/-- The same heterogeneous path retains every inactive choice cursor exactly
once; collection and product frames cannot mint another cursor. -/
theorem heterogeneous_context_retains_choice_cursors
    (inner middle : CutScopeId) (collectionScope : CollectionScopeId)
    (inactive : Search) :
    (ActiveControlContext.plug
      [.choiceLeft inner inactive,
       .collection collectionScope middle inner (.integer 1) (.integer 2)
         [] [] [],
       .productHead middle []]
      (.task inner [] [])).liveCursors = inactive.liveCursors := by
  rfl

/-- Two nested collectors are extracted in exact inner-to-outer order. -/
theorem two_nested_collection_cells_exact
    (inner middle outer : CutScopeId)
    (innerCollection outerCollection : CollectionScopeId) :
    activeCollectionCells
        (ActiveControlContext.plug
          [.collection innerCollection middle inner
             (.integer 1) (.integer 2) [] [] [],
           .collection outerCollection outer middle
             (.integer 3) (.integer 4) [] [] []]
          (.task inner [] [])) =
      some
        [sourceCollectionCell inner innerCollection middle
            (.integer 1) (.integer 2) [] [] [],
         sourceCollectionCell middle outerCollection outer
            (.integer 3) (.integer 4) [] [] []] := by
  rfl

/-- Swapping two genuinely distinct nested collection cells is rejected. -/
theorem swapped_nested_collection_cells_rejected
    (inner middle outer : CutScopeId)
    (innerCollection outerCollection : CollectionScopeId)
    (different : inner ≠ middle) :
    activeCollectionCells
        (ActiveControlContext.plug
          [.collection innerCollection middle inner
             (.integer 1) (.integer 2) [] [] [],
           .collection outerCollection outer middle
             (.integer 3) (.integer 4) [] [] []]
          (.task inner [] [])) ≠
      some
        [sourceCollectionCell middle outerCollection outer
            (.integer 3) (.integer 4) [] [] [],
         sourceCollectionCell inner innerCollection middle
          (.integer 1) (.integer 2) [] [] []] := by
  intro swapped
  rw [two_nested_collection_cells_exact inner middle outer innerCollection
    outerCollection] at swapped
  have heads :
      sourceCollectionCell inner innerCollection middle
          (.integer 1) (.integer 2) [] [] [] =
        sourceCollectionCell middle outerCollection outer
          (.integer 3) (.integer 4) [] [] [] :=
    (List.cons.inj (Option.some.inj swapped)).1
  exact different (congrArg SourceCollectionCell.cutScope heads)

/-- A cut outside a collection is a second syntactic boundary, distinct from
the generator cut owned by the collection frame. -/
theorem outer_cut_and_collection_cut_are_both_present
    (generator caller outer : CutScopeId)
    (collectionScope : CollectionScopeId) (focus : Search)
    (different : generator ≠ caller) :
    ActiveControlContext.plug
          [.collection collectionScope caller generator
             (.integer 1) (.integer 2) [] [] [],
           .cut outer caller]
          focus =
        .cutBoundary caller
          (.collectionBoundary collectionScope caller
            (.cutBoundary generator focus) (.integer 1) (.integer 2) [] [] []) ∧
      generator ≠ caller :=
  ⟨rfl, different⟩

end PLeaTTa.PrologActiveControlContextBridge
