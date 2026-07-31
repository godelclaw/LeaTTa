-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologProductActiveControlEmbeddingBridge
Purpose: Embed the predicate-specific active-product zipper into the
  heterogeneous active-control zipper without changing source search shape,
  cursor ownership order, collection occurrences, or cut-scope typing.
Trusted boundary: none
Main exports:
  toActiveControlFrames, toActiveControlContext,
  plug_toActiveControlContext,
  retainedCursors_toActiveControlContext,
  collectionCells_toActiveControlContext,
  wellScoped_toActiveControlContext
-/
import PLeaTTa.Proofs.PrologActiveControlContextBridge
import PLeaTTa.Proofs.PrologSourceProductContextBridge

namespace PLeaTTa.PrologProductActiveControlEmbeddingBridge

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PLeaTTa.PrologActiveControlContextBridge
open PLeaTTa.PrologSourceProductContextBridge

/-!
`ActiveProductFrame` predates the heterogeneous active-control zipper.  One
such frame is not primitive there: its retained right branch, predicate cut,
and suspended caller tail are three distinct frames in nearest-to-farthest
order.  Making that decomposition explicit lets the mature product/resource
proofs compose with collection and catch contexts without inventing a second
predicate-activation semantics.
-/

/-- Exact heterogeneous spelling of one entered predicate activation.

The retained clause region is owned once by `choiceLeft`; `cut` records the
predicate marker; `productHead` suspends the caller continuation.  None of
these three frames is a collection boundary. -/
def toActiveControlFrames
    (frame : PrologSourceProductContextBridge.ActiveProductFrame) :
    PrologActiveControlContextBridge.ActiveControlContext :=
  [ .choiceLeft frame.predicateScope frame.retained,
    .cut frame.callerScope frame.predicateScope,
    .productHead frame.callerScope frame.callerRest ]

/-- The three-frame spelling reconstructs the original source constructor
tree definitionally. -/
@[simp] theorem plug_toActiveControlFrames
    (frame : ActiveProductFrame) (focus : Search) :
    PrologActiveControlContextBridge.ActiveControlContext.plug
        (toActiveControlFrames frame) focus =
      frame.wrap focus :=
  rfl

/-- One embedded predicate frame contributes exactly its retained right-hand
cursors, once and in their original order. -/
@[simp] theorem retainedCursors_toActiveControlFrames
    (frame : ActiveProductFrame) :
    PrologActiveControlContextBridge.ActiveControlContext.retainedCursors
        (toActiveControlFrames frame) =
      frame.retained.liveCursors := by
  simp [toActiveControlFrames,
    PrologActiveControlContextBridge.ActiveControlContext.retainedCursors,
    PrologActiveControlContextBridge.ActiveControlFrame.retainedCursors]

/-- Predicate activation alone contributes no collection occurrence. -/
@[simp] theorem collectionCells_toActiveControlFrames
    (frame : ActiveProductFrame) :
    PrologActiveControlContextBridge.ActiveControlContext.collectionCells
        (toActiveControlFrames frame) = [] := by
  simp [toActiveControlFrames,
    PrologActiveControlContextBridge.ActiveControlContext.collectionCells,
    PrologActiveControlContextBridge.ActiveControlFrame.collectionCells]

/-- Embed an inner-to-outer predicate stack into the heterogeneous context.
Each source predicate frame expands to its exact three-frame control spelling
before the next outer predicate is appended. -/
def toActiveControlContext :
    PrologSourceProductContextBridge.ActiveProductContext →
      PrologActiveControlContextBridge.ActiveControlContext
  | [] => []
  | frame :: outer =>
      toActiveControlFrames frame ++ toActiveControlContext outer

/-- `plug` is a right action of context concatenation: nearer frames wrap the
focus first, then the outer suffix. -/
theorem activeControl_plug_append
    (inner outer :
      PrologActiveControlContextBridge.ActiveControlContext)
    (focus : Search) :
    PrologActiveControlContextBridge.ActiveControlContext.plug
        (inner ++ outer) focus =
      PrologActiveControlContextBridge.ActiveControlContext.plug outer
        (PrologActiveControlContextBridge.ActiveControlContext.plug inner
          focus) := by
  induction inner generalizing focus with
  | nil => rfl
  | cons frame inner inductionHypothesis =>
      exact inductionHypothesis (frame.wrap focus)

/-- Embedding is representation-preserving for an arbitrary active focus. -/
@[simp] theorem plug_toActiveControlContext
    (context : PrologSourceProductContextBridge.ActiveProductContext)
    (focus : Search) :
    PrologActiveControlContextBridge.ActiveControlContext.plug
        (toActiveControlContext context) focus =
      PrologSourceProductContextBridge.ActiveProductContext.plug context
        focus := by
  induction context generalizing focus with
  | nil => rfl
  | cons frame outer inductionHypothesis =>
      rw [toActiveControlContext, activeControl_plug_append,
        plug_toActiveControlFrames, inductionHypothesis]
      rfl

/-- The embedding neither loses nor duplicates any retained cursor, and it
keeps the exact inner-to-outer order used by the resource zipper. -/
@[simp] theorem retainedCursors_toActiveControlContext
    (context : PrologSourceProductContextBridge.ActiveProductContext) :
    PrologActiveControlContextBridge.ActiveControlContext.retainedCursors
        (toActiveControlContext context) =
      PrologSourceProductContextBridge.ActiveProductContext.retainedCursors
        context := by
  induction context with
  | nil => rfl
  | cons frame outer inductionHypothesis =>
      have frameCursors :
          (toActiveControlFrames frame).flatMap
              PrologActiveControlContextBridge.ActiveControlFrame.retainedCursors =
            frame.retained.liveCursors := by
        simpa only [
          PrologActiveControlContextBridge.ActiveControlContext.retainedCursors]
          using retainedCursors_toActiveControlFrames frame
      have outerCursors :
          (toActiveControlContext outer).flatMap
              PrologActiveControlContextBridge.ActiveControlFrame.retainedCursors =
            outer.flatMap (fun productFrame =>
              productFrame.retained.liveCursors) := by
        simpa only [
          PrologActiveControlContextBridge.ActiveControlContext.retainedCursors,
          PrologSourceProductContextBridge.ActiveProductContext.retainedCursors]
          using inductionHypothesis
      change
        (toActiveControlFrames frame ++
            toActiveControlContext outer).flatMap
              PrologActiveControlContextBridge.ActiveControlFrame.retainedCursors =
          frame.retained.liveCursors ++
            outer.flatMap (fun productFrame =>
              productFrame.retained.liveCursors)
      rw [List.flatMap_append, frameCursors, outerCursors]

/-- Pure predicate stacks remain collection-free after embedding.  This is
the boundary fact used later when a real collection frame is prepended. -/
@[simp] theorem collectionCells_toActiveControlContext
    (context : PrologSourceProductContextBridge.ActiveProductContext) :
    PrologActiveControlContextBridge.ActiveControlContext.collectionCells
        (toActiveControlContext context) = [] := by
  induction context with
  | nil => rfl
  | cons frame outer inductionHypothesis =>
      have frameCells :
          (toActiveControlFrames frame).flatMap
              PrologActiveControlContextBridge.ActiveControlFrame.collectionCells =
            [] := by
        simpa only [
          PrologActiveControlContextBridge.ActiveControlContext.collectionCells]
          using collectionCells_toActiveControlFrames frame
      have outerCells :
          (toActiveControlContext outer).flatMap
              PrologActiveControlContextBridge.ActiveControlFrame.collectionCells =
            [] := by
        simpa only [
          PrologActiveControlContextBridge.ActiveControlContext.collectionCells]
          using inductionHypothesis
      change
        (toActiveControlFrames frame ++
            toActiveControlContext outer).flatMap
              PrologActiveControlContextBridge.ActiveControlFrame.collectionCells =
          []
      rw [List.flatMap_append, frameCells, outerCells]
      rfl

/-- The old predicate-specific scope chain constructs the newer typed
heterogeneous chain.  In particular the retained right is validated at the
predicate scope before the cut maps that scope back to its caller. -/
theorem wellScoped_toActiveControlContext
    {inner outer : CutScopeId}
    {context : PrologSourceProductContextBridge.ActiveProductContext}
    (agreement :
      PrologSourceProductContextBridge.ActiveProductContext.WellScoped
        inner context outer) :
    PrologActiveControlContextBridge.ActiveControlContext.WellScoped
      inner (toActiveControlContext context) outer := by
  induction agreement with
  | nil scope =>
      exact .nil scope
  | cons frame context active retainedScoped outerScoped
      inductionHypothesis =>
      exact
        .cons (.choiceLeft frame.predicateScope frame.retained)
          _ active retainedScoped
          (.cons (.cut frame.callerScope frame.predicateScope)
            _ active True.intro
            (.cons (.productHead frame.callerScope frame.callerRest)
              _ active True.intro inductionHypothesis))

/-! ## Discriminating witnesses -/

/-- Two nested predicate regions retain their two cursor occurrences in
inner-to-outer order after the heterogeneous expansion. -/
theorem two_embedded_product_cursors_exact
    (inner middle outer : CutScopeId)
    (innerCursor middleCursor : Resolver.PreparedCursor) :
    let context :
        PrologSourceProductContextBridge.ActiveProductContext :=
      [{ callerScope := middle
         predicateScope := inner
         retained := .clauses inner innerCursor
         callerRest := [] },
       { callerScope := outer
         predicateScope := middle
         retained := .clauses middle middleCursor
         callerRest := [] }]
    PrologActiveControlContextBridge.ActiveControlContext.retainedCursors
        (toActiveControlContext context) =
      [{ scope := inner, cursor := innerCursor },
       { scope := middle, cursor := middleCursor }] := by
  simp [PrologSourceProductContextBridge.ActiveProductContext.retainedCursors,
    Search.liveCursors]

/-- The three-frame expansion is substantive: omitting the choice frame loses
the retained cursor even though the remaining cut/product scopes still type.
This rejects interpreting the embedding as a cosmetic constructor rename. -/
theorem choice_frame_is_required_for_cursor_ownership
    (caller predicate : CutScopeId) (cursor : Resolver.PreparedCursor)
    (tail : List PeTTaSpec.PrologCore.Goal) :
    PrologActiveControlContextBridge.ActiveControlContext.retainedCursors
        [ .cut caller predicate, .productHead caller tail ] = [] ∧
      PrologActiveControlContextBridge.ActiveControlContext.retainedCursors
        ([ .choiceLeft predicate (.clauses predicate cursor),
           .cut caller predicate, .productHead caller tail ] :
          PrologActiveControlContextBridge.ActiveControlContext) =
        [{ scope := predicate, cursor := cursor }] := by
  simp [PrologActiveControlContextBridge.ActiveControlContext.retainedCursors,
    PrologActiveControlContextBridge.ActiveControlFrame.retainedCursors,
    Search.liveCursors]

end PLeaTTa.PrologProductActiveControlEmbeddingBridge
