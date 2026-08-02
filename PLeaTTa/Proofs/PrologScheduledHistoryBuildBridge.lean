-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologScheduledHistoryBuildBridge
Purpose: Retain Type-valued construction provenance for locally scheduled
  answer histories
Trusted boundary: none
Main exports: ScheduledHistoryBuild, ScheduledHistoryBuild.cells
-/
import PLeaTTa.Proofs.PrologScheduledAnswerPropagationBridge

namespace PLeaTTa.PrologScheduledHistoryBuildBridge

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.Resolver
open PrologProductResourceContextBridge
open PrologScheduledAnswerPropagationBridge

/-!
# Local scheduled-history construction

`ScheduledAnswerHistory.resourceAgreement` deliberately lives in `Prop`.
Eliminating it to choose a payload snapshot would therefore be both rejected
by Lean and architecturally wrong.  This separate Type-valued build tree
records exactly the two certified constructors which can create a local
history: the first local answer and one private resume through an older local
predicate frame.  In particular there is no constructor for task-choice or
catch regions.
-/

/-- One locally owned resource occurrence recorded by the build tree. -/
structure ScheduledHistoryCell
    (alpha : List (LogicVar × String)) where
  resource : RetainedAlternativeSegment
  cursor : PreparedCursor
  ownership : resource.HasIndexedOwnershipAt alpha cursor

/-- Proof-relevant construction history for a literal
`ScheduledAnswerHistory` value.  Its index prevents a build tree for a
shape-compatible history from being reused for another one. -/
inductive ScheduledHistoryBuild
    {alpha : List (LogicVar × String)} :
    {source next : Search} →
      ScheduledAnswerHistory alpha source next → Type where
  | oneLevel (callerScope predicateScope : CutScopeId)
      (bindings : OpenSubstitution.Substitution)
      (cursor : PreparedCursor) (resource : RetainedAlternativeSegment)
      (ownership : resource.HasIndexedOwnershipAt alpha cursor) :
      ScheduledHistoryBuild
        (ScheduledAnswerHistory.oneLevel callerScope predicateScope bindings
          cursor resource ownership)
  | resumed
      {source next : Search}
      {history : ScheduledAnswerHistory alpha source next}
      (inside : ScheduledHistoryBuild history)
      (callerScope predicateScope : CutScopeId)
      (cursor : PreparedCursor) (outerResource : RetainedAlternativeSegment)
      (resume :
        PrivateScheduledResume alpha history callerScope predicateScope cursor
          [] outerResource) :
      ScheduledHistoryBuild resume.nextHistory

namespace ScheduledHistoryBuild

/-- Exact local occurrence order represented by a build tree. -/
def cells
    {alpha : List (LogicVar × String)}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next} :
    ScheduledHistoryBuild history → List (ScheduledHistoryCell alpha)
  | .oneLevel _ _ _ cursor resource ownership =>
      [{ resource := resource, cursor := cursor, ownership := ownership }]
  | .resumed inside _ _ cursor outerResource resume =>
      inside.cells ++
        [{ resource := outerResource
           cursor := cursor
           ownership := resume.outerOwnership }]

/-- Erasing occurrence identities yields exactly the resource list stored by
the constructed history, in executable pull order. -/
theorem cells_map_resource
    {alpha : List (LogicVar × String)}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    (build : ScheduledHistoryBuild history) :
    build.cells.map ScheduledHistoryCell.resource = history.resources := by
  induction build with
  | oneLevel callerScope predicateScope bindings cursor resource ownership =>
      rfl
  | resumed inside callerScope predicateScope cursor outerResource resume
      inductionHypothesis =>
      simp only [cells, List.map_append, List.map_singleton,
        PrivateScheduledResume.nextHistory, ScheduledAnswerHistory.resources,
        List.reverse_cons]
      rw [inductionHypothesis]
      rfl

/-- A build tree is never empty: it begins with the current local resource
and every private resume appends exactly one older occurrence. -/
theorem cells_ne_nil
    {alpha : List (LogicVar × String)}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    (build : ScheduledHistoryBuild history) :
    build.cells ≠ [] := by
  induction build with
  | oneLevel => simp [cells]
  | resumed inside callerScope predicateScope cursor outerResource resume
      inductionHypothesis =>
      simp [cells, inductionHypothesis]

/-- One coordinate indexed by the literal local history construction tree. -/
structure Path
    {alpha : List (LogicVar × String)}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    (build : ScheduledHistoryBuild history) where
  position : Fin build.cells.length

namespace Path

/-- Exact occurrence selected without comparing resource values. -/
def cell
    {alpha : List (LogicVar × String)}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    {build : ScheduledHistoryBuild history}
    (path : Path build) : ScheduledHistoryCell alpha :=
  build.cells.get path.position

end Path

end ScheduledHistoryBuild

end PLeaTTa.PrologScheduledHistoryBuildBridge
