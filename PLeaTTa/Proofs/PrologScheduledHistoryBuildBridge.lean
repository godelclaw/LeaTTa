-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologScheduledHistoryBuildBridge
Purpose: Retain Type-valued construction provenance for locally scheduled
  answer histories
Trusted boundary: none
Main exports: ScheduledHistoryBuild, ScheduledHistoryBuild.cells
-/
import PLeaTTa.Proofs.PrologScheduledAnswerPropagationBridge
import PLeaTTa.Proofs.PrologAnswerSourceCatchupBridge

namespace PLeaTTa.PrologScheduledHistoryBuildBridge

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.Resolver
open PrologAnswerSourceCatchupBridge
open PrologProductResourceContextBridge
open PrologScheduledAnswerPropagationBridge
open PrologSourceProductContextBridge

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

/-- Exact active predicate context retained by a local scheduled history.

The first cell is the innermost predicate which produced the answer.  Every
private resume appends one older predicate frame.  Keeping the delimiter
labels here, alongside the already-audited occurrence cells, prevents a
later source transition from being placed under a shape-compatible but
different cut scope. -/
def activeContext
    {alpha : List (LogicVar × String)}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next} :
    ScheduledHistoryBuild history → ActiveProductContext
  | .oneLevel callerScope predicateScope _bindings cursor _resource
      _ownership =>
      [{ callerScope := callerScope
         predicateScope := predicateScope
         retained := .clauses predicateScope cursor
         callerRest := [] }]
  | .resumed inside callerScope predicateScope cursor _outerResource
      _resume =>
      inside.activeContext ++
        [{ callerScope := callerScope
           predicateScope := predicateScope
           retained := .clauses predicateScope cursor
           callerRest := [] }]

/-- The context and occurrence lists have the same exact depth. -/
@[simp] theorem activeContext_length
    {alpha : List (LogicVar × String)}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    (build : ScheduledHistoryBuild history) :
    build.activeContext.length = build.cells.length := by
  induction build with
  | oneLevel =>
      rfl
  | resumed inside callerScope predicateScope cursor outerResource resume
      inductionHypothesis =>
      simp [activeContext, cells, inductionHypothesis]

/-- Silent progress through one active predicate frame preserves its exact
scope, retained cursor, and caller tail. -/
private theorem silentSteps_under_frame
    {session : Session} {count : Nat} {start finish : Search}
    (frame : ActiveProductFrame)
    (execution : SilentStepsN session count start finish) :
    SilentStepsN session count (frame.wrap start) (frame.wrap finish) := by
  exact
    SilentStepsN.underProduct frame.callerScope frame.callerRest
      (SilentStepsN.underCutBoundary frame.predicateScope
        (SilentStepsN.underChoice frame.predicateScope execution))

/-- After an answer has been privately scheduled at every represented
predicate level, its successor consumes exactly one completed left branch per
history cell and reaches the literal active context around `.done`.

This is deliberately one phase *after* all-empty caller absorption:
`build.cells` contains the answer-producing active predicate as well as the
older frames.  Consequently its count is one greater than the older-only
absorption count for a rooted carrier. -/
theorem next_to_activeContext_done
    {alpha : List (LogicVar × String)}
    {source next : Search}
    {history : ScheduledAnswerHistory alpha source next}
    (build : ScheduledHistoryBuild history) (session : Session) :
    SilentStepsN session build.cells.length next
      (ActiveProductContext.plug build.activeContext .done) := by
  induction build with
  | oneLevel callerScope predicateScope bindings cursor resource ownership =>
      let frame : ActiveProductFrame :=
        { callerScope := callerScope
          predicateScope := predicateScope
          retained := .clauses predicateScope cursor
          callerRest := [] }
      have completion : CompletesN session 1 .done :=
        .now .done (.done session)
      have entered :
          SilentStepsN session 1
            (.choice callerScope .done (frame.wrap .done))
            (frame.wrap .done) :=
        CompletesN.choiceToRight callerScope completion
      simpa [cells, activeContext, frame, ActiveProductFrame.wrap,
        ScheduledAnswerHistory.oneLevelNext] using entered
  | resumed inside callerScope predicateScope cursor outerResource resume
      inductionHypothesis =>
      let frame : ActiveProductFrame :=
        { callerScope := callerScope
          predicateScope := predicateScope
          retained := .clauses predicateScope cursor
          callerRest := [] }
      have completion : CompletesN session 1 .done :=
        .now .done (.done session)
      have lifted := silentSteps_under_frame frame inductionHypothesis
      have combined :=
        (CompletesN.choiceToRight callerScope completion).trans lifted
      simpa [cells, activeContext, frame,
        ActiveProductContext.plug_append, PrivateScheduledResume.nextHistory,
        ActiveProductFrame.wrap, enclosingHeadNext,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using combined

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
