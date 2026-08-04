-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologCommittedScheduledOuterTraceRegression
Purpose: Pin the exact source-control prefix for one empty outer caller after
  a committed predicate answer, and expose the current resource-region seam.
Trusted boundary: none
-/
import PLeaTTa.Proofs.PrologAnswerResourceBridge
import PLeaTTa.Proofs.PrologCommittedScheduledOuterCatchupBridge

namespace PLeaTTa.PrologCommittedScheduledOuterTraceRegression

open Metta (Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open PrologAnswerResourceBridge
open PrologBodyFailureOuterResourceCatchupBridge
open PrologCommittedScheduledOuterCatchupBridge
open PrologCommittedScheduledTerminalBridge
open PrologPersistentFreeCommittedScheduledPayloadBridge
open PrologSourceProductContextBridge

/-! ## One older local frame -/

/-- A committed-scheduled answer nested under one older predicate product.

The older caller is empty, so the inner answer is private: the enclosing
product schedules a new empty caller task before retaining both the exhausted
committed predicate and the older predicate cursor. -/
def oneOuterCommittedSource
    (outerCallerScope outerPredicateScope : CutScopeId)
    (outerCursor : PreparedCursor)
    (innerCallerScope innerPredicateScope : CutScopeId)
    (current : Substitution) : Search :=
  .product outerCallerScope
    (.cutBoundary outerPredicateScope
      (.choice outerPredicateScope
        (committedScheduledSourceProductAt innerCallerScope
          innerPredicateScope current [])
        (.clauses outerPredicateScope outerCursor))) []

/-- Source successor after the older product privately consumes the inner
answer and schedules its own empty caller. -/
def oneOuterCommittedScheduled
    (outerCallerScope outerPredicateScope : CutScopeId)
    (outerCursor : PreparedCursor)
    (innerCallerScope innerPredicateScope : CutScopeId)
    (current : Substitution) : Search :=
  .choice outerCallerScope
    (.task outerCallerScope [] current)
    (.product outerCallerScope
      (.cutBoundary outerPredicateScope
        (.choice outerPredicateScope
          (committedScheduledAfterAnswerAt innerCallerScope
            innerPredicateScope)
          (.clauses outerPredicateScope outerCursor))) [])

/-- Source successor after the older empty caller emits the public answer. -/
def oneOuterCommittedAfterAnswer
    (outerCallerScope outerPredicateScope : CutScopeId)
    (outerCursor : PreparedCursor)
    (innerCallerScope innerPredicateScope : CutScopeId) : Search :=
  .choice outerCallerScope .done
    (.product outerCallerScope
      (.cutBoundary outerPredicateScope
        (.choice outerPredicateScope
          (committedScheduledAfterAnswerAt innerCallerScope
            innerPredicateScope)
          (.clauses outerPredicateScope outerCursor))) [])

/-- Exact target after the exhausted committed predicate falls through and
the older retained cursor becomes the active source focus. -/
def oneOuterCommittedRetained
    (outerCallerScope outerPredicateScope : CutScopeId)
    (outerCursor : PreparedCursor) : Search :=
  .product outerCallerScope
    (.cutBoundary outerPredicateScope
      (.clauses outerPredicateScope outerCursor)) []

/-- The inner answer is consumed privately by the older product. -/
theorem oneOuterCommittedSource_schedules
    (session : Session)
    (outerCallerScope outerPredicateScope : CutScopeId)
    (outerCursor : PreparedCursor)
    (innerCallerScope innerPredicateScope : CutScopeId)
    (current : Substitution) :
    RawStep session
      (oneOuterCommittedSource outerCallerScope outerPredicateScope
        outerCursor innerCallerScope innerPredicateScope current)
      [] .none session
      (.running
        (oneOuterCommittedScheduled outerCallerScope outerPredicateScope
          outerCursor innerCallerScope innerPredicateScope current)) := by
  apply RawStep.productAnswer
  apply RawStep.cutBoundaryProgress
  apply RawStep.choiceProgress
  exact
    committedScheduledSourceProductAt_answer session innerCallerScope
      innerPredicateScope current

/-- The newly scheduled empty outer caller emits exactly the current source
substitution and leaves the exhausted inner control on its right. -/
theorem oneOuterCommittedScheduled_answers
    (session : Session)
    (outerCallerScope outerPredicateScope : CutScopeId)
    (outerCursor : PreparedCursor)
    (innerCallerScope innerPredicateScope : CutScopeId)
    (current : Substitution) :
    RawStep session
      (oneOuterCommittedScheduled outerCallerScope outerPredicateScope
        outerCursor innerCallerScope innerPredicateScope current)
      [.answer current] .none session
      (.running
        (oneOuterCommittedAfterAnswer outerCallerScope outerPredicateScope
          outerCursor innerCallerScope innerPredicateScope)) := by
  apply RawStep.choiceProgress
  exact RawStep.taskAnswer outerCallerScope current session

/-- After the public answer, leftmost DFS takes three real silent source
steps: enter the older right branch, enter the exhausted committed branch,
then consume its completion and expose the older retained cursor. -/
theorem oneOuterCommittedAfterAnswer_reachesRetained
    (session : Session)
    (outerCallerScope outerPredicateScope : CutScopeId)
    (outerCursor : PreparedCursor)
    (innerCallerScope innerPredicateScope : CutScopeId) :
    StepsN 3
      (.running session
        (oneOuterCommittedAfterAnswer outerCallerScope outerPredicateScope
          outerCursor innerCallerScope innerPredicateScope))
      []
      (.running session
        (oneOuterCommittedRetained outerCallerScope outerPredicateScope
          outerCursor)) := by
  let innerExhausted : Search :=
    .product innerCallerScope
      (.cutBoundary innerPredicateScope .done) []
  let outerRight : Search :=
    .product outerCallerScope
      (.cutBoundary outerPredicateScope
        (.choice outerPredicateScope
          (committedScheduledAfterAnswerAt innerCallerScope
            innerPredicateScope)
          (.clauses outerPredicateScope outerCursor))) []
  let afterInnerSwitch : Search :=
    .product outerCallerScope
      (.cutBoundary outerPredicateScope
        (.choice outerPredicateScope innerExhausted
          (.clauses outerPredicateScope outerCursor))) []
  have enterOuterRight :
      Transition
        (.running session
          (oneOuterCommittedAfterAnswer outerCallerScope outerPredicateScope
            outerCursor innerCallerScope innerPredicateScope))
        [] (.running session outerRight) :=
    .ordinary _ [] session session _
      (.choiceComplete outerCallerScope .done outerRight session session
        (.done session))
  have enterInnerExhaustedRaw :
      RawStep session outerRight [] .none session
        (.running afterInnerSwitch) := by
    apply RawStep.productProgress
    · apply RawStep.cutBoundaryProgress
      apply RawStep.choiceProgress
      exact
        .choiceComplete innerCallerScope .done innerExhausted session session
          (.done session)
    · simp [Trace.AnswerFree]
  have enterInnerExhausted :
      Transition (.running session outerRight) []
        (.running session afterInnerSwitch) :=
    .ordinary _ [] session session _ enterInnerExhaustedRaw
  have innerCompletion :
      RawStep session innerExhausted [.completed] .none session
        (.terminal .completed) := by
    apply RawStep.productComplete
    · exact
        .cutBoundaryComplete innerPredicateScope .done session session
          (.done session)
    · simp [Trace.AnswerFree]
  have exposeRetainedRaw :
      RawStep session afterInnerSwitch [] .none session
        (.running
          (oneOuterCommittedRetained outerCallerScope outerPredicateScope
            outerCursor)) := by
    apply RawStep.productProgress
    · apply RawStep.cutBoundaryProgress
      exact
        .choiceComplete outerPredicateScope innerExhausted
          (.clauses outerPredicateScope outerCursor) session session
          innerCompletion
    · simp [Trace.AnswerFree]
  have exposeRetained :
      Transition (.running session afterInnerSwitch) []
        (.running session
          (oneOuterCommittedRetained outerCallerScope outerPredicateScope
            outerCursor)) :=
    .ordinary _ [] session session _ exposeRetainedRaw
  simpa [outerRight, afterInnerSwitch, innerExhausted] using
    (StepsN.succ 2 _ _ _ [] [] enterOuterRight
      (StepsN.succ 1 _ _ _ [] [] enterInnerExhausted
        (StepsN.succ 0 _ _ _ [] [] exposeRetained (.zero _))))

/-- Exact divergence-sensitive count for the whole one-outer-frame prefix.

There is one private scheduling step, one public answer step, and three
post-answer catch-up steps.  None is erased as stuttering. -/
theorem oneOuterCommittedSource_exact_prefix
    (session : Session)
    (outerCallerScope outerPredicateScope : CutScopeId)
    (outerCursor : PreparedCursor)
    (innerCallerScope innerPredicateScope : CutScopeId)
    (current : Substitution) :
    StepsN 5
      (.running session
        (oneOuterCommittedSource outerCallerScope outerPredicateScope
          outerCursor innerCallerScope innerPredicateScope current))
      [.answer current]
      (.running session
        (oneOuterCommittedRetained outerCallerScope outerPredicateScope
          outerCursor)) := by
  have schedule :
      Transition
        (.running session
          (oneOuterCommittedSource outerCallerScope outerPredicateScope
            outerCursor innerCallerScope innerPredicateScope current))
        []
        (.running session
          (oneOuterCommittedScheduled outerCallerScope outerPredicateScope
            outerCursor innerCallerScope innerPredicateScope current)) :=
    .ordinary _ [] session session _
      (oneOuterCommittedSource_schedules session outerCallerScope
        outerPredicateScope outerCursor innerCallerScope innerPredicateScope
        current)
  have answer :
      Transition
        (.running session
          (oneOuterCommittedScheduled outerCallerScope outerPredicateScope
            outerCursor innerCallerScope innerPredicateScope current))
        [.answer current]
        (.running session
          (oneOuterCommittedAfterAnswer outerCallerScope outerPredicateScope
            outerCursor innerCallerScope innerPredicateScope)) :=
    .ordinary _ [.answer current] session session _
      (oneOuterCommittedScheduled_answers session outerCallerScope
        outerPredicateScope outerCursor innerCallerScope innerPredicateScope
        current)
  have catchup :=
    oneOuterCommittedAfterAnswer_reachesRetained session outerCallerScope
      outerPredicateScope outerCursor innerCallerScope innerPredicateScope
  simpa using
    (StepsN.succ 4 _ _ _ [] [.answer current] schedule
      (StepsN.succ 3 _ _ _ [.answer current] [] answer catchup))

/-- The reusable committed-spine bridge reconstructs the same exact
five-step prefix as the direct constructor proof above.

This is the anti-vacuity check for sequential composition: the generic
absorption/descent lemmas do not change the concrete source trace or erase a
step. -/
theorem oneOuterCommittedSource_exact_prefix_via_bridge
    (session : Session)
    (outerCallerScope outerPredicateScope : CutScopeId)
    (outerCursor : PreparedCursor)
    (innerCallerScope innerPredicateScope : CutScopeId)
    (current : Substitution) :
    StepsN 5
      (.running session
        (oneOuterCommittedSource outerCallerScope outerPredicateScope
          outerCursor innerCallerScope innerPredicateScope current))
      [.answer current]
      (.running session
        (oneOuterCommittedRetained outerCallerScope outerPredicateScope
          outerCursor)) := by
  let frame : ActiveProductFrame :=
    { callerScope := outerCallerScope
      predicateScope := outerPredicateScope
      retained := .clauses outerPredicateScope outerCursor
      callerRest := [] }
  have callersEmpty :
      forall candidate, candidate ∈ [frame] -> candidate.callerRest = [] := by
    intro candidate member
    simp only [List.mem_singleton] at member
    subst candidate
    rfl
  have answerPrefix :=
    committedSource_reachesLiftedSuccessor [frame] callersEmpty session
      innerCallerScope innerPredicateScope current
  have descent :=
    committedLiftedSuccessor_descends [frame] session innerCallerScope
      innerPredicateScope
  have completed :=
    committedExhaustedFocus_completes session innerCallerScope
      innerPredicateScope
  have promoted :
      Transition
        (.running session
          (ActiveProductContext.plug [frame]
            (.product innerCallerScope
              (.cutBoundary innerPredicateScope .done) []))) []
        (.running session (frameRetainedFrontier frame outerCursor)) :=
    ActiveProductContext.promoteCompleted [] frame session
      (.product innerCallerScope (.cutBoundary innerPredicateScope .done) [])
      outerCursor rfl completed
  have promotion :
      StepsN 1
        (.running session
          (ActiveProductContext.plug [frame]
            (.product innerCallerScope
              (.cutBoundary innerPredicateScope .done) []))) []
        (.running session (frameRetainedFrontier frame outerCursor)) :=
    .succ 0 _ _ _ [] [] promoted (.zero _)
  have composed := StepsN.trans answerPrefix (StepsN.trans descent promotion)
  simpa [frame, oneOuterCommittedSource, oneOuterCommittedRetained,
    ActiveProductFrame.wrap, frameRetainedFrontier, liftCommittedSuccessor,
    committedScheduledAfterAnswerAt] using composed

/-! ## Representation discriminator -/

/-- The exhausted post-cut right branch is intentionally outside the current
ordinary right-region relation.

That relation proves that a resource-free region still owns a real ordinary
alternative.  The post-cut region owns neither a resource nor an alternative,
so treating it as an empty instance would contradict an existing invariant. -/
theorem exhaustedCommittedRight_not_resourceRegion
    (alpha : List (LogicVar × String))
    (callerScope predicateScope : CutScopeId) :
    ¬ RightAlternativeRegionAgrees alpha
      (.product callerScope (.cutBoundary predicateScope .done) []) [] [] := by
  intro agreement
  have nonempty := agreement.segment_ne_nil_of_resources_nil rfl
  exact nonempty rfl

end PLeaTTa.PrologCommittedScheduledOuterTraceRegression
