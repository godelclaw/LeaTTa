-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologAnswerOriginBridge
Purpose: Characterize the exact leftmost task leaf that emits one source
  answer, including its successor and unchanged persistent session.
Trusted boundary: none
Main exports: AnswerOrigin, AnswerOrigin.toRawStep,
  RawStep.exactAnswer_origin
-/
import PLeaTTa.Proofs.PrologFindallFrameZipperBridge

namespace PLeaTTa.PrologAnswerOriginBridge

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PrologFindallFrameZipperBridge

/-!
# Exact source answer origin

Only an empty task emits a source answer.  Choice, cut, and catch boundaries
may transparently carry that answer along the currently selected left path;
products and collection boundaries consume it instead.  The indexed relation
below records the precise emitting leaf, the whole transparent source path,
and the successor obtained by replacing only that leaf with `done`.

Keeping the leaf cut scope as an index prevents a later bridge from pairing an
answer with a different task occurrence that merely carries the same
substitution.  No world, effect, or answer content is supplied by an oracle.
-/

/-- Exact leftmost source path from one empty answer task to its successor.

The first two indices identify the task occurrence itself.  The final two
indices retain the complete source and successor trees, so right alternatives,
typed catch boundaries, and entry bindings cannot be reconstructed
independently by a consumer. -/
inductive AnswerOrigin (leafScope : CutScopeId)
    (bindings : Substitution) : Search → Search → Prop where
  | task :
      AnswerOrigin leafScope bindings
        (.task leafScope [] bindings) .done
  | choice (scope : CutScopeId) (right : Search)
      {left next : Search}
      (inside : AnswerOrigin leafScope bindings left next) :
      AnswerOrigin leafScope bindings
        (.choice scope left right) (.choice scope next right)
  | cutBoundary (scope : CutScopeId) {body next : Search}
      (inside : AnswerOrigin leafScope bindings body next) :
      AnswerOrigin leafScope bindings
        (.cutBoundary scope body) (.cutBoundary scope next)
  | catchBoundary (handlerScope : ExceptionScopeId) (scope : CutScopeId)
      (catcher : Term) (handler : PeTTaSpec.PrologCore.Goal)
      (entryBindings : Substitution) {body next : Search}
      (inside : AnswerOrigin leafScope bindings body next) :
      AnswerOrigin leafScope bindings
        (.catchBoundary handlerScope scope body catcher handler entryBindings)
        (.catchBoundary handlerScope scope next catcher handler entryBindings)

namespace AnswerOrigin

/-- Every recorded origin reconstructs the exact singleton-answer source
transition, at any persistent session.  In particular the session is
definitionally unchanged. -/
theorem toRawStep
    {leafScope : CutScopeId} {bindings : Substitution}
    {source next : Search}
    (origin : AnswerOrigin leafScope bindings source next)
    (session : Session) :
    RawStep session source [.answer bindings] .none session
      (.running next) := by
  induction origin with
  | task =>
      exact .taskAnswer leafScope bindings session
  | choice scope right inside inductionHypothesis =>
      exact
        .choiceProgress scope _ right _ [.answer bindings]
          session session inductionHypothesis
  | cutBoundary scope inside inductionHypothesis =>
      exact
        .cutBoundaryProgress scope _ _ [.answer bindings]
          session session inductionHypothesis
  | catchBoundary handlerScope scope catcher handler entryBindings inside
      inductionHypothesis =>
      exact
        .catchProgress handlerScope scope _ _ catcher handler entryBindings
          [.answer bindings] .none session session inductionHypothesis

/-- The source path fixes the emitting task occurrence, its bindings, and the
whole successor.  Thus existential origin witnesses cannot be swapped for a
different leaf carrying a compatible-looking answer. -/
theorem indices_unique
    {leftScope rightScope : CutScopeId}
    {leftBindings rightBindings : Substitution}
    {source leftNext rightNext : Search}
    (left : AnswerOrigin leftScope leftBindings source leftNext)
    (right : AnswerOrigin rightScope rightBindings source rightNext) :
    leftScope = rightScope ∧ leftBindings = rightBindings ∧
      leftNext = rightNext := by
  induction left generalizing rightScope rightBindings rightNext with
  | task =>
      cases right
      exact ⟨rfl, rfl, rfl⟩
  | choice scope rightBranch inside inductionHypothesis =>
      cases right with
      | choice _ _ otherInside =>
          rcases inductionHypothesis otherInside with
            ⟨scopeEq, bindingsEq, nextEq⟩
          exact ⟨scopeEq, bindingsEq, congrArg (fun next =>
            Search.choice scope next rightBranch) nextEq⟩
  | cutBoundary scope inside inductionHypothesis =>
      cases right with
      | cutBoundary _ otherInside =>
          rcases inductionHypothesis otherInside with
            ⟨scopeEq, bindingsEq, nextEq⟩
          exact ⟨scopeEq, bindingsEq,
            congrArg (Search.cutBoundary scope) nextEq⟩
  | catchBoundary handlerScope scope catcher handler entryBindings inside
      inductionHypothesis =>
      cases right with
      | catchBoundary _ _ _ _ _ otherInside =>
          rcases inductionHypothesis otherInside with
            ⟨scopeEq, bindingsEq, nextEq⟩
          exact ⟨scopeEq, bindingsEq,
            congrArg
              (fun next => Search.catchBoundary handlerScope scope next
                catcher handler entryBindings)
              nextEq⟩

end AnswerOrigin

namespace RawStep

/-- Complete event-membership inversion for one emitted answer.

Even when the surrounding transition carries other observations, an answer
fixes a transparent left path to one empty task leaf.  It cannot share the
step with an escaping cut, terminate, alter the persistent session, cross a
product, or cross a live collection boundary. -/
theorem answer_mem_origin
    {before after : Session} {source : Search}
    {events : List Observation} {signal : Trace.CutSignal}
    {target : RawTarget} (step : RawStep before source events signal after target)
    {bindings : Substitution} (present : .answer bindings ∈ events) :
    signal = .none ∧ before = after ∧
      ∃ leafScope next,
        target = .running next ∧
          AnswerOrigin leafScope bindings source next := by
  induction step generalizing bindings
  case taskAnswer scope current session =>
    have bindingsEq : bindings = current := by
      simpa using present
    subst bindings
    exact ⟨rfl, rfl, scope, .done, rfl, .task⟩
  case choiceProgress scope left right next events before after child
      inductionHypothesis =>
    rcases inductionHypothesis present with
      ⟨_signalEq, sessionEq, leafScope, foundNext, targetEq, origin⟩
    cases RawTarget.running.inj targetEq
    exact
      ⟨rfl, sessionEq, leafScope, .choice scope next right, rfl,
        .choice scope right origin⟩
  case cutBoundaryProgress scope body next events before after child
      inductionHypothesis =>
    rcases inductionHypothesis present with
      ⟨_signalEq, sessionEq, leafScope, foundNext, targetEq, origin⟩
    cases RawTarget.running.inj targetEq
    exact
      ⟨rfl, sessionEq, leafScope, .cutBoundary scope next, rfl,
        .cutBoundary scope origin⟩
  case catchProgress handlerScope scope body next catcher handler
      entryBindings events signal before after child inductionHypothesis =>
    rcases inductionHypothesis present with
      ⟨signalEq, sessionEq, leafScope, foundNext, targetEq, origin⟩
    cases RawTarget.running.inj targetEq
    exact
      ⟨signalEq, sessionEq, leafScope,
        .catchBoundary handlerScope scope next catcher handler entryBindings,
        rfl,
        .catchBoundary handlerScope scope catcher handler entryBindings
          origin⟩
  case clausesPull pulled =>
    cases pulled <;> simp_all [localPullEvents]
  all_goals try simp_all [Trace.AnswerFree]

/-- An emitted answer can never share its source transition with an escaping
cut.  This rules out the apparent `cutBoundaryCatch` ambiguity independently
of any singleton-event specialization. -/
theorem answer_mem_signal_none
    {before after : Session} {source : Search}
    {events : List Observation} {signal : Trace.CutSignal}
    {target : RawTarget} (step : RawStep before source events signal after target)
    {bindings : Substitution} (present : .answer bindings ∈ events) :
    signal = .none :=
  (answer_mem_origin step present).1

/-- Anti-vacuity for the signal component: a commit-signalled transition
cannot carry an answer observation.  In particular `cutBoundaryCatch` cannot
smuggle an answer through while hiding the child's commit. -/
theorem commit_answer_impossible
    {before after : Session} {source : Search}
    {events : List Observation} {scope : CutScopeId}
    {target : RawTarget}
    (step : RawStep before source events (.commit scope) after target)
    (bindings : Substitution) :
    .answer bindings ∉ events := by
  intro present
  have impossible := answer_mem_signal_none step present
  cases impossible

/-- Complete inversion of one exact answer transition.

The source and successor determine one transparent left path to the actual
empty task leaf.  The transition cannot change the persistent session; any
effectful, collecting, product, committing, or terminal constructor is
excluded by the exact event/signal/target indices. -/
theorem exactAnswer_origin
    {before after : Session} {source next : Search}
    {bindings : Substitution}
    (step :
      RawStep before source [.answer bindings] .none after
        (.running next)) :
    before = after ∧
      ∃ leafScope, AnswerOrigin leafScope bindings source next := by
  rcases answer_mem_origin step (bindings := bindings) (by simp) with
    ⟨_signal, sessionEq, leafScope, foundNext, targetEq, origin⟩
  cases RawTarget.running.inj targetEq
  exact ⟨sessionEq, leafScope, origin⟩

end RawStep

/-- Proof-producing package for one exact answer step.  Unlike a bare raw
transition, this bundle exposes the actual emitting leaf and records that no
persistent source state changed during the answer. -/
structure ExactAnswerProducer
    (before after : Session) (source next : Search)
    (bindings : Substitution) : Prop where
  step :
    RawStep before source [.answer bindings] .none after (.running next)
  sessionExact : before = after
  origin : ∃ leafScope, AnswerOrigin leafScope bindings source next

namespace ExactAnswerProducer

/-- Every exact raw answer transition constructs the full producer package;
the origin and session equality are derived, not separately assumed. -/
theorem ofRawStep
    {before after : Session} {source next : Search}
    {bindings : Substitution}
    (step :
      RawStep before source [.answer bindings] .none after (.running next)) :
    ExactAnswerProducer before after source next bindings := by
  rcases
      PLeaTTa.PrologAnswerOriginBridge.RawStep.exactAnswer_origin step with
    ⟨sessionExact, leafScope, origin⟩
  exact ⟨step, sessionExact, leafScope, origin⟩

end ExactAnswerProducer

/-- A concrete transparent wrapper path exercises all four constructors and
therefore prevents the origin relation from degenerating to the bare task
case. -/
theorem wrapped_answer_origin_inhabited :
    AnswerOrigin 2 ([] : Substitution)
      (.catchBoundary { index := 7 } 2
        (.cutBoundary 2
          (.choice 2 (.task 2 [] []) (.task 2 [.fail] [])))
        (.atom "ball") .truth [])
      (.catchBoundary { index := 7 } 2
        (.cutBoundary 2
          (.choice 2 .done (.task 2 [.fail] [])))
        (.atom "ball") .truth []) := by
  exact
    .catchBoundary { index := 7 } 2 (.atom "ball") .truth []
      (.cutBoundary 2
        (.choice 2 (.task 2 [.fail] []) (.task (leafScope := 2))))

/-- The same source cannot be certified as answering from its inactive right
choice branch.  This is the DFS anti-vacuity guard for the origin index. -/
theorem inactive_right_answer_origin_rejected :
    ¬ AnswerOrigin 9 ([] : Substitution)
      (.choice 2 (.task 2 [] []) (.task 2 [] []))
      (.choice 2 (.task 2 [] []) .done) := by
  intro origin
  cases origin

end PLeaTTa.PrologAnswerOriginBridge
