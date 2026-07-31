-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologAnswerResourceBridge
Purpose: Relate one exact source answer path to the retained executable
  alternative regions and anonymous cut markers that path leaves inactive
Trusted boundary: none
Main exports: RightAlternativeRegionAgrees,
  AnswerOriginResourceAgrees
-/
import PLeaTTa.Proofs.PrologAnswerOriginBridge
import PLeaTTa.Proofs.PrologProductResourceContextBridge

namespace PLeaTTa.PrologAnswerResourceBridge

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PrologAnswerOriginBridge
open PrologControlSegmentSpineBridge
open PrologProductResourceContextBridge

/-!
# Exact alternative ownership along one answer path

`AnswerOrigin` fixes the transparent source path from an empty task to one
answer successor.  This module additionally accounts for the executable
alternative bank in leaf-to-root order.

A source choice does not own one executable alternative.  Its inactive right
region can own zero, one, or many retained clause alternatives.  A scheduled
product right region owns that same list plus the predicate activation's one
anonymous marker.  A cut boundary on the active path owns exactly one marker.
The four endpoints below consume the existing resource and alternative lists;
they do not mint a parallel resource stack.

The accounting cases are exclusive by source shape.  `AnswerOrigin` traverses
the left spine and pairs each inactive right branch wholesale.  Consequently
a cut boundary inside a right branch is not traversed and its marker belongs
to that region, whereas a cut boundary on the left spine is traversed and its
marker belongs to the origin constructor.

Catch has deliberately no constructor.  The current fine executable has no
typed catch frame, so crossing a source catch boundary is fail-closed rather
than being paired with an invented executable resource.
-/

/-- Exact executable bank segment owned by one literal inactive source right
branch.

The clause case excludes the activation marker because the enclosing active
`cutBoundary` consumes it.  After private product scheduling, that boundary
lives inside the inactive right branch; the scheduled case therefore owns the
same clause alternatives and the marker together. -/
inductive RightAlternativeRegionAgrees
    (alpha : List (LogicVar × String)) :
    Search → RetainedAlternativeSegment → List PLeaTTa.Alt → Prop where
  | clauses (scope : CutScopeId)
      (cursor : PeTTaSpec.PrologCore.Resolver.PreparedCursor)
      (resource : RetainedAlternativeSegment)
      (ownership : resource.Owns alpha cursor) :
      RightAlternativeRegionAgrees alpha (.clauses scope cursor)
        resource resource.alts
  | scheduled (callerScope predicateScope : CutScopeId)
      (cursor : PeTTaSpec.PrologCore.Resolver.PreparedCursor)
      (callerTail : List PeTTaSpec.PrologCore.Goal)
      (resource : RetainedAlternativeSegment)
      (ownership : resource.Owns alpha cursor) :
      RightAlternativeRegionAgrees alpha
        (.product callerScope
          (.cutBoundary predicateScope
            (.choice predicateScope .done
              (.clauses predicateScope cursor)))
          callerTail)
        resource (resource.alts ++ [PLeaTTa.Alt.barrier])

namespace RightAlternativeRegionAgrees

/-- A clause region exposes the exact retained scan result and the ownership
certificate for the literal cursor in the source branch. -/
theorem clauses_exact
    {alpha : List (LogicVar × String)} {scope : CutScopeId}
    {cursor : PeTTaSpec.PrologCore.Resolver.PreparedCursor}
    {resource : RetainedAlternativeSegment} {segment : List PLeaTTa.Alt}
    (agreement :
      RightAlternativeRegionAgrees alpha (.clauses scope cursor)
        resource segment) :
    segment = resource.alts ∧ resource.Owns alpha cursor := by
  cases agreement with
  | clauses _ _ _ ownership =>
      exact ⟨rfl, ownership⟩

/-- A scheduled product region exposes the retained scan result followed by
exactly one anonymous predicate marker. -/
theorem scheduled_exact
    {alpha : List (LogicVar × String)}
    {callerScope predicateScope : CutScopeId}
    {cursor : PeTTaSpec.PrologCore.Resolver.PreparedCursor}
    {callerTail : List PeTTaSpec.PrologCore.Goal}
    {resource : RetainedAlternativeSegment} {segment : List PLeaTTa.Alt}
    (agreement :
      RightAlternativeRegionAgrees alpha
        (.product callerScope
          (.cutBoundary predicateScope
            (.choice predicateScope .done
              (.clauses predicateScope cursor)))
          callerTail)
        resource segment) :
    segment = resource.alts ++ [PLeaTTa.Alt.barrier] ∧
      resource.Owns alpha cursor := by
  cases agreement with
  | scheduled _ _ _ _ _ ownership =>
      exact ⟨rfl, ownership⟩

end RightAlternativeRegionAgrees

/-- Lockstep consumption of retained source resources and executable
alternatives along one particular `AnswerOrigin` proof.

Choice descends to the answer leaf first and consumes its inactive right
region while unwinding, which is the executable bank's LIFO order.  A cut
boundary then consumes exactly one anonymous marker.  Task consumes nothing.
There is intentionally no catch-boundary constructor. -/
inductive AnswerOriginResourceAgrees
    (alpha : List (LogicVar × String)) :
    {leafScope : CutScopeId} → {bindings : Substitution} →
    {source next : Search} →
    AnswerOrigin leafScope bindings source next →
    List RetainedAlternativeSegment → List RetainedAlternativeSegment →
    List PLeaTTa.Alt → List PLeaTTa.Alt → Prop where
  | task (leafScope : CutScopeId) (bindings : Substitution)
      (resources : List RetainedAlternativeSegment)
      (alts : List PLeaTTa.Alt) :
      AnswerOriginResourceAgrees alpha
        (AnswerOrigin.task (leafScope := leafScope) (bindings := bindings))
        resources resources alts alts
  | choice (scope : CutScopeId) (right : Search)
      {leafScope : CutScopeId} {bindings : Substitution}
      {left next : Search}
      (inside : AnswerOrigin leafScope bindings left next)
      {beforeResources afterResources : List RetainedAlternativeSegment}
      {beforeAlts afterAlts regionAlts : List PLeaTTa.Alt}
      {resource : RetainedAlternativeSegment}
      (insideAgrees :
        AnswerOriginResourceAgrees alpha inside beforeResources
          (resource :: afterResources) beforeAlts
          (regionAlts ++ afterAlts))
      (regionAgrees :
        RightAlternativeRegionAgrees alpha right resource regionAlts) :
      AnswerOriginResourceAgrees alpha
        (AnswerOrigin.choice scope right inside)
        beforeResources afterResources beforeAlts afterAlts
  | cutBoundary (scope : CutScopeId)
      {leafScope : CutScopeId} {bindings : Substitution}
      {body next : Search}
      (inside : AnswerOrigin leafScope bindings body next)
      {beforeResources afterResources : List RetainedAlternativeSegment}
      {beforeAlts afterAlts : List PLeaTTa.Alt}
      (insideAgrees :
        AnswerOriginResourceAgrees alpha inside beforeResources afterResources
          beforeAlts (PLeaTTa.Alt.barrier :: afterAlts)) :
      AnswerOriginResourceAgrees alpha
        (AnswerOrigin.cutBoundary scope inside)
        beforeResources afterResources beforeAlts afterAlts

/-- One exact answer producer together with the resource zipper for its
actual origin proof.  The source step and persistent-session equality remain
those of `ExactAnswerProducer`; the additional fields only account for the
inactive executable control resources. -/
structure ExactAnswerProducerResourceAgrees
    (alpha : List (LogicVar × String))
    (before after : Session) (source next : Search)
    (bindings : Substitution)
    (beforeResources afterResources : List RetainedAlternativeSegment)
    (beforeAlts afterAlts : List PLeaTTa.Alt) : Prop where
  producer : ExactAnswerProducer before after source next bindings
  originAgreement :
    ∃ leafScope,
      ∃ origin : AnswerOrigin leafScope bindings source next,
        AnswerOriginResourceAgrees alpha origin beforeResources afterResources
          beforeAlts afterAlts

namespace ExactAnswerProducerResourceAgrees

/-- Any certified origin zipper constructs the exact existing answer-producer
packet using the real source transition.  No step or session equality is
postulated independently. -/
theorem ofOrigin
    {alpha : List (LogicVar × String)}
    {leafScope : CutScopeId} {bindings : Substitution}
    {source next : Search}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (session : Session)
    (origin : AnswerOrigin leafScope bindings source next)
    (resourceAgreement :
      AnswerOriginResourceAgrees alpha origin beforeResources afterResources
        beforeAlts afterAlts) :
    ExactAnswerProducerResourceAgrees alpha session session source next
      bindings beforeResources afterResources beforeAlts afterAlts := by
  exact
    ⟨ExactAnswerProducer.ofRawStep (origin.toRawStep session),
      ⟨leafScope, origin, resourceAgreement⟩⟩

end ExactAnswerProducerResourceAgrees

namespace AnswerOriginResourceAgrees

/-- Head projection used to compose the pre-existing source/resource context
zipper with one exact answer-origin zipper. -/
private theorem head_resource_owns
    {alpha : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {currentScope nextScope outerScope : CutScopeId}
    {cursor : PeTTaSpec.PrologCore.Resolver.PreparedCursor}
    {context :
      PrologSourceProductContextBridge.ActiveProductContext}
    (agreement :
      SourceControlResourceContextAgrees alpha qterm currentBarrier
        (segment :: segments) (resource :: resources) currentScope
        ({ callerScope := nextScope
           predicateScope := currentScope
           retained := .clauses currentScope cursor
           callerRest := segment.references } :: context)
        outerScope) :
    resource.Owns alpha cursor := by
  cases agreement with
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership outerAgrees =>
      exact resourceOwnership

/-- Tail projection preserves the exact shifted barrier and source context. -/
private theorem tail_resource_context
    {alpha : List (LogicVar × String)} {qterm : Metta.Atom}
    {currentBarrier : Nat}
    {segment : ControlSegment} {segments : List ControlSegment}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {currentScope nextScope outerScope : CutScopeId}
    {cursor : PeTTaSpec.PrologCore.Resolver.PreparedCursor}
    {context :
      PrologSourceProductContextBridge.ActiveProductContext}
    (agreement :
      SourceControlResourceContextAgrees alpha qterm currentBarrier
        (segment :: segments) (resource :: resources) currentScope
        ({ callerScope := nextScope
           predicateScope := currentScope
           retained := .clauses currentScope cursor
           callerRest := segment.references } :: context)
        outerScope) :
    SourceControlResourceContextAgrees alpha qterm segment.barrier
      segments resources nextScope context outerScope := by
  cases agreement with
  | cons currentBarrier currentScope nextScope outerScope segment segments
      resource resources cursor context segmentAgrees resourceRest
      resourceQuery resourceBarrier resourceOwnership outerAgrees =>
      exact outerAgrees

/-- Resource consumption is ordered prefix removal: the residual resource
list is a literal suffix of the incoming list. -/
theorem resources_suffix
    {alpha : List (LogicVar × String)}
    {leafScope : CutScopeId} {bindings : Substitution}
    {source next : Search}
    {origin : AnswerOrigin leafScope bindings source next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (agreement :
      AnswerOriginResourceAgrees alpha origin beforeResources afterResources
        beforeAlts afterAlts) :
    ∃ consumed, beforeResources = consumed ++ afterResources := by
  induction agreement with
  | task =>
      exact ⟨[], rfl⟩
  | @choice scope right leafScope bindings left next inside beforeResources
      afterResources beforeAlts afterAlts regionAlts resource insideAgrees
      regionAgrees inductionHypothesis =>
      rcases inductionHypothesis with ⟨consumed, consumedEq⟩
      refine ⟨consumed ++ [resource], ?_⟩
      rw [consumedEq]
      simp only [List.append_assoc, List.singleton_append]
  | cutBoundary scope inside insideAgrees inductionHypothesis =>
      exact inductionHypothesis

/-- Alternative consumption has the same ordered-prefix property.  In
particular no inactive executable alternative can be skipped or reordered. -/
theorem alts_suffix
    {alpha : List (LogicVar × String)}
    {leafScope : CutScopeId} {bindings : Substitution}
    {source next : Search}
    {origin : AnswerOrigin leafScope bindings source next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (agreement :
      AnswerOriginResourceAgrees alpha origin beforeResources afterResources
        beforeAlts afterAlts) :
    ∃ consumed, beforeAlts = consumed ++ afterAlts := by
  induction agreement with
  | task =>
      exact ⟨[], rfl⟩
  | @choice scope right leafScope bindings left next inside beforeResources
      afterResources beforeAlts afterAlts regionAlts resource insideAgrees
      regionAgrees inductionHypothesis =>
      rcases inductionHypothesis with ⟨consumed, consumedEq⟩
      refine ⟨consumed ++ regionAlts, ?_⟩
      rw [consumedEq]
      simp only [List.append_assoc]
  | cutBoundary scope inside insideAgrees inductionHypothesis =>
      rcases inductionHypothesis with ⟨consumed, consumedEq⟩
      refine ⟨consumed ++ [PLeaTTa.Alt.barrier], ?_⟩
      rw [consumedEq]
      simp only [List.append_assoc, List.singleton_append]

/-- The active-call shape consumes the retained clause alternatives at its
choice and the activation's one marker at its enclosing cut boundary. -/
theorem active_call_exact
    {alpha : List (LogicVar × String)}
    (predicateScope : CutScopeId) (bindings : Substitution)
    (cursor : PeTTaSpec.PrologCore.Resolver.PreparedCursor)
    (resource : RetainedAlternativeSegment)
    (resources : List RetainedAlternativeSegment)
    (base : List PLeaTTa.Alt)
    (ownership : resource.Owns alpha cursor) :
    AnswerOriginResourceAgrees alpha
      (AnswerOrigin.cutBoundary predicateScope
        (AnswerOrigin.choice predicateScope (.clauses predicateScope cursor)
          (AnswerOrigin.task
            (leafScope := predicateScope) (bindings := bindings))))
      (resource :: resources) resources
      (resource.alts ++ (PLeaTTa.Alt.barrier :: base)) base := by
  apply AnswerOriginResourceAgrees.cutBoundary
  apply AnswerOriginResourceAgrees.choice
  · exact AnswerOriginResourceAgrees.task _ _ _ _
  · exact RightAlternativeRegionAgrees.clauses _ _ _ ownership

/-- After private product scheduling, the answer path crosses only the outer
choice.  Its inactive right region therefore consumes the retained clause
alternatives and the same activation marker together, exactly once. -/
theorem scheduled_call_exact
    {alpha : List (LogicVar × String)}
    (callerScope predicateScope : CutScopeId) (bindings : Substitution)
    (cursor : PeTTaSpec.PrologCore.Resolver.PreparedCursor)
    (callerTail : List PeTTaSpec.PrologCore.Goal)
    (resource : RetainedAlternativeSegment)
    (resources : List RetainedAlternativeSegment)
    (base : List PLeaTTa.Alt)
    (ownership : resource.Owns alpha cursor) :
    AnswerOriginResourceAgrees alpha
      (AnswerOrigin.choice callerScope
        (.product callerScope
          (.cutBoundary predicateScope
            (.choice predicateScope .done
              (.clauses predicateScope cursor)))
          callerTail)
        (AnswerOrigin.task
          (leafScope := callerScope) (bindings := bindings)))
      (resource :: resources) resources
      ((resource.alts ++ [PLeaTTa.Alt.barrier]) ++ base) base := by
  apply AnswerOriginResourceAgrees.choice
  · exact AnswerOriginResourceAgrees.task _ _ _ _
  · exact RightAlternativeRegionAgrees.scheduled _ _ _ _ _ ownership

/-- Inversion of the active-call witness: the list prefix and the literal
cursor ownership are both forced by the origin, not supplied afterward. -/
theorem active_call_prefix_exact
    {alpha : List (LogicVar × String)}
    {predicateScope : CutScopeId} {bindings : Substitution}
    {cursor : PeTTaSpec.PrologCore.Resolver.PreparedCursor}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (agreement :
      AnswerOriginResourceAgrees alpha
        (AnswerOrigin.cutBoundary predicateScope
          (AnswerOrigin.choice predicateScope (.clauses predicateScope cursor)
            (AnswerOrigin.task
              (leafScope := predicateScope) (bindings := bindings))))
        (resource :: resources) resources beforeAlts afterAlts) :
    beforeAlts =
        resource.alts ++ (PLeaTTa.Alt.barrier :: afterAlts) ∧
      resource.Owns alpha cursor := by
  cases agreement with
  | cutBoundary _ inside insideAgrees =>
      cases insideAgrees with
      | choice _ _ leafOrigin leafAgrees regionAgrees =>
          cases leafAgrees
          rcases regionAgrees.clauses_exact with
            ⟨segmentExact, ownership⟩
          subst segmentExact
          exact ⟨rfl, ownership⟩

/-- Inversion of the scheduled-call witness: one choice owns the retained
scan and exactly one marker, with no second cut-boundary consumption. -/
theorem scheduled_call_prefix_exact
    {alpha : List (LogicVar × String)}
    {callerScope predicateScope : CutScopeId} {bindings : Substitution}
    {cursor : PeTTaSpec.PrologCore.Resolver.PreparedCursor}
    {callerTail : List PeTTaSpec.PrologCore.Goal}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (agreement :
      AnswerOriginResourceAgrees alpha
        (AnswerOrigin.choice callerScope
          (.product callerScope
            (.cutBoundary predicateScope
              (.choice predicateScope .done
                (.clauses predicateScope cursor)))
            callerTail)
          (AnswerOrigin.task
            (leafScope := callerScope) (bindings := bindings)))
        (resource :: resources) resources beforeAlts afterAlts) :
    beforeAlts =
        (resource.alts ++ [PLeaTTa.Alt.barrier]) ++ afterAlts ∧
      resource.Owns alpha cursor := by
  cases agreement with
  | choice _ _ leafOrigin leafAgrees regionAgrees =>
      cases leafAgrees
      rcases regionAgrees.scheduled_exact with
        ⟨segmentExact, ownership⟩
      subst segmentExact
      exact ⟨rfl, ownership⟩

/-- A realistic nested state exercises both right-region constructors and
the active cut constructor in their actual leaf-to-root order: an inner call
is active inside the caller continuation of an already scheduled outer call. -/
theorem active_under_scheduled_exact
    {alpha : List (LogicVar × String)}
    (outerCallerScope outerPredicateScope innerPredicateScope : CutScopeId)
    (bindings : Substitution)
    (innerCursor outerCursor :
      PeTTaSpec.PrologCore.Resolver.PreparedCursor)
    (outerCallerTail : List PeTTaSpec.PrologCore.Goal)
    (innerResource outerResource : RetainedAlternativeSegment)
    (base : List PLeaTTa.Alt)
    (innerOwnership : innerResource.Owns alpha innerCursor)
    (outerOwnership : outerResource.Owns alpha outerCursor) :
    AnswerOriginResourceAgrees alpha
      (AnswerOrigin.choice outerCallerScope
        (.product outerCallerScope
          (.cutBoundary outerPredicateScope
            (.choice outerPredicateScope .done
              (.clauses outerPredicateScope outerCursor)))
          outerCallerTail)
        (AnswerOrigin.cutBoundary innerPredicateScope
          (AnswerOrigin.choice innerPredicateScope
            (.clauses innerPredicateScope innerCursor)
            (AnswerOrigin.task
              (leafScope := innerPredicateScope) (bindings := bindings)))))
      [innerResource, outerResource] []
      (innerResource.alts ++
        (PLeaTTa.Alt.barrier ::
          ((outerResource.alts ++ [PLeaTTa.Alt.barrier]) ++ base)))
      base := by
  apply AnswerOriginResourceAgrees.choice
  · exact
      active_call_exact innerPredicateScope bindings innerCursor innerResource
        [outerResource]
        ((outerResource.alts ++ [PLeaTTa.Alt.barrier]) ++ base)
        innerOwnership
  · exact
      RightAlternativeRegionAgrees.scheduled outerCallerScope
        outerPredicateScope outerCursor outerCallerTail outerResource
        outerOwnership

/-- The nested clauses/cut/scheduled path is constructively inhabited.  The
two exact resources come from the existing arbitrary-depth context zipper,
so this witness does not assume resource ownership independently. -/
theorem nested_answer_resource_path_is_inhabited :
    ∃ innerCursor outerCursor :
        PeTTaSpec.PrologCore.Resolver.PreparedCursor,
      ∃ innerResource outerResource : RetainedAlternativeSegment,
        AnswerOriginResourceAgrees ([] : List (LogicVar × String))
          (AnswerOrigin.choice 3
            (.product 3
              (.cutBoundary 2
                (.choice 2 .done (.clauses 2 outerCursor)))
              [])
            (AnswerOrigin.cutBoundary 1
              (AnswerOrigin.choice 1 (.clauses 1 innerCursor)
                (AnswerOrigin.task
                  (leafScope := 1) (bindings := ([] : Substitution))))))
          [innerResource, outerResource] []
          (innerResource.alts ++
            (PLeaTTa.Alt.barrier ::
              (outerResource.alts ++ [PLeaTTa.Alt.barrier])))
          [] := by
  let emptySegment : ControlSegment :=
    { barrier := 0
      references := []
      executables := [] }
  have emptySegmentAgrees : emptySegment.Agrees [] := by
    exact PrologOrdinaryStepBridge.NormalizedAlphaGoalsAgree.nil
  obtain
      ⟨innerCursor, outerCursor, innerResource, outerResource, alignment⟩ :=
    two_resource_frames_are_inhabited (.sym "answer-origin-query")
      1 2 3 0 emptySegment emptySegment emptySegmentAgrees emptySegmentAgrees
  have innerOwnership : innerResource.Owns [] innerCursor :=
    head_resource_owns alignment
  have outerAlignment := tail_resource_context alignment
  have outerOwnership : outerResource.Owns [] outerCursor :=
    head_resource_owns outerAlignment
  refine ⟨innerCursor, outerCursor, innerResource, outerResource, ?_⟩
  simpa using
    (active_under_scheduled_exact 3 2 1 ([] : Substitution)
      innerCursor outerCursor [] innerResource outerResource []
      innerOwnership outerOwnership)

/-- Omitting the active predicate's marker is rejected even when the retained
clause bank itself is empty. -/
theorem active_missing_marker_rejected
    {alpha : List (LogicVar × String)}
    {predicateScope : CutScopeId} {bindings : Substitution}
    {cursor : PeTTaSpec.PrologCore.Resolver.PreparedCursor}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {base : List PLeaTTa.Alt} :
    ¬ AnswerOriginResourceAgrees alpha
      (AnswerOrigin.cutBoundary predicateScope
        (AnswerOrigin.choice predicateScope (.clauses predicateScope cursor)
          (AnswerOrigin.task
            (leafScope := predicateScope) (bindings := bindings))))
      (resource :: resources) resources
      (resource.alts ++ base) base := by
  intro agreement
  have prefixExact := (active_call_prefix_exact agreement).1
  have lengths := congrArg List.length prefixExact
  simp only [List.length_append, List.length_cons] at lengths
  omega

/-- Counting the scheduled predicate marker twice is likewise rejected. -/
theorem scheduled_double_marker_rejected
    {alpha : List (LogicVar × String)}
    {callerScope predicateScope : CutScopeId} {bindings : Substitution}
    {cursor : PeTTaSpec.PrologCore.Resolver.PreparedCursor}
    {callerTail : List PeTTaSpec.PrologCore.Goal}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {base : List PLeaTTa.Alt} :
    ¬ AnswerOriginResourceAgrees alpha
      (AnswerOrigin.choice callerScope
        (.product callerScope
          (.cutBoundary predicateScope
            (.choice predicateScope .done
              (.clauses predicateScope cursor)))
          callerTail)
        (AnswerOrigin.task
          (leafScope := callerScope) (bindings := bindings)))
      (resource :: resources) resources
      ((resource.alts ++
        [PLeaTTa.Alt.barrier, PLeaTTa.Alt.barrier]) ++ base) base := by
  intro agreement
  have prefixExact := (scheduled_call_prefix_exact agreement).1
  have lengths := congrArg List.length prefixExact
  simp only [List.length_append, List.length_cons, List.length_nil] at lengths
  omega

/-- If upstream ownership distinguishes an empty-bank cursor, the origin
zipper cannot replace it merely because the executable segment is empty.
The separate counterexample below records that `Owns` itself does not yet
distinguish every exhausted call identity. -/
theorem empty_bank_wrong_cursor_rejected_of_notOwned
    {alpha : List (LogicVar × String)}
    {predicateScope : CutScopeId} {bindings : Substitution}
    {cursor : PeTTaSpec.PrologCore.Resolver.PreparedCursor}
    {resource : RetainedAlternativeSegment}
    {resources : List RetainedAlternativeSegment}
    {base : List PLeaTTa.Alt}
    (_empty : resource.alts = [])
    (notOwned : ¬ resource.Owns alpha cursor) :
    ¬ AnswerOriginResourceAgrees alpha
      (AnswerOrigin.cutBoundary predicateScope
        (AnswerOrigin.choice predicateScope (.clauses predicateScope cursor)
          (AnswerOrigin.task
            (leafScope := predicateScope) (bindings := bindings))))
      (resource :: resources) resources
      (PLeaTTa.Alt.barrier :: base) base := by
  intro agreement
  have ownership := (active_call_prefix_exact agreement).2
  exact notOwned ownership

private def exhaustedIdentityCursor
    (predicate : String) :
    PeTTaSpec.PrologCore.Resolver.PreparedCursor :=
  { callGeneration := 0
    predicate := predicate
    arguments := [.atom "owned-output"]
    bindings := []
    reservationStart := 0
    remaining := []
    reservedUntil := 0 }

private def exhaustedIdentityResource : RetainedAlternativeSegment :=
  { argsv := []
    args := []
    res := .sym "owned-output"
    rest := []
    binding := []
    qterm := .sym "answer-origin-query"
    barrier := 0
    counter := 0
    alts := []
    finalCounter := 0 }

private theorem exhaustedIdentityResource_owns
    (predicate : String) :
    exhaustedIdentityResource.Owns ([] : List (LogicVar × String))
      (exhaustedIdentityCursor predicate) := by
  refine ⟨[], ?_, ?_, rfl, .nil, ?_, ?_⟩
  · refine ⟨.nil 0, ?_, ?_, ?_⟩
    · intro index member
      simp [exhaustedIdentityCursor,
        PeTTaSpec.PrologCore.Resolver.termsVariables,
        PeTTaSpec.PrologCore.Resolver.termVariables,
        PeTTaSpec.PrologCore.Resolver.substitutionVariables] at member
    · intro branch member
      simp [exhaustedIdentityCursor] at member
    · intro branch member
      simp [exhaustedIdentityCursor] at member
  · apply
      PLeaTTa.PrologRecursiveCallPayloadBridge.NormalizedCallAgrees.representative
    constructor
    simpa [exhaustedIdentityCursor, exhaustedIdentityResource] using
      (PrologStateBridge.AlphaTermsAgree.cons
        (PrologStateBridge.AlphaTermAgrees.atom
          (alpha := ([] : List (LogicVar × String)))
          (by decide) (by decide))
        PrologStateBridge.AlphaTermsAgree.nil)
  · intro clause member
    simp at member
  · exact PrologActivationMacro.ResolutionScan.nil 0

/-- Upstream exhausted-resource ownership is not injective on call identity:
one literal empty descriptor owns two cursors with different predicate names.
The origin zipper remains exact conditional proof data, but unconditional
occurrence recovery requires strengthening the resource certificate (or an
explicit observational quotient) rather than pretending this seam is closed. -/
theorem exhausted_resource_ownership_not_cursor_injective :
    let leftCursor := exhaustedIdentityCursor "owned-left"
    let rightCursor := exhaustedIdentityCursor "owned-right"
    leftCursor ≠ rightCursor ∧
      exhaustedIdentityResource.alts = [] ∧
      exhaustedIdentityResource.Owns [] leftCursor ∧
      exhaustedIdentityResource.Owns [] rightCursor := by
  dsimp only
  constructor
  · intro cursorsEq
    have predicatesEq := congrArg
      PeTTaSpec.PrologCore.Resolver.PreparedCursor.predicate cursorsEq
    simp [exhaustedIdentityCursor] at predicatesEq
  · exact
      ⟨rfl, exhaustedIdentityResource_owns "owned-left",
        exhaustedIdentityResource_owns "owned-right"⟩

/-- Swapping inner and outer resource cells is rejected as soon as the outer
cell does not own the literal inner cursor.  This is the LIFO-order guard. -/
theorem swapped_resource_order_rejected
    {alpha : List (LogicVar × String)}
    {outerCallerScope outerPredicateScope innerPredicateScope : CutScopeId}
    {bindings : Substitution}
    {innerCursor outerCursor :
      PeTTaSpec.PrologCore.Resolver.PreparedCursor}
    {outerCallerTail : List PeTTaSpec.PrologCore.Goal}
    {innerResource outerResource : RetainedAlternativeSegment}
    {beforeAlts base : List PLeaTTa.Alt}
    (outerNotInner : ¬ outerResource.Owns alpha innerCursor) :
    ¬ AnswerOriginResourceAgrees alpha
      (AnswerOrigin.choice outerCallerScope
        (.product outerCallerScope
          (.cutBoundary outerPredicateScope
            (.choice outerPredicateScope .done
              (.clauses outerPredicateScope outerCursor)))
          outerCallerTail)
        (AnswerOrigin.cutBoundary innerPredicateScope
          (AnswerOrigin.choice innerPredicateScope
            (.clauses innerPredicateScope innerCursor)
            (AnswerOrigin.task
              (leafScope := innerPredicateScope) (bindings := bindings)))))
      [outerResource, innerResource] [] beforeAlts base := by
  intro agreement
  cases agreement with
  | choice _ _ insideOrigin insideAgrees regionAgrees =>
      cases insideAgrees with
      | cutBoundary _ activeOrigin activeAgrees =>
          cases activeAgrees with
          | choice _ _ leafOrigin leafAgrees innerRegionAgrees =>
              cases leafAgrees
              exact outerNotInner innerRegionAgrees.clauses_exact.2

/-- Catch crossings are unrepresentable until the fine executable owns a
typed catch frame. -/
theorem catch_fail_closed
    {alpha : List (LogicVar × String)}
    {leafScope scope : CutScopeId} {bindings entryBindings : Substitution}
    {handlerScope : ExceptionScopeId} {catcher : Term}
    {handler : PeTTaSpec.PrologCore.Goal} {body next : Search}
    {inside : AnswerOrigin leafScope bindings body next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (agreement :
      AnswerOriginResourceAgrees alpha
        (AnswerOrigin.catchBoundary handlerScope scope catcher handler
          entryBindings inside)
        beforeResources afterResources beforeAlts afterAlts) :
    False := by
  cases agreement

end AnswerOriginResourceAgrees

end PLeaTTa.PrologAnswerResourceBridge
