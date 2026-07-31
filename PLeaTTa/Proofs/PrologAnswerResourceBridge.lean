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
open PrologSourceProductContextBridge

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

mutual

  /-- Exact executable bank slice owned by one literal inactive source right
  branch.

  A clause branch is singleton and excludes its activation marker because the
  enclosing active cut boundary consumes that marker.  A scheduled branch is
  the literal right product produced by an earlier `RawStep.productAnswer`.
  Its complete nonempty slice is certified by an exact historical answer
  origin indexed by successor `next`; this does not identify a separately
  recorded scheduling-event token.  The relation never recognizes or
  normalizes a `choice ... done ...` syntax pattern. -/
  inductive RightAlternativeRegionAgrees
      (alpha : List (LogicVar × String)) :
      Search → List RetainedAlternativeSegment → List PLeaTTa.Alt → Prop where
    | clauses (scope : CutScopeId)
        (cursor : PeTTaSpec.PrologCore.Resolver.PreparedCursor)
        (resource : RetainedAlternativeSegment)
        (ownership : resource.Owns alpha cursor) :
        RightAlternativeRegionAgrees alpha (.clauses scope cursor)
          [resource] resource.alts
    | scheduled (callerScope : CutScopeId)
        (callerTail : List PeTTaSpec.PrologCore.Goal)
        {leafScope : CutScopeId} {bindings : Substitution}
        {head next : Search}
        (origin : AnswerOrigin leafScope bindings head next)
        (resources : List RetainedAlternativeSegment)
        (nonempty : resources ≠ [])
        (history :
          AnswerOriginResourceAgrees alpha origin resources []
            (flattenOwnedAlts resources []) []) :
        RightAlternativeRegionAgrees alpha
          (.product callerScope next callerTail) resources
          (flattenOwnedAlts resources [])

  /-- Lockstep consumption of retained source resources and executable
  alternatives along one particular `AnswerOrigin` proof.

  Choice descends to the answer leaf first and consumes its literal inactive
  right slice while unwinding, which is the executable bank's LIFO order.  A
  cut boundary then consumes exactly one anonymous marker.  Task consumes
  nothing.  There is intentionally no catch-boundary constructor. -/
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
        {regionResources : List RetainedAlternativeSegment}
        {beforeAlts afterAlts regionAlts : List PLeaTTa.Alt}
        (insideAgrees :
          AnswerOriginResourceAgrees alpha inside beforeResources
            (regionResources ++ afterResources) beforeAlts
            (regionAlts ++ afterAlts))
        (regionAgrees :
          RightAlternativeRegionAgrees alpha right regionResources regionAlts) :
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

end

namespace RightAlternativeRegionAgrees

/-- A clause region exposes the exact retained scan result and the ownership
certificate for the literal cursor in the source branch. -/
theorem clauses_exact
    {alpha : List (LogicVar × String)} {scope : CutScopeId}
    {cursor : PeTTaSpec.PrologCore.Resolver.PreparedCursor}
    {resource : RetainedAlternativeSegment} {segment : List PLeaTTa.Alt}
    (agreement :
      RightAlternativeRegionAgrees alpha (.clauses scope cursor)
        [resource] segment) :
    segment = resource.alts ∧ resource.Owns alpha cursor := by
  cases agreement with
  | clauses _ _ _ ownership =>
      exact ⟨rfl, ownership⟩

/-- Shape inversion for a clause region without presupposing the singleton
resource.  This is the robust form used by order-rejection proofs: the
relation itself identifies the unique owning resource. -/
theorem clauses_shape
    {alpha : List (LogicVar × String)} {scope : CutScopeId}
    {cursor : PeTTaSpec.PrologCore.Resolver.PreparedCursor}
    {resources : List RetainedAlternativeSegment}
    {segment : List PLeaTTa.Alt}
    (agreement :
      RightAlternativeRegionAgrees alpha (.clauses scope cursor)
        resources segment) :
    ∃ resource : RetainedAlternativeSegment,
      resources = [resource] ∧ segment = resource.alts ∧
        resource.Owns alpha cursor := by
  cases agreement with
  | clauses _ _ resource ownership =>
      exact ⟨resource, rfl, rfl, ownership⟩

/-- A scheduled product exposes its literal nonempty flattened resource slice
and an exact answer origin indexed by its inner successor.

The historical source is existential because it is no longer present in the
right branch.  No separate event identity is claimed; the successor, resource
slice, and totally consumed bank are indices and hence cannot be reconstructed
independently. -/
theorem scheduled_exact
    {alpha : List (LogicVar × String)}
    {callerScope : CutScopeId}
    {callerTail : List PeTTaSpec.PrologCore.Goal}
    {next : Search}
    {resources : List RetainedAlternativeSegment}
    {segment : List PLeaTTa.Alt}
    (agreement :
      RightAlternativeRegionAgrees alpha
        (.product callerScope next callerTail) resources segment) :
    segment = flattenOwnedAlts resources [] ∧ resources ≠ [] ∧
      ∃ (leafScope : CutScopeId) (bindings : Substitution) (head : Search),
        ∃ origin : AnswerOrigin leafScope bindings head next,
          AnswerOriginResourceAgrees alpha origin resources []
            (flattenOwnedAlts resources []) [] := by
  cases agreement with
  | scheduled callerScope callerTail origin resources nonempty history =>
      exact ⟨rfl, nonempty, _, _, _, origin, history⟩

/-- No inactive source choice can be paired with an empty resource slice. -/
theorem resources_ne_nil
    {alpha : List (LogicVar × String)}
    {right : Search} {resources : List RetainedAlternativeSegment}
    {segment : List PLeaTTa.Alt}
    (agreement : RightAlternativeRegionAgrees alpha right resources segment) :
    resources ≠ [] := by
  cases agreement with
  | clauses => simp
  | scheduled _ _ _ _ nonempty _ => exact nonempty

end RightAlternativeRegionAgrees

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

/-- Endpoint inversion for the unique task constructor, kept nondependent so
later proofs never ask constructor elimination to solve list equations. -/
theorem task_endpoints_exact
    {alpha : List (LogicVar × String)}
    {leafScope : CutScopeId} {bindings : Substitution}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (agreement :
      AnswerOriginResourceAgrees alpha
        (AnswerOrigin.task (leafScope := leafScope) (bindings := bindings))
        beforeResources afterResources beforeAlts afterAlts) :
    beforeResources = afterResources ∧ beforeAlts = afterAlts := by
  cases agreement
  exact ⟨rfl, rfl⟩

/-- Exact nondependent inversion of one source-choice zipper layer. -/
theorem choice_layer_exact
    {alpha : List (LogicVar × String)}
    {scope leafScope : CutScopeId} {bindings : Substitution}
    {left next right : Search}
    {inside : AnswerOrigin leafScope bindings left next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (agreement :
      AnswerOriginResourceAgrees alpha
        (AnswerOrigin.choice scope right inside)
        beforeResources afterResources beforeAlts afterAlts) :
    ∃ regionResources : List RetainedAlternativeSegment,
      ∃ regionAlts : List PLeaTTa.Alt,
        AnswerOriginResourceAgrees alpha inside beforeResources
            (regionResources ++ afterResources) beforeAlts
            (regionAlts ++ afterAlts) ∧
          RightAlternativeRegionAgrees alpha right regionResources regionAlts := by
  cases agreement with
  | choice _ _ _ insideAgrees regionAgrees =>
      exact ⟨_, _, insideAgrees, regionAgrees⟩

/-- Exact nondependent inversion of one active cut-boundary zipper layer. -/
theorem cutBoundary_layer_exact
    {alpha : List (LogicVar × String)}
    {scope leafScope : CutScopeId} {bindings : Substitution}
    {body next : Search}
    {inside : AnswerOrigin leafScope bindings body next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (agreement :
      AnswerOriginResourceAgrees alpha
        (AnswerOrigin.cutBoundary scope inside)
        beforeResources afterResources beforeAlts afterAlts) :
    AnswerOriginResourceAgrees alpha inside beforeResources afterResources
      beforeAlts (PLeaTTa.Alt.barrier :: afterAlts) := by
  cases agreement with
  | cutBoundary _ _ insideAgrees => exact insideAgrees

/-- Every retained resource in a certified slice contains ordinary branches
only.  Predicate markers are introduced solely by `flattenOwnedAlts`. -/
private def ResourcesBarrierFree
    (resources : List RetainedAlternativeSegment) : Prop :=
  ∀ resource, resource ∈ resources → PLeaTTa.barrierCount resource.alts = 0

private theorem ResourcesBarrierFree.append
    {left right : List RetainedAlternativeSegment}
    (leftFree : ResourcesBarrierFree left)
    (rightFree : ResourcesBarrierFree right) :
    ResourcesBarrierFree (left ++ right) := by
  intro resource member
  simp only [List.mem_append] at member
  rcases member with member | member
  · exact leftFree resource member
  · exact rightFree resource member

mutual

  /-- A literal inactive region certifies marker-freedom of every resource it
  owns, including a fossilized scheduled region of arbitrary historical
  depth. -/
  private theorem right_resources_barrier_free
      {alpha : List (LogicVar × String)}
      {right : Search} {resources : List RetainedAlternativeSegment}
      {segment : List PLeaTTa.Alt}
      (agreement :
        RightAlternativeRegionAgrees alpha right resources segment) :
      ResourcesBarrierFree resources := by
    cases agreement with
    | clauses _ _ resource ownership =>
        intro candidate member
        simp only [List.mem_singleton] at member
        subst candidate
        exact RetainedAlternativeSegment.barrierCount_zero ownership
    | scheduled _ _ origin resources _ history =>
        rcases origin_consumed_resources_barrier_free history with
          ⟨consumed, resourcesEq, consumedFree⟩
        have exactResources : resources = consumed := by
          simpa only [List.append_nil] using resourcesEq
        rw [exactResources]
        exact consumedFree

  /-- The resources removed by an answer-origin zipper form a marker-free
  ordered prefix.  This is the resource analogue of `resources_suffix`, with
  the ownership invariant retained rather than erased. -/
  private theorem origin_consumed_resources_barrier_free
      {alpha : List (LogicVar × String)}
      {leafScope : CutScopeId} {bindings : Substitution}
      {source next : Search}
      {origin : AnswerOrigin leafScope bindings source next}
      {beforeResources afterResources : List RetainedAlternativeSegment}
      {beforeAlts afterAlts : List PLeaTTa.Alt}
      (agreement :
        AnswerOriginResourceAgrees alpha origin beforeResources afterResources
          beforeAlts afterAlts) :
      ∃ consumed : List RetainedAlternativeSegment,
        beforeResources = consumed ++ afterResources ∧
          ResourcesBarrierFree consumed := by
    cases agreement with
    | task =>
        refine ⟨[], rfl, ?_⟩
        intro resource member
        simp at member
    | choice _ _ _ insideAgrees regionAgrees =>
        rcases origin_consumed_resources_barrier_free insideAgrees with
          ⟨insideConsumed, beforeEq, insideFree⟩
        refine ⟨insideConsumed ++ _, ?_, ResourcesBarrierFree.append
          insideFree (right_resources_barrier_free regionAgrees)⟩
        rw [beforeEq]
        simp only [List.append_assoc]
    | cutBoundary _ _ insideAgrees =>
        exact origin_consumed_resources_barrier_free insideAgrees

end

/-- Flattening a marker-free resource slice inserts exactly one anonymous
predicate marker per resource, above any older base bank. -/
private theorem flattenOwnedAlts_barrierCount_exact
    {resources : List RetainedAlternativeSegment}
    {base : List PLeaTTa.Alt}
    (resourcesFree : ResourcesBarrierFree resources) :
    PLeaTTa.barrierCount (flattenOwnedAlts resources base) =
      resources.length + PLeaTTa.barrierCount base := by
  induction resources with
  | nil => simp
  | cons resource resources inductionHypothesis =>
      have headFree : PLeaTTa.barrierCount resource.alts = 0 :=
        resourcesFree resource (by simp)
      have tailFree : ResourcesBarrierFree resources := by
        intro candidate member
        exact resourcesFree candidate (by simp [member])
      simp only [flattenOwnedAlts_cons, PLeaTTa.barrierCount_append,
        PLeaTTa.barrierCount_cons_barrier, headFree, Nat.zero_add,
        List.length_cons, inductionHypothesis tailFree]
      omega

/-- A fossilized scheduled region contains exactly one marker for each
historically consumed resource.  The count follows from ownership, not from
recognizing a particular successor syntax. -/
theorem scheduled_barrierCount_exact
    {alpha : List (LogicVar × String)}
    {callerScope : CutScopeId}
    {callerTail : List PeTTaSpec.PrologCore.Goal}
    {next : Search}
    {resources : List RetainedAlternativeSegment}
    {segment : List PLeaTTa.Alt}
    (agreement :
      RightAlternativeRegionAgrees alpha
        (.product callerScope next callerTail) resources segment) :
    PLeaTTa.barrierCount segment = resources.length := by
  rcases agreement.scheduled_exact with
    ⟨segmentEq, _nonempty, _leafScope, _bindings, _head, _origin, _history⟩
  rw [segmentEq]
  have count := flattenOwnedAlts_barrierCount_exact (base := [])
    (right_resources_barrier_free agreement)
  change PLeaTTa.barrierCount (flattenOwnedAlts resources []) =
    resources.length + 0 at count
  omega

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

/-- Resource and alternative consumption are simultaneously ordered prefix
removal.  This uses the generated mutual recursor: the scheduled-history
hypothesis is structurally traversed for well-foundedness, while only the
active origin's induction hypothesis contributes to these two suffix facts. -/
private theorem endpoints_suffix
    {alpha : List (LogicVar × String)}
    {leafScope : CutScopeId} {bindings : Substitution}
    {source next : Search}
    {origin : AnswerOrigin leafScope bindings source next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts afterAlts : List PLeaTTa.Alt}
    (agreement :
      AnswerOriginResourceAgrees alpha origin beforeResources afterResources
        beforeAlts afterAlts) :
    (∃ consumed, beforeResources = consumed ++ afterResources) ∧
      ∃ consumed, beforeAlts = consumed ++ afterAlts := by
  exact AnswerOriginResourceAgrees.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ beforeResources afterResources beforeAlts afterAlts _ =>
      (∃ consumed, beforeResources = consumed ++ afterResources) ∧
        ∃ consumed, beforeAlts = consumed ++ afterAlts)
    (fun _ _ _ _ => True.intro)
    (by intros; trivial)
    (fun _ _ _ _ => ⟨⟨[], rfl⟩, ⟨[], rfl⟩⟩)
    (by
      intro scope right leafScope bindings left next inside
        beforeResources afterResources regionResources
        beforeAlts afterAlts regionAlts insideAgrees regionAgrees
        insideHypothesis regionHypothesis
      rcases insideHypothesis with
        ⟨⟨consumedResources, resourcesEq⟩, ⟨consumedAlts, altsEq⟩⟩
      constructor
      · refine ⟨consumedResources ++ regionResources, ?_⟩
        rw [resourcesEq]
        simp only [List.append_assoc]
      · refine ⟨consumedAlts ++ regionAlts, ?_⟩
        rw [altsEq]
        simp only [List.append_assoc])
    (by
      intro scope leafScope bindings body next inside
        beforeResources afterResources beforeAlts afterAlts insideAgrees
        insideHypothesis
      rcases insideHypothesis with
        ⟨resourcesHypothesis, ⟨consumedAlts, altsEq⟩⟩
      exact
        ⟨resourcesHypothesis, ⟨consumedAlts ++ [PLeaTTa.Alt.barrier], by
          rw [altsEq]
          simp only [List.append_assoc, List.singleton_append]⟩⟩)
    agreement

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
    ∃ consumed, beforeResources = consumed ++ afterResources :=
  (endpoints_suffix agreement).1

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
    ∃ consumed, beforeAlts = consumed ++ afterAlts :=
  (endpoints_suffix agreement).2

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
    (regionResources := [resource]) (regionAlts := resource.alts)
  · exact AnswerOriginResourceAgrees.task _ _ _ _
  · exact RightAlternativeRegionAgrees.clauses _ _ _ ownership

/-- A one-level scheduled right branch is the historical product successor of
the exact active-call answer path.  This is a corollary of the general
history-indexed constructor, not a second depth-specific representation. -/
theorem one_level_scheduled_region_exact
    {alpha : List (LogicVar × String)}
    (callerScope predicateScope : CutScopeId) (bindings : Substitution)
    (cursor : PeTTaSpec.PrologCore.Resolver.PreparedCursor)
    (callerTail : List PeTTaSpec.PrologCore.Goal)
    (resource : RetainedAlternativeSegment)
    (ownership : resource.Owns alpha cursor) :
    RightAlternativeRegionAgrees alpha
      (.product callerScope
        (.cutBoundary predicateScope
          (.choice predicateScope .done (.clauses predicateScope cursor)))
        callerTail)
      [resource] (resource.alts ++ [PLeaTTa.Alt.barrier]) := by
  let origin :
      AnswerOrigin predicateScope bindings
        (.cutBoundary predicateScope
          (.choice predicateScope (.task predicateScope [] bindings)
            (.clauses predicateScope cursor)))
        (.cutBoundary predicateScope
          (.choice predicateScope .done (.clauses predicateScope cursor))) :=
    .cutBoundary predicateScope
      (.choice predicateScope (.clauses predicateScope cursor) .task)
  have history :
      AnswerOriginResourceAgrees alpha origin [resource] []
        (flattenOwnedAlts [resource] []) [] := by
    simpa [flattenOwnedAlts] using
      (active_call_exact predicateScope bindings cursor resource [] [] ownership)
  simpa [flattenOwnedAlts] using
    (RightAlternativeRegionAgrees.scheduled callerScope callerTail origin
      [resource] (by simp) history)

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
    (regionResources := [resource])
    (regionAlts := resource.alts ++ [PLeaTTa.Alt.barrier])
  · exact AnswerOriginResourceAgrees.task _ _ _ _
  · exact
      one_level_scheduled_region_exact callerScope predicateScope bindings
        cursor callerTail resource ownership

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
  have activeChoice := cutBoundary_layer_exact
    (inside :=
      AnswerOrigin.choice predicateScope (.clauses predicateScope cursor)
        (AnswerOrigin.task
          (leafScope := predicateScope) (bindings := bindings)))
    agreement
  rcases choice_layer_exact activeChoice with
    ⟨regionResources, regionAlts, leafAgrees, regionAgrees⟩
  have leafEndpoints := task_endpoints_exact leafAgrees
  have regionResourcesExact : [resource] = regionResources := by
    apply List.append_cancel_right
    simpa only [List.singleton_append] using leafEndpoints.1
  subst regionResources
  rcases regionAgrees.clauses_exact with ⟨regionAltsExact, ownership⟩
  subst regionAlts
  exact ⟨leafEndpoints.2, ownership⟩

/-- A singleton historical slice ending in the literal one-level predicate
successor recovers ownership of that successor's retained cursor.

The proof inverts the carried `AnswerOrigin`: only cut/choice/task can produce
this successor shape.  Thus scheduled provenance cannot substitute an
unrelated cursor merely because its flattened alternative bank is equal. -/
theorem one_level_scheduled_history_owns
    {alpha : List (LogicVar × String)}
    {leafScope predicateScope : CutScopeId} {bindings : Substitution}
    {head : Search}
    {cursor : PeTTaSpec.PrologCore.Resolver.PreparedCursor}
    {resource : RetainedAlternativeSegment}
    {origin :
      AnswerOrigin leafScope bindings head
        (.cutBoundary predicateScope
          (.choice predicateScope .done (.clauses predicateScope cursor)))}
    (history :
      AnswerOriginResourceAgrees alpha origin [resource] []
        (flattenOwnedAlts [resource] []) []) :
    resource.Owns alpha cursor := by
  cases origin with
  | cutBoundary _ inside =>
      have activeChoice := cutBoundary_layer_exact (inside := inside) history
      cases inside with
      | choice _ _ leaf =>
          rcases choice_layer_exact (inside := leaf) activeChoice with
            ⟨regionResources, regionAlts, leafAgrees, regionAgrees⟩
          cases leaf with
          | task =>
              have leafEndpoints := task_endpoints_exact leafAgrees
              have regionResourcesExact : [resource] = regionResources := by
                apply List.append_cancel_right
                simpa only [List.singleton_append] using leafEndpoints.1
              subst regionResources
              exact regionAgrees.clauses_exact.2

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
  rcases choice_layer_exact agreement with
    ⟨regionResources, regionAlts, leafAgrees, regionAgrees⟩
  have leafEndpoints := task_endpoints_exact leafAgrees
  have regionResourcesExact : [resource] = regionResources := by
    apply List.append_cancel_right
    simpa only [List.singleton_append] using leafEndpoints.1
  subst regionResources
  rcases regionAgrees.scheduled_exact with
    ⟨regionAltsExact, _nonempty, leafScope, priorBindings, head, origin,
      history⟩
  have ownership : resource.Owns alpha cursor :=
    one_level_scheduled_history_owns history
  have regionAltsOne :
      regionAlts = resource.alts ++ [PLeaTTa.Alt.barrier] := by
    simpa [flattenOwnedAlts] using regionAltsExact
  subst regionAlts
  exact ⟨leafEndpoints.2, ownership⟩

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
  let innerOrigin :
      AnswerOrigin innerPredicateScope bindings
        (.cutBoundary innerPredicateScope
          (.choice innerPredicateScope
            (.task innerPredicateScope [] bindings)
            (.clauses innerPredicateScope innerCursor)))
        (.cutBoundary innerPredicateScope
          (.choice innerPredicateScope .done
            (.clauses innerPredicateScope innerCursor))) :=
    .cutBoundary innerPredicateScope
      (.choice innerPredicateScope (.clauses innerPredicateScope innerCursor)
        .task)
  have insideAgrees :
      AnswerOriginResourceAgrees alpha innerOrigin
        [innerResource, outerResource] [outerResource]
        (innerResource.alts ++
          (PLeaTTa.Alt.barrier ::
            ((outerResource.alts ++ [PLeaTTa.Alt.barrier]) ++ base)))
        ((outerResource.alts ++ [PLeaTTa.Alt.barrier]) ++ base) :=
    active_call_exact innerPredicateScope bindings innerCursor innerResource
      [outerResource]
      ((outerResource.alts ++ [PLeaTTa.Alt.barrier]) ++ base)
      innerOwnership
  have regionAgrees :
      RightAlternativeRegionAgrees alpha
        (.product outerCallerScope
          (.cutBoundary outerPredicateScope
            (.choice outerPredicateScope .done
              (.clauses outerPredicateScope outerCursor)))
          outerCallerTail)
        [outerResource]
        (outerResource.alts ++ [PLeaTTa.Alt.barrier]) :=
    one_level_scheduled_region_exact outerCallerScope outerPredicateScope
      bindings outerCursor outerCallerTail outerResource outerOwnership
  exact AnswerOriginResourceAgrees.choice
    (alpha := alpha)
    (scope := outerCallerScope)
    (right :=
      .product outerCallerScope
        (.cutBoundary outerPredicateScope
          (.choice outerPredicateScope .done
            (.clauses outerPredicateScope outerCursor)))
        outerCallerTail)
    (inside := innerOrigin)
    (beforeResources := [innerResource, outerResource])
    (afterResources := [])
    (regionResources := [outerResource])
    (beforeAlts :=
      innerResource.alts ++
        (PLeaTTa.Alt.barrier ::
          ((outerResource.alts ++ [PLeaTTa.Alt.barrier]) ++ base)))
    (afterAlts := base)
    (regionAlts := outerResource.alts ++ [PLeaTTa.Alt.barrier])
    insideAgrees regionAgrees

/-- Scheduling the answer produced by `active_under_scheduled_exact` freezes
the complete two-resource history as one inactive right region.  This is the
first shape that cannot be represented by a singleton scheduled-resource
model: the literal successor contains the inner and outer retained predicate
regions together, in leaf-to-root order. -/
theorem two_level_scheduled_region_exact
    {alpha : List (LogicVar × String)}
    (finalCallerScope outerCallerScope outerPredicateScope
      innerPredicateScope : CutScopeId)
    (bindings : Substitution)
    (innerCursor outerCursor :
      PeTTaSpec.PrologCore.Resolver.PreparedCursor)
    (finalCallerTail outerCallerTail : List PeTTaSpec.PrologCore.Goal)
    (innerResource outerResource : RetainedAlternativeSegment)
    (innerOwnership : innerResource.Owns alpha innerCursor)
    (outerOwnership : outerResource.Owns alpha outerCursor) :
    RightAlternativeRegionAgrees alpha
      (.product finalCallerScope
        (.choice outerCallerScope
          (.cutBoundary innerPredicateScope
            (.choice innerPredicateScope .done
              (.clauses innerPredicateScope innerCursor)))
          (.product outerCallerScope
            (.cutBoundary outerPredicateScope
              (.choice outerPredicateScope .done
                (.clauses outerPredicateScope outerCursor)))
            outerCallerTail))
        finalCallerTail)
      [innerResource, outerResource]
      (flattenOwnedAlts [innerResource, outerResource] []) := by
  let origin :
      AnswerOrigin innerPredicateScope bindings
        (.choice outerCallerScope
          (.cutBoundary innerPredicateScope
            (.choice innerPredicateScope
              (.task innerPredicateScope [] bindings)
              (.clauses innerPredicateScope innerCursor)))
          (.product outerCallerScope
            (.cutBoundary outerPredicateScope
              (.choice outerPredicateScope .done
                (.clauses outerPredicateScope outerCursor)))
            outerCallerTail))
        (.choice outerCallerScope
          (.cutBoundary innerPredicateScope
            (.choice innerPredicateScope .done
              (.clauses innerPredicateScope innerCursor)))
          (.product outerCallerScope
            (.cutBoundary outerPredicateScope
              (.choice outerPredicateScope .done
                (.clauses outerPredicateScope outerCursor)))
            outerCallerTail)) :=
    .choice outerCallerScope
      (.product outerCallerScope
        (.cutBoundary outerPredicateScope
          (.choice outerPredicateScope .done
            (.clauses outerPredicateScope outerCursor)))
        outerCallerTail)
      (.cutBoundary innerPredicateScope
        (.choice innerPredicateScope
          (.clauses innerPredicateScope innerCursor) .task))
  have history :
      AnswerOriginResourceAgrees alpha origin
        [innerResource, outerResource] []
        (flattenOwnedAlts [innerResource, outerResource] []) [] := by
    simpa [origin, flattenOwnedAlts, List.append_assoc] using
      (active_under_scheduled_exact outerCallerScope outerPredicateScope
        innerPredicateScope bindings innerCursor outerCursor outerCallerTail
        innerResource outerResource [] innerOwnership outerOwnership)
  exact RightAlternativeRegionAgrees.scheduled finalCallerScope finalCallerTail
    origin [innerResource, outerResource] (by simp) history

/-- The concrete two-level scheduled slice contains two markers, neither one
nor three.  This is an observation-level discriminator against dropping one
historical resource or counting one boundary twice. -/
theorem two_level_scheduled_marker_count_discriminates
    {alpha : List (LogicVar × String)}
    (finalCallerScope outerCallerScope outerPredicateScope
      innerPredicateScope : CutScopeId)
    (bindings : Substitution)
    (innerCursor outerCursor :
      PeTTaSpec.PrologCore.Resolver.PreparedCursor)
    (finalCallerTail outerCallerTail : List PeTTaSpec.PrologCore.Goal)
    (innerResource outerResource : RetainedAlternativeSegment)
    (innerOwnership : innerResource.Owns alpha innerCursor)
    (outerOwnership : outerResource.Owns alpha outerCursor) :
    let segment := flattenOwnedAlts [innerResource, outerResource] []
    PLeaTTa.barrierCount segment = 2 ∧
      PLeaTTa.barrierCount segment ≠ 1 ∧
      PLeaTTa.barrierCount segment ≠ 3 := by
  dsimp only
  have region := two_level_scheduled_region_exact
    finalCallerScope outerCallerScope outerPredicateScope innerPredicateScope
    bindings innerCursor outerCursor finalCallerTail outerCallerTail
    innerResource outerResource innerOwnership outerOwnership
  have exactCount := scheduled_barrierCount_exact region
  simp only [List.length_cons, List.length_nil] at exactCount
  omega

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

/-- The generalized scheduled constructor has a genuine two-resource
inhabitant obtained from the source/resource context zipper.  Its bank has
exactly two markers, so neither the relation nor the marker theorem is
vacuously restricted to singleton histories. -/
theorem two_resource_scheduled_region_is_inhabited :
    ∃ next : Search,
      ∃ resources : List RetainedAlternativeSegment,
        ∃ segment : List PLeaTTa.Alt,
          resources.length = 2 ∧
            RightAlternativeRegionAgrees ([] : List (LogicVar × String))
              (.product 4 next []) resources segment ∧
            PLeaTTa.barrierCount segment = 2 := by
  obtain
      ⟨innerCursor, outerCursor, innerResource, outerResource, historical⟩ :=
    nested_answer_resource_path_is_inhabited
  let next : Search :=
    .choice 3
      (.cutBoundary 1
        (.choice 1 .done (.clauses 1 innerCursor)))
      (.product 3
        (.cutBoundary 2
          (.choice 2 .done (.clauses 2 outerCursor)))
        [])
  let origin : AnswerOrigin 1 ([] : Substitution)
      (.choice 3
        (.cutBoundary 1
          (.choice 1 (.task 1 [] []) (.clauses 1 innerCursor)))
        (.product 3
          (.cutBoundary 2
            (.choice 2 .done (.clauses 2 outerCursor)))
          []))
      next :=
    .choice 3
      (.product 3
        (.cutBoundary 2
          (.choice 2 .done (.clauses 2 outerCursor)))
        [])
      (.cutBoundary 1
        (.choice 1 (.clauses 1 innerCursor) .task))
  have history :
      AnswerOriginResourceAgrees ([] : List (LogicVar × String)) origin
        [innerResource, outerResource] []
        (flattenOwnedAlts [innerResource, outerResource] []) [] := by
    simpa [origin, next, flattenOwnedAlts, List.append_assoc] using historical
  have region :
      RightAlternativeRegionAgrees ([] : List (LogicVar × String))
        (.product 4 next []) [innerResource, outerResource]
        (flattenOwnedAlts [innerResource, outerResource] []) :=
    .scheduled 4 [] origin [innerResource, outerResource] (by simp) history
  refine ⟨next, [innerResource, outerResource],
    flattenOwnedAlts [innerResource, outerResource] [], by simp, region, ?_⟩
  simpa using scheduled_barrierCount_exact region

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
  rcases choice_layer_exact
      (inside :=
        AnswerOrigin.cutBoundary innerPredicateScope
          (AnswerOrigin.choice innerPredicateScope
            (.clauses innerPredicateScope innerCursor)
            (AnswerOrigin.task
              (leafScope := innerPredicateScope) (bindings := bindings))))
      agreement with
    ⟨outerRegionResources, outerRegionAlts, insideAgrees, _outerRegion⟩
  have activeChoice := cutBoundary_layer_exact
    (inside :=
      AnswerOrigin.choice innerPredicateScope
        (.clauses innerPredicateScope innerCursor)
        (AnswerOrigin.task
          (leafScope := innerPredicateScope) (bindings := bindings)))
    insideAgrees
  rcases choice_layer_exact
      (inside :=
        AnswerOrigin.task
          (leafScope := innerPredicateScope) (bindings := bindings))
      activeChoice with
    ⟨innerRegionResources, innerRegionAlts, leafAgrees, innerRegion⟩
  have leafEndpoints := task_endpoints_exact leafAgrees
  rcases innerRegion.clauses_shape with
    ⟨ownedResource, innerResourcesEq, _innerAltsEq, owned⟩
  subst innerRegionResources
  have resourceHeadEq : outerResource = ownedResource := by
    have resourcesEq := leafEndpoints.1
    simp only [List.singleton_append, List.cons.injEq] at resourcesEq
    exact resourcesEq.1
  subst ownedResource
  exact outerNotInner owned

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
