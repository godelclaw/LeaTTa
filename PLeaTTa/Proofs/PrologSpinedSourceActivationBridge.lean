-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologSpinedSourceActivationBridge
Purpose: Compose representative retained-clause activation with the
  arbitrary-depth independent-source product context zipper.
Trusted boundary: none
Main exports:
  SourceControlContextAgrees,
  SpinedRepresentativeProductActivation.sourceStep_throughContext,
  SpinedRepresentativeProductActivation.sourceStep_throughAlignedContext
-/
import PLeaTTa.Proofs.PrologSourceProductContextBridge

namespace PLeaTTa.PrologSpinedSourceActivationBridge

open Metta
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open PrologControlSegmentSpineBridge
open PrologRepresentativeProductActivationBridge
open PrologRepresentativeStepActivationBridge
open PrologSourceProductContextBridge

/-- Source caller tails in their exact inner-to-outer execution order. -/
def sourceCallerGoals (context : ActiveProductContext) :
    List PeTTaSpec.PrologCore.Goal :=
  context.flatMap ActiveProductFrame.callerRest

/-- Ordered alignment between the executable control segments and the older
independent-source predicate frames.

Source scope identities and executable barrier tags are intentionally not
equated: they are different allocation spaces.  Instead, each constructor
pairs the current source predicate scope with one older caller segment,
requires that segment's source/executable spelling to agree at its own
barrier, and advances to an arbitrary next source scope.  Cursor-to-`Alt`
resource ownership is deliberately not part of this relation. -/
inductive SourceControlContextAgrees
    (alpha : List (LogicVar × String)) :
    CutScopeId → List ControlSegment → ActiveProductContext →
      CutScopeId → Prop where
  | nil (scope : CutScopeId) :
      SourceControlContextAgrees alpha scope [] [] scope
  | cons (currentScope nextScope outerScope : CutScopeId)
      (segment : ControlSegment) (segments : List ControlSegment)
      (retained : Search) (context : ActiveProductContext)
      (segmentAgrees : segment.Agrees alpha)
      (retainedScoped : retained.WellScoped currentScope)
      (outerAgrees :
        SourceControlContextAgrees alpha nextScope segments context
          outerScope) :
      SourceControlContextAgrees alpha currentScope
        (segment :: segments)
        ({ callerScope := nextScope
           predicateScope := currentScope
           retained := retained
           callerRest := segment.references } ::
         context)
        outerScope

namespace SourceControlContextAgrees

/-- Alignment is one-to-one: no source frame or executable control segment is
inserted or dropped. -/
theorem length_eq
    {alpha : List (LogicVar × String)}
    {inner outer : CutScopeId}
    {segments : List ControlSegment}
    {context : ActiveProductContext}
    (agreement :
      SourceControlContextAgrees alpha inner segments context outer) :
    context.length = segments.length := by
  induction agreement with
  | nil =>
      rfl
  | cons currentScope nextScope outerScope segment segments retained context
      segmentAgrees retainedScoped outerAgrees inductionHypothesis =>
      simp only [List.length_cons, inductionHypothesis]

/-- Every source frame's caller tail is exactly the corresponding segment's
source goal list, preserving the stored segment order. -/
theorem sourceCallerGoals_eq_flattenReferences
    {alpha : List (LogicVar × String)}
    {inner outer : CutScopeId}
    {segments : List ControlSegment}
    {context : ActiveProductContext}
    (agreement :
      SourceControlContextAgrees alpha inner segments context outer) :
    sourceCallerGoals context = flattenReferences segments := by
  induction agreement with
  | nil =>
      rfl
  | cons currentScope nextScope outerScope segment segments retained context
      segmentAgrees retainedScoped outerAgrees inductionHypothesis =>
      change
        segment.references ++ sourceCallerGoals context =
          segment.references ++ flattenReferences segments
      rw [inductionHypothesis]

/-- The alignment's scope indices and retained-branch premises construct the
generic zipper's source `WellScoped` chain. -/
theorem contextWellScoped
    {alpha : List (LogicVar × String)}
    {inner outer : CutScopeId}
    {segments : List ControlSegment}
    {context : ActiveProductContext}
    (agreement :
      SourceControlContextAgrees alpha inner segments context outer) :
    ActiveProductContext.WellScoped inner context outer := by
  induction agreement with
  | nil scope =>
      exact .nil scope
  | cons currentScope nextScope outerScope segment segments retained context
      segmentAgrees retainedScoped outerAgrees inductionHypothesis =>
      exact
        .cons
          { callerScope := nextScope
            predicateScope := currentScope
            retained := retained
            callerRest := segment.references }
          context outerScope retainedScoped inductionHypothesis

/-- The active source scope and caller goals of the head frame are fixed by
the first control segment, rather than merely carried as unrelated indices. -/
theorem head_shape
    {alpha : List (LogicVar × String)}
    {inner outer : CutScopeId}
    {segment : ControlSegment} {segments : List ControlSegment}
    {frame : ActiveProductFrame} {context : ActiveProductContext}
    (agreement :
      SourceControlContextAgrees alpha inner (segment :: segments)
        (frame :: context) outer) :
    frame.predicateScope = inner ∧
      frame.callerRest = segment.references := by
  cases agreement
  exact ⟨rfl, rfl⟩

end SourceControlContextAgrees

/-- Two distinct nesting levels are constructively alignable in the intended
inner-to-outer order. -/
theorem two_control_frames_are_inhabited
    {alpha : List (LogicVar × String)}
    (inner middle outer : CutScopeId)
    (first second : ControlSegment)
    (firstRetained secondRetained : Search)
    (firstAgrees : first.Agrees alpha)
    (secondAgrees : second.Agrees alpha)
    (firstScoped : firstRetained.WellScoped inner)
    (secondScoped : secondRetained.WellScoped middle) :
    SourceControlContextAgrees alpha inner [first, second]
      [{ callerScope := middle
         predicateScope := inner
         retained := firstRetained
         callerRest := first.references },
       { callerScope := outer
         predicateScope := middle
         retained := secondRetained
         callerRest := second.references }]
      outer := by
  exact
    .cons inner middle outer first [second] firstRetained
      [{ callerScope := outer
         predicateScope := middle
         retained := secondRetained
         callerRest := second.references }]
      firstAgrees firstScoped
      (.cons middle outer outer second [] secondRetained []
        secondAgrees secondScoped (.nil outer))

/-- A context whose head caller goals do not equal the first control segment's
source goals cannot satisfy the alignment relation. -/
theorem wrong_head_caller_goals_is_rejected
    {alpha : List (LogicVar × String)}
    {inner next outer : CutScopeId}
    {segment : ControlSegment} {segments : List ControlSegment}
    {retained : Search} {wrong : List PeTTaSpec.PrologCore.Goal}
    {context : ActiveProductContext}
    (different : wrong ≠ segment.references) :
    ¬ SourceControlContextAgrees alpha inner (segment :: segments)
      ({ callerScope := next
         predicateScope := inner
         retained := retained
         callerRest := wrong } ::
       context)
      outer := by
  intro agreement
  exact different agreement.head_shape.2

/-- A relation that checks only the head frame is insufficient: even when the
first caller tail is exact, corrupting only the second caller tail makes the
whole ordered alignment impossible. -/
theorem wrong_middle_caller_goals_is_rejected
    {alpha : List (LogicVar × String)}
    {inner middle next outer : CutScopeId}
    {first second : ControlSegment} {segments : List ControlSegment}
    {firstRetained secondRetained : Search}
    {wrong : List PeTTaSpec.PrologCore.Goal}
    {context : ActiveProductContext}
    (different : wrong ≠ second.references) :
    ¬ SourceControlContextAgrees alpha inner
      (first :: second :: segments)
      ({ callerScope := middle
         predicateScope := inner
         retained := firstRetained
         callerRest := first.references } ::
       { callerScope := next
         predicateScope := middle
         retained := secondRetained
         callerRest := wrong } ::
       context)
      outer := by
  intro agreement
  cases agreement with
  | cons currentScope nextScope outerScope segment segments retained context
      segmentAgrees retainedScoped outerAgrees =>
      exact different outerAgrees.head_shape.2

/-- The pre-pull local product frontier is well-scoped at its caller scope. -/
theorem sourceProductFrontier_wellScoped
    (callerScope : CutScopeId) (opened : OpenedCall)
    (finish : PreparedCursor)
    (referenceRest : List PeTTaSpec.PrologCore.Goal) :
    (sourceProductFrontier callerScope opened finish
      referenceRest).WellScoped callerScope := by
  exact
    .product callerScope _ referenceRest
      (.cutBoundary callerScope opened.scope _
        (.clauses opened.scope finish))

/-- The post-pull body/retained-cursor product is well-scoped at its caller
scope. -/
theorem activatedSourceProduct_wellScoped
    (callerScope : CutScopeId) (opened : OpenedCall)
    (finish : PreparedCursor) (branch : ClauseBranch)
    (branchTail : List ClauseBranch) (independentResult : Substitution)
    (referenceRest : List PeTTaSpec.PrologCore.Goal) :
    (activatedSourceProduct callerScope opened finish branch branchTail
      independentResult referenceRest).WellScoped callerScope := by
  exact
    .product callerScope _ referenceRest
      (.cutBoundary callerScope opened.scope _
        (.choice opened.scope _ _
          (.task opened.scope branch.body independentResult)
          (.clauses opened.scope (finish.advance branch branchTail))))

/-- The real representative retained-clause source transition lifts through
any already-entered source predicate context.

This theorem preserves the activation's exact empty event list, session
endpoints, and non-committing signal.  It deliberately does not assert that
`context` corresponds to the executable `outer` control segments; that
cross-representation alignment is a separate composition obligation rather
than an implicit list-index convention. -/
theorem
    _root_.PLeaTTa.PrologRepresentativeProductActivationBridge.SpinedRepresentativeProductActivation.sourceStep_throughContext
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {copied : PLeaTTa.Clause}
    {segmentReferenceRest : List PeTTaSpec.PrologCore.Goal}
    {segmentExecutableRest : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {qterm : Atom} {bodyBarrier callerBarrier startCounter : Nat}
    {callerScope : CutScopeId}
    {independentResult : Substitution}
    {representative : TreeSubstitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattenedRepresentative : TreeSubstitution}
    {installed : Subst}
    (activation :
      SpinedRepresentativeProductActivation prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        segmentReferenceRest segmentExecutableRest outer qterm bodyBarrier
        callerBarrier startCounter callerScope independentResult representative
        nextAlpha sourceCanonical flattenedRepresentative installed)
    (context : ActiveProductContext) :
    RawStep opened.session
      (ActiveProductContext.plug context
        (sourceProductFrontier callerScope opened finish
          segmentReferenceRest))
      [] .none opened.session
      (.running
        (ActiveProductContext.plug context
          (activatedSourceProduct callerScope opened finish branch branchTail
            independentResult segmentReferenceRest))) := by
  exact
    ActiveProductContext.liftProgress context activation.sourceStep
      (by simp [Trace.AnswerFree])

/-- A source/executable-control-aligned context packages the actual lifted
activation step together with global pre/post scope safety and the exact
source/executable caller-order identity.

The executable segment order is tied to the source frame order through
`SourceControlContextAgrees`; cursor-to-`Alt` ownership remains an explicit
subsequent resource-linearity obligation. -/
theorem
    _root_.PLeaTTa.PrologRepresentativeProductActivationBridge.SpinedRepresentativeProductActivation.sourceStep_throughAlignedContext
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {alpha support : List (LogicVar × String)}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {opened : OpenedCall} {pending : DemandDrivenCallStep.PendingCall}
    {finish : PreparedCursor} {branch : ClauseBranch}
    {branchTail : List ClauseBranch} {altTail : List PLeaTTa.Alt}
    {copied : PLeaTTa.Clause}
    {segmentReferenceRest : List PeTTaSpec.PrologCore.Goal}
    {segmentExecutableRest : List PLeaTTa.Goal}
    {outer : List ControlSegment}
    {qterm : Atom} {bodyBarrier callerBarrier startCounter : Nat}
    {callerScope outerScope : CutScopeId}
    {independentResult : Substitution}
    {representative : TreeSubstitution}
    {nextAlpha : List (LogicVar × String)}
    {sourceCanonical flattenedRepresentative : TreeSubstitution}
    {installed : Subst}
    {context : ActiveProductContext}
    (activation :
      SpinedRepresentativeProductActivation prog gt alpha support canonical
        referenceBase opened pending finish branch branchTail altTail copied
        segmentReferenceRest segmentExecutableRest outer qterm bodyBarrier
        callerBarrier startCounter callerScope independentResult representative
        nextAlpha sourceCanonical flattenedRepresentative installed)
    (alignment :
      SourceControlContextAgrees nextAlpha callerScope outer context
        outerScope) :
    RawStep opened.session
        (ActiveProductContext.plug context
          (sourceProductFrontier callerScope opened finish
            segmentReferenceRest))
        [] .none opened.session
        (.running
          (ActiveProductContext.plug context
            (activatedSourceProduct callerScope opened finish branch branchTail
              independentResult segmentReferenceRest))) ∧
      (ActiveProductContext.plug context
        (sourceProductFrontier callerScope opened finish
          segmentReferenceRest)).WellScoped outerScope ∧
      (ActiveProductContext.plug context
        (activatedSourceProduct callerScope opened finish branch branchTail
          independentResult segmentReferenceRest)).WellScoped outerScope ∧
      sourceCallerGoals context = flattenReferences outer := by
  have contextScoped := alignment.contextWellScoped
  exact
    ⟨activation.sourceStep_throughContext context,
      ActiveProductContext.plug_wellScoped contextScoped
        (sourceProductFrontier_wellScoped callerScope opened finish
          segmentReferenceRest),
      ActiveProductContext.plug_wellScoped contextScoped
        (activatedSourceProduct_wellScoped callerScope opened finish branch
          branchTail independentResult segmentReferenceRest),
      alignment.sourceCallerGoals_eq_flattenReferences⟩

end PLeaTTa.PrologSpinedSourceActivationBridge
