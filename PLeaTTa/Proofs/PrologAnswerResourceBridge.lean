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
import PLeaTTa.Proofs.PrologOrdinaryStepBridge
import PLeaTTa.Proofs.PrologProductResourceContextBridge

namespace PLeaTTa.PrologAnswerResourceBridge

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open PrologAnswerOriginBridge
open PrologControlSegmentSpineBridge
open PrologGoalAlpha
open PrologMguComposition
open PrologMguTopology
open PrologMguVariant
open PrologOrdinaryStepBridge
open PrologProductResourceContextBridge
open PrologStateBridge
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

/-- Control for one executable amb alternative.

Most alternatives retain ordinary normalized task agreement.  The sole
additional shape is the pinned empty-branch equation: the independent source
stores `value = output`, while `ambBranchGoals` schedules `output = value`.
The constructor records only that exact reversal and keeps the shared task
data separate.  It does not identify the two ordered MGU association lists;
their semantic variation is proved by the data-level successor theorem. -/
inductive TaskChoicePayloadAgrees
    (alpha support : List (LogicVar × String)) (barrier : Nat)
    (canonical : TreeSubstitution)
    (referenceBase current : Substitution) (runtime : Metta.Subst) :
    List PeTTaSpec.PrologCore.Goal -> List PLeaTTa.Goal -> Prop where
  | ordinary
      {references : List PeTTaSpec.PrologCore.Goal}
      {executables : List PLeaTTa.Goal}
      (payload :
        TaskPayloadAgrees alpha support barrier canonical referenceBase current
          runtime references executables) :
      TaskChoicePayloadAgrees alpha support barrier canonical referenceBase
        current runtime references executables
  | symmetricUnify
      {referenceValue referenceOutput : Term}
      {executableValue executableOutput : Metta.Atom}
      {referenceTail : List PeTTaSpec.PrologCore.Goal}
      {executableTail : List PLeaTTa.Goal}
      (data :
        TaskDataAgrees alpha support canonical referenceBase current runtime)
      (value : AlphaTermAgrees alpha referenceValue executableValue)
      (output : AlphaTermAgrees alpha referenceOutput executableOutput)
      (tail :
        NormalizedAlphaGoalsAgree alpha barrier referenceTail executableTail) :
      TaskChoicePayloadAgrees alpha support barrier canonical referenceBase
        current runtime
        (.unify referenceValue referenceOutput :: referenceTail)
        (.eq executableOutput executableValue :: executableTail)

namespace TaskChoicePayloadAgrees

/-- Both task-choice control spellings carry the same control-independent
substitution and valuation certificate. -/
theorem data
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution}
    {referenceBase current : Substitution} {runtime : Metta.Subst}
    {references : List PeTTaSpec.PrologCore.Goal}
    {executables : List PLeaTTa.Goal}
    (agreement :
      TaskChoicePayloadAgrees alpha support barrier canonical referenceBase
        current runtime references executables) :
    TaskDataAgrees alpha support canonical referenceBase current runtime := by
  cases agreement with
  | ordinary payload => exact payload.data
  | symmetricUnify data => exact data

/-- One ready task-choice equality preserves the actual source successor
even when the empty-amb lowering reverses its executable operands.

The ordinary case reuses strict normalized control.  The symmetric case
feeds the singleton-swap worklist equivalence to the certified data-level MGU
algorithm; the installed runtime binding is therefore a cumulative variant
of the source result rather than being asserted equal to its ordered list. -/
theorem afterUnifySuccessData
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution}
    {referenceBase current result : Substitution} {runtime : Metta.Subst}
    {left right : Term} {executableLeft executableRight : Metta.Atom}
    {referenceTail : List PeTTaSpec.PrologCore.Goal}
    {executableTail : List PLeaTTa.Goal}
    (agreement :
      TaskChoicePayloadAgrees alpha support barrier canonical referenceBase
        current runtime (.unify left right :: referenceTail)
        (.eq executableLeft executableRight :: executableTail))
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote right))
    (supportIncluded : ∀ pair, pair ∈ support → pair ∈ alpha)
    (runtimeAvoids : AlphaRuntimeNamesAvoid support runtime)
    (resolved : UnifyResolution current left right result) :
    ∃ sourceExtension : TreeSubstitution,
      ∃ installed : Metta.Subst,
        PLeaTTa.unifyB runtime executableLeft executableRight =
          some installed ∧
        TaskDataAgrees alpha support (sourceExtension ++ canonical)
          referenceBase result installed := by
  cases agreement with
  | ordinary payload =>
      cases payload.control with
      | cons head tail =>
          cases head with
          | unify leftAgreement rightAgreement =>
              exact payload.afterUnifySuccessData
                leftAgreement rightAgreement leftSupported rightSupported
                supportIncluded runtimeAvoids resolved
  | symmetricUnify data valueAgreement outputAgreement tail =>
      exact data.afterUnifySuccessData_of_equivalent
        (sourceLeft := left) (sourceRight := right)
        (runtimeLeft := right) (runtimeRight := left)
        (PrologSequentialMgu.singleton_swap_unificationEquivalent
          (Term.denote left) (Term.denote right))
        outputAgreement valueAgreement rightSupported leftSupported
        supportIncluded runtimeAvoids resolved

/-- A source clash forces failure of the actual executable branch equality,
including the empty-literal lowering which reverses its operands.

The ordinary case reuses identity-equation failure reflection.  The
`symmetricUnify` case constructs strict readings for `right = left`, then
transports runtime success back through singleton-swap equivalence before
contradicting the source clash.  No ordered residual substitution or operand
orientation is identified. -/
theorem unifyB_eq_none_of_no_resolution
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution}
    {referenceBase current : Substitution} {runtime : Metta.Subst}
    {left right : Term} {executableLeft executableRight : Metta.Atom}
    {referenceTail : List PeTTaSpec.PrologCore.Goal}
    {executableTail : List PLeaTTa.Goal}
    (agreement :
      TaskChoicePayloadAgrees alpha support barrier canonical referenceBase
        current runtime (.unify left right :: referenceTail)
        (.eq executableLeft executableRight :: executableTail))
    (leftSupported :
      AlphaTreeSupported alpha support (Term.denote left))
    (rightSupported :
      AlphaTreeSupported alpha support (Term.denote right))
    (aliasSafe : CurrentUnifyOperandsAliasSafe current left right)
    (clash : ¬ ∃ result, UnifyResolution current left right result) :
    PLeaTTa.unifyB runtime executableLeft executableRight = none := by
  cases agreement with
  | ordinary payload =>
      cases payload.control with
      | cons head tail =>
          cases head with
          | unify leftAgreement rightAgreement =>
              have strict :=
                payload.strictUnifyOperands_of_currentAliasSafe
                  leftAgreement rightAgreement leftSupported rightSupported
                  aliasSafe
              exact payload.unifyB_eq_none_of_no_resolution strict clash
  | symmetricUnify data valueAgreement outputAgreement tail =>
      have swappedSafe :
          CurrentUnifyOperandsAliasSafe current right left :=
        ⟨aliasSafe.2, aliasSafe.1⟩
      have strict :=
        data.strictUnifyOperands_of_currentAliasSafe
          outputAgreement valueAgreement rightSupported leftSupported
          swappedSafe
      exact
        data.unifyB_eq_none_of_no_resolution_of_equivalent
          (sourceLeft := left) (sourceRight := right)
          (runtimeLeft := right) (runtimeRight := left)
          (PrologSequentialMgu.singleton_swap_unificationEquivalent
            (Term.denote left) (Term.denote right))
          strict clash

end TaskChoicePayloadAgrees

/-- Ordered source-task provenance for the ordinary alternatives emitted by
one executable `amb` step.

The relation is deliberately indexed by the source scope and binding, the
executable barrier and binding, and one common canonical valuation.  Hence a
consumer cannot pair branches from different activations merely because their
goal lists happen to agree.  `last` and `more` mirror `Search.disjoin`
exactly: every source leaf is a nonempty task, every executable leaf is one
ordinary `Alt.br`, and branch order and multiplicity are structural indices.

No retained cursor occurs here.  These alternatives are source tasks created
by a disjunction, not unopened clause occurrences.  In particular, the type
cannot carry an answer, effect, cut marker, or cursor resource supplied by an
oracle. -/
inductive TaskChoiceAlternativeRegionAgrees
    (alpha support : List (LogicVar × String))
    (scope : CutScopeId) (barrier : Nat)
    (canonical : TreeSubstitution)
    (referenceBase current : Substitution) (runtime : Metta.Subst) :
    Search -> List PLeaTTa.Alt -> Prop where
  | last (referenceHead : PeTTaSpec.PrologCore.Goal)
      (referenceTail : List PeTTaSpec.PrologCore.Goal)
      (executableGoals : List PLeaTTa.Goal)
      (payload :
        TaskChoicePayloadAgrees alpha support barrier canonical referenceBase current
          runtime (referenceHead :: referenceTail) executableGoals) :
      TaskChoiceAlternativeRegionAgrees alpha support scope barrier canonical
        referenceBase current runtime
        (.task scope (referenceHead :: referenceTail) current)
        [.br executableGoals runtime]
  | more (referenceHead : PeTTaSpec.PrologCore.Goal)
      (referenceTail : List PeTTaSpec.PrologCore.Goal)
      (executableGoals : List PLeaTTa.Goal)
      (right : Search) (tailAlts : List PLeaTTa.Alt)
      (payload :
        TaskChoicePayloadAgrees alpha support barrier canonical referenceBase current
          runtime (referenceHead :: referenceTail) executableGoals)
      (tail :
        TaskChoiceAlternativeRegionAgrees alpha support scope barrier canonical
          referenceBase current runtime right tailAlts) :
      TaskChoiceAlternativeRegionAgrees alpha support scope barrier canonical
        referenceBase current runtime
        (.choice scope (.task scope (referenceHead :: referenceTail) current)
          right)
        (.br executableGoals runtime :: tailAlts)

/-- Ordered branch payloads before their concrete source-choice tree is
formed.  Every branch shares the same source continuation, source/runtime
bindings, canonical valuation, and executable barrier.  This is the exact
list-shaped interface consumed by an executable `amb` compiler equation. -/
inductive OrderedTaskChoicePayloadsAgree
    (alpha support : List (LogicVar × String))
    (barrier : Nat) (canonical : TreeSubstitution)
    (referenceBase current : Substitution) (runtime : Metta.Subst)
    (referenceTail : List PeTTaSpec.PrologCore.Goal) :
    List PeTTaSpec.PrologCore.Goal -> List (List PLeaTTa.Goal) -> Prop where
  | nil :
      OrderedTaskChoicePayloadsAgree alpha support barrier canonical
        referenceBase current runtime referenceTail [] []
  | cons (referenceHead : PeTTaSpec.PrologCore.Goal)
      (executableGoals : List PLeaTTa.Goal)
      {referenceHeads : List PeTTaSpec.PrologCore.Goal}
      {executableBranches : List (List PLeaTTa.Goal)}
      (payload :
        TaskChoicePayloadAgrees alpha support barrier canonical referenceBase current
          runtime (referenceHead :: referenceTail) executableGoals)
      (tail :
        OrderedTaskChoicePayloadsAgree alpha support barrier canonical
          referenceBase current runtime referenceTail referenceHeads
          executableBranches) :
      OrderedTaskChoicePayloadsAgree alpha support barrier canonical
        referenceBase current runtime referenceTail
        (referenceHead :: referenceHeads)
        (executableGoals :: executableBranches)

namespace AlphaLiteralAmbBranchesAgree

/-- Literal amb branch agreement elaborates to the exact ordered executable
alternative payloads consumed by `Step.amb`.

Every source branch shares `referenceTail`; every executable branch shares
`executableTail`; and `ambBranchGoals_empty` contributes exactly the reversed
`output = value` equality recorded by `TaskChoicePayloadAgrees.symmetricUnify`.
List induction preserves branch order and duplicate multiplicity. -/
theorem toOrderedTaskChoicePayloads
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution}
    {referenceBase current : Substitution} {runtime : Metta.Subst}
    {referenceOutput : Term} {executableOutput : Metta.Atom}
    {referenceBranches : List PeTTaSpec.PrologCore.Goal}
    {executableBranches : List (Metta.Atom × List PLeaTTa.Goal)}
    (branches :
      AlphaLiteralAmbBranchesAgree alpha referenceOutput executableOutput
        referenceBranches executableBranches)
    (data :
      TaskDataAgrees alpha support canonical referenceBase current runtime)
    (referenceTail : List PeTTaSpec.PrologCore.Goal)
    (executableTail : List PLeaTTa.Goal)
    (tailControl :
      NormalizedAlphaGoalsAgree alpha barrier referenceTail executableTail) :
    OrderedTaskChoicePayloadsAgree alpha support barrier canonical
      referenceBase current runtime referenceTail referenceBranches
      (executableBranches.map fun branch =>
        PLeaTTa.ambBranchGoals executableOutput branch ++ executableTail) := by
  induction branches with
  | nil output =>
      exact .nil
  | @cons referenceValue executableValue referenceBranches
      executableBranches value output tail inductionHypothesis =>
      simpa using
        OrderedTaskChoicePayloadsAgree.cons
          (.unify referenceValue referenceOutput)
          (PLeaTTa.ambBranchGoals executableOutput (executableValue, []) ++
            executableTail)
          (by simpa using
            (TaskChoicePayloadAgrees.symmetricUnify data value output
              tailControl))
          inductionHypothesis

end AlphaLiteralAmbBranchesAgree

namespace OrderedTaskChoicePayloadsAgree

/-- Nonempty ordered branch payloads elaborate into the literal
`Search.disjoin` tree and same-order executable alternative list. -/
theorem toTaskChoiceAlternativeRegion
    {alpha support : List (LogicVar × String)}
    {scope : CutScopeId} {barrier : Nat}
    {canonical : TreeSubstitution}
    {referenceBase current : Substitution} {runtime : Metta.Subst}
    {referenceTail : List PeTTaSpec.PrologCore.Goal}
    {referenceHeads : List PeTTaSpec.PrologCore.Goal}
    {executableBranches : List (List PLeaTTa.Goal)}
    (agreement :
      OrderedTaskChoicePayloadsAgree alpha support barrier canonical
        referenceBase current runtime referenceTail referenceHeads
        executableBranches)
    (nonempty : referenceHeads ≠ []) :
    TaskChoiceAlternativeRegionAgrees alpha support scope barrier canonical
      referenceBase current runtime
      (Search.disjoin scope referenceHeads referenceTail current)
      (executableBranches.map (fun goals => PLeaTTa.Alt.br goals runtime)) := by
  induction agreement with
  | nil => contradiction
  | @cons referenceHead executableGoals referenceHeads executableBranches
      payload tail inductionHypothesis =>
      cases referenceHeads with
      | nil =>
          cases tail
          simpa [Search.disjoin] using
            (TaskChoiceAlternativeRegionAgrees.last referenceHead referenceTail
              executableGoals payload)
      | cons nextReference remaining =>
          simpa [Search.disjoin] using
            (TaskChoiceAlternativeRegionAgrees.more referenceHead referenceTail
              executableGoals
              (Search.disjoin scope (nextReference :: remaining) referenceTail
                current)
              (executableBranches.map
                (fun goals => PLeaTTa.Alt.br goals runtime))
              payload (inductionHypothesis (by simp)))

end OrderedTaskChoicePayloadsAgree

namespace TaskChoiceAlternativeRegionAgrees

/-- Every task-choice region begins with a literal ordinary branch.  The
head and tail are recovered from indexed provenance rather than by inspecting
an untyped alternative list. -/
theorem alts_head_exact
    {alpha support : List (LogicVar × String)}
    {scope : CutScopeId} {barrier : Nat}
    {canonical : TreeSubstitution}
    {referenceBase current : Substitution} {runtime : Metta.Subst}
    {source : Search} {alts : List PLeaTTa.Alt}
    (agreement :
      TaskChoiceAlternativeRegionAgrees alpha support scope barrier canonical
        referenceBase current runtime source alts) :
    ∃ goals : List PLeaTTa.Goal, ∃ tail : List PLeaTTa.Alt,
      alts = .br goals runtime :: tail := by
  cases agreement with
  | last _ _ goals _ => exact ⟨goals, [], rfl⟩
  | more _ _ goals _ tail _ _ => exact ⟨goals, tail, rfl⟩

/-- Task-choice banks contain ordinary branches only; source disjunctions do
not mint anonymous predicate-cut markers. -/
theorem barrierCount_zero
    {alpha support : List (LogicVar × String)}
    {scope : CutScopeId} {barrier : Nat}
    {canonical : TreeSubstitution}
    {referenceBase current : Substitution} {runtime : Metta.Subst}
    {source : Search} {alts : List PLeaTTa.Alt}
    (agreement :
      TaskChoiceAlternativeRegionAgrees alpha support scope barrier canonical
        referenceBase current runtime source alts) :
    PLeaTTa.barrierCount alts = 0 := by
  induction agreement with
  | last => simp
  | more _ _ _ _ _ _ _ inductionHypothesis => simp [inductionHypothesis]

end TaskChoiceAlternativeRegionAgrees

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
        (original cursor : PeTTaSpec.PrologCore.Resolver.PreparedCursor)
        (position : Nat)
        (positioned : CallScopedCursorPosition original cursor position)
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
    | taskChoices (support : List (LogicVar × String))
        (scope : CutScopeId) (barrier : Nat)
        (canonical : TreeSubstitution)
        (referenceBase current : Substitution) (runtime : Metta.Subst)
        (right : Search) (goals : List PLeaTTa.Goal)
        (tail : List PLeaTTa.Alt)
        (choices :
          TaskChoiceAlternativeRegionAgrees alpha support scope barrier
            canonical referenceBase current runtime right
            (.br goals runtime :: tail)) :
        RightAlternativeRegionAgrees alpha right []
          (.br goals runtime :: tail)

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

namespace OrderedTaskChoicePayloadsAgree

/-- The same ordered payload evidence packages directly as a resource-zipper
right region.  It owns no cursor resource and its executable bank is the
literal same-order branch map. -/
theorem toRightAlternativeRegion
    {alpha support : List (LogicVar × String)}
    {scope : CutScopeId} {barrier : Nat}
    {canonical : TreeSubstitution}
    {referenceBase current : Substitution} {runtime : Metta.Subst}
    {referenceTail : List PeTTaSpec.PrologCore.Goal}
    {referenceHeads : List PeTTaSpec.PrologCore.Goal}
    {executableBranches : List (List PLeaTTa.Goal)}
    (agreement :
      OrderedTaskChoicePayloadsAgree alpha support barrier canonical
        referenceBase current runtime referenceTail referenceHeads
        executableBranches)
    (nonempty : referenceHeads ≠ []) :
    RightAlternativeRegionAgrees alpha
      (Search.disjoin scope referenceHeads referenceTail current) []
      (executableBranches.map (fun goals => PLeaTTa.Alt.br goals runtime)) := by
  cases agreement with
  | nil => contradiction
  | @cons referenceHead executableGoals referenceHeads executableBranches
      payload tail =>
      exact
        .taskChoices support scope barrier canonical referenceBase current
          runtime _ executableGoals
          (executableBranches.map (fun goals => PLeaTTa.Alt.br goals runtime))
          ((OrderedTaskChoicePayloadsAgree.cons referenceHead executableGoals
              payload tail).toTaskChoiceAlternativeRegion (by simp))

end OrderedTaskChoicePayloadsAgree

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
  | clauses _ _ _ _ _ _ ownership =>
      exact ⟨rfl, ownership⟩

/-- A clause region retains the immutable call-start cursor and the absolute
position of its current suffix head.  The position is source-derived and
call-scoped; it is not reconstructed from the executable alternative counter,
which omits conservatively rejected occurrences. -/
theorem clauses_position_exact
    {alpha : List (LogicVar × String)} {scope : CutScopeId}
    {cursor : PeTTaSpec.PrologCore.Resolver.PreparedCursor}
    {resource : RetainedAlternativeSegment} {segment : List PLeaTTa.Alt}
    (agreement :
      RightAlternativeRegionAgrees alpha (.clauses scope cursor)
        [resource] segment) :
    exists original position,
      CallScopedCursorPosition original cursor position /\
        segment = resource.alts /\
        resource.Owns alpha cursor := by
  cases agreement with
  | clauses _ original _ position positioned _ ownership =>
      exact ⟨original, position, positioned, rfl, ownership⟩

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
  | clauses _ _ _ _ _ resource ownership =>
      exact ⟨resource, rfl, rfl, ownership⟩
  | taskChoices => contradiction

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
  | taskChoices => contradiction

/-- A region with no retained cursor resources still owns a genuine ordinary
alternative.  Thus task choices cannot be laundered into a resource-free,
branch-free phantom region. -/
theorem segment_ne_nil_of_resources_nil
    {alpha : List (LogicVar × String)}
    {right : Search} {resources : List RetainedAlternativeSegment}
    {segment : List PLeaTTa.Alt}
    (agreement : RightAlternativeRegionAgrees alpha right resources segment)
    (resourcesEmpty : resources = []) :
    segment ≠ [] := by
  cases agreement with
  | clauses => simp at resourcesEmpty
  | scheduled _ _ _ _ nonempty _ => exact (nonempty resourcesEmpty).elim
  | taskChoices => simp

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
    | clauses _ _ _ _ _ resource ownership =>
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
    | taskChoices =>
        intro candidate member
        simp at member

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
    (by intros; trivial)
    (by intros; trivial)
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
theorem active_call_exact_at
    {alpha : List (LogicVar × String)}
    (predicateScope : CutScopeId) (bindings : Substitution)
    (original : PeTTaSpec.PrologCore.Resolver.PreparedCursor)
    (cursor : PeTTaSpec.PrologCore.Resolver.PreparedCursor)
    (position : Nat)
    (positioned : CallScopedCursorPosition original cursor position)
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
  · exact RightAlternativeRegionAgrees.clauses _ original cursor position
      positioned resource ownership

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
      (active_call_exact_at predicateScope bindings cursor cursor 0
        (CallScopedCursorPosition.refl cursor) resource [] [] ownership)
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
    active_call_exact_at innerPredicateScope bindings innerCursor innerCursor 0
      (CallScopedCursorPosition.refl innerCursor) innerResource [outerResource]
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
`PreparedCallIdentity` below discharges that premise for distinct exhausted
calls; nonempty duplicate occurrences remain a deliberately separate case. -/
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

private def exhaustedIdentityResource
    (predicate : String) : RetainedAlternativeSegment :=
  { callIdentity :=
      PreparedCallIdentity.ofCursor (exhaustedIdentityCursor predicate)
    argsv := []
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
    (exhaustedIdentityResource predicate).Owns
      ([] : List (LogicVar × String))
      (exhaustedIdentityCursor predicate) := by
  refine ⟨rfl, [], ?_, ?_, rfl, .nil, ?_, ?_⟩
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

/-- The repaired exhausted-resource certificate discriminates distinct call
occurrences even though both executable alternative banks are empty.  This is
the concrete anti-vacuity counterpart of `Owns.exhausted_cursor_injective`:
the formerly admitted predicate substitution is now rejected. -/
theorem exhausted_resource_wrong_predicate_rejected :
    let leftCursor := exhaustedIdentityCursor "owned-left"
    let rightCursor := exhaustedIdentityCursor "owned-right"
    let resource := exhaustedIdentityResource "owned-left"
    leftCursor ≠ rightCursor ∧
      resource.alts = [] ∧
      resource.Owns [] leftCursor ∧
      ¬ resource.Owns [] rightCursor := by
  dsimp only
  have cursorsDifferent :
      exhaustedIdentityCursor "owned-left" ≠
        exhaustedIdentityCursor "owned-right" := by
    intro cursorsEq
    have predicatesEq := congrArg
      PeTTaSpec.PrologCore.Resolver.PreparedCursor.predicate cursorsEq
    simp [exhaustedIdentityCursor] at predicatesEq
  have leftOwnership := exhaustedIdentityResource_owns "owned-left"
  refine ⟨cursorsDifferent, rfl, leftOwnership, ?_⟩
  intro rightOwnership
  exact cursorsDifferent
    (RetainedAlternativeSegment.Owns.exhausted_cursor_injective
      leftOwnership rightOwnership (by rfl) (by rfl))

private def duplicateOccurrenceReference
    (id : ClauseId) : VersionedClause :=
  { id := id
    clause :=
      { predicate := "duplicate-occurrence"
        arguments := [.integer 1]
        body := [] }
    created := 0 }

private def duplicateOccurrenceExecutable : PLeaTTa.Clause :=
  { params := []
    result := .gnd (.int 1)
    body := [] }

private def duplicateOccurrenceBranch (id : ClauseId) : ClauseBranch :=
  PrologCallEntryBridge.preparedBranchOf 0 [.integer 1] [] 0
    (duplicateOccurrenceReference id)

private def duplicateOccurrenceCursor (id : ClauseId) : PreparedCursor :=
  { callGeneration := 0
    predicate := "duplicate-occurrence"
    arguments := [.integer 1]
    bindings := []
    reservationStart := 0
    remaining := [duplicateOccurrenceBranch id]
    reservedUntil := (duplicateOccurrenceBranch id).nextFresh }

private def duplicateOccurrenceResource : RetainedAlternativeSegment :=
  { callIdentity :=
      PreparedCallIdentity.ofCursor (duplicateOccurrenceCursor 0)
    argsv := []
    args := []
    res := .gnd (.int 1)
    rest := []
    binding := []
    qterm := .sym "duplicate-query"
    barrier := 0
    counter := 0
    alts :=
      [PrologActivationMacro.resolutionAlt [] [] (.gnd (.int 1)) [] []
        (.sym "duplicate-query") 0 0 duplicateOccurrenceExecutable]
    finalCounter := 1 }

private theorem duplicateOccurrenceCandidateAgreement
    (id : ClauseId) :
    PrologCallEntryBridge.CandidateClauseAgrees "duplicate-occurrence"
      (duplicateOccurrenceReference id) duplicateOccurrenceExecutable := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := .nil
      support := ?_ }
  · exact ⟨[], .integer 1, rfl, .nil, .integer 1⟩
  · intro name
    simp [duplicateOccurrenceReference, duplicateOccurrenceExecutable,
      LocalClause.variables, PLeaTTa.resolutionClauseVars,
      Metta.Atom.vars, PLeaTTa.specializationGoalsVars,
      Resolver.termsVariables, Resolver.termVariables, Resolver.goalsVariables]

private theorem duplicateOccurrenceSupported (id : ClauseId) :
    PrologCallPayloadBridge.SupportedPreparedCandidateAgrees 0
      "duplicate-occurrence" [.integer 1] []
      (duplicateOccurrenceBranch id) duplicateOccurrenceExecutable := by
  refine .intro (duplicateOccurrenceReference id) 0
    duplicateOccurrenceExecutable (duplicateOccurrenceCandidateAgreement id)
    ?_ ?_
  · intro left right leftMember rightMember
    simp [duplicateOccurrenceReference, LocalClause.variables,
      Resolver.termsVariables, Resolver.termVariables,
      Resolver.goalsVariables] at leftMember
  · change
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] []
        (duplicateOccurrenceCandidateAgreement id).body
    have proofEq :
        (duplicateOccurrenceCandidateAgreement id).body =
          (CompilerAdequacy.GoalsAgree.nil :
            CompilerAdequacy.GoalsAgree [] []) :=
      Subsingleton.elim _ _
    rw [proofEq]
    exact .nil

private theorem duplicateOccurrenceWellFormed (id : ClauseId) :
    (duplicateOccurrenceCursor id).WellFormed := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      .cons 0 (duplicateOccurrenceBranch id) []
        (duplicateOccurrenceBranch id).nextFresh
        (by
          change
            0 ≤
              ((duplicateOccurrenceReference id).clause.freshCopy 0).firstFresh
          exact
            (duplicateOccurrenceReference id).clause.freshCopy_first_ge_seed 0)
        (by
          change
            ((duplicateOccurrenceReference id).clause.freshCopy 0).firstFresh ≤
              ((duplicateOccurrenceReference id).clause.freshCopy 0).nextFresh
          rw [LocalClause.freshCopy_next]
          omega)
        (.nil (duplicateOccurrenceBranch id).nextFresh)
  · intro index member
    simp [duplicateOccurrenceCursor, Resolver.termsVariables,
      Resolver.termVariables, Resolver.substitutionVariables] at member
  · intro branch member
    simp [duplicateOccurrenceCursor] at member
    subst branch
    rfl
  · intro branch member
    simp [duplicateOccurrenceCursor] at member
    subst branch
    intro source index targetMember
    simpa [duplicateOccurrenceBranch,
      PrologCallEntryBridge.preparedBranchOf] using
      (duplicateOccurrenceReference id).clause.freshCopy_target_range 0
        targetMember

private theorem duplicateOccurrenceQuery (id : ClauseId) :
    PrologRecursiveCallPayloadBridge.RepresentativeNormalizedCallAgrees []
      (duplicateOccurrenceCursor id) [] (.gnd (.int 1)) := by
  apply
    PrologRecursiveCallPayloadBridge.NormalizedCallAgrees.representative
  constructor
  simpa [duplicateOccurrenceCursor] using
    (AlphaTermsAgree.cons
      (AlphaTermAgrees.integer (alpha := []) 1)
      AlphaTermsAgree.nil)

private theorem duplicateOccurrenceResource_owns (id : ClauseId) :
    duplicateOccurrenceResource.Owns
      ([] : List (LogicVar × String)) (duplicateOccurrenceCursor id) := by
  refine
    ⟨rfl, [duplicateOccurrenceExecutable],
      duplicateOccurrenceWellFormed id, ?_, rfl,
      .cons (duplicateOccurrenceSupported id) .nil, ?_, ?_⟩
  · simpa [duplicateOccurrenceResource] using duplicateOccurrenceQuery id
  · intro clause member
    simp [duplicateOccurrenceExecutable] at member
    subst clause
    rfl
  · simpa [duplicateOccurrenceResource] using
      (PrologActivationMacro.ResolutionScan.retained
        duplicateOccurrenceExecutable [] 0 1 []
        (by
          have retained :
              PrologActivationMacro.resolutionClauseRetained []
                  (.gnd (.int 1)) duplicateOccurrenceExecutable = true := by
            rfl
          simpa using retained)
        (PrologActivationMacro.ResolutionScan.nil 1))

/-- Exact call-level identity intentionally does not identify a live duplicate
source occurrence.  Two clauses with different stable `ClauseId`s but equal
source content own the same executable alternative bank.  Thus the repaired
exhausted theorem must not be generalized to arbitrary cursors without an
activation/occurrence key or an explicit observational quotient. -/
theorem nonempty_duplicate_occurrence_ownership_not_cursor_injective :
    let leftCursor := duplicateOccurrenceCursor 0
    let rightCursor := duplicateOccurrenceCursor 1
    let resource := duplicateOccurrenceResource
    leftCursor ≠ rightCursor ∧
      leftCursor.remaining ≠ [] ∧
      rightCursor.remaining ≠ [] ∧
      resource.Owns [] leftCursor ∧
      resource.Owns [] rightCursor := by
  dsimp only
  have cursorsDifferent :
      duplicateOccurrenceCursor 0 ≠ duplicateOccurrenceCursor 1 := by
    intro cursorsEq
    have idsEq := congrArg
      (fun cursor : PreparedCursor =>
        cursor.remaining.map ClauseBranch.sourceId)
      cursorsEq
    simp [duplicateOccurrenceCursor, duplicateOccurrenceBranch,
      PrologCallEntryBridge.preparedBranchOf,
      duplicateOccurrenceReference] at idsEq
  exact
    ⟨cursorsDifferent, by simp [duplicateOccurrenceCursor],
      by simp [duplicateOccurrenceCursor],
      duplicateOccurrenceResource_owns 0,
      duplicateOccurrenceResource_owns 1⟩

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

private def taskChoiceEmptyRuntimeTopological :
    PLeaTTa.SubstTopological [] := by
  refine
    { order := []
      nodup := by simp
      domain := ?_
      decreases := ?_ }
  · intro name
    simp [Metta.Subst.lookup]
  · intro source value dependency lookup
    simp [Metta.Subst.lookup] at lookup

private theorem taskChoiceEmptyData :
    TaskDataAgrees [] [] [] [] [] [] := by
  refine
    { alphaShared := ?_
      canonicalWellFormed := TreeSubstitution.wellFormed_nil
      bindingShape := rfl
      valuation := ?_ }
  · constructor <;> intro <;> simp_all
  · refine
      ⟨[], TreeSubstitutionVariants.refl [],
        TreeSubstitutionTopological.nil, ?_,
        ⟨taskChoiceEmptyRuntimeTopological⟩, ?_⟩
    · intro entry member
      simp at member
    · intro identity name member
      simp at member

private theorem taskChoiceTruthPayload (barrier : Nat) :
    TaskPayloadAgrees [] [] barrier [] [] [] [] [.truth] [] :=
  taskChoiceEmptyData.withControl (.truth .nil)

private theorem taskChoiceUnifyOnePayload (barrier : Nat) :
    TaskPayloadAgrees [] [] barrier [] [] [] []
      [.unify (.integer 1) (.integer 1)]
      [.eq (.gnd (.int 1)) (.gnd (.int 1))] := by
  apply taskChoiceEmptyData.withControl
  exact
    .cons
      (.unify (AlphaTermAgrees.integer (alpha := []) 1)
        (AlphaTermAgrees.integer (alpha := []) 1))
      .nil

private theorem threeTaskChoicePayloads :
    OrderedTaskChoicePayloadsAgree [] [] 0 [] [] [] [] []
      [.truth, .unify (.integer 1) (.integer 1),
        .unify (.integer 1) (.integer 1)]
      [[], [.eq (.gnd (.int 1)) (.gnd (.int 1))],
        [.eq (.gnd (.int 1)) (.gnd (.int 1))]] :=
  .cons .truth [] (.ordinary (taskChoiceTruthPayload 0))
    (.cons (.unify (.integer 1) (.integer 1))
      [.eq (.gnd (.int 1)) (.gnd (.int 1))]
      (.ordinary (taskChoiceUnifyOnePayload 0))
      (.cons (.unify (.integer 1) (.integer 1))
        [.eq (.gnd (.int 1)) (.gnd (.int 1))]
        (.ordinary (taskChoiceUnifyOnePayload 0)) .nil))

/-- A three-way source disjunction owns exactly three same-order ordinary
alternatives and no cursor resource or cut marker.  The last two branches are
duplicates, so the witness pins multiplicity rather than merely set content. -/
theorem three_branch_task_choice_region_is_inhabited :
    let referenceBranches : List PeTTaSpec.PrologCore.Goal :=
      [.truth, .unify (.integer 1) (.integer 1),
        .unify (.integer 1) (.integer 1)]
    let equality : PLeaTTa.Goal :=
      .eq (.gnd (.int 1)) (.gnd (.int 1))
    let executableAlts : List PLeaTTa.Alt :=
      [.br [] [], .br [equality] [], .br [equality] []]
    (exists _region :
        RightAlternativeRegionAgrees []
          (Search.disjoin 7 referenceBranches [] []) [] executableAlts,
      executableAlts.length = 3 /\
        PLeaTTa.barrierCount executableAlts = 0) := by
  dsimp only
  have region := threeTaskChoicePayloads.toRightAlternativeRegion
    (scope := 7) (by simp)
  exact ⟨by simpa using region, by simp, by simp⟩

/-- Swapping the first two executable alternatives while retaining the same
source choice tree is rejected.  This is an observation-level order guard,
not an inequality between internal proof objects. -/
theorem swapped_task_choice_order_rejected :
    let referenceBranches : List PeTTaSpec.PrologCore.Goal :=
      [.truth, .unify (.integer 1) (.integer 1),
        .unify (.integer 1) (.integer 1)]
    let equality : PLeaTTa.Goal :=
      .eq (.gnd (.int 1)) (.gnd (.int 1))
    ¬ RightAlternativeRegionAgrees []
      (Search.disjoin 7 referenceBranches [] []) []
      [.br [equality] [], .br [] [], .br [equality] []] := by
  dsimp only
  intro agreement
  cases agreement with
  | taskChoices _ _ _ _ _ _ _ _ _ _ choices =>
      cases choices with
      | more _ _ _ _ _ payload _ =>
          cases payload with
          | ordinary ordinary =>
              cases ordinary.control with
              | truth tail => cases tail
              | cons head tail => cases head

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
