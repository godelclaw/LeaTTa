-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologFindallClosedBankBridge
Purpose: Reachable closed alternative-bank certificates for local findall
Trusted boundary: none
Main exports: ClosedLiteralFindallReadyRelates,
  ClosedLiteralDisjunctionActivationAgrees,
  ClosedAnswerOriginResourceAgrees,
  contextual_entry_produces_closed_ready,
  ClosedLiteralFindallReadyRelates.schedule,
  ClosedAnswerOriginResourceAgrees.classifyPull
-/
import PLeaTTa.Proofs.PrologFindallDisjunctionBridge
import PLeaTTa.Proofs.PrologAnswerPullClassificationBridge

namespace PLeaTTa.PrologFindallClosedBankBridge

open Metta (Atom Subst GroundingTable)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PrologActiveControlContextBridge
open PrologAnswerOriginBridge
open PrologAnswerPullClassificationBridge
open PrologAnswerResourceBridge
open PrologDisjunctionStepBridge
open PrologFindallDisjunctionBridge
open PrologFindallEntryBridge
open PrologGoalAlpha
open PrologProductResourceContextBridge
open PrologStateBridge
open DemandDrivenStep

/-!
# Closed local `findall/3` generator banks

The generic disjunction scheduler preserves an arbitrary older executable
alternative suffix.  That generality is necessary for ordinary predicate
calls, but a real `findall/3` generator begins in `subConfOf` with `alts := []`.
This module records the reachable specialization structurally:

* entry couples the independently typed ready payload to the exact empty bank;
* one real source/fine disjunction step returns a
  `TaskChoiceActivationAgrees` indexed by the literal older suffix `[]`;
* an answer origin whose older suffix is `[]` has only local-live or terminal
  pull outcomes.  The generic `baseLive` constructor is uninhabited there.

This is an entry-and-one-step preservation checkpoint, not yet a global
invariant over every generator transition.
-/

/-- A ready literal-disjunction focus whose complete executable alternative
bank is closed.  Keeping the ready payload and the empty-bank equation in one
certificate prevents an unrelated empty state from being paired with the
compiler/source agreement. -/
structure ClosedLiteralFindallReadyRelates
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String)) (barrier : Nat)
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (session : Session) (current : Substitution)
    (referenceOutput : Term)
    (referenceBranches referenceTail : List PeTTaSpec.PrologCore.Goal)
    (runtime : Metta.Subst) (executableOutput : Metta.Atom)
    (executableBranches : List (Metta.Atom × List PLeaTTa.Goal))
    (executableTail : List PLeaTTa.Goal)
    (state : OpenConf) : Prop where
  ready :
    ReadyLiteralDisjunctionRelates freshFrontier alpha support barrier
      canonical referenceBase session current referenceOutput
      referenceBranches referenceTail runtime executableOutput
      executableBranches executableTail state
  bank_empty : state.control.alts = []

/-- Post-scheduling source/executable agreement specialized to a closed
generator bank.  The empty older suffix is an index of the original structural
activation relation, so a caller cannot later reinterpret newly installed
literal alternatives as being followed by an arbitrary caller base. -/
structure ClosedLiteralDisjunctionActivationAgrees
    (alpha support : List (LogicVar × String))
    (scope : CutScopeId) (barrier : Nat)
    (canonical : TreeSubstitution)
    (referenceBase current : Substitution) (runtime : Metta.Subst)
    (source : Search)
    (executableCurrent : Option (List PLeaTTa.Goal × Metta.Subst))
    (executableAlts : List PLeaTTa.Alt) : Prop where
  activation :
    TaskChoiceActivationAgrees alpha support scope barrier canonical
      referenceBase current runtime [] source executableCurrent executableAlts

namespace ClosedLiteralDisjunctionActivationAgrees

/-- A closed literal activation has exactly the two scheduler shapes: the
last source branch leaves the bank empty, while any residual source choice
installs a real ordinary executable branch at the head.  In particular the
closed certificate cannot be witnessed solely by carrying an arbitrary older
suffix through the scheduler. -/
theorem bank_shape
    {alpha support : List (LogicVar × String)}
    {scope : CutScopeId} {barrier : Nat}
    {canonical : TreeSubstitution}
    {referenceBase current : Substitution} {runtime : Metta.Subst}
    {source : Search}
    {executableCurrent : Option (List PLeaTTa.Goal × Metta.Subst)}
    {executableAlts : List PLeaTTa.Alt}
    (closed :
      ClosedLiteralDisjunctionActivationAgrees alpha support scope barrier
        canonical referenceBase current runtime source executableCurrent
        executableAlts) :
    executableAlts = [] ∨
      ∃ goals : List PLeaTTa.Goal, ∃ tail : List PLeaTTa.Alt,
        executableAlts = .br goals runtime :: tail := by
  cases closed.activation with
  | last => exact .inl rfl
  | more _ _ _ _ _ _ tail =>
      rcases tail.alts_head_exact with ⟨goals, rest, exactAlts⟩
      exact .inr ⟨goals, rest, by simpa using exactAlts⟩

end ClosedLiteralDisjunctionActivationAgrees

/-- Real contextual `findall/3` entry produces the closed ready certificate.

The proof uses the exact state already carried by the entry relation; the
empty bank is the executable `enterFindall` equation, not a reachability
assumption supplied by the caller.

[SPEC translator.pl:112-116; metta.pl:251-256; SWI:findall/3] -/
theorem contextual_entry_produces_closed_ready
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {context : ActiveControlContext} {session : Session}
    {callerScope : CutScopeId}
    {referenceTemplate referenceAmbOutput referenceResult : Term}
    {referenceBranches : List PeTTaSpec.PrologCore.Goal}
    {referenceRest : List PeTTaSpec.PrologCore.Goal}
    {referenceBindings : Substitution}
    {executableTemplate executableAmbOutput executableResult : Metta.Atom}
    {executableBranches : List (Metta.Atom × List PLeaTTa.Goal)}
    {executableTail executableRest : List PLeaTTa.Goal}
    {executableBinding : Metta.Subst} {before : OpenConf}
    (entry :
      ContextualLiteralFindallEntryRelates freshFrontier alpha support barrier
        canonical referenceBase prog gt context session callerScope
        referenceTemplate referenceAmbOutput referenceResult referenceBranches
        referenceRest referenceBindings executableTemplate executableAmbOutput
        executableResult executableBranches executableTail executableRest
        executableBinding before) :
    ClosedLiteralFindallReadyRelates freshFrontier alpha support barrier
      canonical referenceBase (openFindall session).session referenceBindings
      referenceAmbOutput referenceBranches [] executableBinding
      executableAmbOutput executableBranches executableTail
      (executableLiteralFindallEntered before executableTemplate
        executableBranches executableAmbOutput executableResult executableTail
        executableRest executableBinding) := by
  exact
    { ready := entry.ready
      bank_empty := enterFindall_active_alts_empty before executableTemplate
        (.amb executableBranches executableAmbOutput :: executableTail)
        executableResult executableRest executableBinding }

namespace ClosedLiteralFindallReadyRelates

/-- One real literal-disjunction step preserves closed ownership: the source
takes `taskDisjunction`, the fine machine takes its actual `amb` step, and the
resulting activation is indexed by the empty older suffix.

[SPEC translator.pl:112-116; metta.pl:251-256; SWI:findall/3] -/
theorem schedule
    {prog : PLeaTTa.Prog} {gt : Metta.GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : TreeSubstitution} {referenceBase : Substitution}
    {session : Session} {scope : CutScopeId} {current : Substitution}
    {referenceOutput : Term}
    {referenceBranches referenceTail : List PeTTaSpec.PrologCore.Goal}
    {runtime : Metta.Subst} {executableOutput : Metta.Atom}
    {executableBranches : List (Metta.Atom × List PLeaTTa.Goal)}
    {executableTail : List PLeaTTa.Goal} {state : OpenConf}
    (closed :
      ClosedLiteralFindallReadyRelates freshFrontier alpha support barrier
        canonical referenceBase session current referenceOutput
        referenceBranches referenceTail runtime executableOutput
        executableBranches executableTail state) :
    ∃ referenceValue : Term,
      ∃ remainingReferences : List PeTTaSpec.PrologCore.Goal,
        ∃ executableValue : Metta.Atom,
          ∃ remainingExecutables :
              List (Metta.Atom × List PLeaTTa.Goal),
            referenceBranches =
                .unify referenceValue referenceOutput ::
                  remainingReferences ∧
              executableBranches =
                (executableValue, []) :: remainingExecutables ∧
              let next := literalAmbPulledSuccessor state executableOutput
                executableValue remainingExecutables executableTail runtime
              RawStep session
                  (.task scope
                    (.disjunction referenceBranches :: referenceTail) current)
                  [] .none session
                  (.running
                    (Search.disjoin scope referenceBranches referenceTail
                      current)) ∧
                DemandDrivenCallStep.Step prog gt (.ready state)
                  (.ready next) ∧
                ClosedLiteralDisjunctionActivationAgrees alpha support scope
                  barrier canonical referenceBase current runtime
                  (Search.disjoin scope referenceBranches referenceTail current)
                  next.control.cur next.control.alts ∧
                SessionRelatesPersistent freshFrontier session
                  next.persistent ∧
                next.frames = state.frames ∧
                next.scopes = state.scopes := by
  obtain
    ⟨referenceValue, remainingReferences, executableValue,
      remainingExecutables, referenceShape, executableShape, sourceStep,
      fineStep, activation, persistent, frames, scopes⟩ :=
    literal_disjunction_step_correspondence (prog := prog) (gt := gt)
      closed.ready
  have closedActivation :
      TaskChoiceActivationAgrees alpha support scope barrier canonical
        referenceBase current runtime []
        (Search.disjoin scope referenceBranches referenceTail current)
        (literalAmbPulledSuccessor state executableOutput executableValue
          remainingExecutables executableTail runtime).control.cur
        (literalAmbPulledSuccessor state executableOutput executableValue
          remainingExecutables executableTail runtime).control.alts := by
    rw [closed.bank_empty] at activation
    exact activation
  exact
    ⟨referenceValue, remainingReferences, executableValue,
      remainingExecutables, referenceShape, executableShape, sourceStep,
      fineStep, ⟨closedActivation⟩, persistent, frames, scopes⟩

end ClosedLiteralFindallReadyRelates

/-- Exact answer-resource origin with no executable alternatives outside the
locally owned origin zipper.  The empty older endpoint is part of the field's
type, rather than a proposition attached to a generic base. -/
structure ClosedAnswerOriginResourceAgrees
    (alpha : List (LogicVar × String))
    {leafScope : CutScopeId} {bindings : Substitution}
    {source next : Search}
    (origin : AnswerOrigin leafScope bindings source next)
    (beforeResources afterResources : List RetainedAlternativeSegment)
    (beforeAlts : List PLeaTTa.Alt) : Prop where
  agreement :
    AnswerOriginResourceAgrees alpha origin beforeResources afterResources
      beforeAlts []

/-- Pull outcomes available from a closed answer origin.  There is no
`baseLive` constructor: after all local regions fall through, `pullAux []`
must terminate. -/
inductive ClosedOriginPullOutcome
    (alpha : List (LogicVar × String))
    {leafScope : CutScopeId} {bindings : Substitution}
    {source next : Search}
    {origin : AnswerOrigin leafScope bindings source next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts : List PLeaTTa.Alt}
    (closed :
      ClosedAnswerOriginResourceAgrees alpha origin beforeResources
        afterResources beforeAlts) :
    List Observation → Prop where
  | localLive (goals : List PLeaTTa.Goal) (binding : Metta.Subst)
      (rest : List PLeaTTa.Alt)
      (landing :
        OriginPrefixLanding alpha closed.agreement goals binding rest) :
      ClosedOriginPullOutcome alpha closed []
  | terminal
      (falls : OriginPrefixFallsThrough alpha closed.agreement) :
      ClosedOriginPullOutcome alpha closed [.completed]

namespace ClosedAnswerOriginResourceAgrees

/-- The generic three-way classifier collapses constructively to the exact
two cases available at a closed older endpoint.

[SPEC metta.pl:251-256; SWI:findall/3] -/
theorem classifyPull
    {alpha : List (LogicVar × String)}
    {leafScope : CutScopeId} {bindings : Substitution}
    {source next : Search}
    {origin : AnswerOrigin leafScope bindings source next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts : List PLeaTTa.Alt}
    (closed :
      ClosedAnswerOriginResourceAgrees alpha origin beforeResources
        afterResources beforeAlts) :
    ∃ events, ClosedOriginPullOutcome alpha closed events := by
  rcases AnswerOriginResourceAgrees.classifyPrefix closed.agreement with
    ⟨goals, binding, rest, landing⟩ | falls
  · exact ⟨[], .localLive goals binding rest landing⟩
  · exact ⟨[.completed], .terminal falls⟩

/-- Every generic pull outcome over a closed origin is one of the two closed
cases.  The impossible `baseLive` branch is rejected by the literal equation
`pullAux [] = some _`. -/
theorem ofOriginPullOutcome
    {alpha : List (LogicVar × String)}
    {leafScope : CutScopeId} {bindings : Substitution}
    {source next : Search}
    {origin : AnswerOrigin leafScope bindings source next}
    {beforeResources afterResources : List RetainedAlternativeSegment}
    {beforeAlts : List PLeaTTa.Alt}
    {closed :
      ClosedAnswerOriginResourceAgrees alpha origin beforeResources
        afterResources beforeAlts}
    {events : List Observation}
    (outcome : OriginPullOutcome alpha closed.agreement events) :
    ClosedOriginPullOutcome alpha closed events := by
  cases outcome with
  | localLive goals binding rest landing =>
      exact .localLive goals binding rest landing
  | baseLive falls goals binding rest basePull =>
      simp [PLeaTTa.pullAux] at basePull
  | terminal falls _ =>
      exact .terminal falls

end ClosedAnswerOriginResourceAgrees

/-- The generic live-base witness is genuinely outside the closed fragment.
The same task origin can preserve its live singleton base, but cannot consume
that base to the empty closed endpoint without a source-owned region.

[SPEC metta.pl:251-256; SWI:findall/3] -/
theorem live_older_base_is_generic_but_not_closed :
    let base : List PLeaTTa.Alt := [.br [] []]
    let origin :
        AnswerOrigin 0 ([] : Substitution) (.task 0 [] []) .done := .task
    (∃ agreement :
        AnswerOriginResourceAgrees ([] : List (LogicVar × String)) origin
          [] [] base base,
        OriginPullOutcome [] agreement []) ∧
      ¬ AnswerOriginResourceAgrees ([] : List (LogicVar × String)) origin
          [] [] base [] := by
  dsimp only
  constructor
  · let agreement :
        AnswerOriginResourceAgrees ([] : List (LogicVar × String))
          (AnswerOrigin.task (leafScope := 0) (bindings := []))
          [] [] [.br [] []] [.br [] []] :=
      .task 0 [] [] [.br [] []]
    exact
      ⟨agreement,
        .baseLive (.task 0 [] [] [.br [] []] rfl) [] [] [] rfl⟩
  · intro closed
    cases closed

end PLeaTTa.PrologFindallClosedBankBridge
