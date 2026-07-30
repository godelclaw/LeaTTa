-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologDatabaseActionStepBridge
Purpose: Exact one-step source/executable correspondence for supported local
  `assertaPredicate` and `assertzPredicate` world actions.
Trusted boundary: none
Main exports:
  SourceDatabaseEffectErasure,
  ReadyAssertionRelates,
  assertion_step_correspondence
-/
import PLeaTTa.Proofs.PrologOrdinaryStepBridge

namespace PLeaTTa.PrologDatabaseActionStepBridge

open Metta (Atom Subst GroundingTable)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.DatabaseActions
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PrologStateBridge
open PrologOrdinaryStepBridge
open DemandDrivenStep

/-!
The independent semantics records database mutations as typed observations,
whereas the sealed executable step is intentionally unlabelled.  This module
does not call those traces equal.  `SourceDatabaseEffectErasure` names the
projection explicitly: erasure is licensed only by the exact declarative
mutation and by related persistent states on both sides.

Retraction is absent deliberately.  The current executable uses alpha-key
matching, drops the pattern binding, and fails without the pinned `false`
fallback.  Those measured divergences remain FAIL rows; premises excluding
them would not constitute a retract correspondence.
-/

/-- The two assertion operations whose current source and executable
behaviors agree on the supported finite-clause fragment. -/
inductive AssertionOperation where
  | asserta
  | assertz
deriving Repr, Inhabited, DecidableEq

namespace AssertionOperation

def predicate : AssertionOperation → String
  | .asserta => "assertaPredicate"
  | .assertz => "assertzPredicate"

def front : AssertionOperation → Bool
  | .asserta => true
  | .assertz => false

def update : AssertionOperation → Resolver.Database → Resolver.LocalClause →
    Resolver.Database
  | .asserta => Resolver.Database.asserta
  | .assertz => Resolver.Database.assertz

def effect : AssertionOperation → Resolver.Database → Resolver.LocalClause →
    LocalDatabaseEffect
  | .asserta => fun database clause =>
      .asserta (database.allocate clause)
  | .assertz => fun database clause =>
      .assertz (database.allocate clause)

def mutation (operation : AssertionOperation)
    (database : Resolver.Database) (clause : Resolver.LocalClause) :
    DatabaseMutation database (operation.effect database clause)
      (operation.update database clause) := by
  cases operation with
  | asserta => exact .asserta database clause
  | assertz => exact .assertz database clause

end AssertionOperation

/-- Explicit projection from one typed source effect to one unlabelled
executable persistent-state transition.

This relation does not erase an arbitrary observation.  The singleton event
must be the exact `DatabaseMutation`, and the before/after databases must
project to the actual before/after executable worlds. -/
inductive SourceDatabaseEffectErasure
    (events : List Observation)
    (before after : Session)
    (beforePersistent afterPersistent : Persistent) : Prop where
  | intro (effect : LocalDatabaseEffect)
      (events_eq : events = [.effect effect])
      (mutation :
        DatabaseMutation before.resolver.database effect
          after.resolver.database)
      (beforeState :
        DatabaseRelatesWorld before.resolver.database beforePersistent.world)
      (afterState :
        DatabaseRelatesWorld after.resolver.database afterPersistent.world)

/-- Effect erasure is not silent stuttering: a database mutation must retain
its one typed source observation. -/
theorem SourceDatabaseEffectErasure.rejects_empty_events
    (before after : Session)
    (beforePersistent afterPersistent : Persistent) :
    ¬ SourceDatabaseEffectErasure [] before after beforePersistent
      afterPersistent := by
  rintro ⟨effect, events, _mutation, _beforeState, _afterState⟩
  simp at events

/-- Exact executable successor of one successful assertion dispatch. -/
def assertionSuccessor (operation : AssertionOperation)
    (state : OpenConf) (executableResult : Atom)
    (executableTail : List PLeaTTa.Goal) (runtime : Subst)
    (functor : String) (executableClause : PLeaTTa.Clause) : OpenConf :=
  OpenConf.ofConf
    { state.toConf with
      cur := some
        (PLeaTTa.Goal.eq executableResult trueA :: executableTail, runtime)
      world :=
        PLeaTTa.installPredicateClause state.persistent.world operation.front
          functor executableClause
      counter := state.persistent.counter + 1 }
    state.frames

@[simp] theorem assertionSuccessor_world
    (operation : AssertionOperation) (state : OpenConf)
    (executableResult : Atom) (executableTail : List PLeaTTa.Goal)
    (runtime : Subst) (functor : String)
    (executableClause : PLeaTTa.Clause) :
    (assertionSuccessor operation state executableResult executableTail
      runtime functor executableClause).persistent.world =
        PLeaTTa.installPredicateClause state.persistent.world operation.front
          functor executableClause := by
  rfl

@[simp] theorem assertionSuccessor_counter
    (operation : AssertionOperation) (state : OpenConf)
    (executableResult : Atom) (executableTail : List PLeaTTa.Goal)
    (runtime : Subst) (functor : String)
    (executableClause : PLeaTTa.Clause) :
    (assertionSuccessor operation state executableResult executableTail
      runtime functor executableClause).persistent.counter =
        state.persistent.counter + 1 := by
  rfl

@[simp] theorem assertionSuccessor_current
    (operation : AssertionOperation) (state : OpenConf)
    (executableResult : Atom) (executableTail : List PLeaTTa.Goal)
    (runtime : Subst) (functor : String)
    (executableClause : PLeaTTa.Clause) :
    (assertionSuccessor operation state executableResult executableTail
      runtime functor executableClause).control.cur =
        some
          (PLeaTTa.Goal.eq executableResult trueA :: executableTail,
            runtime) := by
  rfl

@[simp] theorem assertionSuccessor_frames
    (operation : AssertionOperation) (state : OpenConf)
    (executableResult : Atom) (executableTail : List PLeaTTa.Goal)
    (runtime : Subst) (functor : String)
    (executableClause : PLeaTTa.Clause) :
    (assertionSuccessor operation state executableResult executableTail
      runtime functor executableClause).frames = state.frames := by
  rfl

/-- A nontrivial existing head distinguishes front insertion from the
deliberately wrong back-insertion successor. -/
theorem asserta_successor_rejects_back_edge
    (state : OpenConf) (executableResult : Atom)
    (executableTail : List PLeaTTa.Goal) (runtime : Subst)
    (functor : String) (executableClause : PLeaTTa.Clause)
    (oldHead : String × PLeaTTa.Clause)
    (oldTail : List (String × PLeaTTa.Clause))
    (old :
      state.persistent.world.progClauses = oldHead :: oldTail)
    (different : (functor, executableClause) ≠ oldHead)
    (noDescendants :
      state.persistent.world.specializationDescendants functor = []) :
    (assertionSuccessor .asserta state executableResult executableTail
        runtime functor executableClause).persistent.world.progClauses ≠
      state.persistent.world.progClauses ++
        [(functor, executableClause)] := by
  rw [assertionSuccessor_world,
    PLeaTTa.installPredicateClause_progClauses_of_no_descendants
      _ _ _ _ noDescendants,
    if_pos (by simp [AssertionOperation.front]), old]
  intro wrong
  have headEq : (functor, executableClause) = oldHead := by
    simpa using congrArg List.head? wrong
  exact different headEq

/-- Symmetrically, a nontrivial existing head distinguishes back insertion
from the deliberately wrong front-insertion successor. -/
theorem assertz_successor_rejects_front_edge
    (state : OpenConf) (executableResult : Atom)
    (executableTail : List PLeaTTa.Goal) (runtime : Subst)
    (functor : String) (executableClause : PLeaTTa.Clause)
    (oldHead : String × PLeaTTa.Clause)
    (oldTail : List (String × PLeaTTa.Clause))
    (old :
      state.persistent.world.progClauses = oldHead :: oldTail)
    (different : (functor, executableClause) ≠ oldHead)
    (noDescendants :
      state.persistent.world.specializationDescendants functor = []) :
    (assertionSuccessor .assertz state executableResult executableTail
        runtime functor executableClause).persistent.world.progClauses ≠
      (functor, executableClause) ::
        state.persistent.world.progClauses := by
  rw [assertionSuccessor_world,
    PLeaTTa.installPredicateClause_progClauses_of_no_descendants
      _ _ _ _ noDescendants,
    if_neg (by simp [AssertionOperation.front]), old]
  intro wrong
  have headEq : oldHead = (functor, executableClause) := by
    simpa using congrArg List.head? wrong
  exact different headEq.symm

/-- The semantic state relation itself rejects pairing source `asserta`
with an executable back insertion.  Unlike the list-shape witness above,
this theorem passes through the exact `DatabaseRelatesWorld` relation used by
the step correspondence. -/
theorem asserta_relation_rejects_back_projection
    {database : Resolver.Database} {world afterWorld : PWorld}
    {reference : Resolver.LocalClause}
    {appended oldHead : String × PLeaTTa.Clause}
    {oldTail : List (String × PLeaTTa.Clause)}
    (before : DatabaseRelatesWorld database world)
    (old :
      world.progClauses = oldHead :: oldTail)
    (different : reference.predicate ≠ oldHead.1)
    (wrongProjection :
      afterWorld.progClauses = world.progClauses ++ [appended]) :
    ¬ DatabaseRelatesWorld (database.asserta reference) afterWorld := by
  intro wrong
  have live := wrong.liveClauses
  rw [currentVisibleEntries_asserta before.generationClosed reference,
    wrongProjection, old] at live
  cases live with
  | cons head _tail =>
      have headAgrees : LocalClauseAgrees reference oldHead := by
        simpa [VersionedClauseAgrees, Resolver.Database.allocate] using head
      exact different headAgrees.predicate

/-- Symmetrically, the semantic state relation rejects pairing source
`assertz` with an executable front insertion. -/
theorem assertz_relation_rejects_front_projection
    {database : Resolver.Database} {world afterWorld : PWorld}
    {reference : Resolver.LocalClause}
    {existing : Resolver.VersionedClause}
    {sourceTail : List Resolver.VersionedClause}
    {prepended : String × PLeaTTa.Clause}
    (before : DatabaseRelatesWorld database world)
    (source :
      currentVisibleEntries database = existing :: sourceTail)
    (different : existing.clause.predicate ≠ prepended.1)
    (wrongProjection :
      afterWorld.progClauses = prepended :: world.progClauses) :
    ¬ DatabaseRelatesWorld (database.assertz reference) afterWorld := by
  intro wrong
  have live := wrong.liveClauses
  rw [currentVisibleEntries_assertz before.generationClosed reference,
    source, wrongProjection] at live
  cases live with
  | cons head _tail =>
      exact different head.predicate

/-- The executable freshness advance is observable in the successor state;
an unchanged counter cannot masquerade as a successful assertion. -/
theorem assertionSuccessor_rejects_unchanged_counter
    (operation : AssertionOperation) (state : OpenConf)
    (executableResult : Atom) (executableTail : List PLeaTTa.Goal)
    (runtime : Subst) (functor : String)
    (executableClause : PLeaTTa.Clause) :
    (assertionSuccessor operation state executableResult executableTail
        runtime functor executableClause).persistent.counter ≠
      state.persistent.counter := by
  rw [assertionSuccessor_counter]
  omega

/-- Complete ready-state contract for one supported assertion.

The source and executable decoders are both real functions.  Their outputs
are related by `LocalClauseAgrees`; the bridge cannot supply an unrelated
executable clause.  The no-descendant premise exposes the current fragment
boundary around specialization invalidation.  `postPayload` certifies the
actual equality goal installed by both source and executable transitions. -/
structure ReadyAssertionRelates
    (gt : GroundingTable)
    (freshFrontier : FreshFrontierRelation)
    (alpha support : List (LogicVar × String)) (barrier : Nat)
    (canonical : Canonical.TreeSubstitution) (referenceBase : Substitution)
    (operation : AssertionOperation)
    (session : Session) (current : Substitution)
    (payload result : Term)
    (references : List PeTTaSpec.PrologCore.Goal)
    (referenceClause : Resolver.LocalClause)
    (state : OpenConf) : Type where
  executablePayload : Atom
  executableResult : Atom
  executableTail : List PLeaTTa.Goal
  runtime : Subst
  functor : String
  executableClause : PLeaTTa.Clause
  persistent :
    SessionRelatesPersistent freshFrontier session state.persistent
  currentControl :
    state.control.cur =
      some
        (PLeaTTa.Goal.wact operation.predicate [executablePayload]
            executableResult ::
          executableTail, runtime)
  sourceDecoded :
    decodePredicateClause (current.applyTerm payload) =
      some referenceClause
  executableDecoded :
    PLeaTTa.predicateClause? gt (subst runtime executablePayload) =
      some (functor, executableClause)
  clause :
    LocalClauseAgrees referenceClause (functor, executableClause)
  noDescendants :
    state.persistent.world.specializationDescendants functor = []
  freshAfter :
    freshFrontier session.resolver.nextFresh
      (state.persistent.counter + 1)
  postPayload :
    TaskPayloadAgrees alpha support barrier canonical referenceBase current
      runtime
      (.unify result (.atom "true") :: references)
      (PLeaTTa.Goal.eq executableResult trueA :: executableTail)

namespace ReadyAssertionRelates

private theorem executableStep
    {prog : PLeaTTa.Prog} {gt : GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : Canonical.TreeSubstitution} {referenceBase : Substitution}
    {operation : AssertionOperation}
    {session : Session} {current : Substitution}
    {payload result : Term}
    {references : List PeTTaSpec.PrologCore.Goal}
    {referenceClause : Resolver.LocalClause} {state : OpenConf}
    (agreement :
      ReadyAssertionRelates gt freshFrontier alpha support barrier canonical
        referenceBase operation session current payload result references
        referenceClause state) :
    DemandDrivenCallStep.Step prog gt (.ready state)
      (.ready
        (assertionSuccessor operation state agreement.executableResult
          agreement.executableTail agreement.runtime agreement.functor
          agreement.executableClause)) := by
  have sealedHead :
      state.toConf.cur =
        some
          (PLeaTTa.Goal.wact operation.predicate
              [agreement.executablePayload] agreement.executableResult ::
            agreement.executableTail, agreement.runtime) := by
    simpa [OpenConf.toConf, Control.toConf] using agreement.currentControl
  have notFindall : ¬ findallRunHead state.toConf := by
    simp [findallRunHead, sealedHead]
  have notLocalCall :
      ¬ DemandDrivenCallStep.LocalResolveHead state := by
    simp [DemandDrivenCallStep.LocalResolveHead, sealedHead]
  have counterExact :
      max state.toConf.counter (state.persistent.counter + 1) =
        state.persistent.counter + 1 := by
    change max state.persistent.counter (state.persistent.counter + 1) =
      state.persistent.counter + 1
    omega
  apply DemandDrivenCallStep.Step.ordinary state
    (assertionSuccessor operation state agreement.executableResult
      agreement.executableTail agreement.runtime agreement.functor
      agreement.executableClause) notLocalCall
  apply DemandDrivenStep.Step.ordinary state
    (assertionSuccessor operation state agreement.executableResult
      agreement.executableTail agreement.runtime agreement.functor
      agreement.executableClause).toConf notFindall
  cases operation with
  | asserta =>
      have dispatch :=
        PLeaTTa.wactDispatch_assertaPredicate state.persistent.world gt
          state.persistent.counter (subst agreement.runtime
            agreement.executablePayload)
          agreement.functor agreement.executableClause
          agreement.executableDecoded
      simpa [assertionSuccessor, AssertionOperation.predicate,
        AssertionOperation.front, counterExact] using
        (PLeaTTa.Step.wact_ok (prog := prog) state.toConf "assertaPredicate"
          [agreement.executablePayload] agreement.executableResult trueA
          agreement.executableTail agreement.runtime
          (PLeaTTa.installPredicateClause state.persistent.world true
            agreement.functor agreement.executableClause)
          (state.persistent.counter + 1) sealedHead dispatch)
  | assertz =>
      have dispatch :=
        PLeaTTa.wactDispatch_assertzPredicate state.persistent.world gt
          state.persistent.counter (subst agreement.runtime
            agreement.executablePayload)
          agreement.functor agreement.executableClause
          agreement.executableDecoded
      simpa [assertionSuccessor, AssertionOperation.predicate,
        AssertionOperation.front, counterExact] using
        (PLeaTTa.Step.wact_ok (prog := prog) state.toConf "assertzPredicate"
          [agreement.executablePayload] agreement.executableResult trueA
          agreement.executableTail agreement.runtime
          (PLeaTTa.installPredicateClause state.persistent.world false
            agreement.functor agreement.executableClause)
          (state.persistent.counter + 1) sealedHead dispatch)

private theorem persistentAfter
    {gt : GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : Canonical.TreeSubstitution} {referenceBase : Substitution}
    {operation : AssertionOperation}
    {session : Session} {current : Substitution}
    {payload result : Term}
    {references : List PeTTaSpec.PrologCore.Goal}
    {referenceClause : Resolver.LocalClause} {state : OpenConf}
    (agreement :
      ReadyAssertionRelates gt freshFrontier alpha support barrier canonical
        referenceBase operation session current payload result references
        referenceClause state) :
    SessionRelatesPersistent freshFrontier
      (session.withDatabase
        (operation.update session.resolver.database referenceClause))
      (assertionSuccessor operation state agreement.executableResult
        agreement.executableTail agreement.runtime agreement.functor
        agreement.executableClause).persistent := by
  constructor
  · cases operation with
    | asserta =>
        apply agreement.persistent.database.asserta_of_projection
          agreement.clause
        · simpa [AssertionOperation.front] using
            PLeaTTa.installPredicateClause_progClauses_of_no_descendants
              state.persistent.world true agreement.functor
              agreement.executableClause agreement.noDescendants
        · exact
            PLeaTTa.installPredicateClause_coherent_of_no_descendants
              state.persistent.world true agreement.functor
              agreement.executableClause
              agreement.persistent.database.clauseIndex
              agreement.noDescendants
    | assertz =>
        apply agreement.persistent.database.assertz_of_projection
          agreement.clause
        · simpa [AssertionOperation.front] using
            PLeaTTa.installPredicateClause_progClauses_of_no_descendants
              state.persistent.world false agreement.functor
              agreement.executableClause agreement.noDescendants
        · exact
            PLeaTTa.installPredicateClause_coherent_of_no_descendants
              state.persistent.world false agreement.functor
              agreement.executableClause
              agreement.persistent.database.clauseIndex
              agreement.noDescendants
  · simpa [Session.withDatabase, AssertionOperation.update] using
      agreement.freshAfter

private theorem sourceStep
    {gt : GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : Canonical.TreeSubstitution} {referenceBase : Substitution}
    {operation : AssertionOperation}
    {session : Session} {scope : CutScopeId}
    {current : Substitution} {payload result : Term}
    {references : List PeTTaSpec.PrologCore.Goal}
    {referenceClause : Resolver.LocalClause} {state : OpenConf}
    (agreement :
      ReadyAssertionRelates gt freshFrontier alpha support barrier canonical
        referenceBase operation session current payload result references
        referenceClause state) :
    RawStep session
      (.task scope
        (.call operation.predicate [payload, result] :: references) current)
      [.effect
        (operation.effect session.resolver.database referenceClause)]
      .none
      (session.withDatabase
        (operation.update session.resolver.database referenceClause))
      (.running
        (.task scope
          (.unify result (.atom "true") :: references) current)) := by
  cases operation with
  | asserta =>
      exact
        RawStep.taskAsserta scope payload result references current session
          referenceClause (predicate := "assertaPredicate")
          (arguments := [payload, result]) rfl agreement.sourceDecoded
  | assertz =>
      exact
        RawStep.taskAssertz scope payload result references current session
          referenceClause (predicate := "assertzPredicate")
          (arguments := [payload, result]) rfl agreement.sourceDecoded

/-- One supported assertion takes one real transition in each semantics.

The source emits its exact typed mutation.  The executable transition is
unlabelled, so `SourceDatabaseEffectErasure` records the intentional
observation projection and requires exact related before/after stores.
Substitutions, ordered continuation goals, frames, and the abstract fresh
frontier remain related. -/
theorem assertion_step_correspondence
    {prog : PLeaTTa.Prog} {gt : GroundingTable}
    {freshFrontier : FreshFrontierRelation}
    {alpha support : List (LogicVar × String)} {barrier : Nat}
    {canonical : Canonical.TreeSubstitution} {referenceBase : Substitution}
    {operation : AssertionOperation}
    {session : Session} {scope : CutScopeId}
    {current : Substitution} {payload result : Term}
    {references : List PeTTaSpec.PrologCore.Goal}
    {referenceClause : Resolver.LocalClause} {state : OpenConf}
    (agreement :
      ReadyAssertionRelates gt freshFrontier alpha support barrier canonical
        referenceBase operation session current payload result references
        referenceClause state) :
    let sourceAfter :=
      session.withDatabase
        (operation.update session.resolver.database referenceClause)
    let executableAfter :=
      assertionSuccessor operation state agreement.executableResult
        agreement.executableTail agreement.runtime agreement.functor
        agreement.executableClause
    RawStep session
        (.task scope
          (.call operation.predicate [payload, result] :: references) current)
        [.effect
          (operation.effect session.resolver.database referenceClause)]
        .none sourceAfter
        (.running
          (.task scope
            (.unify result (.atom "true") :: references) current)) ∧
      DemandDrivenCallStep.Step prog gt (.ready state)
        (.ready executableAfter) ∧
      SourceDatabaseEffectErasure
        [.effect
          (operation.effect session.resolver.database referenceClause)]
        session sourceAfter state.persistent executableAfter.persistent ∧
      ReadyTaskRelates freshFrontier alpha support barrier canonical
        referenceBase sourceAfter current
        (.unify result (.atom "true") :: references) executableAfter := by
  dsimp only
  have source := agreement.sourceStep (scope := scope)
  have executable := agreement.executableStep (prog := prog)
  have persistent := agreement.persistentAfter
  refine ⟨source, executable, ?_, ?_⟩
  · exact
      .intro (operation.effect session.resolver.database referenceClause) rfl
        (operation.mutation session.resolver.database referenceClause)
        agreement.persistent.database persistent.database
  · exact
      ⟨PLeaTTa.Goal.eq agreement.executableResult trueA ::
          agreement.executableTail,
        agreement.runtime, persistent, assertionSuccessor_current _ _ _ _ _ _
          _, agreement.postPayload⟩

end ReadyAssertionRelates

end PLeaTTa.PrologDatabaseActionStepBridge
