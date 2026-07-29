-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PrologCallStepBridge
Purpose: Relate independent local-call opening to the executable fine
  install-before-pull phase without assuming head-unifier adequacy.
Trusted boundary: none
Main exports: CallEntryBankRelates,
  taskCall_callEnter_bank_correspondence
-/
import PLeaTTa.Proofs.PrologCallEntryBridge
import PLeaTTa.Proofs.DemandDrivenCallStep

namespace PLeaTTa.PrologCallStepBridge

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Resolver
open PeTTaSpec.PrologCore.GoalSemantics
open PrologStateBridge
open PrologCallEntryBridge
open PrologActivationMacro
open DemandDrivenStep
open DemandDrivenCallStep

/-!
The independent `taskCall` transition opens and eagerly reserves a prepared
cursor before any clause is pulled.  Sealed `Step.call_resolve` historically
installed and pulled the executable alternative bank atomically.  The
additive fine lane separates those actions, so its `callEnter` transition can
now correspond to independent call opening without importing either
unifier's correctness.

`CallEntryBankRelates` is deliberately a control-and-ownership relation, not
the complete state bisimulation.  It pins the exact database projection,
candidate spine, scan decisions, persistent high-water endpoints, old
continuation ownership, and nominal cut-scope advance.  Term/substitution
payload agreement and the ranked independent reject/pull macro remain later
obligations.
-/

/-- Exact post-entry relation before either side performs head unification.
The independent and executable numeric fresh counters remain distinct
currencies; `bank` carries their occurrence-level allocation evidence instead
of asserting a false equality. -/
structure CallEntryBankRelates
    (opened : OpenedCall) (before : OpenConf) (pending : PendingCall)
    (argsv args : List Metta.Atom) (res : Metta.Atom)
    (rest : List PLeaTTa.Goal) (binding : Metta.Subst)
    (qterm : Metta.Atom) (barrier startCounter : Nat) : Prop where
  outer : pending.outer = before.control
  frames : pending.frames = before.frames
  world : pending.persistent.world = before.persistent.world
  callHead :
    before.toConf.cur =
      some (PLeaTTa.Goal.call opened.cursor.predicate args res :: rest,
        binding)
  substitutedArgs : argsv = args.map (PLeaTTa.subst binding)
  barrierExact : barrier = barrierDepth before.toConf + 1
  startCounterExact : startCounter = before.toConf.counter
  database :
    DatabaseRelatesWorld opened.session.resolver.database
      pending.persistent.world
  arity : opened.cursor.arguments.length = args.length + 1
  bank :
    PreparedBankRelates opened.cursor argsv args res rest binding qterm
      barrier
      (pending.persistent.world.resolutionCandidates
        opened.cursor.predicate args.length)
      startCounter pending.branches pending.persistent.counter
  sourceFresh :
    opened.session.resolver.nextFresh = opened.cursor.reservedUntil
  cutScopeAdvanced :
    opened.session.nextCutScope = opened.scope + 1

/-- The concrete independent opener and the concrete executable pending
package satisfy the post-entry relation.  Rewriting by the actual
`resolveAlts` equation preserves the complete source-ordered bank, including
every conservative false positive. -/
theorem openedFor_pendingCallOf_relates
    {session : Session} {state : OpenConf}
    (database :
      DatabaseRelatesWorld session.resolver.database state.persistent.world)
    (ready : state.persistent.world.clauseIndexReady = true)
    (predicate : String)
    (referenceArguments : List Term)
    (referenceBindings :
      PeTTaSpec.PrologCore.OpenSubstitution.Substitution)
    (args : List Metta.Atom) (res : Metta.Atom)
    (rest : List PLeaTTa.Goal) (binding : Metta.Subst)
    (branches : List Alt) (finalCounter : Nat)
    (arity : referenceArguments.length = args.length + 1)
    (head :
      state.toConf.cur =
        some (PLeaTTa.Goal.call predicate args res :: rest, binding))
    (scanned :
      resolveAlts
        (state.persistent.world.resolutionCandidates predicate args.length)
        (args.map (PLeaTTa.subst binding)) args res rest binding
          state.control.qterm (barrierDepth state.toConf + 1)
          state.toConf.counter =
        (branches, finalCounter)) :
    CallEntryBankRelates
      (openedFor session predicate referenceArguments referenceBindings)
      state (pendingCallOf state branches finalCounter)
      (args.map (PLeaTTa.subst binding)) args res rest binding
      state.control.qterm (barrierDepth state.toConf + 1)
      state.toConf.counter := by
  constructor
  · rfl
  · rfl
  · rfl
  · simpa [openedFor, openLocalCall, requestFor, prepareCall] using head
  · rfl
  · rfl
  · rfl
  · simpa [openedFor, openLocalCall, requestFor, prepareCall, pendingCallOf]
      using database
  · simpa [openedFor, openLocalCall, requestFor, prepareCall] using arity
  · have prepared :=
      PrologCallEntryBridge.DatabaseRelatesWorld.prepareCall_resolveAlts
      database ready
        (requestFor predicate referenceArguments referenceBindings)
        (args.map (PLeaTTa.subst binding)) args res rest binding
        state.control.qterm (barrierDepth state.toConf + 1)
        state.toConf.counter arity
    simp only [requestFor] at prepared
    rw [scanned] at prepared
    simpa [openedFor, openLocalCall, requestFor, prepareCall, pendingCallOf]
      using prepared
  · change
      (prepareCall session.resolver
        (requestFor predicate referenceArguments
          referenceBindings)).2.nextFresh =
        (prepareCall session.resolver
          (requestFor predicate referenceArguments
            referenceBindings)).1.reservedUntil
    exact prepareCall_nextFresh_eq_reservedUntil session.resolver
      (requestFor predicate referenceArguments referenceBindings)
  · rfl

/-- Exact paired call-entry transitions.  A nonempty independent call-start
snapshot derives both sealed dispatch guards; the independent side enters its
prepared cursor and the executable side enters the typed pending bank.  The
statement stops before either full-head MGU, so no unifier premise is hidden
inside call opening.

[SPEC metta.pl:251-256] -/
theorem taskCall_callEnter_bank_correspondence
    {prog : Prog} {gt : Metta.GroundingTable}
    {session : Session} {state : OpenConf}
    (database :
      DatabaseRelatesWorld session.resolver.database state.persistent.world)
    (ready : state.persistent.world.clauseIndexReady = true)
    (scope : CutScopeId) (predicate : String)
    (referenceArguments : List Term)
    (referenceRest : List PeTTaSpec.PrologCore.Goal)
    (referenceBindings :
      PeTTaSpec.PrologCore.OpenSubstitution.Substitution)
    (args : List Metta.Atom) (res : Metta.Atom)
    (rest : List PLeaTTa.Goal) (binding : Metta.Subst)
    (branches : List Alt) (finalCounter : Nat)
    (arity : referenceArguments.length = args.length + 1)
    (notThrow : ¬ BuiltinThrowCall predicate referenceArguments)
    (nonempty :
      session.resolver.database.visibleClausesAt
        session.resolver.database.generation predicate
          referenceArguments.length ≠ [])
    (head :
      state.toConf.cur =
        some (PLeaTTa.Goal.call predicate args res :: rest, binding))
    (scanned :
      resolveAlts
        (state.toConf.world.resolutionCandidates predicate args.length)
        (args.map (PLeaTTa.subst binding)) args res rest binding
          state.toConf.qterm (barrierDepth state.toConf + 1)
          state.toConf.counter =
        (branches, finalCounter)) :
    RawStep session
        (.task scope
          (.call predicate referenceArguments :: referenceRest)
          referenceBindings)
        [.opened
          (requestFor predicate referenceArguments referenceBindings)]
        .none
        (openedFor session predicate referenceArguments
          referenceBindings).session
        (.running
          (.product scope
            (.cutBoundary
              (openedFor session predicate referenceArguments
                referenceBindings).scope
              (.clauses
                (openedFor session predicate referenceArguments
                  referenceBindings).scope
                (openedFor session predicate referenceArguments
                  referenceBindings).cursor))
            referenceRest)) ∧
      DemandDrivenCallStep.Step prog gt (.ready state)
        (.callPending (pendingCallOf state branches finalCounter)) ∧
      CallEntryBankRelates
        (openedFor session predicate referenceArguments referenceBindings)
        state (pendingCallOf state branches finalCounter)
        (args.map (PLeaTTa.subst binding)) args res rest binding
        state.control.qterm (barrierDepth state.toConf + 1)
        state.persistent.counter := by
  have dispatch :=
    PrologCallEntryBridge.DatabaseRelatesWorld.callResolve_dispatch
      database ready predicate args.length
      (by simpa [arity] using nonempty)
  refine ⟨.taskCall scope predicate referenceArguments referenceRest
      referenceBindings session notThrow,
    .callEnter state predicate args res rest binding branches finalCounter
      head dispatch.1 dispatch.2 scanned, ?_⟩
  exact openedFor_pendingCallOf_relates database ready predicate
    referenceArguments referenceBindings args res rest binding
    branches finalCounter arity head scanned

end PLeaTTa.PrologCallStepBridge
