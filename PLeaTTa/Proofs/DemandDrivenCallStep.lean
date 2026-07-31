-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.DemandDrivenCallStep
Purpose: Add an install-before-pull local-call phase to the fine executable
  lane while retaining the sealed machine's atomic call_resolve rule.
Trusted boundary: none
Main exports: FineConf, Step, local_call_expands_and_collapses
-/
import PLeaTTa.Proofs.DemandDrivenStep
import PLeaTTa.Proofs.PrologActivationMacro

namespace PLeaTTa.DemandDrivenCallStep

open Metta (Atom Subst GroundingTable)
open DemandDrivenStep
open PrologActivationMacro

/-!
The sealed `PLeaTTa.Step.call_resolve` installs the `resolveAlts` bank and
immediately pulls its first branch in one atomic step.  The independent local
semantics exposes call opening before it pulls a clause.  Relating those
states without importing head-unification facts therefore requires one real
fine-only intermediate state.

`FineConf` is a typed active-control variant around the already-proved
`DemandDrivenStep.OpenConf`: a state is either ready to execute ordinary
machine control or owns one transient pending local-call bank.  A pending
call is not a backtrackable frame and cannot nest.  It owns the exact
`ResolutionScan` output, including conservative false positives; the old
alternative bank is not changed until `callPull`.

Two fine steps collapse to the existing one sealed step:

1. `callEnter` computes and owns the bank, advancing only the global counter.
2. `callPull` splices `branches ++ barrier :: oldAlts` and calls the shared
   executable `pull`.

No unifier appears in either rule.  The leading full-head equality remains
the first goal of every retained alternative and is executed by the ordinary
`eq_ok`/`eq_fail` lane later.
-/

/-- The transient install-only phase of one locally owned predicate call.
`outer` carries the old backtrackable control exactly once.  The current
persistent state carries the advanced counter and unchanged world. -/
structure PendingCall where
  persistent : Persistent
  outer : Control
  frames : List Frame
  scopes : ScopeHighWaters
  branches : List Alt
deriving Repr

/-- The exact pre-pull configuration hidden inside a pending call.  Barrier
placement and cache update are shared verbatim with sealed `call_resolve`. -/
def PendingCall.installed (pending : PendingCall) : OpenConf :=
  { persistent := pending.persistent
    control :=
      { pending.outer with
        cur := none
        alts := pending.branches ++ Alt.barrier :: pending.outer.alts
        barriers := pushBarrierCache pending.outer.barriers }
    frames := pending.frames
    scopes := pending.scopes }

/-- Pull the first retained branch, or skip the barrier when the scan produced
no branch.  This is the same `pull` function used by the sealed machine. -/
def PendingCall.pulled (pending : PendingCall) : OpenConf :=
  pending.installed.stepOpen (pull pending.installed.toConf)

/-- A fine executable state has exactly one active-control phase.  The
transient call phase is a variant rather than an optional field, so unrelated
steps cannot accidentally execute while a bank is installed but unpulled. -/
inductive FineConf where
  | ready (state : OpenConf)
  | callPending (pending : PendingCall)
deriving Repr

/-- Project a fine state to the sealed state it refines.  A pending phase is
ghost-erased to its post-pull configuration: entering the pending phase
corresponds to the atomic sealed call step, and leaving it is a bounded
fine-only stutter. -/
def FineConf.toSealed : FineConf → Conf
  | .ready state => state.toConf
  | .callPending pending => pending.pulled.toConf

/-- Exact local-resolution head recognized by sealed `Step.call_resolve`.
The result bank is intentionally absent: `resolveAlts` computes it in
`callEnter`, rather than accepting it from an oracle. -/
def LocalResolveHead (state : OpenConf) : Prop :=
  ∃ f args res rest binding,
    state.toConf.cur =
        some (Goal.call f args res :: rest, binding) ∧
      state.toConf.world.clauseHeadCandidates f ≠ [] ∧
      (state.toConf.world.resolutionCandidates f args.length).any
        (fun clause => clause.params.length == args.length)

/-- Construct the unique fine-only pending package for one actual executable
scan result. -/
def pendingCallOf (state : OpenConf) (branches : List Alt)
    (counter : Nat) : PendingCall :=
  { persistent :=
      { world := state.persistent.world
        counter := counter }
    outer := state.control
    frames := state.frames
    scopes := state.scopes.afterLocalCall
    branches := branches }

@[simp] theorem pendingCallOf_world (state : OpenConf)
    (branches : List Alt) (counter : Nat) :
    (pendingCallOf state branches counter).persistent.world =
      state.persistent.world := rfl

@[simp] theorem pendingCallOf_counter (state : OpenConf)
    (branches : List Alt) (counter : Nat) :
    (pendingCallOf state branches counter).persistent.counter = counter := rfl

@[simp] theorem pendingCallOf_frames (state : OpenConf)
    (branches : List Alt) (counter : Nat) :
    (pendingCallOf state branches counter).frames = state.frames := rfl

@[simp] theorem pendingCallOf_scopes (state : OpenConf)
    (branches : List Alt) (counter : Nat) :
    (pendingCallOf state branches counter).scopes =
      state.scopes.afterLocalCall := rfl

@[simp] theorem PendingCall.pulled_scopes (pending : PendingCall) :
    pending.pulled.scopes = pending.scopes := rfl

@[simp] theorem PendingCall.installed_scopes (pending : PendingCall) :
    pending.installed.scopes = pending.scopes := rfl

@[simp] theorem pull_world (conf : Conf) :
    (pull conf).world = conf.world := by
  unfold pull
  generalize pullAuxTracked conf.barriers conf.alts = result
  rcases result with ⟨result, cache⟩
  cases result <;> rfl

@[simp] theorem PendingCall.pulled_persistent (pending : PendingCall) :
    pending.pulled.persistent = pending.persistent := by
  cases pending with
  | mk persistent outer frames scopes branches =>
      cases persistent
      simp [PendingCall.pulled, PendingCall.installed, OpenConf.stepOpen,
        OpenConf.ofConfWith, OpenConf.toConf, Control.toConf, persistentOf]

/-- One call-fine transition.  Existing nested-findall steps lift only when a
local resolve head is absent, structurally excluding the old atomic
`call_resolve` path from this lane. -/
inductive Step (prog : Prog) (gt : GroundingTable) :
    FineConf → FineConf → Prop where
  | ordinary (before after : OpenConf)
      (notLocalCall : ¬ LocalResolveHead before)
      (step : DemandDrivenStep.Step prog gt before after) :
      Step prog gt (.ready before) (.ready after)
  | callEnter (state : OpenConf) (f : String) (args : List Atom)
      (res : Atom) (rest : List Goal) (binding : Subst)
      (branches : List Alt) (counter : Nat)
      (head : state.toConf.cur =
        some (Goal.call f args res :: rest, binding))
      (headNonempty : state.toConf.world.clauseHeadCandidates f ≠ [])
      (arityPresent :
        (state.toConf.world.resolutionCandidates f args.length).any
          (fun clause => clause.params.length == args.length))
      (scanned :
        resolveAlts
          (state.toConf.world.resolutionCandidates f args.length)
          (args.map (subst binding)) args res rest binding state.toConf.qterm
          (barrierDepth state.toConf + 1) state.toConf.counter =
            (branches, counter)) :
      Step prog gt (.ready state)
        (.callPending (pendingCallOf state branches counter))
  | callPull (pending : PendingCall) :
      Step prog gt (.callPending pending) (.ready pending.pulled)

/-- Exact step-counted closure for the call-fine lane.  The install and pull
phases are both present transitions; neither may disappear into an
observation-list quotient. -/
inductive StepsN (prog : Prog) (gt : GroundingTable) :
    Nat → FineConf → FineConf → Prop where
  | zero (state : FineConf) : StepsN prog gt 0 state state
  | succ (n : Nat) (before middle after : FineConf) :
      Step prog gt before middle → StepsN prog gt n middle after →
      StepsN prog gt (n + 1) before after

/-- Exact finite call-lane prefixes compose without erasing the explicit
install, pull, or equality phases. -/
theorem StepsN.trans {prog : Prog} {gt : GroundingTable}
    {left middle right : FineConf} {m n : Nat}
    (first : StepsN prog gt m left middle)
    (second : StepsN prog gt n middle right) :
    StepsN prog gt (m + n) left right := by
  induction first with
  | zero state => simpa using second
  | succ k before stepMiddle after step tail inductionHypothesis =>
      have combined :=
        StepsN.succ (k + n) before stepMiddle right step
          (inductionHypothesis second)
      have lengthEq : k + n + 1 = k + 1 + n := by
        rw [Nat.add_assoc, Nat.add_comm n 1, ← Nat.add_assoc]
      rw [lengthEq] at combined
      exact combined

/-- The pending variant contains the exact sealed pre-pull configuration:
same world, advanced counter, exact branch bank, one barrier before the old
alternatives, and the exact barrier-cache increment. -/
theorem pendingCallOf_installed_toConf
    (state : OpenConf) (branches : List Alt) (counter : Nat) :
    (pendingCallOf state branches counter).installed.toConf =
      { state.toConf with
        cur := none
        counter := counter
        alts := branches ++ (Alt.barrier :: state.toConf.alts)
        barriers := pushBarrierCache state.toConf.barriers } := by
  cases state with
  | mk persistent control frames =>
      cases persistent
      cases control
      rfl

/-- Pulling a pending call produces exactly the sealed `call_resolve`
successor, including the empty-bank case which skips the freshly installed
barrier. -/
theorem pendingCallOf_pulled_toConf
    (state : OpenConf) (branches : List Alt) (counter : Nat) :
    (pendingCallOf state branches counter).pulled.toConf =
      pull
        { state.toConf with
          cur := none
          counter := counter
          alts := branches ++ (Alt.barrier :: state.toConf.alts)
          barriers := pushBarrierCache state.toConf.barriers } := by
  simp [PendingCall.pulled, pendingCallOf_installed_toConf]

/-- The install step advances the executable high-water by exactly one per
conservatively retained occurrence.  False-positive candidates are counted
and retained; no MGU premise appears. -/
theorem callEnter_counter_exact
    {state : OpenConf} {f : String} {args : List Atom} {res : Atom}
    {rest : List Goal} {binding : Subst} {branches : List Alt}
    {counter : Nat}
    (scanned :
      resolveAlts
        (state.toConf.world.resolutionCandidates f args.length)
        (args.map (subst binding)) args res rest binding state.toConf.qterm
        (barrierDepth state.toConf + 1) state.toConf.counter =
          (branches, counter)) :
    counter =
      state.toConf.counter +
        retainedClauseCount (args.map (subst binding))
          (subst binding res)
          (state.toConf.world.resolutionCandidates f args.length) := by
  have exact :=
    resolveAlts_counter_exact
      (state.toConf.world.resolutionCandidates f args.length)
      (args.map (subst binding)) args res rest binding state.toConf.qterm
      (barrierDepth state.toConf + 1) state.toConf.counter
  rw [scanned] at exact
  exact exact

/-- The pending bank has exactly one occurrence for every conservatively
retained executable candidate.  Extensionally equal clauses are not
deduplicated. -/
theorem callEnter_length_exact
    {state : OpenConf} {f : String} {args : List Atom} {res : Atom}
    {rest : List Goal} {binding : Subst} {branches : List Alt}
    {counter : Nat}
    (scanned :
      resolveAlts
        (state.toConf.world.resolutionCandidates f args.length)
        (args.map (subst binding)) args res rest binding state.toConf.qterm
        (barrierDepth state.toConf + 1) state.toConf.counter =
          (branches, counter)) :
    branches.length =
      retainedClauseCount (args.map (subst binding))
        (subst binding res)
        (state.toConf.world.resolutionCandidates f args.length) := by
  have exact :=
    resolveAlts_length_exact
      (state.toConf.world.resolutionCandidates f args.length)
      (args.map (subst binding)) args res rest binding state.toConf.qterm
      (barrierDepth state.toConf + 1) state.toConf.counter
  rw [scanned] at exact
  exact exact

/-- A local resolve head cannot take the lifted atomic lane.  Every fine step
from such a ready state is therefore an install-only `callEnter`. -/
theorem localResolveHead_forces_callEnter
    {prog : Prog} {gt : GroundingTable} {state : OpenConf} {after : FineConf}
    (hLocal : LocalResolveHead state)
    (step : Step prog gt (.ready state) after) :
    ∃ pending, after = .callPending pending := by
  cases step with
  | ordinary before next notLocalCall nested =>
      exact False.elim (notLocalCall hLocal)
  | callEnter state f args res rest binding branches counter head
      headNonempty arityPresent scanned =>
      exact ⟨pendingCallOf state branches counter, rfl⟩

/-- There is no one-step ready-to-ready shortcut for a locally resolved call.
This rules out accidentally retaining the old atomic lane alongside the fine
one. -/
theorem localResolveHead_not_direct_ready
    {prog : Prog} {gt : GroundingTable}
    {state after : OpenConf}
    (hLocal : LocalResolveHead state)
    (step : Step prog gt (.ready state) (.ready after)) :
    False := by
  cases step with
  | ordinary before next notLocalCall nested =>
      exact notLocalCall hLocal

/-- A pending local call has exactly one successor.  No unrelated machine
rule can execute while the bank is installed but unpulled. -/
theorem pending_step_unique
    {prog : Prog} {gt : GroundingTable}
    {pending : PendingCall} {after : FineConf}
    (step : Step prog gt (.callPending pending) after) :
    after = .ready pending.pulled := by
  cases step
  rfl

/-- The install projection is one genuine sealed `call_resolve` step.  The
fine intermediate is not observationally invented: erasing it yields the
exact post-pull sealed state. -/
theorem callEnter_projects_to_sealed
    {prog : Prog} {gt : GroundingTable}
    {state : OpenConf} {f : String} {args : List Atom} {res : Atom}
    {rest : List Goal} {binding : Subst} {branches : List Alt}
    {counter : Nat}
    (head : state.toConf.cur =
      some (Goal.call f args res :: rest, binding))
    (headNonempty : state.toConf.world.clauseHeadCandidates f ≠ [])
    (arityPresent :
      (state.toConf.world.resolutionCandidates f args.length).any
        (fun clause => clause.params.length == args.length))
    (scanned :
      resolveAlts
        (state.toConf.world.resolutionCandidates f args.length)
        (args.map (subst binding)) args res rest binding state.toConf.qterm
        (barrierDepth state.toConf + 1) state.toConf.counter =
          (branches, counter)) :
    PLeaTTa.Step prog gt state.toConf
      (FineConf.callPending
        (pendingCallOf state branches counter)).toSealed := by
  simpa [FineConf.toSealed, pendingCallOf_pulled_toConf] using
    (PLeaTTa.Step.call_resolve state.toConf f args res rest binding branches
      counter head headNonempty arityPresent scanned)

/-- Leaving the pending phase is a single bounded fine step whose sealed
projection is unchanged.  It cannot hide divergence: every pending phase has
this constructor as its only successor. -/
theorem callPull_projection_stutters (pending : PendingCall) :
    (FineConf.callPending pending).toSealed =
      (FineConf.ready pending.pulled).toSealed := rfl

/-- Exact two-step fine expansion and one-step sealed collapse for a local
call.  This is the call counterpart of the nested-findall macro expansion;
it introduces a real intermediate state but no new sealed behavior. -/
theorem local_call_expands_and_collapses
    {prog : Prog} {gt : GroundingTable}
    (state : OpenConf) (f : String) (args : List Atom) (res : Atom)
    (rest : List Goal) (binding : Subst) (branches : List Alt)
    (counter : Nat)
    (head : state.toConf.cur =
      some (Goal.call f args res :: rest, binding))
    (headNonempty : state.toConf.world.clauseHeadCandidates f ≠ [])
    (arityPresent :
      (state.toConf.world.resolutionCandidates f args.length).any
        (fun clause => clause.params.length == args.length))
    (scanned :
      resolveAlts
        (state.toConf.world.resolutionCandidates f args.length)
        (args.map (subst binding)) args res rest binding state.toConf.qterm
        (barrierDepth state.toConf + 1) state.toConf.counter =
          (branches, counter)) :
    Step prog gt (.ready state)
        (.callPending (pendingCallOf state branches counter)) ∧
      Step prog gt (.callPending (pendingCallOf state branches counter))
        (.ready (pendingCallOf state branches counter).pulled) ∧
      PLeaTTa.Step prog gt state.toConf
        (pendingCallOf state branches counter).pulled.toConf := by
  refine ⟨.callEnter state f args res rest binding branches counter head
      headNonempty arityPresent scanned,
    .callPull (pendingCallOf state branches counter), ?_⟩
  exact callEnter_projects_to_sealed head headNonempty arityPresent scanned

/-- The same expansion with an exact fine-step count.  A local call is one
sealed step and exactly two call-fine steps on the same endpoints. -/
theorem local_call_exact_two_steps
    {prog : Prog} {gt : GroundingTable}
    (state : OpenConf) (f : String) (args : List Atom) (res : Atom)
    (rest : List Goal) (binding : Subst) (branches : List Alt)
    (counter : Nat)
    (head : state.toConf.cur =
      some (Goal.call f args res :: rest, binding))
    (headNonempty : state.toConf.world.clauseHeadCandidates f ≠ [])
    (arityPresent :
      (state.toConf.world.resolutionCandidates f args.length).any
        (fun clause => clause.params.length == args.length))
    (scanned :
      resolveAlts
        (state.toConf.world.resolutionCandidates f args.length)
        (args.map (subst binding)) args res rest binding state.toConf.qterm
        (barrierDepth state.toConf + 1) state.toConf.counter =
          (branches, counter)) :
    StepsN prog gt 2 (.ready state)
      (.ready (pendingCallOf state branches counter).pulled) := by
  exact .succ 1 (.ready state)
    (.callPending (pendingCallOf state branches counter))
    (.ready (pendingCallOf state branches counter).pulled)
    (.callEnter state f args res rest binding branches counter head
      headNonempty arityPresent scanned)
    (.succ 0 (.callPending (pendingCallOf state branches counter))
      (.ready (pendingCallOf state branches counter).pulled)
      (.ready (pendingCallOf state branches counter).pulled)
      (.callPull (pendingCallOf state branches counter))
      (.zero (.ready (pendingCallOf state branches counter).pulled)))

end PLeaTTa.DemandDrivenCallStep
