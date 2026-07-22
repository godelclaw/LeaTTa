-- SPDX-License-Identifier: Apache-2.0

import PLeaTTa.Semantics

/-!
# Demand-driven nested execution for the sealed machine

`PLeaTTa.Step.findall` is a terminating-run macro rule: its premise contains
an entire terminal nested `StepStar`.  Such a rule cannot expose a finite
prefix of a generator that answers and then diverges.  This file begins an
additive fine-grained lane without weakening the desired equivalence to answer
lists or stuttering.

The executable configuration is split by rollback discipline.  `Persistent`
contains the dynamic world and global fresh high-water and is never stored in
a backtrackable frame.  `Control` contains the currently active continuation.
Entering `findall/3` *transfers* the suspended outer control into a typed frame
and starts a fresh inner control; exit combines the still-current persistent
state with that frame.  Restoring a stale world or counter is therefore not a
constructor of this representation.
-/

namespace PLeaTTa.DemandDrivenStep

open Metta (Atom Subst GroundingTable)

/-- Non-backtrackable executable state.  Dynamic updates and fresh allocation
must be threaded through every transition, including failure and unwind. -/
structure Persistent where
  world : PWorld
  counter : Nat
deriving Repr

/-- The active or suspended control component of an executable configuration.
It deliberately excludes `world` and `counter`. -/
structure Control where
  cur : Option (List Goal × Subst)
  alts : List Alt
  qterm : Atom
  answers : List Atom := []
  answerKeys : List (Option PersistentSubst.AtomExactKey) :=
    answers.map PersistentSubst.atomExactKey
  answerKeys_sound :
    answerKeys = answers.map PersistentSubst.atomExactKey := by rfl
  barriers : Option Nat := none
deriving Repr

def persistentOf (conf : Conf) : Persistent :=
  { world := conf.world, counter := conf.counter }

def controlOf (conf : Conf) : Control :=
  { cur := conf.cur
    alts := conf.alts
    qterm := conf.qterm
    answers := conf.answers
    answerKeys := conf.answerKeys
    answerKeys_sound := conf.answerKeys_sound
    barriers := conf.barriers }

def Control.toConf (control : Control) (persistent : Persistent) : Conf :=
  { cur := control.cur
    alts := control.alts
    world := persistent.world
    counter := persistent.counter
    qterm := control.qterm
    answers := control.answers
    answerKeys := control.answerKeys
    answerKeys_sound := control.answerKeys_sound
    barriers := control.barriers }

@[simp] theorem control_toConf (conf : Conf) :
    (controlOf conf).toConf (persistentOf conf) = conf := by
  apply Conf.ext <;> rfl

@[simp] theorem Control.toConf_persistent
    (control : Control) (persistent : Persistent) :
    persistentOf (control.toConf persistent) = persistent := by
  cases persistent
  rfl

@[simp] theorem Control.toConf_control
    (control : Control) (persistent : Persistent) :
    controlOf (control.toConf persistent) = control := by
  cases control
  rfl

def Control.answerValues (control : Control) : List Atom :=
  control.answers.reverse

/-- Backtrackable caller data for one `findall/3` activation.  The absence of
`PWorld` and the global counter is load-bearing: an exit cannot restore either
from this value. -/
structure FindallFrame where
  outer : Control
  template : Atom
  result : Atom
  rest : List Goal
  binding : Subst
deriving Repr

/-- Typed nested-control frames.  Later catch, soft-cut, transaction, and table
frames receive distinct constructors because cut and exception propagation
differ by delimiter kind. -/
inductive Frame where
  | findall (frame : FindallFrame)
deriving Repr

/-- Fine-grained executable state.  `frames` owns suspended continuations;
`control` owns the only active continuation. -/
structure OpenConf where
  persistent : Persistent
  control : Control
  frames : List Frame := []
deriving Repr

def OpenConf.ofConf (conf : Conf) (frames : List Frame := []) : OpenConf :=
  { persistent := persistentOf conf, control := controlOf conf, frames := frames }

def OpenConf.toConf (state : OpenConf) : Conf :=
  state.control.toConf state.persistent

@[simp] theorem OpenConf.ofConf_toConf (conf : Conf) (frames : List Frame) :
    (OpenConf.ofConf conf frames).toConf = conf := by
  exact control_toConf conf

@[simp] theorem OpenConf.ofConf_frames (conf : Conf) (frames : List Frame) :
    (OpenConf.ofConf conf frames).frames = frames := rfl

/-- Globally terminal means no active machine work and no suspended caller. -/
def Terminal (state : OpenConf) : Prop :=
  PLeaTTa.Terminal state.toConf ∧ state.frames = []

/-- Transfer the outer continuation into a typed frame and start the private
generator control.  The persistent component is retained, not copied into the
frame. -/
def enterFindall (state : OpenConf) (template : Atom) (sub : List Goal)
    (result : Atom) (rest : List Goal) (binding : Subst) : OpenConf :=
  let frame : FindallFrame :=
    { outer := state.control
      template := template
      result := result
      rest := rest
      binding := binding }
  OpenConf.ofConf (subConfOf state.toConf sub binding template)
    (.findall frame :: state.frames)

/-- Rejoin a terminal generator.  Only the bag and suspended control are
restored; the persistent world and high-water come exclusively from `inner`. -/
def resumeFindall (inner : OpenConf) (frame : FindallFrame)
    (remaining : List Frame) : OpenConf :=
  { persistent := inner.persistent
    control :=
      { frame.outer with
        cur := some
          (Goal.eq frame.result (chainOf inner.control.answerValues) ::
            frame.rest, frame.binding) }
    frames := remaining }

@[simp] theorem enterFindall_persistent (state : OpenConf)
    (template : Atom) (sub : List Goal) (result : Atom) (rest : List Goal)
    (binding : Subst) :
    (enterFindall state template sub result rest binding).persistent =
      state.persistent := by
  cases state with
  | mk persistent control frames =>
      cases persistent
      rfl

@[simp] theorem resumeFindall_persistent (inner : OpenConf)
    (frame : FindallFrame) (remaining : List Frame) :
    (resumeFindall inner frame remaining).persistent = inner.persistent := rfl

/-- Flatten all active and suspended alternative stacks.  This is a resource
partition view, not a scheduler: only `control.alts` is runnable. -/
def Frame.suspendedAlts : Frame → List Alt
  | .findall frame => frame.outer.alts

def ownedAlts (state : OpenConf) : List Alt :=
  state.control.alts ++ state.frames.flatMap Frame.suspendedAlts

@[simp] theorem enterFindall_transfers_alts (state : OpenConf)
    (template : Atom) (sub : List Goal) (result : Atom) (rest : List Goal)
    (binding : Subst) :
    ownedAlts (enterFindall state template sub result rest binding) =
      ownedAlts state := by
  simp [ownedAlts, enterFindall, OpenConf.ofConf, controlOf, subConfOf,
    Frame.suspendedAlts]

@[simp] theorem resumeFindall_transfers_alts
    (inner : OpenConf) (frame : FindallFrame) (remaining : List Frame)
    (frameHead : inner.frames = .findall frame :: remaining)
    (done : PLeaTTa.Terminal inner.toConf) :
    ownedAlts (resumeFindall inner frame remaining) =
      ownedAlts inner := by
  rcases done with ⟨currentDone, alternativesDone⟩
  have innerAlts : inner.control.alts = [] := by
    simpa [OpenConf.toConf, Control.toConf] using alternativesDone
  simp [ownedAlts, resumeFindall, innerAlts, frameHead]
  change frame.outer.alts = frame.outer.alts
  rfl

/-- One fine-grained executable transition.  A non-`findall` sealed step stays
one step.  A `findall` head has only entry and a suspended collector can leave
only after its active generator is terminal. -/
inductive Step (prog : Prog) (gt : GroundingTable) :
    OpenConf → OpenConf → Prop where
  | ordinary (state : OpenConf) (next : Conf)
      (notFindall : ¬ findallRunHead state.toConf)
      (step : PLeaTTa.Step prog gt state.toConf next) :
      Step prog gt state (OpenConf.ofConf next state.frames)
  | findallEnter (state : OpenConf) (template : Atom) (sub : List Goal)
      (result : Atom) (rest : List Goal) (binding : Subst)
      (head : state.toConf.cur =
        some (Goal.findall template sub result :: rest, binding)) :
      Step prog gt state
        (enterFindall state template sub result rest binding)
  | findallExit (inner : OpenConf) (frame : FindallFrame)
      (remaining : List Frame)
      (frameHead : inner.frames = .findall frame :: remaining)
      (done : PLeaTTa.Terminal inner.toConf) :
      Step prog gt inner (resumeFindall inner frame remaining)

/-- Exact step-counted closure.  Silent/private generator progress remains a
step and therefore cannot be erased into an observation-list equality. -/
inductive StepsN (prog : Prog) (gt : GroundingTable) :
    Nat → OpenConf → OpenConf → Prop where
  | zero (state : OpenConf) : StepsN prog gt 0 state state
  | succ (n : Nat) (before middle after : OpenConf) :
      Step prog gt before middle → StepsN prog gt n middle after →
      StepsN prog gt (n + 1) before after

theorem StepsN.trans {prog : Prog} {gt : GroundingTable}
    {left middle right : OpenConf} {m n : Nat}
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

/-- Sealed runs with no nested `findall` head, retaining exact step count. -/
inductive FlatStepsN (prog : Prog) (gt : GroundingTable) :
    Nat → Conf → Conf → Prop where
  | zero (state : Conf) : FlatStepsN prog gt 0 state state
  | succ (n : Nat) (before middle after : Conf)
      (notFindall : ¬ findallRunHead before)
      (step : PLeaTTa.Step prog gt before middle)
      (tail : FlatStepsN prog gt n middle after) :
      FlatStepsN prog gt (n + 1) before after

theorem FlatStepsN.toStepStar {prog : Prog} {gt : GroundingTable}
    {n : Nat} {before after : Conf}
    (steps : FlatStepsN prog gt n before after) :
    PLeaTTa.StepStar prog gt before after := by
  induction steps with
  | zero state => exact .refl state
  | succ n before middle after _ step _ inductionHypothesis =>
      exact .tail before middle after step inductionHypothesis

/-- Every private machine step remains one fine step under a fixed frame
stack.  No zero-step quotient is used. -/
theorem FlatStepsN.lift {prog : Prog} {gt : GroundingTable}
    {n : Nat} {before after : Conf} (frames : List Frame)
    (steps : FlatStepsN prog gt n before after) :
    StepsN prog gt n (OpenConf.ofConf before frames)
      (OpenConf.ofConf after frames) := by
  induction steps with
  | zero state => exact .zero _
  | succ n before middle after notFindall machineStep tail
      inductionHypothesis =>
      apply StepsN.succ n _ (OpenConf.ofConf middle frames) _
      · exact .ordinary _ middle (by simpa using notFindall)
          (by simpa using machineStep)
      · exact inductionHypothesis

/-- A prefix of `n` generator steps becomes exactly `n+1` open-machine steps:
one entry plus every private step.  The collector remains live. -/
theorem findall_prefix_lifts
    (prog : Prog) (gt : GroundingTable) (outer : OpenConf)
    (template : Atom) (sub : List Goal) (result : Atom)
    (rest : List Goal) (binding : Subst) (n : Nat) (inner : Conf)
    (head : outer.toConf.cur =
      some (Goal.findall template sub result :: rest, binding))
    (run : FlatStepsN prog gt n
      (subConfOf outer.toConf sub binding template) inner) :
    StepsN prog gt (n + 1) outer
      (OpenConf.ofConf inner
        (.findall
          { outer := outer.control
            template := template
            result := result
            rest := rest
            binding := binding } :: outer.frames)) := by
  apply StepsN.succ n outer
    (enterFindall outer template sub result rest binding) _
  · exact .findallEnter outer template sub result rest binding head
  · simpa [enterFindall] using
      run.lift
        (.findall
          { outer := outer.control
            template := template
            result := result
            rest := rest
            binding := binding } :: outer.frames)

/-- A terminating flat nested run expands the old atomic collector into entry,
all `n` generator steps, and one terminal exit.  This is the first direction
of the terminating-run collapse theorem and, unlike the old macro rule, does
not erase the intermediate states. -/
theorem findall_macro_expands
    (prog : Prog) (gt : GroundingTable) (outer : OpenConf)
    (template : Atom) (sub : List Goal) (result : Atom)
    (rest : List Goal) (binding : Subst) (n : Nat) (inner : Conf)
    (head : outer.toConf.cur =
      some (Goal.findall template sub result :: rest, binding))
    (run : FlatStepsN prog gt n
      (subConfOf outer.toConf sub binding template) inner)
    (done : PLeaTTa.Terminal inner) :
    StepsN prog gt (n + 2) outer
      (resumeFindall
        (OpenConf.ofConf inner
          (.findall
            { outer := outer.control
              template := template
              result := result
              rest := rest
              binding := binding } :: outer.frames))
        { outer := outer.control
          template := template
          result := result
          rest := rest
          binding := binding }
        outer.frames) := by
  let frame : FindallFrame :=
    { outer := outer.control
      template := template
      result := result
      rest := rest
      binding := binding }
  let suspended := OpenConf.ofConf inner (.findall frame :: outer.frames)
  have prefixRun : StepsN prog gt (n + 1) outer suspended := by
    simpa [frame, suspended] using
      findall_prefix_lifts prog gt outer template sub result rest binding n
        inner head run
  have exitStep : Step prog gt suspended
      (resumeFindall suspended frame outer.frames) := by
    apply Step.findallExit suspended frame outer.frames
    · rfl
    · simpa [suspended] using done
  have exit : StepsN prog gt 1 suspended
      (resumeFindall suspended frame outer.frames) := by
    simpa using StepsN.succ 0 suspended
      (resumeFindall suspended frame outer.frames)
      (resumeFindall suspended frame outer.frames) exitStep (.zero _)
  have combined := prefixRun.trans exit
  simpa [frame, suspended, Nat.add_assoc] using combined

theorem suspended_findall_not_terminal (inner : OpenConf)
    (frame : FindallFrame) (remaining : List Frame) :
    ¬ Terminal { inner with frames := .findall frame :: remaining } := by
  simp [Terminal]

/-- The fine relation has no atomic collector shortcut: a step at a findall
head is forced to transfer into the framed generator state. -/
theorem findall_step_forces_entry
    {prog : Prog} {gt : GroundingTable} (state : OpenConf)
    (template : Atom) (sub : List Goal) (result : Atom)
    (rest : List Goal) (binding : Subst)
    (head : state.toConf.cur =
      some (Goal.findall template sub result :: rest, binding))
    {next : OpenConf} (step : Step prog gt state next) :
    next = enterFindall state template sub result rest binding := by
  cases step with
  | ordinary next notFindall machineStep =>
      exfalso
      exact notFindall ⟨template, sub, result, rest, binding, head⟩
  | findallEnter enteredTemplate enteredSub enteredResult enteredRest
      enteredBinding enteredHead =>
      simp_all
  | findallExit frame remaining frameHead done =>
      exfalso
      rcases done with ⟨currentDone, _⟩
      rw [head] at currentDone
      exact Option.some_ne_none _ currentDone

/-- The externally visible answer accumulator belongs to the oldest suspended
caller.  Private collector answers cannot leak through this projection. -/
def publicControl : Control → List Frame → Control
  | current, [] => current
  | _, .findall frame :: remaining => publicControl frame.outer remaining

def publicAnswers (state : OpenConf) : List Atom :=
  (publicControl state.control state.frames).answerValues

@[simp] theorem publicAnswers_under_findall (persistent : Persistent)
    (current : Control) (frame : FindallFrame) (remaining : List Frame) :
    publicAnswers
        { persistent := persistent
          control := current
          frames := .findall frame :: remaining } =
      publicAnswers
        { persistent := persistent
          control := frame.outer
          frames := remaining } := by
  rfl

/-- Exact successor used by the sealed answer rule. -/
def answerSuccessor (inner : Conf) (binding : Subst) : Conf :=
  pull { inner with
    cur := none
    answers := subst binding inner.qterm :: inner.answers
    answerKeys :=
      PersistentSubst.atomExactKey (subst binding inner.qterm) ::
        inner.answerKeys
    answerKeys_sound := by
      simp only [List.map_cons]
      rw [inner.answerKeys_sound] }

/-- A private generator answer is suppressed from the public accumulator but
is still exactly one fine transition.  Thus infinitely many private answers
cannot collapse to a zero-step empty observation list. -/
theorem nested_answer_is_one_private_step
    (prog : Prog) (gt : GroundingTable) (inner : Conf)
    (frame : FindallFrame) (remaining : List Frame) (binding : Subst)
    (head : inner.cur = some ([], binding)) :
    Step prog gt
        (OpenConf.ofConf inner (.findall frame :: remaining))
        (OpenConf.ofConf (answerSuccessor inner binding)
          (.findall frame :: remaining)) ∧
      publicAnswers
          (OpenConf.ofConf (answerSuccessor inner binding)
            (.findall frame :: remaining)) =
        publicAnswers
          (OpenConf.ofConf inner (.findall frame :: remaining)) := by
  constructor
  · apply Step.ordinary
    · intro findallHead
      rcases findallHead with ⟨template, sub, result, rest, other, conflict⟩
      rw [OpenConf.ofConf_toConf] at conflict
      rw [head] at conflict
      cases conflict
    · simpa [answerSuccessor] using
        (PLeaTTa.Step.answer inner binding head :
          PLeaTTa.Step prog gt inner (answerSuccessor inner binding))
  · rfl

/-- Effects and dynamic updates produced by a generator survive collection
exit because the frame contains no persistent state to restore. -/
theorem findall_exit_keeps_inner_world_and_highWater
    (inner : OpenConf) (frame : FindallFrame) (remaining : List Frame) :
    (resumeFindall inner frame remaining).persistent.world =
        inner.persistent.world ∧
      (resumeFindall inner frame remaining).persistent.counter =
        inner.persistent.counter := by
  exact ⟨rfl, rfl⟩

/-- The current sealed relation treats every outer findall step atomically:
the step can exist only with a terminal nested `StepStar` premise. -/
theorem sealed_findall_step_has_terminal_subrun
    {prog : Prog} {gt : GroundingTable} (outer next : Conf)
    (template : Atom) (sub : List Goal) (result : Atom)
    (rest : List Goal) (binding : Subst)
    (head : outer.cur =
      some (Goal.findall template sub result :: rest, binding))
    (step : PLeaTTa.Step prog gt outer next) :
    ∃ inner,
      PLeaTTa.StepStar prog gt
        (subConfOf outer sub binding template) inner ∧
      PLeaTTa.Terminal inner := by
  cases step <;> simp_all [subConfOf]
  case findall => exact ⟨_, by assumption, by assumption⟩

end PLeaTTa.DemandDrivenStep
