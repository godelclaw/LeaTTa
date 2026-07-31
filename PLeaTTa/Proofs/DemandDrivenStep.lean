-- SPDX-License-Identifier: Apache-2.0

import PLeaTTa.Semantics
import PLeaTTa.Proofs.FindallCopy
import PLeaTTa.Proofs.Unification

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
  /-- Fine-lane cut frontier immediately before this frame was pushed.
  This is executable allocation history, not a copied source identity. -/
  preCut : Nat
  /-- Fine-lane collection frontier immediately before this frame was
  pushed.  It cannot be reconstructed from the current frontier because
  local calls may advance `preCut` without advancing this bank. -/
  preCollection : Nat
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

/-- Open-layer-only allocation chronology for the three typed control
delimiters.  These are not the sealed machine's positional barrier depths and
are deliberately kept separate from both `Persistent.counter` and `Conf`.

The fields are present before every delimiter lane is connected so that
future catch/collection refinements cannot silently reuse the cut frontier.
Only a transition justified by executable syntax may advance a field. -/
structure ScopeHighWaters where
  nextCutScope : Nat := 1
  nextExceptionScope : Nat := 1
  nextCollectionScope : Nat := 1
deriving Repr, DecidableEq

namespace ScopeHighWaters

/-- One executable local-predicate entry allocates one cut delimiter and
cannot alter either of the other typed frontiers. -/
def afterLocalCall (scopes : ScopeHighWaters) : ScopeHighWaters :=
  { scopes with nextCutScope := scopes.nextCutScope + 1 }

@[simp] theorem afterLocalCall_cut (scopes : ScopeHighWaters) :
    scopes.afterLocalCall.nextCutScope = scopes.nextCutScope + 1 := rfl

@[simp] theorem afterLocalCall_exception (scopes : ScopeHighWaters) :
    scopes.afterLocalCall.nextExceptionScope =
      scopes.nextExceptionScope := rfl

@[simp] theorem afterLocalCall_collection (scopes : ScopeHighWaters) :
    scopes.afterLocalCall.nextCollectionScope =
      scopes.nextCollectionScope := rfl

/-- The cut allocation is a real open-state change, not a cosmetic wrapper
around the sealed configuration. -/
theorem afterLocalCall_ne (scopes : ScopeHighWaters) :
    scopes.afterLocalCall ≠ scopes := by
  intro same
  have cutSame := congrArg ScopeHighWaters.nextCutScope same
  simp only [afterLocalCall_cut] at cutSame
  omega

/-- One executable `findall/3` entry allocates independent cut and
collection delimiters.  It cannot consume an exception identity.  Allocation
happens at entry even when the generator later fails or diverges. -/
def afterFindall (scopes : ScopeHighWaters) : ScopeHighWaters :=
  { scopes with
    nextCutScope := scopes.nextCutScope + 1
    nextCollectionScope := scopes.nextCollectionScope + 1 }

@[simp] theorem afterFindall_cut (scopes : ScopeHighWaters) :
    scopes.afterFindall.nextCutScope = scopes.nextCutScope + 1 := rfl

@[simp] theorem afterFindall_exception (scopes : ScopeHighWaters) :
    scopes.afterFindall.nextExceptionScope =
      scopes.nextExceptionScope := rfl

@[simp] theorem afterFindall_collection (scopes : ScopeHighWaters) :
    scopes.afterFindall.nextCollectionScope =
      scopes.nextCollectionScope + 1 := rfl

/-- Collector entry changes both of its typed allocation banks. -/
theorem afterFindall_ne (scopes : ScopeHighWaters) :
    scopes.afterFindall ≠ scopes := by
  intro same
  have collectionSame :=
    congrArg ScopeHighWaters.nextCollectionScope same
  simp only [afterFindall_collection] at collectionSame
  omega

end ScopeHighWaters

/-- Fine-grained executable state.  `frames` owns suspended continuations;
`control` owns the only active continuation.  `scopes` is open-layer-only
non-backtrackable chronology, parallel to `frames`: sealed projection erases
it, and no frame can restore it. -/
structure OpenConf where
  persistent : Persistent
  control : Control
  frames : List Frame := []
  scopes : ScopeHighWaters := {}
deriving Repr

def OpenConf.ofConf (conf : Conf) (frames : List Frame := []) : OpenConf :=
  { persistent := persistentOf conf
    control := controlOf conf
    frames := frames }

/-- Reconstitute sealed data at an explicitly supplied open-layer frontier.
Unlike `ofConf`, this constructor never invents a non-initial chronology. -/
def OpenConf.ofConfWith (conf : Conf) (frames : List Frame)
    (scopes : ScopeHighWaters) : OpenConf :=
  { persistent := persistentOf conf
    control := controlOf conf
    frames := frames
    scopes := scopes }

/-- Advance sealed data while structurally carrying every open-only resource.
Transition code uses this constructor instead of `ofConf`, so an ordinary
sealed step cannot reset frames or scope chronology accidentally. -/
def OpenConf.stepOpen (state : OpenConf) (next : Conf) : OpenConf :=
  OpenConf.ofConfWith next state.frames state.scopes

def OpenConf.toConf (state : OpenConf) : Conf :=
  state.control.toConf state.persistent

@[simp] theorem OpenConf.ofConf_toConf (conf : Conf) (frames : List Frame) :
    (OpenConf.ofConf conf frames).toConf = conf := by
  exact control_toConf conf

@[simp] theorem OpenConf.ofConf_frames (conf : Conf) (frames : List Frame) :
    (OpenConf.ofConf conf frames).frames = frames := rfl

@[simp] theorem OpenConf.ofConf_scopes (conf : Conf) (frames : List Frame) :
    (OpenConf.ofConf conf frames).scopes = {} := rfl

@[simp] theorem OpenConf.ofConfWith_toConf (conf : Conf)
    (frames : List Frame) (scopes : ScopeHighWaters) :
    (OpenConf.ofConfWith conf frames scopes).toConf = conf := by
  exact control_toConf conf

@[simp] theorem OpenConf.ofConfWith_frames (conf : Conf)
    (frames : List Frame) (scopes : ScopeHighWaters) :
    (OpenConf.ofConfWith conf frames scopes).frames = frames := rfl

@[simp] theorem OpenConf.ofConfWith_scopes (conf : Conf)
    (frames : List Frame) (scopes : ScopeHighWaters) :
    (OpenConf.ofConfWith conf frames scopes).scopes = scopes := rfl

@[simp] theorem OpenConf.stepOpen_toConf (state : OpenConf) (next : Conf) :
    (state.stepOpen next).toConf = next := by
  exact control_toConf next

@[simp] theorem OpenConf.stepOpen_frames (state : OpenConf) (next : Conf) :
    (state.stepOpen next).frames = state.frames := rfl

@[simp] theorem OpenConf.stepOpen_scopes (state : OpenConf) (next : Conf) :
    (state.stepOpen next).scopes = state.scopes := rfl

/-- The sealed projection plus the two open-only resource components determine
the complete fine state.

This is the extensionality principle used by correspondence proofs: equality
of `toConf` recovers both persistent and backtrackable control through their
proved inverse projections, while frames and typed scope chronology remain
explicit rather than being erased. -/
theorem OpenConf.eq_of_toConf_eq_of_frames_eq_of_scopes_eq
    {left right : OpenConf}
    (conf : left.toConf = right.toConf)
    (frames : left.frames = right.frames)
    (scopes : left.scopes = right.scopes) :
    left = right := by
  cases left with
  | mk leftPersistent leftControl leftFrames leftScopes =>
      cases right with
      | mk rightPersistent rightControl rightFrames rightScopes =>
          have persistent : leftPersistent = rightPersistent := by
            have projected := congrArg persistentOf conf
            simpa [OpenConf.toConf] using projected
          have control : leftControl = rightControl := by
            have projected := congrArg controlOf conf
            simpa [OpenConf.toConf] using projected
          change leftFrames = rightFrames at frames
          change leftScopes = rightScopes at scopes
          subst rightPersistent
          subst rightControl
          subst rightFrames
          subst rightScopes
          rfl

/-- Globally terminal means no active machine work and no suspended caller. -/
def Terminal (state : OpenConf) : Prop :=
  PLeaTTa.Terminal state.toConf ∧ state.frames = []

/-- Transfer the outer continuation into a typed frame and start the private
generator control.  The persistent component is retained, not copied into the
frame. -/
def enterFindall (state : OpenConf) (template : Atom) (sub : List Goal)
    (result : Atom) (rest : List Goal) (binding : Subst) : OpenConf :=
  let frame : FindallFrame :=
    { preCut := state.scopes.nextCutScope
      preCollection := state.scopes.nextCollectionScope
      outer := state.control
      template := template
      result := result
      rest := rest
      binding := binding }
  { state.stepOpen (subConfOf state.toConf sub binding template) with
    frames := .findall frame :: state.frames
    scopes := state.scopes.afterFindall }

/-- Rejoin a terminal generator.  Only the bag and suspended control are
restored; the persistent world and high-water come exclusively from `inner`. -/
def resumeFindall (inner : OpenConf) (frame : FindallFrame)
    (remaining : List Frame) : OpenConf :=
  let copied :=
    copyFindallBag inner.persistent.counter inner.control.answerValues
  { persistent := { inner.persistent with counter := copied.counter }
    control :=
      { frame.outer with
        cur := some
          (Goal.eq frame.result (chainOf copied.values) ::
            frame.rest, frame.binding) }
    frames := remaining
    scopes := inner.scopes }

/-- Rejoin from an already-certified copied bag.  This is the local fine
copy lane's exit; unlike `resumeFindall`, it performs no copying itself. -/
def resumeFindallCopied (persistent : Persistent)
    (scopes : ScopeHighWaters) (frame : FindallFrame)
    (remaining : List Frame) (copiedValues : List Atom) : OpenConf :=
  { persistent := persistent
    control :=
      { frame.outer with
        cur := some
          (Goal.eq frame.result (chainOf copiedValues) ::
            frame.rest, frame.binding) }
    frames := remaining
    scopes := scopes }

/-- The atomic collector is exactly rejoining the certified batch result. -/
theorem resumeFindall_eq_copied (inner : OpenConf)
    (frame : FindallFrame) (remaining : List Frame) :
    resumeFindall inner frame remaining =
      resumeFindallCopied
        { inner.persistent with
          counter :=
            (copyFindallBag inner.persistent.counter
              inner.control.answerValues).counter }
        inner.scopes
        frame remaining
        (copyFindallBag inner.persistent.counter
          inner.control.answerValues).values := by
  rfl

/-- The suspended frame generated from a plain outer machine state at one
explicit fine-lane frontier.  Requiring `scopes` prevents macro proofs from
defaulting or reconstructing the historical occurrence indices. -/
def findallFrameOf (outer : Conf) (scopes : ScopeHighWaters)
    (template result : Atom)
    (rest : List Goal) (binding : Subst) : FindallFrame :=
  { preCut := scopes.nextCutScope
    preCollection := scopes.nextCollectionScope
    outer := controlOf outer
    template := template
    result := result
    rest := rest
    binding := binding }

/-- Exact atomic successor used by the sealed `Step.findall` constructor. -/
def findallSuccessor (outer inner : Conf) (result : Atom)
    (rest : List Goal) (binding : Subst) : Conf :=
  rejoinFindall outer inner result rest binding

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

/-- Exact open-state successor of one private generator answer.  `stepOpen`
is load-bearing: it carries the live frame stack and all typed scope
high-waters instead of reconstructing either from the sealed configuration. -/
def privateAnswerTarget (state : OpenConf) (binding : Subst) : OpenConf :=
  state.stepOpen (answerSuccessor state.toConf binding)

/-- Pulling the next alternative cannot alter the non-backtrackable world or
fresh high-water. -/
@[simp] theorem privateAnswer_pull_persistent (conf : Conf) :
    persistentOf (pull conf) = persistentOf conf := by
  unfold pull persistentOf
  generalize pullAuxTracked conf.barriers conf.alts = result
  rcases result with ⟨next, cache⟩
  cases next <;> rfl

/-- World state is outside the backtrackable alternative bank. -/
@[simp] theorem privateAnswer_pull_world (conf : Conf) :
    (pull conf).world = conf.world := by
  unfold pull
  generalize pullAuxTracked conf.barriers conf.alts = result
  rcases result with ⟨next, cache⟩
  cases next <;> rfl

/-- The general-purpose fresh counter is likewise outside the alternative
bank. -/
@[simp] theorem privateAnswer_pull_counter (conf : Conf) :
    (pull conf).counter = conf.counter := by
  unfold pull
  generalize pullAuxTracked conf.barriers conf.alts = result
  rcases result with ⟨next, cache⟩
  cases next <;> rfl

/-- Pulling changes control position only; the observable query term remains
the one installed when the private generator was entered. -/
@[simp] theorem privateAnswer_pull_qterm (conf : Conf) :
    (pull conf).qterm = conf.qterm := by
  unfold pull
  generalize pullAuxTracked conf.barriers conf.alts = result
  rcases result with ⟨next, cache⟩
  cases next <;> rfl

/-- Pulling cannot rewrite the reverse-discovery answer accumulator. -/
@[simp] theorem privateAnswer_pull_answers (conf : Conf) :
    (pull conf).answers = conf.answers := by
  unfold pull
  generalize pullAuxTracked conf.barriers conf.alts = result
  rcases result with ⟨next, cache⟩
  cases next <;> rfl

@[simp] theorem privateAnswerTarget_frames
    (state : OpenConf) (binding : Subst) :
    (privateAnswerTarget state binding).frames = state.frames := rfl

@[simp] theorem privateAnswerTarget_scopes
    (state : OpenConf) (binding : Subst) :
    (privateAnswerTarget state binding).scopes = state.scopes := rfl

@[simp] theorem privateAnswerTarget_persistent
    (state : OpenConf) (binding : Subst) :
    (privateAnswerTarget state binding).persistent = state.persistent := by
  simp [privateAnswerTarget, OpenConf.stepOpen, OpenConf.ofConfWith,
    answerSuccessor, OpenConf.toConf, Control.toConf, persistentOf]

@[simp] theorem privateAnswerTarget_qterm
    (state : OpenConf) (binding : Subst) :
    (privateAnswerTarget state binding).control.qterm =
      state.control.qterm := by
  simp [privateAnswerTarget, OpenConf.stepOpen, OpenConf.ofConfWith,
    answerSuccessor, OpenConf.toConf, Control.toConf, controlOf]

@[simp] theorem privateAnswerTarget_answers
    (state : OpenConf) (binding : Subst) :
    (privateAnswerTarget state binding).control.answers =
      subst binding state.control.qterm :: state.control.answers := by
  simp [privateAnswerTarget, OpenConf.stepOpen, OpenConf.ofConfWith,
    answerSuccessor, OpenConf.toConf, Control.toConf, controlOf]

@[simp] theorem enterFindall_ofConfWith (outer : Conf) (frames : List Frame)
    (scopes : ScopeHighWaters)
    (template : Atom) (sub : List Goal) (result : Atom)
    (rest : List Goal) (binding : Subst) :
    enterFindall (OpenConf.ofConfWith outer frames scopes)
        template sub result rest binding =
      OpenConf.ofConfWith (subConfOf outer sub binding template)
        (.findall
          (findallFrameOf outer scopes template result rest binding) ::
          frames)
        scopes.afterFindall := by
  rfl

@[simp] theorem enterFindall_ofConf (outer : Conf) (frames : List Frame)
    (template : Atom) (sub : List Goal) (result : Atom)
    (rest : List Goal) (binding : Subst) :
    enterFindall (OpenConf.ofConf outer frames) template sub result rest binding =
      OpenConf.ofConfWith (subConfOf outer sub binding template)
        (.findall
          (findallFrameOf outer {} template result rest binding) ::
          frames)
        ({} : ScopeHighWaters).afterFindall := by
  rfl

@[simp] theorem resumeFindall_ofConfWith (outer inner : Conf)
    (frames : List Frame) (entryScopes currentScopes : ScopeHighWaters)
    (template result : Atom)
    (rest : List Goal) (binding : Subst) :
    resumeFindall
        (OpenConf.ofConfWith inner
          (.findall
            (findallFrameOf outer entryScopes template result rest binding) ::
            frames)
          currentScopes)
        (findallFrameOf outer entryScopes template result rest binding)
        frames =
      OpenConf.ofConfWith
        (findallSuccessor outer inner result rest binding) frames
        currentScopes := by
  cases outer
  cases inner
  rfl

@[simp] theorem resumeFindall_ofConf (outer inner : Conf)
    (frames : List Frame) (template result : Atom)
    (rest : List Goal) (binding : Subst) :
    resumeFindall
        (OpenConf.ofConf inner
          (.findall
            (findallFrameOf outer {} template result rest binding) ::
            frames))
        (findallFrameOf outer {} template result rest binding) frames =
      OpenConf.ofConf (findallSuccessor outer inner result rest binding)
        frames := by
  exact resumeFindall_ofConfWith outer inner frames {}
    {} template result rest binding

@[simp] theorem enterFindall_persistent (state : OpenConf)
    (template : Atom) (sub : List Goal) (result : Atom) (rest : List Goal)
    (binding : Subst) :
    (enterFindall state template sub result rest binding).persistent =
      state.persistent := by
  cases state with
  | mk persistent control frames scopes =>
      cases persistent
      rfl

@[simp] theorem resumeFindall_persistent (inner : OpenConf)
    (frame : FindallFrame) (remaining : List Frame) :
    (resumeFindall inner frame remaining).persistent =
      { inner.persistent with
        counter :=
          (copyFindallBag inner.persistent.counter
            inner.control.answerValues).counter } := rfl

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
  simp [ownedAlts, enterFindall, controlOf, subConfOf,
    OpenConf.stepOpen, OpenConf.ofConfWith, Frame.suspendedAlts]

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
      Step prog gt state (state.stepOpen next)
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

/-- Collector allocation is witnessed by the actual fine entry transition,
not merely by the allocator helper.  The exception bank is the negative
control: `findall/3` cannot consume from it. -/
theorem findall_entry_scopes_exact
    (prog : Prog) (gt : GroundingTable) (state : OpenConf)
    (template : Atom) (sub : List Goal) (result : Atom)
    (rest : List Goal) (binding : Subst)
    (head : state.toConf.cur =
      some (Goal.findall template sub result :: rest, binding)) :
    Step prog gt state
        (enterFindall state template sub result rest binding) ∧
      (enterFindall state template sub result rest binding).scopes.nextCutScope =
        state.scopes.nextCutScope + 1 ∧
      (enterFindall state template sub result rest
          binding).scopes.nextExceptionScope =
        state.scopes.nextExceptionScope ∧
      (enterFindall state template sub result rest
          binding).scopes.nextCollectionScope =
        state.scopes.nextCollectionScope + 1 := by
  refine ⟨.findallEnter state template sub result rest binding head, ?_⟩
  simp [enterFindall]

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

/-- A bracketed terminating execution for the currently fine-grained
`findall` fragment.  Ordinary sealed steps remain one step; a collector owns
one recursively structured inner run plus its entry and exit.  This gives one
induction principle for arbitrarily nested terminating collectors without
turning their nonterminal prefixes into atomic steps. -/
inductive MacroStepsN (prog : Prog) (gt : GroundingTable) :
    Nat → Conf → ScopeHighWaters → Conf → ScopeHighWaters → Prop where
  | zero (state : Conf) (scopes : ScopeHighWaters) :
      MacroStepsN prog gt 0 state scopes state scopes
  | ordinary (n : Nat) (before middle after : Conf)
      (scopes finalScopes : ScopeHighWaters)
      (notFindall : ¬ findallRunHead before)
      (step : PLeaTTa.Step prog gt before middle)
      (tail : MacroStepsN prog gt n middle scopes after finalScopes) :
      MacroStepsN prog gt (n + 1) before scopes after finalScopes
  | findall (innerCount tailCount : Nat) (outer inner finish : Conf)
      (outerScopes innerScopes finishScopes : ScopeHighWaters)
      (template : Atom) (sub : List Goal) (result : Atom)
      (rest : List Goal) (binding : Subst)
      (head : outer.cur =
        some (Goal.findall template sub result :: rest, binding))
      (innerRun : MacroStepsN prog gt innerCount
        (subConfOf outer sub binding template) outerScopes.afterFindall
        inner innerScopes)
      (done : PLeaTTa.Terminal inner)
      (tail : MacroStepsN prog gt tailCount
        (findallSuccessor outer inner result rest binding) innerScopes
        finish finishScopes) :
      MacroStepsN prog gt (innerCount + 2 + tailCount)
        outer outerScopes finish finishScopes

namespace MacroStepsN

/-- Sequential composition of bracketed runs.  This is the algebra used by
the prefix parser when an open collector closes and rejoins its caller. -/
theorem trans {prog : Prog} {gt : GroundingTable}
    {left middle right : Conf} {m n : Nat}
    {leftScopes middleScopes rightScopes : ScopeHighWaters}
    (first : MacroStepsN prog gt m
      left leftScopes middle middleScopes)
    (second : MacroStepsN prog gt n
      middle middleScopes right rightScopes) :
    MacroStepsN prog gt (m + n) left leftScopes right rightScopes := by
  induction first with
  | zero state scopes => simpa using second
  | ordinary k before stepMiddle after scopes finalScopes notFindall step tail
      tailIH =>
      have combined :=
        MacroStepsN.ordinary (k + n) before stepMiddle right
          scopes rightScopes notFindall step (tailIH second)
      have lengthEq : k + n + 1 = k + 1 + n := by omega
      rw [lengthEq] at combined
      exact combined
  | findall innerCount tailCount outer inner finish outerScopes innerScopes
      finishScopes template sub result rest binding head innerRun done tail
      innerIH tailIH =>
      simpa [Nat.add_assoc] using
        MacroStepsN.findall innerCount (tailCount + n) outer inner right
          outerScopes innerScopes rightScopes template sub result rest binding
          head innerRun done (tailIH second)

/-- Erasing fine collector boundaries from a structured terminating run gives
an ordinary sealed run.  Nested collectors collapse recursively. -/
theorem toStepStar {prog : Prog} {gt : GroundingTable}
    {n : Nat} {before after : Conf}
    {beforeScopes afterScopes : ScopeHighWaters}
    (execution : MacroStepsN prog gt n
      before beforeScopes after afterScopes) :
    PLeaTTa.StepStar prog gt before after := by
  induction execution with
  | zero state scopes => exact .refl state
  | ordinary n before middle after scopes finalScopes _ step _ tailIH =>
      exact .tail before middle after step tailIH
  | findall innerCount tailCount outer inner finish outerScopes innerScopes
      finishScopes template sub result rest binding head innerRun done tail
      innerIH tailIH =>
      apply PLeaTTa.StepStar.tail outer
        (findallSuccessor outer inner result rest binding) finish
      · simpa [findallSuccessor] using
          (PLeaTTa.Step.findall outer inner template sub result rest binding
            head innerIH done :
            PLeaTTa.Step prog gt outer
              (findallSuccessor outer inner result rest binding))
      · exact tailIH

/-- Expanding a structured terminating run under any fixed suspended frame
stack gives its exact fine-step count.  Every nested collector contributes
one entry and one exit; every private inner transition remains present. -/
theorem lift {prog : Prog} {gt : GroundingTable}
    {n : Nat} {before after : Conf}
    {beforeScopes afterScopes : ScopeHighWaters}
    (frames : List Frame)
    (execution : MacroStepsN prog gt n
      before beforeScopes after afterScopes) :
    StepsN prog gt n (OpenConf.ofConfWith before frames beforeScopes)
      (OpenConf.ofConfWith after frames afterScopes) := by
  induction execution generalizing frames with
  | zero state scopes => exact .zero _
  | ordinary n before middle after scopes finalScopes notFindall machineStep
      tail tailIH =>
      apply StepsN.succ n _
        (OpenConf.ofConfWith middle frames scopes) _
      · exact .ordinary _ middle (by simpa using notFindall)
          (by simpa using machineStep)
      · exact tailIH frames
  | findall innerCount tailCount outer inner finish outerScopes innerScopes
      finishScopes template sub result rest binding head innerRun done tail
      innerIH tailIH =>
      let frame :=
        findallFrameOf outer outerScopes template result rest binding
      let entered :=
        OpenConf.ofConfWith (subConfOf outer sub binding template)
          (.findall frame :: frames) outerScopes.afterFindall
      let resumed :=
        OpenConf.ofConfWith
          (findallSuccessor outer inner result rest binding)
          frames innerScopes
      have entryStep : Step prog gt
          (OpenConf.ofConfWith outer frames outerScopes) entered := by
        simpa [entered, frame] using
          (Step.findallEnter
            (OpenConf.ofConfWith outer frames outerScopes)
            template sub result rest binding (by simpa using head))
      have entryRun : StepsN prog gt 1
          (OpenConf.ofConfWith outer frames outerScopes) entered := by
        simpa using StepsN.succ 0 _ entered entered entryStep (.zero entered)
      have nestedRun : StepsN prog gt innerCount entered
          (OpenConf.ofConfWith inner
            (.findall frame :: frames) innerScopes) := by
        simpa [entered] using innerIH (.findall frame :: frames)
      have exitStep : Step prog gt
          (OpenConf.ofConfWith inner
            (.findall frame :: frames) innerScopes) resumed := by
        have exited :=
          Step.findallExit
            (OpenConf.ofConfWith inner
              (.findall frame :: frames) innerScopes)
            frame frames rfl
            (by simpa using done) (prog := prog) (gt := gt)
        rw [show
          resumeFindall
              (OpenConf.ofConfWith inner
                (.findall frame :: frames) innerScopes)
              frame frames =
            OpenConf.ofConfWith
              (findallSuccessor outer inner result rest binding)
              frames innerScopes by
            simpa only [frame] using
              (resumeFindall_ofConfWith outer inner frames outerScopes
                innerScopes template result rest binding)] at exited
        simpa [resumed] using exited
      have exitRun : StepsN prog gt 1
          (OpenConf.ofConfWith inner
            (.findall frame :: frames) innerScopes) resumed := by
        simpa using StepsN.succ 0 _ resumed resumed exitStep (.zero resumed)
      have tailRun : StepsN prog gt tailCount resumed
          (OpenConf.ofConfWith finish frames finishScopes) := by
        simpa [resumed] using tailIH frames
      have combined := entryRun.trans (nestedRun.trans (exitRun.trans tailRun))
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using combined

/-- Structured collector runs never roll back either allocator they own and
never consume an exception identity.  This is independent of the sealed
configuration projection, which deliberately cannot see these fields. -/
theorem scopes_mono {prog : Prog} {gt : GroundingTable}
    {n : Nat} {before after : Conf}
    {beforeScopes afterScopes : ScopeHighWaters}
    (execution : MacroStepsN prog gt n
      before beforeScopes after afterScopes) :
    beforeScopes.nextCutScope ≤ afterScopes.nextCutScope ∧
      beforeScopes.nextExceptionScope = afterScopes.nextExceptionScope ∧
      beforeScopes.nextCollectionScope ≤
        afterScopes.nextCollectionScope := by
  induction execution with
  | zero state scopes =>
      exact ⟨Nat.le_refl _, rfl, Nat.le_refl _⟩
  | ordinary n before middle after scopes finalScopes notFindall step tail
      tailIH =>
      exact tailIH
  | findall innerCount tailCount outer inner finish outerScopes innerScopes
      finishScopes template sub result rest binding head innerRun done tail
      innerIH tailIH =>
      rcases innerIH with
        ⟨innerCut, innerException, innerCollection⟩
      rcases tailIH with
        ⟨tailCut, tailException, tailCollection⟩
      constructor
      · simp only [ScopeHighWaters.afterFindall_cut] at innerCut
        omega
      constructor
      · simpa only [ScopeHighWaters.afterFindall_exception] using
          innerException.trans tailException
      · simp only [ScopeHighWaters.afterFindall_collection] at innerCollection
        omega

/-- Since `findall/3` is the only fine macro that advances either delimiter
bank, cut and collection allocations stay paired across every structured
terminating run.  This is deliberately local to `MacroStepsN`: the
call-aware source semantics also allocates cut scopes for ordinary local
calls, so this equation must not be exported as a cross-layer invariant. -/
theorem cut_collection_balance {prog : Prog} {gt : GroundingTable}
    {n : Nat} {before after : Conf}
    {beforeScopes afterScopes : ScopeHighWaters}
    (execution : MacroStepsN prog gt n
      before beforeScopes after afterScopes) :
    afterScopes.nextCutScope + beforeScopes.nextCollectionScope =
      afterScopes.nextCollectionScope + beforeScopes.nextCutScope := by
  induction execution with
  | zero state scopes =>
      omega
  | ordinary n before middle after scopes finalScopes notFindall step tail
      tailIH =>
      exact tailIH
  | findall innerCount tailCount outer inner finish outerScopes innerScopes
      finishScopes template sub result rest binding head innerRun done tail
      innerIH tailIH =>
      simp only [ScopeHighWaters.afterFindall_cut,
        ScopeHighWaters.afterFindall_collection] at innerIH
      omega

/-- A collector consumes one fresh cut and collection identity at entry, and
its tail retains every further allocation made by the nested generator.  In
particular, resuming from the stale post-entry frontier is not admitted. -/
theorem findall_retains_nested_scopes {prog : Prog} {gt : GroundingTable}
    {innerCount tailCount : Nat} {outer inner finish : Conf}
    {outerScopes innerScopes finishScopes : ScopeHighWaters}
    {template result : Atom} {sub rest : List Goal} {binding : Subst}
    (innerRun : MacroStepsN prog gt innerCount
      (subConfOf outer sub binding template) outerScopes.afterFindall
      inner innerScopes)
    (tail : MacroStepsN prog gt tailCount
      (findallSuccessor outer inner result rest binding) innerScopes
      finish finishScopes) :
    outerScopes.nextCutScope < finishScopes.nextCutScope ∧
      outerScopes.nextCollectionScope <
        finishScopes.nextCollectionScope ∧
      innerScopes.nextCutScope ≤ finishScopes.nextCutScope ∧
      innerScopes.nextCollectionScope ≤
        finishScopes.nextCollectionScope := by
  rcases innerRun.scopes_mono with
    ⟨innerCut, innerException, innerCollection⟩
  rcases tail.scopes_mono with
    ⟨tailCut, tailException, tailCollection⟩
  simp only [ScopeHighWaters.afterFindall_cut] at innerCut
  simp only [ScopeHighWaters.afterFindall_collection] at innerCollection
  omega

/-- Two connected collector entries cannot reuse the first entry's
identities.  This is the arithmetic guard for both nested and sibling
collectors: the second body starts from the first body's actual output
frontier, not from a stale copy of the original state. -/
theorem two_findall_entries_accumulate {prog : Prog} {gt : GroundingTable}
    {firstCount secondCount : Nat}
    {firstStart firstFinish secondStart secondFinish : Conf}
    {startScopes middleScopes finishScopes : ScopeHighWaters}
    (firstBody : MacroStepsN prog gt firstCount
      firstStart startScopes.afterFindall firstFinish middleScopes)
    (secondBody : MacroStepsN prog gt secondCount
      secondStart middleScopes.afterFindall secondFinish finishScopes) :
    startScopes.nextCutScope + 2 ≤ finishScopes.nextCutScope ∧
      startScopes.nextCollectionScope + 2 ≤
        finishScopes.nextCollectionScope ∧
      startScopes.nextExceptionScope =
        finishScopes.nextExceptionScope := by
  rcases firstBody.scopes_mono with
    ⟨firstCut, firstException, firstCollection⟩
  rcases secondBody.scopes_mono with
    ⟨secondCut, secondException, secondCollection⟩
  simp only [ScopeHighWaters.afterFindall_cut] at firstCut secondCut
  simp only [ScopeHighWaters.afterFindall_collection] at firstCollection secondCollection
  simp only [ScopeHighWaters.afterFindall_exception] at firstException secondException
  omega

/-- Constructor-level anti-stale witness for sibling collectors.  The first
collector rejoins its actual tail frontier, `between` carries that frontier
to the second source head, and the second `MacroStepsN.findall` is constructed
there.  Thus the combined derivation itself—not merely arithmetic premises—
forces two distinct cut and collection allocations.  Reusing
`startScopes.afterFindall` at the second entry would make this construction
ill-typed.

The intervening run is explicit because a real first collector rejoins at
its result-unification goal before reaching its sibling. -/
theorem sibling_findalls_construct_and_accumulate
    {prog : Prog} {gt : GroundingTable}
    {firstInnerCount betweenCount secondInnerCount tailCount : Nat}
    {firstOuter firstInner secondOuter secondInner finish : Conf}
    {startScopes firstInnerScopes secondOuterScopes secondInnerScopes
      finishScopes : ScopeHighWaters}
    {firstTemplate secondTemplate firstResult secondResult : Atom}
    {firstSub firstRest secondSub secondRest : List Goal}
    {firstBinding secondBinding : Subst}
    (firstHead : firstOuter.cur =
      some (Goal.findall firstTemplate firstSub firstResult :: firstRest,
        firstBinding))
    (firstInnerRun : MacroStepsN prog gt firstInnerCount
      (subConfOf firstOuter firstSub firstBinding firstTemplate)
      startScopes.afterFindall firstInner firstInnerScopes)
    (firstDone : PLeaTTa.Terminal firstInner)
    (between : MacroStepsN prog gt betweenCount
      (findallSuccessor firstOuter firstInner firstResult firstRest
        firstBinding)
      firstInnerScopes secondOuter secondOuterScopes)
    (secondHead : secondOuter.cur =
      some (Goal.findall secondTemplate secondSub secondResult :: secondRest,
        secondBinding))
    (secondInnerRun : MacroStepsN prog gt secondInnerCount
      (subConfOf secondOuter secondSub secondBinding secondTemplate)
      secondOuterScopes.afterFindall secondInner secondInnerScopes)
    (secondDone : PLeaTTa.Terminal secondInner)
    (tail : MacroStepsN prog gt tailCount
      (findallSuccessor secondOuter secondInner secondResult secondRest
        secondBinding)
      secondInnerScopes finish finishScopes) :
    ∃ _ : MacroStepsN prog gt
        (firstInnerCount + 2 +
          (betweenCount + (secondInnerCount + 2 + tailCount)))
        firstOuter startScopes finish finishScopes,
      startScopes.nextCutScope + 2 ≤ finishScopes.nextCutScope ∧
      startScopes.nextCollectionScope + 2 ≤
        finishScopes.nextCollectionScope ∧
      startScopes.nextExceptionScope =
        finishScopes.nextExceptionScope ∧
      finishScopes.nextCollectionScope ≠
        startScopes.nextCollectionScope + 1 := by
  let secondRun : MacroStepsN prog gt
      (secondInnerCount + 2 + tailCount)
      secondOuter secondOuterScopes finish finishScopes :=
    .findall secondInnerCount tailCount secondOuter secondInner finish
      secondOuterScopes secondInnerScopes finishScopes secondTemplate
      secondSub secondResult secondRest secondBinding secondHead
      secondInnerRun secondDone tail
  let firstTail : MacroStepsN prog gt
      (betweenCount + (secondInnerCount + 2 + tailCount))
      (findallSuccessor firstOuter firstInner firstResult firstRest
        firstBinding)
      firstInnerScopes finish finishScopes :=
    between.trans secondRun
  let execution : MacroStepsN prog gt
      (firstInnerCount + 2 +
        (betweenCount + (secondInnerCount + 2 + tailCount)))
      firstOuter startScopes finish finishScopes :=
    .findall firstInnerCount
      (betweenCount + (secondInnerCount + 2 + tailCount))
      firstOuter firstInner finish startScopes firstInnerScopes finishScopes
      firstTemplate firstSub firstResult firstRest firstBinding firstHead
      firstInnerRun firstDone firstTail
  rcases firstInnerRun.scopes_mono with
    ⟨firstInnerCut, firstInnerException, firstInnerCollection⟩
  rcases between.scopes_mono with
    ⟨betweenCut, betweenException, betweenCollection⟩
  rcases secondInnerRun.scopes_mono with
    ⟨secondInnerCut, secondInnerException, secondInnerCollection⟩
  rcases tail.scopes_mono with
    ⟨tailCut, tailException, tailCollection⟩
  simp only [ScopeHighWaters.afterFindall_cut] at firstInnerCut secondInnerCut
  simp only [ScopeHighWaters.afterFindall_collection] at firstInnerCollection secondInnerCollection
  simp only [ScopeHighWaters.afterFindall_exception] at firstInnerException secondInnerException
  exact ⟨execution, by omega, by omega, by omega, by omega⟩

end MacroStepsN

/-- A parsed fine prefix relative to a protected caller-frame suffix.  A
`closed` prefix has returned to that suffix.  An `open` prefix records the
already completed caller macro, the pending collector entry, and recursively
parses the active generator above the newly pushed frame. -/
inductive MacroPrefixN (prog : Prog) (gt : GroundingTable) :
    List Frame → Nat → Conf → ScopeHighWaters → OpenConf → Prop where
  | closed (baseFrames : List Frame) (n : Nat) (start finish : Conf)
      (startScopes finishScopes : ScopeHighWaters)
      (run : MacroStepsN prog gt n
        start startScopes finish finishScopes) :
      MacroPrefixN prog gt baseFrames n start startScopes
        (OpenConf.ofConfWith finish baseFrames finishScopes)
  | suspended (baseFrames : List Frame) (beforeCount innerCount : Nat)
      (start outer : Conf)
      (startScopes outerScopes : ScopeHighWaters)
      (template : Atom) (sub : List Goal) (result : Atom)
      (rest : List Goal) (binding : Subst) (target : OpenConf)
      (before : MacroStepsN prog gt beforeCount
        start startScopes outer outerScopes)
      (head : outer.cur =
        some (Goal.findall template sub result :: rest, binding))
      (inner : MacroPrefixN prog gt
        (.findall
          (findallFrameOf outer outerScopes template result rest binding) ::
          baseFrames)
        innerCount (subConfOf outer sub binding template)
        outerScopes.afterFindall target) :
      MacroPrefixN prog gt baseFrames (beforeCount + 1 + innerCount)
        start startScopes target

namespace MacroPrefixN

/-- One fine step cannot cross a protected frame suffix when its source owns
at least one frame above that suffix.  An exit removes only the unique top
frame; ordinary work preserves the stack and entry adds one. -/
theorem step_preserves_suffix_of_strict {prog : Prog} {gt : GroundingTable}
    {baseFrames : List Frame} {before after : OpenConf}
    (strict : ∃ top extra,
      before.frames = top :: (extra ++ baseFrames))
    (step : Step prog gt before after) :
    ∃ extra, after.frames = extra ++ baseFrames := by
  rcases strict with ⟨top, extra, framesEq⟩
  cases step with
  | ordinary next notFindall machineStep =>
      exact ⟨top :: extra, by simpa using framesEq⟩
  | findallEnter template sub result rest binding head =>
      refine ⟨.findall
        { preCut := before.scopes.nextCutScope
          preCollection := before.scopes.nextCollectionScope
          outer := before.control
          template := template
          result := result
          rest := rest
          binding := binding } :: top :: extra, ?_⟩
      simp [enterFindall, framesEq]
  | findallExit frame remaining frameHead done =>
      rw [framesEq] at frameHead
      injection frameHead with _ tailEq
      exact ⟨extra, by simpa [resumeFindall] using tailEq.symm⟩

/-- Every parsed target owns a stack extending its protected caller suffix. -/
theorem frames_suffix {prog : Prog} {gt : GroundingTable}
    {baseFrames : List Frame} {n : Nat} {start : Conf}
    {startScopes : ScopeHighWaters} {target : OpenConf}
    (parsed : MacroPrefixN prog gt
      baseFrames n start startScopes target) :
    ∃ extra, target.frames = extra ++ baseFrames := by
  induction parsed with
  | closed => exact ⟨[], rfl⟩
  | suspended baseFrames beforeCount innerCount start outer startScopes
      outerScopes template sub result rest binding target before head inner
      innerIH =>
      rcases innerIH with ⟨extra, framesEq⟩
      refine ⟨extra ++ [.findall
        (findallFrameOf outer outerScopes template result rest binding)], ?_⟩
      rw [framesEq, List.append_assoc]
      rfl

/-- An open parser state owns at least one frame above the protected suffix. -/
theorem open_frames_cons_suffix {prog : Prog} {gt : GroundingTable}
    {baseFrames : List Frame} {beforeCount innerCount : Nat}
    {start outer : Conf} {template : Atom} {sub : List Goal}
    {result : Atom} {rest : List Goal} {binding : Subst}
    {startScopes outerScopes : ScopeHighWaters}
    {target : OpenConf}
    (_before : MacroStepsN prog gt beforeCount
      start startScopes outer outerScopes)
    (_head : outer.cur =
      some (Goal.findall template sub result :: rest, binding))
    (inner : MacroPrefixN prog gt
      (.findall
        (findallFrameOf outer outerScopes template result rest binding) ::
        baseFrames)
      innerCount (subConfOf outer sub binding template)
      outerScopes.afterFindall target) :
    ∃ top extra, target.frames = top :: (extra ++ baseFrames) := by
  rcases inner.frames_suffix with ⟨extra, framesEq⟩
  cases extra with
  | nil =>
      exact ⟨.findall
        (findallFrameOf outer outerScopes template result rest binding), [],
        by simpa using framesEq⟩
  | cons top tail =>
      refine ⟨top,
        tail ++ [.findall
          (findallFrameOf outer outerScopes template result rest binding)],
        ?_⟩
      rw [framesEq]
      simp only [List.cons_append, List.append_assoc]
      rfl

/-- Extend a parsed prefix by one fine step without crossing its protected
caller suffix.  The only non-local case is an exit: a closed inner parser is
folded into one `MacroStepsN.findall`, whereas an exit above a still-open
inner parser is delegated recursively. -/
theorem advance {prog : Prog} {gt : GroundingTable}
    {baseFrames : List Frame} {n : Nat} {start : Conf}
    {startScopes : ScopeHighWaters}
    {before after : OpenConf}
    (parsed : MacroPrefixN prog gt
      baseFrames n start startScopes before)
    (oneStep : Step prog gt before after)
    (afterSuffix : ∃ extra, after.frames = extra ++ baseFrames) :
    MacroPrefixN prog gt baseFrames (n + 1)
      start startScopes after := by
  induction parsed generalizing after with
  | closed baseFrames n start finish startScopes finishScopes run =>
      cases oneStep with
      | ordinary next notFindall machineStep =>
          let tail : MacroStepsN prog gt 1
              finish finishScopes next finishScopes :=
            .ordinary 0 finish next next finishScopes finishScopes
              notFindall machineStep (.zero next finishScopes)
          simpa [OpenConf.stepOpen, OpenConf.ofConfWith, OpenConf.ofConf] using
            MacroPrefixN.closed baseFrames (n + 1) start next
              startScopes finishScopes
              (run.trans tail)
      | findallEnter template sub result rest binding head =>
          let frame :=
            findallFrameOf finish finishScopes template result rest binding
          let innerStart := subConfOf finish sub binding template
          have inner : MacroPrefixN prog gt (.findall frame :: baseFrames) 0
              innerStart finishScopes.afterFindall
              (OpenConf.ofConfWith innerStart
                (.findall frame :: baseFrames)
                finishScopes.afterFindall) :=
            .closed _ 0 innerStart innerStart
              finishScopes.afterFindall finishScopes.afterFindall
              (.zero innerStart finishScopes.afterFindall)
          simpa [frame, innerStart] using
            MacroPrefixN.suspended baseFrames n 0 start finish
              startScopes finishScopes template sub result rest binding _
              run (by simpa using head) inner
      | findallExit frame remaining frameHead done =>
          rcases afterSuffix with ⟨extra, afterFrames⟩
          have baseEq : baseFrames = .findall frame :: remaining := by
            simpa using frameHead
          have remainingEq : remaining = extra ++ baseFrames := by
            simpa [resumeFindall] using afterFrames
          have longer := congrArg List.length baseEq
          have shorter := congrArg List.length remainingEq
          simp at longer shorter
          omega
  | suspended baseFrames beforeCount innerCount start outer startScopes
      outerScopes template sub result rest binding target beforeRun head
      innerParsed innerIH =>
      cases oneStep with
      | ordinary next notFindall machineStep =>
          rcases innerParsed.frames_suffix with ⟨extra, targetFrames⟩
          have recursiveStep : Step prog gt target
              (target.stepOpen next) :=
            .ordinary target next notFindall machineStep
          have recursiveSuffix : ∃ more,
              (target.stepOpen next).frames =
                more ++
                  (.findall
                    (findallFrameOf outer outerScopes template result rest
                      binding) ::
                    baseFrames) :=
            ⟨extra, by simpa using targetFrames⟩
          have advanced := innerIH recursiveStep recursiveSuffix
          have rebuilt := MacroPrefixN.suspended baseFrames beforeCount
            (innerCount + 1) start outer startScopes outerScopes
            template sub result rest binding _ beforeRun head advanced
          simpa [Nat.add_assoc] using rebuilt
      | findallEnter nestedTemplate nestedSub nestedResult nestedRest
          nestedBinding nestedHead =>
          rcases innerParsed.frames_suffix with ⟨extra, targetFrames⟩
          let nestedFrame :=
            { preCut := target.scopes.nextCutScope
              preCollection := target.scopes.nextCollectionScope
              outer := target.control
              template := nestedTemplate
              result := nestedResult
              rest := nestedRest
              binding := nestedBinding : FindallFrame }
          have recursiveStep : Step prog gt target
              (enterFindall target nestedTemplate nestedSub nestedResult
                nestedRest nestedBinding) :=
            .findallEnter target nestedTemplate nestedSub nestedResult
              nestedRest nestedBinding nestedHead
          have recursiveSuffix : ∃ more,
              (enterFindall target nestedTemplate nestedSub nestedResult
                nestedRest nestedBinding).frames =
                more ++
                  (.findall
                    (findallFrameOf outer outerScopes template result rest
                      binding) ::
                    baseFrames) := by
            refine ⟨.findall nestedFrame :: extra, ?_⟩
            simp [enterFindall, nestedFrame, targetFrames]
          have advanced := innerIH recursiveStep recursiveSuffix
          have rebuilt := MacroPrefixN.suspended baseFrames beforeCount
            (innerCount + 1) start outer startScopes outerScopes
            template sub result rest binding _ beforeRun head advanced
          simpa [Nat.add_assoc] using rebuilt
      | findallExit exitFrame remaining frameHead done =>
          cases innerParsed with
          | closed innerBase innerCount innerStart innerFinish
              innerStartScopes innerFinishScopes innerRun =>
              have frameEq :
                  findallFrameOf outer outerScopes template result rest
                    binding =
                    exitFrame := by
                simpa using congrArg List.head? frameHead
              have remainingEq : baseFrames = remaining := by
                simpa using congrArg List.tail frameHead
              subst exitFrame
              subst remaining
              let successor :=
                findallSuccessor outer innerFinish result rest binding
              let collector : MacroStepsN prog gt (innerCount + 2)
                  outer outerScopes successor innerFinishScopes :=
                .findall innerCount 0 outer innerFinish successor
                  outerScopes innerFinishScopes innerFinishScopes
                  template sub result rest binding head innerRun
                  (by simpa using done)
                  (.zero successor innerFinishScopes)
              have combined := beforeRun.trans collector
              have combined' : MacroStepsN prog gt
                  ((beforeCount + 1 + innerCount) + 1)
                  start startScopes successor innerFinishScopes := by
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                  combined
              rw [show
                resumeFindall
                    (OpenConf.ofConfWith innerFinish
                      (.findall
                        (findallFrameOf outer outerScopes template result
                          rest binding) :: baseFrames)
                      innerFinishScopes)
                    (findallFrameOf outer outerScopes template result rest
                      binding)
                    baseFrames =
                  OpenConf.ofConfWith successor baseFrames innerFinishScopes by
                simpa only [successor] using
                  (resumeFindall_ofConfWith outer innerFinish baseFrames
                    outerScopes innerFinishScopes template result rest
                    binding)]
              simpa [successor] using
                MacroPrefixN.closed baseFrames _ start successor
                  startScopes innerFinishScopes combined'
          | suspended nestedBase nestedBeforeCount nestedInnerCount nestedStart
              nestedOuter nestedStartScopes nestedOuterScopes nestedTemplate
              nestedSub nestedResult nestedRest nestedBinding nestedTarget
              nestedBefore nestedHead nestedInner =>
              have strict : ∃ top extra,
                  target.frames = top ::
                    (extra ++
                      (.findall
                        (findallFrameOf outer outerScopes template result rest
                          binding) ::
                        baseFrames)) :=
                open_frames_cons_suffix nestedBefore nestedHead nestedInner
              have recursiveStep : Step prog gt target
                  (resumeFindall target exitFrame remaining) :=
                .findallExit target exitFrame remaining frameHead done
              have recursiveSuffix :=
                step_preserves_suffix_of_strict strict recursiveStep
              have advanced := innerIH recursiveStep recursiveSuffix
              have rebuilt := MacroPrefixN.suspended baseFrames beforeCount
                _ start outer startScopes outerScopes template sub result rest
                binding _ beforeRun head advanced
              simpa [Nat.add_assoc] using rebuilt

/-- Extend a top-level parsed prefix by an arbitrary fine run.  With no
protected caller frames, every intermediate target trivially has the empty
list as a suffix, so `advance` can be iterated without an additional safety
premise. -/
theorem extendRoot {prog : Prog} {gt : GroundingTable}
    {m n : Nat} {start : Conf} {startScopes : ScopeHighWaters}
    {before after : OpenConf}
    (parsed : MacroPrefixN prog gt [] m start startScopes before)
    (execution : StepsN prog gt n before after) :
    MacroPrefixN prog gt [] (m + n) start startScopes after := by
  induction execution generalizing m start startScopes with
  | zero state => simpa using parsed
  | succ count before middle after oneStep tail tailIH =>
      have middleSuffix : ∃ extra, middle.frames = extra ++ ([] : List Frame) :=
        ⟨middle.frames, by simp⟩
      have advanced := parsed.advance oneStep middleSuffix
      have finished := tailIH advanced
      have countEq : (m + 1) + count = m + (count + 1) := by omega
      rw [countEq] at finished
      exact finished

/-- Parse any top-level fine run into either a closed macro run or an explicit
stack of unpaired collector entries. -/
theorem ofRootSteps {prog : Prog} {gt : GroundingTable}
    {n : Nat} {start : Conf} {startScopes : ScopeHighWaters}
    {target : OpenConf}
    (execution : StepsN prog gt n
      (OpenConf.ofConfWith start [] startScopes) target) :
    MacroPrefixN prog gt [] n start startScopes target := by
  have initial : MacroPrefixN prog gt [] 0 start startScopes
      (OpenConf.ofConfWith start [] startScopes) :=
    .closed [] 0 start start startScopes startScopes
      (.zero start startScopes)
  simpa using initial.extendRoot execution

/-- A top-level parsed prefix is either a closed macro with an exact plain
endpoint, or it still owns at least one suspended collector frame. -/
theorem root_closed_or_has_frames {prog : Prog} {gt : GroundingTable}
    {n : Nat} {start : Conf} {startScopes : ScopeHighWaters}
    {target : OpenConf}
    (parsed : MacroPrefixN prog gt [] n start startScopes target) :
    (∃ finish finishScopes,
        target = OpenConf.ofConfWith finish [] finishScopes ∧
        MacroStepsN prog gt n
          start startScopes finish finishScopes) ∨
      target.frames ≠ [] := by
  cases parsed with
  | closed baseFrames count parsedStart parsedFinish parsedStartScopes
      parsedFinishScopes run =>
      exact Or.inl ⟨parsedFinish, parsedFinishScopes, rfl, run⟩
  | suspended baseFrames beforeCount innerCount parsedStart outer
      parsedStartScopes outerScopes template sub result rest binding target
      beforeRun head inner =>
      right
      rcases open_frames_cons_suffix beforeRun head inner with
        ⟨top, extra, framesEq⟩
      intro emptyFrames
      rw [emptyFrames] at framesEq
      simp at framesEq

/-- Completeness of the bracket parser for closed top-level runs.  Returning
to an empty frame stack excludes the suspended case, so every such raw
`StepsN` derivation yields a `MacroStepsN` with the same exact count and
endpoints. -/
theorem closedRootSteps_complete {prog : Prog} {gt : GroundingTable}
    {n : Nat} {start finish : Conf}
    {startScopes finishScopes : ScopeHighWaters}
    (execution : StepsN prog gt n
      (OpenConf.ofConfWith start [] startScopes)
      (OpenConf.ofConfWith finish [] finishScopes)) :
    MacroStepsN prog gt n start startScopes finish finishScopes := by
  have parsed := ofRootSteps execution
  rcases parsed.root_closed_or_has_frames with
    ⟨parsedFinish, parsedFinishScopes, endpoint, run⟩ | stillOpen
  · have finishEq : finish = parsedFinish := by
      have projected := congrArg OpenConf.toConf endpoint
      simpa using projected
    subst parsedFinish
    have scopesEq : finishScopes = parsedFinishScopes := by
      have projected := congrArg OpenConf.scopes endpoint
      simpa using projected
    subst parsedFinishScopes
    exact run
  · exact False.elim (stillOpen rfl)

/-- Exact terminating-run correspondence for the fine `findall` lane.  This
is count-preserving in both directions and includes arbitrary collector
nesting; open prefixes are intentionally outside the right-hand side. -/
theorem closedRootSteps_iff_macro {prog : Prog} {gt : GroundingTable}
    {n : Nat} {start finish : Conf}
    {startScopes finishScopes : ScopeHighWaters} :
    StepsN prog gt n
        (OpenConf.ofConfWith start [] startScopes)
        (OpenConf.ofConfWith finish [] finishScopes) ↔
      MacroStepsN prog gt n start startScopes finish finishScopes := by
  constructor
  · exact closedRootSteps_complete
  · intro structured
    exact MacroStepsN.lift [] structured

/-- Every closed top-level fine run is licensed by the sealed `StepStar`.
Unlike answer-list projection, this theorem is obtained only after the exact
frame-bracket parser has ruled out every unpaired open prefix. -/
theorem closedRootSteps_collapse_to_sealed {prog : Prog}
    {gt : GroundingTable} {n : Nat} {start finish : Conf}
    {startScopes finishScopes : ScopeHighWaters}
    (execution : StepsN prog gt n
      (OpenConf.ofConfWith start [] startScopes)
      (OpenConf.ofConfWith finish [] finishScopes)) :
    PLeaTTa.StepStar prog gt start finish :=
  (closedRootSteps_complete execution).toStepStar

end MacroPrefixN

/-- One arbitrarily nested terminating collector has both views at once: its
fine lane contains exactly entry, every recursively expanded inner step, and
exit, while its sealed view is exactly the existing atomic `findall` step.
This is the reusable terminating-run bridge; it does not claim that an
unstructured `StepsN` derivation has already been parsed into `MacroStepsN`. -/
theorem findall_nested_run_expands_and_collapses
    (prog : Prog) (gt : GroundingTable) (outer inner : Conf)
    (frames : List Frame) (scopes innerScopes : ScopeHighWaters)
    (template : Atom) (sub : List Goal)
    (result : Atom) (rest : List Goal) (binding : Subst) (n : Nat)
    (head : outer.cur =
      some (Goal.findall template sub result :: rest, binding))
    (innerRun : MacroStepsN prog gt n
      (subConfOf outer sub binding template) scopes.afterFindall
      inner innerScopes)
    (done : PLeaTTa.Terminal inner) :
    StepsN prog gt (n + 2)
        (OpenConf.ofConfWith outer frames scopes)
        (OpenConf.ofConfWith
          (findallSuccessor outer inner result rest binding)
          frames innerScopes) ∧
      PLeaTTa.Step prog gt outer
        (findallSuccessor outer inner result rest binding) := by
  let structured : MacroStepsN prog gt (n + 2)
      outer scopes
      (findallSuccessor outer inner result rest binding) innerScopes :=
    .findall n 0 outer inner
      (findallSuccessor outer inner result rest binding)
      scopes innerScopes innerScopes template sub result rest binding
      head innerRun done (.zero _ innerScopes)
  constructor
  · exact structured.lift frames
  · simpa [findallSuccessor] using
      (PLeaTTa.Step.findall outer inner template sub result rest binding head
        innerRun.toStepStar done :
        PLeaTTa.Step prog gt outer
          (findallSuccessor outer inner result rest binding))

/-- Concrete anti-vacuity witness: an empty generator goal-list succeeds once.
Its collector is therefore one sealed step but exactly three fine steps
(entry, private answer, exit). -/
theorem empty_generator_findall_is_three_fine_steps
    (prog : Prog) (gt : GroundingTable) (outer : Conf)
    (frames : List Frame) (template result : Atom)
    (rest : List Goal) (binding : Subst)
    (head : outer.cur =
      some (Goal.findall template [] result :: rest, binding)) :
    ∃ inner,
      PLeaTTa.Terminal inner ∧
      StepsN prog gt 3 (OpenConf.ofConf outer frames)
        (OpenConf.ofConfWith
          (findallSuccessor outer inner result rest binding)
          frames ({} : ScopeHighWaters).afterFindall) ∧
      PLeaTTa.Step prog gt outer
        (findallSuccessor outer inner result rest binding) := by
  let start := subConfOf outer [] binding template
  let inner := answerSuccessor start binding
  have answerStep : PLeaTTa.Step prog gt start inner := by
    exact PLeaTTa.Step.answer start binding (by rfl)
  have notFindall : ¬ findallRunHead start := by
    rintro ⟨otherTemplate, otherSub, otherResult, otherRest, otherBinding,
      conflict⟩
    simp [start, subConfOf] at conflict
  have done : PLeaTTa.Terminal inner := by
    cases hbarriers : outer.barriers <;>
      simp [inner, start, answerSuccessor, subConfOf, PLeaTTa.Terminal, pull,
        pullAuxTracked, pullAuxCached, pullAux, resetBarrierCache, hbarriers]
  have innerRun : MacroStepsN prog gt 1
      start ({} : ScopeHighWaters).afterFindall
      inner ({} : ScopeHighWaters).afterFindall := by
    simpa using MacroStepsN.ordinary 0 start inner inner
      ({} : ScopeHighWaters).afterFindall
      ({} : ScopeHighWaters).afterFindall
      notFindall answerStep
      (.zero inner ({} : ScopeHighWaters).afterFindall)
  have bridge := findall_nested_run_expands_and_collapses prog gt outer inner
    frames {} ({} : ScopeHighWaters).afterFindall
    template [] result rest binding 1 head innerRun done
  exact
    ⟨inner, done,
      by
        simpa [OpenConf.ofConf, OpenConf.ofConfWith] using bridge.1,
      bridge.2⟩

/-- An empty generator succeeds once, and the sealed collector copies its
residual variable before placing it in the bag.  The nested run still records
the raw source variable, while the atomic rejoin produces a distinct compact
name.  This pins the copy boundary rather than merely testing the helper in
isolation.

[SPEC SWI-Prolog manual, `findall/3`: template copies are made for every
solution] -/
theorem empty_generator_findall_copies_source_variable
    (prog : Prog) (gt : GroundingTable) (outer : Conf)
    (frames : List Frame) (source : String) (result : Atom)
    (rest : List Goal)
    (head : outer.cur =
      some (Goal.findall (.var source) [] result :: rest, [])) :
    ∃ inner,
      inner = answerSuccessor
        (subConfOf outer [] [] (.var source)) [] ∧
      PLeaTTa.Terminal inner ∧
      StepsN prog gt 3 (OpenConf.ofConf outer frames)
        (OpenConf.ofConfWith
          (findallSuccessor outer inner result rest [])
          frames ({} : ScopeHighWaters).afterFindall) ∧
      PLeaTTa.Step prog gt outer
        (findallSuccessor outer inner result rest []) ∧
      inner.answerValues = [.var source] ∧
      ∃ copiedName,
        (copyFindallBag inner.counter inner.answerValues).values =
          [.var copiedName] ∧ copiedName ≠ source := by
  let start := subConfOf outer [] [] (.var source)
  let inner := answerSuccessor start []
  have answerStep : PLeaTTa.Step prog gt start inner := by
    exact PLeaTTa.Step.answer start [] (by rfl)
  have notFindall : ¬ findallRunHead start := by
    rintro ⟨otherTemplate, otherSub, otherResult, otherRest, otherBinding,
      conflict⟩
    simp [start, subConfOf] at conflict
  have done : PLeaTTa.Terminal inner := by
    cases hbarriers : outer.barriers <;>
      simp [inner, start, answerSuccessor, subConfOf, PLeaTTa.Terminal, pull,
        pullAuxTracked, pullAuxCached, pullAux, resetBarrierCache, hbarriers]
  have innerRun : MacroStepsN prog gt 1
      start ({} : ScopeHighWaters).afterFindall
      inner ({} : ScopeHighWaters).afterFindall := by
    simpa using MacroStepsN.ordinary 0 start inner inner
      ({} : ScopeHighWaters).afterFindall
      ({} : ScopeHighWaters).afterFindall
      notFindall answerStep
      (.zero inner ({} : ScopeHighWaters).afterFindall)
  have bridge := findall_nested_run_expands_and_collapses prog gt outer inner
    frames {} ({} : ScopeHighWaters).afterFindall
    (.var source) [] result rest [] 1 head innerRun done
  have answers : inner.answerValues = [.var source] := by
    cases hbarriers : outer.barriers <;>
      simp [inner, start, answerSuccessor, subConfOf, Conf.answerValues, pull,
        pullAuxTracked, pullAuxCached, pullAux, resetBarrierCache, hbarriers]
  refine
    ⟨inner, rfl, done,
      by
        simpa [OpenConf.ofConf, OpenConf.ofConfWith] using bridge.1,
      bridge.2, answers, ?_⟩
  let seed := advanceCounterPastAtoms inner.counter [.var source]
  refine
    ⟨source ++ resolutionCompactSuffix seed, ?_,
      FindallCopy.compact_copy_name_ne_source source seed⟩
  rw [answers]
  simp only [copyFindallBag]
  rw [FindallCopy.copyFindallAtom_var]

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

/-- A source-shaped two-branch generator reaches a terminal nested run whose
raw accumulator contains the same source variable twice.  The certified
rejoin copies those two solutions separately: the bag keeps length/order and
its two residual variable identities are duplicate-free.  This is the sealed
counterpart of the differential `findall-fresh-copy.metta` witness.

[SPEC translator.pl:112-116; SWI-Prolog manual, `findall/3`] -/
theorem two_answer_findall_copies_source_variables_apart
    (prog : Prog) (gt : GroundingTable) (outer : Conf)
    (source : String) (result : Atom) (rest : List Goal)
    (head : outer.cur = some
      (Goal.findall (.var source)
        [Goal.amb [(.var source, []), (.var source, [])] (.var source)]
        result :: rest, [])) :
    ∃ inner,
      FlatStepsN prog gt 5
        (subConfOf outer
          [Goal.amb [(.var source, []), (.var source, [])] (.var source)]
          [] (.var source)) inner ∧
      PLeaTTa.Terminal inner ∧
      inner.answerValues = [.var source, .var source] ∧
      PLeaTTa.Step prog gt outer
        (findallSuccessor outer inner result rest []) ∧
      (copyFindallBag inner.counter inner.answerValues).values.length = 2 ∧
      (chainOf
        (copyFindallBag inner.counter inner.answerValues).values).vars.Nodup := by
  let x : Atom := .var source
  let branches : List (Atom × List Goal) := [(x, []), (x, [])]
  let start := subConfOf outer [Goal.amb branches x] [] x
  let afterAmb := pull
    { start with
      cur := none
      alts := branches.map (fun (term, goals) =>
        Alt.br (ambBranchGoals x (term, goals) ++ []) []) ++ start.alts }
  let afterEq1 : Conf := { afterAmb with cur := some ([], []) }
  let afterAnswer1 := answerSuccessor afterEq1 []
  let afterEq2 : Conf := { afterAnswer1 with cur := some ([], []) }
  let inner := answerSuccessor afterEq2 []
  have afterAmbCur : afterAmb.cur =
      some ([Goal.eq x x], []) := by
    cases hbarriers : outer.barriers <;>
      simp [afterAmb, start, branches, x, subConfOf, pull,
        pullAuxTracked, pullAuxCached, pullAux, resetBarrierCache, hbarriers]
  have afterAnswer1Cur : afterAnswer1.cur =
      some ([Goal.eq x x], []) := by
    cases hbarriers : outer.barriers <;>
      simp [afterAnswer1, answerSuccessor, afterEq1, afterAmb, start, branches,
        x, subConfOf, pull, pullAuxTracked, pullAuxCached, pullAux,
        resetBarrierCache, hbarriers, ambBranchGoals]
  have unifySelf : unifyB [] x x = some [] := by
    simp [x, unifyB, unifyTopExact_var_self]
  have trimAfterAmb : trimFor [] afterAmb.qterm [] = [] := by
    rfl
  have trimAfterAnswer1 : trimFor [] afterAnswer1.qterm [] = [] := by
    rfl
  have stepAmb : PLeaTTa.Step prog gt start afterAmb := by
    exact PLeaTTa.Step.amb start branches x [] [] (by rfl)
  have stepEq1 : PLeaTTa.Step prog gt afterAmb afterEq1 := by
    simpa [afterEq1, trimAfterAmb] using
      (PLeaTTa.Step.eq_ok afterAmb x x [] [] [] afterAmbCur unifySelf)
  have stepAnswer1 : PLeaTTa.Step prog gt afterEq1 afterAnswer1 := by
    exact PLeaTTa.Step.answer afterEq1 [] (by rfl)
  have stepEq2 : PLeaTTa.Step prog gt afterAnswer1 afterEq2 := by
    simpa [afterEq2, trimAfterAnswer1] using
      (PLeaTTa.Step.eq_ok afterAnswer1 x x [] [] [] afterAnswer1Cur unifySelf)
  have stepAnswer2 : PLeaTTa.Step prog gt afterEq2 inner := by
    exact PLeaTTa.Step.answer afterEq2 [] (by rfl)
  have notFindallStart : ¬ findallRunHead start := by
    rintro ⟨template, sub, output, tail, binding, conflict⟩
    simp [start, subConfOf] at conflict
  have notFindallAfterAmb : ¬ findallRunHead afterAmb := by
    rintro ⟨template, sub, output, tail, binding, conflict⟩
    rw [afterAmbCur] at conflict
    cases conflict
  have notFindallAfterEq1 : ¬ findallRunHead afterEq1 := by
    rintro ⟨template, sub, output, tail, binding, conflict⟩
    simp [afterEq1] at conflict
  have notFindallAfterAnswer1 : ¬ findallRunHead afterAnswer1 := by
    rintro ⟨template, sub, output, tail, binding, conflict⟩
    rw [afterAnswer1Cur] at conflict
    cases conflict
  have notFindallAfterEq2 : ¬ findallRunHead afterEq2 := by
    rintro ⟨template, sub, output, tail, binding, conflict⟩
    simp [afterEq2] at conflict
  have run : FlatStepsN prog gt 5 start inner :=
    .succ 4 start afterAmb inner notFindallStart stepAmb
      (.succ 3 afterAmb afterEq1 inner notFindallAfterAmb stepEq1
        (.succ 2 afterEq1 afterAnswer1 inner notFindallAfterEq1 stepAnswer1
          (.succ 1 afterAnswer1 afterEq2 inner notFindallAfterAnswer1 stepEq2
            (.succ 0 afterEq2 inner inner notFindallAfterEq2 stepAnswer2
              (.zero inner)))))
  have done : PLeaTTa.Terminal inner := by
    cases hbarriers : outer.barriers <;>
      simp [inner, afterEq2, afterAnswer1, answerSuccessor, afterEq1,
        afterAmb, start, branches, x, subConfOf, PLeaTTa.Terminal, pull,
        pullAuxTracked, pullAuxCached, pullAux, resetBarrierCache, hbarriers,
        ambBranchGoals]
  have answers : inner.answerValues = [x, x] := by
    cases hbarriers : outer.barriers <;>
      simp [inner, afterEq2, afterAnswer1, answerSuccessor, afterEq1,
        afterAmb, start, branches, x, subConfOf, Conf.answerValues, pull,
        pullAuxTracked, pullAuxCached, pullAux, resetBarrierCache, hbarriers,
        ambBranchGoals]
  have sealed : PLeaTTa.Step prog gt outer
      (findallSuccessor outer inner result rest []) := by
    exact PLeaTTa.Step.findall outer inner (.var source)
      [Goal.amb [(.var source, []), (.var source, [])] (.var source)]
      result rest [] head run.toStepStar done
  refine ⟨inner, ?_, done, ?_, sealed, ?_, ?_⟩
  · simpa [start, branches, x] using run
  · simpa [x] using answers
  · simp [answers]
  · have separated :=
      FindallCopy.copyFindallBag_two_same_variables_separate
        inner.counter source
    rw [answers]
    rw [separated.1]
    simp [chainOf, consC, nilA, Atom.vars, separated.2]

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
      · simpa [OpenConf.stepOpen, OpenConf.ofConfWith, OpenConf.ofConf] using
          (Step.ordinary (OpenConf.ofConf before frames) middle
            (by simpa using notFindall) (by simpa using machineStep))
      · exact inductionHypothesis

/-- The same exact lift under an arbitrary already-established open-layer
scope frontier.  Ordinary private steps preserve that frontier
definitionally. -/
theorem FlatStepsN.liftWith {prog : Prog} {gt : GroundingTable}
    {n : Nat} {before after : Conf} (frames : List Frame)
    (scopes : ScopeHighWaters)
    (steps : FlatStepsN prog gt n before after) :
    StepsN prog gt n (OpenConf.ofConfWith before frames scopes)
      (OpenConf.ofConfWith after frames scopes) := by
  induction steps with
  | zero state => exact .zero _
  | succ n before middle after notFindall machineStep tail
      inductionHypothesis =>
      apply StepsN.succ n _
        (OpenConf.ofConfWith middle frames scopes) _
      · simpa [OpenConf.stepOpen] using
          (Step.ordinary (OpenConf.ofConfWith before frames scopes) middle
            (by simpa using notFindall) (by simpa using machineStep))
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
      (OpenConf.ofConfWith inner
        (.findall
          { preCut := outer.scopes.nextCutScope
            preCollection := outer.scopes.nextCollectionScope
            outer := outer.control
            template := template
            result := result
            rest := rest
            binding := binding } :: outer.frames)
        outer.scopes.afterFindall) := by
  apply StepsN.succ n outer
    (enterFindall outer template sub result rest binding) _
  · exact .findallEnter outer template sub result rest binding head
  · simpa [enterFindall, OpenConf.stepOpen, OpenConf.ofConfWith] using
      run.liftWith
        (.findall
          { preCut := outer.scopes.nextCutScope
            preCollection := outer.scopes.nextCollectionScope
            outer := outer.control
            template := template
            result := result
            rest := rest
            binding := binding } :: outer.frames)
        outer.scopes.afterFindall

/-- Entry allocation is already present on every finite still-open generator
prefix.  No completion premise is available here, so a divergent generator
cannot defer or roll back its delimiter identities. -/
theorem findall_open_prefix_scopes_exact
    (prog : Prog) (gt : GroundingTable) (outer : OpenConf)
    (template : Atom) (sub : List Goal) (result : Atom)
    (rest : List Goal) (binding : Subst) (n : Nat) (inner : Conf)
    (head : outer.toConf.cur =
      some (Goal.findall template sub result :: rest, binding))
    (run : FlatStepsN prog gt n
      (subConfOf outer.toConf sub binding template) inner) :
    ∃ target,
      StepsN prog gt (n + 1) outer target ∧
      target.frames =
        .findall
          { preCut := outer.scopes.nextCutScope
            preCollection := outer.scopes.nextCollectionScope
            outer := outer.control
            template := template
            result := result
            rest := rest
            binding := binding } :: outer.frames ∧
      target.scopes.nextCutScope =
        outer.scopes.nextCutScope + 1 ∧
      target.scopes.nextExceptionScope =
        outer.scopes.nextExceptionScope ∧
      target.scopes.nextCollectionScope =
        outer.scopes.nextCollectionScope + 1 := by
  let target :=
    OpenConf.ofConfWith inner
      (.findall
        { preCut := outer.scopes.nextCutScope
          preCollection := outer.scopes.nextCollectionScope
          outer := outer.control
          template := template
          result := result
          rest := rest
          binding := binding } :: outer.frames)
      outer.scopes.afterFindall
  refine ⟨target, ?_, rfl, ?_⟩
  · exact findall_prefix_lifts prog gt outer template sub result rest binding
      n inner head run
  · simp [target]

/-- An entry plus any still-open private generator prefix cannot be the
endpoint of a bracketed terminating macro run lifted under the caller's frame
stack: the live collector frame is still owned by the target.  This prevents
the terminating collapse theorem from being (mis)applied to an unpaired
prefix, including every finite prefix of a divergent generator. -/
theorem findall_unpaired_prefix_has_no_macro_collapse
    (prog : Prog) (gt : GroundingTable) (outer : OpenConf)
    (template : Atom) (sub : List Goal) (result : Atom)
    (rest : List Goal) (binding : Subst) (n : Nat) (inner : Conf)
    (head : outer.toConf.cur =
      some (Goal.findall template sub result :: rest, binding))
    (run : FlatStepsN prog gt n
      (subConfOf outer.toConf sub binding template) inner) :
    let target := OpenConf.ofConfWith inner
      (.findall
        { preCut := outer.scopes.nextCutScope
          preCollection := outer.scopes.nextCollectionScope
          outer := outer.control
          template := template
          result := result
          rest := rest
          binding := binding } :: outer.frames)
      outer.scopes.afterFindall
    StepsN prog gt (n + 1) outer target ∧
      ∀ (macroCount : Nat) (finish : Conf)
          (finishScopes : ScopeHighWaters),
        MacroStepsN prog gt macroCount
          outer.toConf outer.scopes finish finishScopes →
        OpenConf.ofConfWith finish outer.frames finishScopes ≠ target := by
  dsimp only
  constructor
  · exact findall_prefix_lifts prog gt outer template sub result rest binding n
      inner head run
  · intro macroCount finish finishScopes macroRun endpoint
    have frameConflict := congrArg OpenConf.frames endpoint
    simp at frameConflict

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
        (OpenConf.ofConfWith inner
          (.findall
            { preCut := outer.scopes.nextCutScope
              preCollection := outer.scopes.nextCollectionScope
              outer := outer.control
              template := template
              result := result
              rest := rest
              binding := binding } :: outer.frames)
          outer.scopes.afterFindall)
        { preCut := outer.scopes.nextCutScope
          preCollection := outer.scopes.nextCollectionScope
          outer := outer.control
          template := template
          result := result
          rest := rest
          binding := binding }
        outer.frames) := by
  let frame : FindallFrame :=
    { preCut := outer.scopes.nextCutScope
      preCollection := outer.scopes.nextCollectionScope
      outer := outer.control
      template := template
      result := result
      rest := rest
      binding := binding }
  let suspended :=
    OpenConf.ofConfWith inner (.findall frame :: outer.frames)
      outer.scopes.afterFindall
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

/-- Conversely, a terminating flat fine-grained collector is licensed by the
existing sealed atomic `findall` rule.  The conclusion names the exact state
reached by the fine entry/run/exit path, so the collapse preserves the inner
world and fresh high-water, the duplicate-sensitive answer order, and every
field of the suspended outer continuation. -/
theorem findall_flat_run_collapses_to_sealed_step
    (prog : Prog) (gt : GroundingTable) (outer : OpenConf)
    (template : Atom) (sub : List Goal) (result : Atom)
    (rest : List Goal) (binding : Subst) (n : Nat) (inner : Conf)
    (head : outer.toConf.cur =
      some (Goal.findall template sub result :: rest, binding))
    (run : FlatStepsN prog gt n
      (subConfOf outer.toConf sub binding template) inner)
    (done : PLeaTTa.Terminal inner) :
    PLeaTTa.Step prog gt outer.toConf
      (resumeFindall
        (OpenConf.ofConf inner
          (.findall
            { preCut := ({} : ScopeHighWaters).nextCutScope
              preCollection := ({} : ScopeHighWaters).nextCollectionScope
              outer := outer.control
              template := template
              result := result
              rest := rest
              binding := binding } :: outer.frames))
        { preCut := ({} : ScopeHighWaters).nextCutScope
          preCollection := ({} : ScopeHighWaters).nextCollectionScope
          outer := outer.control
          template := template
          result := result
          rest := rest
          binding := binding }
        outer.frames).toConf := by
  apply PLeaTTa.Step.findall outer.toConf inner template sub result rest binding
  · exact head
  · exact run.toStepStar
  · exact done

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

/-- A private generator answer is suppressed from the public accumulator but
is still exactly one fine transition.  Thus infinitely many private answers
cannot collapse to a zero-step empty observation list. -/
theorem answer_is_one_private_step
    (prog : Prog) (gt : GroundingTable) (state : OpenConf)
    (frame : FindallFrame) (remaining : List Frame) (binding : Subst)
    (frameHead : state.frames = .findall frame :: remaining)
    (head : state.toConf.cur = some ([], binding)) :
    Step prog gt state (privateAnswerTarget state binding) ∧
      (privateAnswerTarget state binding).frames = state.frames ∧
      (privateAnswerTarget state binding).scopes = state.scopes ∧
      (privateAnswerTarget state binding).persistent = state.persistent ∧
      (privateAnswerTarget state binding).control.qterm =
        state.control.qterm ∧
      (privateAnswerTarget state binding).control.answers =
        subst binding state.control.qterm :: state.control.answers ∧
      publicAnswers (privateAnswerTarget state binding) =
        publicAnswers state := by
  have notFindall : ¬ findallRunHead state.toConf := by
    intro findallHead
    rcases findallHead with
      ⟨template, sub, result, rest, otherBinding, conflict⟩
    rw [head] at conflict
    cases conflict
  have fineStep :
      Step prog gt state (privateAnswerTarget state binding) := by
    simpa [privateAnswerTarget] using
      (Step.ordinary state (answerSuccessor state.toConf binding)
        notFindall
        (PLeaTTa.Step.answer state.toConf binding head))
  refine ⟨fineStep, by simp, by simp, by simp, by simp, by simp, ?_⟩
  simp [publicAnswers, publicControl, privateAnswerTarget, OpenConf.stepOpen,
    OpenConf.ofConfWith, frameHead]

/-- Constructor-shaped specialization retained for the existing flat-run
proofs.  Unlike `answer_is_one_private_step`, this older surface starts from
the initial open-layer scope frontiers. -/
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
      inner.persistent.counter ≤
        (resumeFindall inner frame remaining).persistent.counter := by
  constructor
  · rfl
  · exact copyFindallBag_counter_mono _ _

/-! ## Additive fine copy phase

`Step.findallExit` above remains the atomic terminating-run macro-spec used by
the established frame-bracket parser.  The following second lane refines only
that exit.  It transfers a terminal collector into a local phase, consumes
exactly one materialized source value per certified microstep, and rejoins
after the private reverse accumulator is complete.  Generic trace/provider
types never receive a constructor for copied answer content. -/

/-- Non-backtrackable world plus the linearly owned suspended continuation
during residual-bag copying.  The active generator and its top frame have
been consumed; `bag.counter` is the sole fresh high-water in this phase. -/
structure FindallCopyPhase where
  world : PWorld
  scopes : ScopeHighWaters
  frame : FindallFrame
  remainingFrames : List Frame
  bag : FindallCopy.BagCopyState
deriving Repr

/-- Transfer a terminal collector into its certified local copy phase. -/
def beginFindallCopy (inner : OpenConf) (frame : FindallFrame)
    (remaining : List Frame) : FindallCopyPhase :=
  { world := inner.persistent.world
    scopes := inner.scopes
    frame := frame
    remainingFrames := remaining
    bag :=
      FindallCopy.BagCopyState.initial inner.persistent.counter
        inner.control.answerValues }

/-- Rejoin a completed local copy phase.  The caller receives source-order
values by reversing the phase's private accumulator exactly once. -/
def finishFindallCopy (phase : FindallCopyPhase) : OpenConf :=
  resumeFindallCopied
    { world := phase.world, counter := phase.bag.counter }
    phase.scopes
    phase.frame phase.remainingFrames phase.bag.copiedRev.reverse

/-- Additive state space: established open-machine states are retained
unchanged, while the new constructor represents only bounded certified local
copy work. -/
inductive CopyOpenConf where
  | open (state : OpenConf)
  | copying (phase : FindallCopyPhase)
deriving Repr

/-- Fine transition relation with no atomic collector exit.  Ordinary work
and collector entry mirror the established lane.  A terminal collector must
transfer into `FindallCopyPhase`; each `copyNext` is justified by the local
functional copy relation, and `copyFinish` requires exhausted input. -/
inductive CopyStep (prog : Prog) (gt : GroundingTable) :
    CopyOpenConf → CopyOpenConf → Prop where
  | ordinary (state : OpenConf) (next : Conf)
      (notFindall : ¬ findallRunHead state.toConf)
      (step : PLeaTTa.Step prog gt state.toConf next) :
      CopyStep prog gt (.open state)
        (.open (state.stepOpen next))
  | findallEnter (state : OpenConf) (template : Atom) (sub : List Goal)
      (result : Atom) (rest : List Goal) (binding : Subst)
      (head : state.toConf.cur =
        some (Goal.findall template sub result :: rest, binding)) :
      CopyStep prog gt (.open state)
        (.open (enterFindall state template sub result rest binding))
  | copyBegin (inner : OpenConf) (frame : FindallFrame)
      (remaining : List Frame)
      (frameHead : inner.frames = .findall frame :: remaining)
      (done : PLeaTTa.Terminal inner.toConf) :
      CopyStep prog gt (.open inner)
        (.copying (beginFindallCopy inner frame remaining))
  | copyNext (phase : FindallCopyPhase)
      (nextBag : FindallCopy.BagCopyState)
      (step : FindallCopy.BagCopyStep phase.bag nextBag) :
      CopyStep prog gt (.copying phase)
        (.copying { phase with bag := nextBag })
  | copyFinish (phase : FindallCopyPhase)
      (done : phase.bag.remaining = []) :
      CopyStep prog gt (.copying phase)
        (.open (finishFindallCopy phase))

/-- Exact step-counted closure of the additive copy lane. -/
inductive CopyStepsN (prog : Prog) (gt : GroundingTable) :
    Nat → CopyOpenConf → CopyOpenConf → Prop where
  | zero (state : CopyOpenConf) : CopyStepsN prog gt 0 state state
  | succ (n : Nat) (before middle after : CopyOpenConf) :
      CopyStep prog gt before middle →
      CopyStepsN prog gt n middle after →
      CopyStepsN prog gt (n + 1) before after

theorem CopyStepsN.trans {prog : Prog} {gt : GroundingTable}
    {left middle right : CopyOpenConf} {m n : Nat}
    (first : CopyStepsN prog gt m left middle)
    (second : CopyStepsN prog gt n middle right) :
    CopyStepsN prog gt (m + n) left right := by
  induction first with
  | zero state => simpa using second
  | succ count before stepMiddle after step tail inductionHypothesis =>
      have combined :=
        CopyStepsN.succ (count + n) before stepMiddle right step
          (inductionHypothesis second)
      have lengthEq : count + n + 1 = count + 1 + n := by omega
      rw [lengthEq] at combined
      exact combined

/-- Lift the certified bag copier under a fixed, linearly owned collector
context.  Every bag microstep remains exactly one open-machine microstep. -/
theorem BagCopyStepsN_lift
    {prog : Prog} {gt : GroundingTable}
    {n : Nat} {before after : FindallCopy.BagCopyState}
    (world : PWorld) (scopes : ScopeHighWaters) (frame : FindallFrame)
    (remaining : List Frame)
    (steps : FindallCopy.BagCopyStepsN n before after) :
    CopyStepsN prog gt n
      (.copying
        { world := world
          scopes := scopes
          frame := frame
          remainingFrames := remaining
          bag := before })
      (.copying
        { world := world
          scopes := scopes
          frame := frame
          remainingFrames := remaining
          bag := after }) := by
  induction steps with
  | zero state => exact .zero _
  | succ count before middle after step tail inductionHypothesis =>
      exact .succ count _ _ _
        (.copyNext _ middle step)
        inductionHypothesis

/-- The phase's world and suspended-continuation metadata are invariant under
one local copy step; only the private bag state can change. -/
theorem CopyStep.copyNext_preserves_context
    {prog : Prog} {gt : GroundingTable}
    {phase nextPhase : FindallCopyPhase}
    (step : CopyStep prog gt (.copying phase) (.copying nextPhase)) :
    nextPhase.world = phase.world ∧
      nextPhase.scopes = phase.scopes ∧
      nextPhase.frame = phase.frame ∧
      nextPhase.remainingFrames = phase.remainingFrames := by
  cases step
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The fresh high-water cannot move backwards during a local copy step. -/
theorem CopyStep.copyNext_counter_mono
    {prog : Prog} {gt : GroundingTable}
    {phase nextPhase : FindallCopyPhase}
    (step : CopyStep prog gt (.copying phase) (.copying nextPhase)) :
    phase.bag.counter ≤ nextPhase.bag.counter := by
  cases step with
  | copyNext _ _ bagStep =>
      exact bagStep.counter_mono

/-- Public caller answers remain unchanged throughout one private copy
microstep.  This is content isolation, not observation-list erasure: the
transition is still counted by `CopyStepsN`. -/
theorem CopyStep.copyNext_publicAnswers
    {prog : Prog} {gt : GroundingTable}
    {phase nextPhase : FindallCopyPhase}
    (step : CopyStep prog gt (.copying phase) (.copying nextPhase)) :
    publicAnswers
        { persistent :=
            { world := nextPhase.world
              counter := nextPhase.bag.counter }
          control := nextPhase.frame.outer
          frames := nextPhase.remainingFrames } =
      publicAnswers
        { persistent :=
            { world := phase.world
              counter := phase.bag.counter }
          control := phase.frame.outer
          frames := phase.remainingFrames } := by
  cases step
  rfl

/-- The exact terminal microstep state computed from a collector. -/
def completedFindallCopyPhase (inner : OpenConf) (frame : FindallFrame)
    (remaining : List Frame) : FindallCopyPhase :=
  let copied :=
    copyFindallBag inner.persistent.counter inner.control.answerValues
  { world := inner.persistent.world
    scopes := inner.scopes
    frame := frame
    remainingFrames := remaining
    bag :=
      { remaining := []
        copiedRev := copied.values.reverse
        counter := copied.counter } }

/-- The certified one-at-a-time phase runs for exactly one step per source
solution and reaches the macro copier's exact terminal state. -/
theorem findallCopyPhase_exact
    {prog : Prog} {gt : GroundingTable}
    (inner : OpenConf) (frame : FindallFrame)
    (remaining : List Frame) :
    CopyStepsN prog gt inner.control.answerValues.length
      (.copying (beginFindallCopy inner frame remaining))
      (.copying (completedFindallCopyPhase inner frame remaining)) := by
  simpa [beginFindallCopy, completedFindallCopyPhase] using
    BagCopyStepsN_lift inner.persistent.world inner.scopes frame remaining
      (FindallCopy.BagCopyStepsN.run_initial
        inner.persistent.counter inner.control.answerValues)

/-- Finishing the exact microstep fold is definitionally the shared atomic
collector.  This is the non-stuttering collapse: copied content, order,
multiplicity, world, counter, and caller continuation all coincide. -/
theorem completedFindallCopyPhase_finish
    (inner : OpenConf) (frame : FindallFrame)
    (remaining : List Frame) :
    finishFindallCopy
        (completedFindallCopyPhase inner frame remaining) =
      resumeFindall inner frame remaining := by
  rw [resumeFindall_eq_copied]
  simp [finishFindallCopy, completedFindallCopyPhase,
    resumeFindallCopied]

/-- One atomic `findallExit` expands to: transfer, exactly one certified local
copy step per source solution, and rejoin.  The endpoint is byte-for-byte the
atomic macro successor; no answer-list quotient or stuttering assumption is
used. -/
theorem findallExit_copy_expands
    (prog : Prog) (gt : GroundingTable)
    (inner : OpenConf) (frame : FindallFrame)
    (remaining : List Frame)
    (frameHead : inner.frames = .findall frame :: remaining)
    (done : PLeaTTa.Terminal inner.toConf) :
    CopyStepsN prog gt (inner.control.answerValues.length + 2)
      (.open inner) (.open (resumeFindall inner frame remaining)) := by
  let started := beginFindallCopy inner frame remaining
  let completed := completedFindallCopyPhase inner frame remaining
  have beginStep :
      CopyStep prog gt (.open inner) (.copying started) := by
    exact .copyBegin inner frame remaining frameHead done
  have beginRun :
      CopyStepsN prog gt 1 (.open inner) (.copying started) := by
    simpa using
      CopyStepsN.succ 0 _ (.copying started) (.copying started)
        beginStep (.zero _)
  have copyRun :
      CopyStepsN prog gt inner.control.answerValues.length
        (.copying started) (.copying completed) := by
    simpa [started, completed] using
      findallCopyPhase_exact (prog := prog) (gt := gt)
        inner frame remaining
  have finishedInput :
      completed.bag.remaining = [] := by
    rfl
  have finishStep :
      CopyStep prog gt (.copying completed)
        (.open (finishFindallCopy completed)) :=
    .copyFinish completed finishedInput
  have finishRun :
      CopyStepsN prog gt 1 (.copying completed)
        (.open (finishFindallCopy completed)) := by
    simpa using
      CopyStepsN.succ 0 _ _ _ finishStep (.zero _)
  have combined := beginRun.trans (copyRun.trans finishRun)
  rw [completedFindallCopyPhase_finish] at combined
  have countEq :
      1 + (inner.control.answerValues.length + 1) =
        inner.control.answerValues.length + 2 := by
    omega
  rw [countEq] at combined
  exact combined

/-- The additive expansion and the atomic established step are paired on the
same source and target.  Thus the local copy phase refines rather than
replaces the existing sealed/OpenConf collector. -/
theorem findallExit_copy_expands_and_collapses
    (prog : Prog) (gt : GroundingTable)
    (inner : OpenConf) (frame : FindallFrame)
    (remaining : List Frame)
    (frameHead : inner.frames = .findall frame :: remaining)
    (done : PLeaTTa.Terminal inner.toConf) :
    CopyStepsN prog gt (inner.control.answerValues.length + 2)
        (.open inner) (.open (resumeFindall inner frame remaining)) ∧
      Step prog gt inner (resumeFindall inner frame remaining) := by
  exact
    ⟨findallExit_copy_expands prog gt inner frame remaining frameHead done,
      .findallExit inner frame remaining frameHead done⟩

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
