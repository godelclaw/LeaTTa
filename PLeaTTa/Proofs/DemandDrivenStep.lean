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

/-- The suspended frame generated from a plain outer machine state. -/
def findallFrameOf (outer : Conf) (template result : Atom)
    (rest : List Goal) (binding : Subst) : FindallFrame :=
  { outer := controlOf outer
    template := template
    result := result
    rest := rest
    binding := binding }

/-- Exact atomic successor used by the sealed `Step.findall` constructor. -/
def findallSuccessor (outer inner : Conf) (result : Atom)
    (rest : List Goal) (binding : Subst) : Conf :=
  { outer with
    cur := some (Goal.eq result (chainOf inner.answerValues) :: rest, binding)
    world := inner.world
    counter := inner.counter }

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

@[simp] theorem enterFindall_ofConf (outer : Conf) (frames : List Frame)
    (template : Atom) (sub : List Goal) (result : Atom)
    (rest : List Goal) (binding : Subst) :
    enterFindall (OpenConf.ofConf outer frames) template sub result rest binding =
      OpenConf.ofConf (subConfOf outer sub binding template)
        (.findall (findallFrameOf outer template result rest binding) ::
          frames) := by
  rfl

@[simp] theorem resumeFindall_ofConf (outer inner : Conf)
    (frames : List Frame) (template result : Atom)
    (rest : List Goal) (binding : Subst) :
    resumeFindall
        (OpenConf.ofConf inner
          (.findall (findallFrameOf outer template result rest binding) ::
            frames))
        (findallFrameOf outer template result rest binding) frames =
      OpenConf.ofConf (findallSuccessor outer inner result rest binding)
        frames := by
  cases outer
  cases inner
  rfl

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

/-- A bracketed terminating execution for the currently fine-grained
`findall` fragment.  Ordinary sealed steps remain one step; a collector owns
one recursively structured inner run plus its entry and exit.  This gives one
induction principle for arbitrarily nested terminating collectors without
turning their nonterminal prefixes into atomic steps. -/
inductive MacroStepsN (prog : Prog) (gt : GroundingTable) :
    Nat → Conf → Conf → Prop where
  | zero (state : Conf) : MacroStepsN prog gt 0 state state
  | ordinary (n : Nat) (before middle after : Conf)
      (notFindall : ¬ findallRunHead before)
      (step : PLeaTTa.Step prog gt before middle)
      (tail : MacroStepsN prog gt n middle after) :
      MacroStepsN prog gt (n + 1) before after
  | findall (innerCount tailCount : Nat) (outer inner finish : Conf)
      (template : Atom) (sub : List Goal) (result : Atom)
      (rest : List Goal) (binding : Subst)
      (head : outer.cur =
        some (Goal.findall template sub result :: rest, binding))
      (innerRun : MacroStepsN prog gt innerCount
        (subConfOf outer sub binding template) inner)
      (done : PLeaTTa.Terminal inner)
      (tail : MacroStepsN prog gt tailCount
        (findallSuccessor outer inner result rest binding) finish) :
      MacroStepsN prog gt (innerCount + 2 + tailCount) outer finish

namespace MacroStepsN

/-- Sequential composition of bracketed runs.  This is the algebra used by
the prefix parser when an open collector closes and rejoins its caller. -/
theorem trans {prog : Prog} {gt : GroundingTable}
    {left middle right : Conf} {m n : Nat}
    (first : MacroStepsN prog gt m left middle)
    (second : MacroStepsN prog gt n middle right) :
    MacroStepsN prog gt (m + n) left right := by
  induction first with
  | zero state => simpa using second
  | ordinary k before stepMiddle after notFindall step tail tailIH =>
      have combined := MacroStepsN.ordinary (k + n) before stepMiddle right
        notFindall step (tailIH second)
      have lengthEq : k + n + 1 = k + 1 + n := by omega
      rw [lengthEq] at combined
      exact combined
  | findall innerCount tailCount outer inner finish template sub result rest
      binding head innerRun done tail innerIH tailIH =>
      simpa [Nat.add_assoc] using
        MacroStepsN.findall innerCount (tailCount + n) outer inner right
          template sub result rest binding head innerRun done (tailIH second)

/-- Erasing fine collector boundaries from a structured terminating run gives
an ordinary sealed run.  Nested collectors collapse recursively. -/
theorem toStepStar {prog : Prog} {gt : GroundingTable}
    {n : Nat} {before after : Conf}
    (execution : MacroStepsN prog gt n before after) :
    PLeaTTa.StepStar prog gt before after := by
  induction execution with
  | zero state => exact .refl state
  | ordinary n before middle after _ step _ tailIH =>
      exact .tail before middle after step tailIH
  | findall innerCount tailCount outer inner finish template sub result rest
      binding head innerRun done tail innerIH tailIH =>
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
    {n : Nat} {before after : Conf} (frames : List Frame)
    (execution : MacroStepsN prog gt n before after) :
    StepsN prog gt n (OpenConf.ofConf before frames)
      (OpenConf.ofConf after frames) := by
  induction execution generalizing frames with
  | zero state => exact .zero _
  | ordinary n before middle after notFindall machineStep tail tailIH =>
      apply StepsN.succ n _ (OpenConf.ofConf middle frames) _
      · exact .ordinary _ middle (by simpa using notFindall)
          (by simpa using machineStep)
      · exact tailIH frames
  | findall innerCount tailCount outer inner finish template sub result rest
      binding head innerRun done tail innerIH tailIH =>
      let frame := findallFrameOf outer template result rest binding
      let entered := OpenConf.ofConf (subConfOf outer sub binding template)
        (.findall frame :: frames)
      let resumed := OpenConf.ofConf
        (findallSuccessor outer inner result rest binding) frames
      have entryStep : Step prog gt (OpenConf.ofConf outer frames) entered := by
        simpa [entered, frame] using
          (Step.findallEnter (OpenConf.ofConf outer frames) template sub result
            rest binding (by simpa using head))
      have entryRun : StepsN prog gt 1 (OpenConf.ofConf outer frames)
          entered := by
        simpa using StepsN.succ 0 _ entered entered entryStep (.zero entered)
      have nestedRun : StepsN prog gt innerCount entered
          (OpenConf.ofConf inner (.findall frame :: frames)) := by
        simpa [entered] using innerIH (.findall frame :: frames)
      have exitStep : Step prog gt
          (OpenConf.ofConf inner (.findall frame :: frames)) resumed := by
        simpa [resumed, frame] using
          (Step.findallExit
            (OpenConf.ofConf inner (.findall frame :: frames)) frame frames rfl
            (by simpa using done))
      have exitRun : StepsN prog gt 1
          (OpenConf.ofConf inner (.findall frame :: frames)) resumed := by
        simpa using StepsN.succ 0 _ resumed resumed exitStep (.zero resumed)
      have tailRun : StepsN prog gt tailCount resumed
          (OpenConf.ofConf finish frames) := by
        simpa [resumed] using tailIH frames
      have combined := entryRun.trans (nestedRun.trans (exitRun.trans tailRun))
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using combined

end MacroStepsN

/-- A parsed fine prefix relative to a protected caller-frame suffix.  A
`closed` prefix has returned to that suffix.  An `open` prefix records the
already completed caller macro, the pending collector entry, and recursively
parses the active generator above the newly pushed frame. -/
inductive MacroPrefixN (prog : Prog) (gt : GroundingTable) :
    List Frame → Nat → Conf → OpenConf → Prop where
  | closed (baseFrames : List Frame) (n : Nat) (start finish : Conf)
      (run : MacroStepsN prog gt n start finish) :
      MacroPrefixN prog gt baseFrames n start
        (OpenConf.ofConf finish baseFrames)
  | suspended (baseFrames : List Frame) (beforeCount innerCount : Nat)
      (start outer : Conf)
      (template : Atom) (sub : List Goal) (result : Atom)
      (rest : List Goal) (binding : Subst) (target : OpenConf)
      (before : MacroStepsN prog gt beforeCount start outer)
      (head : outer.cur =
        some (Goal.findall template sub result :: rest, binding))
      (inner : MacroPrefixN prog gt
        (.findall (findallFrameOf outer template result rest binding) ::
          baseFrames)
        innerCount (subConfOf outer sub binding template) target) :
      MacroPrefixN prog gt baseFrames (beforeCount + 1 + innerCount)
        start target

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
        { outer := before.control
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
    {baseFrames : List Frame} {n : Nat} {start : Conf} {target : OpenConf}
    (parsed : MacroPrefixN prog gt baseFrames n start target) :
    ∃ extra, target.frames = extra ++ baseFrames := by
  induction parsed with
  | closed => exact ⟨[], rfl⟩
  | suspended baseFrames beforeCount innerCount start outer template sub result rest binding
      target before head inner innerIH =>
      rcases innerIH with ⟨extra, framesEq⟩
      refine ⟨extra ++ [.findall
        (findallFrameOf outer template result rest binding)], ?_⟩
      rw [framesEq, List.append_assoc]
      rfl

/-- An open parser state owns at least one frame above the protected suffix. -/
theorem open_frames_cons_suffix {prog : Prog} {gt : GroundingTable}
    {baseFrames : List Frame} {beforeCount innerCount : Nat}
    {start outer : Conf} {template : Atom} {sub : List Goal}
    {result : Atom} {rest : List Goal} {binding : Subst}
    {target : OpenConf}
    (_before : MacroStepsN prog gt beforeCount start outer)
    (_head : outer.cur =
      some (Goal.findall template sub result :: rest, binding))
    (inner : MacroPrefixN prog gt
      (.findall (findallFrameOf outer template result rest binding) ::
        baseFrames)
      innerCount (subConfOf outer sub binding template) target) :
    ∃ top extra, target.frames = top :: (extra ++ baseFrames) := by
  rcases inner.frames_suffix with ⟨extra, framesEq⟩
  cases extra with
  | nil =>
      exact ⟨.findall (findallFrameOf outer template result rest binding), [],
        by simpa using framesEq⟩
  | cons top tail =>
      refine ⟨top,
        tail ++ [.findall
          (findallFrameOf outer template result rest binding)], ?_⟩
      rw [framesEq]
      simp only [List.cons_append, List.append_assoc]
      rfl

/-- Extend a parsed prefix by one fine step without crossing its protected
caller suffix.  The only non-local case is an exit: a closed inner parser is
folded into one `MacroStepsN.findall`, whereas an exit above a still-open
inner parser is delegated recursively. -/
theorem advance {prog : Prog} {gt : GroundingTable}
    {baseFrames : List Frame} {n : Nat} {start : Conf}
    {before after : OpenConf}
    (parsed : MacroPrefixN prog gt baseFrames n start before)
    (oneStep : Step prog gt before after)
    (afterSuffix : ∃ extra, after.frames = extra ++ baseFrames) :
    MacroPrefixN prog gt baseFrames (n + 1) start after := by
  induction parsed generalizing after with
  | closed baseFrames n start finish run =>
      cases oneStep with
      | ordinary next notFindall machineStep =>
          let tail : MacroStepsN prog gt 1 finish next :=
            .ordinary 0 finish next next notFindall machineStep (.zero next)
          simpa using MacroPrefixN.closed baseFrames (n + 1) start next
            (run.trans tail)
      | findallEnter template sub result rest binding head =>
          let frame := findallFrameOf finish template result rest binding
          let innerStart := subConfOf finish sub binding template
          have inner : MacroPrefixN prog gt (.findall frame :: baseFrames) 0
              innerStart (OpenConf.ofConf innerStart
                (.findall frame :: baseFrames)) :=
            .closed _ 0 innerStart innerStart (.zero innerStart)
          simpa [frame, innerStart] using
            MacroPrefixN.suspended baseFrames n 0 start finish template sub
              result rest binding _ run (by simpa using head) inner
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
  | suspended baseFrames beforeCount innerCount start outer template sub result
      rest binding target beforeRun head innerParsed innerIH =>
      cases oneStep with
      | ordinary next notFindall machineStep =>
          rcases innerParsed.frames_suffix with ⟨extra, targetFrames⟩
          have recursiveStep : Step prog gt target
              (OpenConf.ofConf next target.frames) :=
            .ordinary target next notFindall machineStep
          have recursiveSuffix : ∃ more,
              (OpenConf.ofConf next target.frames).frames =
                more ++
                  (.findall
                    (findallFrameOf outer template result rest binding) ::
                    baseFrames) :=
            ⟨extra, by simpa using targetFrames⟩
          have advanced := innerIH recursiveStep recursiveSuffix
          have rebuilt := MacroPrefixN.suspended baseFrames beforeCount
            (innerCount + 1) start outer template sub result rest binding _
            beforeRun head advanced
          simpa [Nat.add_assoc] using rebuilt
      | findallEnter nestedTemplate nestedSub nestedResult nestedRest
          nestedBinding nestedHead =>
          rcases innerParsed.frames_suffix with ⟨extra, targetFrames⟩
          let nestedFrame :=
            { outer := target.control
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
                    (findallFrameOf outer template result rest binding) ::
                    baseFrames) := by
            refine ⟨.findall nestedFrame :: extra, ?_⟩
            simp [enterFindall, nestedFrame, targetFrames]
          have advanced := innerIH recursiveStep recursiveSuffix
          have rebuilt := MacroPrefixN.suspended baseFrames beforeCount
            (innerCount + 1) start outer template sub result rest binding _
            beforeRun head advanced
          simpa [Nat.add_assoc] using rebuilt
      | findallExit exitFrame remaining frameHead done =>
          cases innerParsed with
          | closed innerBase innerCount innerStart innerFinish innerRun =>
              have frameEq :
                  findallFrameOf outer template result rest binding =
                    exitFrame := by
                simpa using congrArg List.head? frameHead
              have remainingEq : baseFrames = remaining := by
                simpa using congrArg List.tail frameHead
              subst exitFrame
              subst remaining
              let successor :=
                findallSuccessor outer innerFinish result rest binding
              let collector : MacroStepsN prog gt (innerCount + 2) outer
                  successor :=
                .findall innerCount 0 outer innerFinish successor template sub
                  result rest binding head innerRun (by simpa using done)
                  (.zero successor)
              have combined := beforeRun.trans collector
              have combined' : MacroStepsN prog gt
                  ((beforeCount + 1 + innerCount) + 1) start successor := by
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                  combined
              simpa [successor] using
                MacroPrefixN.closed baseFrames _ start successor combined'
          | suspended nestedBase nestedBeforeCount nestedInnerCount nestedStart
              nestedOuter nestedTemplate nestedSub nestedResult nestedRest
              nestedBinding nestedTarget nestedBefore nestedHead nestedInner =>
              have strict : ∃ top extra,
                  target.frames = top ::
                    (extra ++
                      (.findall
                        (findallFrameOf outer template result rest binding) ::
                        baseFrames)) :=
                open_frames_cons_suffix nestedBefore nestedHead nestedInner
              have recursiveStep : Step prog gt target
                  (resumeFindall target exitFrame remaining) :=
                .findallExit target exitFrame remaining frameHead done
              have recursiveSuffix :=
                step_preserves_suffix_of_strict strict recursiveStep
              have advanced := innerIH recursiveStep recursiveSuffix
              have rebuilt := MacroPrefixN.suspended baseFrames beforeCount
                _ start outer template sub result rest binding _
                beforeRun head advanced
              simpa [Nat.add_assoc] using rebuilt

/-- Extend a top-level parsed prefix by an arbitrary fine run.  With no
protected caller frames, every intermediate target trivially has the empty
list as a suffix, so `advance` can be iterated without an additional safety
premise. -/
theorem extendRoot {prog : Prog} {gt : GroundingTable}
    {m n : Nat} {start : Conf} {before after : OpenConf}
    (parsed : MacroPrefixN prog gt [] m start before)
    (execution : StepsN prog gt n before after) :
    MacroPrefixN prog gt [] (m + n) start after := by
  induction execution generalizing m start with
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
    {n : Nat} {start : Conf} {target : OpenConf}
    (execution : StepsN prog gt n (OpenConf.ofConf start []) target) :
    MacroPrefixN prog gt [] n start target := by
  have initial : MacroPrefixN prog gt [] 0 start
      (OpenConf.ofConf start []) :=
    .closed [] 0 start start (.zero start)
  simpa using initial.extendRoot execution

/-- A top-level parsed prefix is either a closed macro with an exact plain
endpoint, or it still owns at least one suspended collector frame. -/
theorem root_closed_or_has_frames {prog : Prog} {gt : GroundingTable}
    {n : Nat} {start : Conf} {target : OpenConf}
    (parsed : MacroPrefixN prog gt [] n start target) :
    (∃ finish,
        target = OpenConf.ofConf finish [] ∧
        MacroStepsN prog gt n start finish) ∨
      target.frames ≠ [] := by
  cases parsed with
  | closed baseFrames count parsedStart parsedFinish run =>
      exact Or.inl ⟨parsedFinish, rfl, run⟩
  | suspended baseFrames beforeCount innerCount parsedStart outer template sub
      result rest binding target beforeRun head inner =>
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
    (execution : StepsN prog gt n (OpenConf.ofConf start [])
      (OpenConf.ofConf finish [])) :
    MacroStepsN prog gt n start finish := by
  have parsed := ofRootSteps execution
  rcases parsed.root_closed_or_has_frames with
    ⟨parsedFinish, endpoint, run⟩ | stillOpen
  · have finishEq : finish = parsedFinish := by
      have projected := congrArg OpenConf.toConf endpoint
      simpa using projected
    subst parsedFinish
    exact run
  · exact False.elim (stillOpen rfl)

/-- Exact terminating-run correspondence for the fine `findall` lane.  This
is count-preserving in both directions and includes arbitrary collector
nesting; open prefixes are intentionally outside the right-hand side. -/
theorem closedRootSteps_iff_macro {prog : Prog} {gt : GroundingTable}
    {n : Nat} {start finish : Conf} :
    StepsN prog gt n (OpenConf.ofConf start [])
        (OpenConf.ofConf finish []) ↔
      MacroStepsN prog gt n start finish := by
  constructor
  · exact closedRootSteps_complete
  · intro structured
    exact MacroStepsN.lift [] structured

/-- Every closed top-level fine run is licensed by the sealed `StepStar`.
Unlike answer-list projection, this theorem is obtained only after the exact
frame-bracket parser has ruled out every unpaired open prefix. -/
theorem closedRootSteps_collapse_to_sealed {prog : Prog}
    {gt : GroundingTable} {n : Nat} {start finish : Conf}
    (execution : StepsN prog gt n (OpenConf.ofConf start [])
      (OpenConf.ofConf finish [])) :
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
    (frames : List Frame) (template : Atom) (sub : List Goal)
    (result : Atom) (rest : List Goal) (binding : Subst) (n : Nat)
    (head : outer.cur =
      some (Goal.findall template sub result :: rest, binding))
    (innerRun : MacroStepsN prog gt n
      (subConfOf outer sub binding template) inner)
    (done : PLeaTTa.Terminal inner) :
    StepsN prog gt (n + 2) (OpenConf.ofConf outer frames)
        (OpenConf.ofConf
          (findallSuccessor outer inner result rest binding) frames) ∧
      PLeaTTa.Step prog gt outer
        (findallSuccessor outer inner result rest binding) := by
  let structured : MacroStepsN prog gt (n + 2) outer
      (findallSuccessor outer inner result rest binding) :=
    .findall n 0 outer inner
      (findallSuccessor outer inner result rest binding)
      template sub result rest binding head innerRun done (.zero _)
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
        (OpenConf.ofConf
          (findallSuccessor outer inner result rest binding) frames) ∧
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
  have innerRun : MacroStepsN prog gt 1 start inner := by
    simpa using MacroStepsN.ordinary 0 start inner inner notFindall answerStep
      (.zero inner)
  have bridge := findall_nested_run_expands_and_collapses prog gt outer inner
    frames template [] result rest binding 1 head innerRun done
  exact ⟨inner, done, by simpa using bridge.1, bridge.2⟩

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
    let target := OpenConf.ofConf inner
      (.findall
        { outer := outer.control
          template := template
          result := result
          rest := rest
          binding := binding } :: outer.frames)
    StepsN prog gt (n + 1) outer target ∧
      ∀ (macroCount : Nat) (finish : Conf),
        MacroStepsN prog gt macroCount outer.toConf finish →
        OpenConf.ofConf finish outer.frames ≠ target := by
  dsimp only
  constructor
  · exact findall_prefix_lifts prog gt outer template sub result rest binding n
      inner head run
  · intro macroCount finish macroRun endpoint
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
