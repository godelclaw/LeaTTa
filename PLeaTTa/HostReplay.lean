import PLeaTTa.HostMachine

namespace PLeaTTa
namespace HostReplay

open Metta (Atom GroundingTable)
open HostMachine

def StateAligned (transcript : List HostExchange) {Binding : Type}
    (live replay : HostMachine.State Binding) : Prop :=
  live.core = replay.core ∧
  live.frames = replay.frames ∧
  live.host.mode = .live ∧
  replay.host.mode = .replay ∧
  replay.host.transcript = transcript ∧
  live.host.cursor = replay.host.cursor ∧
  live.host.pending = none ∧ live.host.ready = none ∧
  replay.host.pending = none ∧ replay.host.ready = none

def StepAligned (transcript : List HostExchange) {Binding : Type}
    (live replay : HostMachine.StepOutcome Binding) : Prop :=
  match live, replay with
  | .progressed left, .progressed right => StateAligned transcript left right
  | .exhausted left, .exhausted right => StateAligned transcript left right
  | .errored left leftError, .errored right rightError =>
      StateAligned transcript left right ∧ leftError = rightError
  | _, _ => False

def clearPending (session : HostSession) : HostSession :=
  { session with pending := none, ready := none }

private def completeRecordedStep (engine : SubstEngine) (prog : Prog)
    (gt : GroundingTable) (transcript : List HostExchange) (fuel : Nat) :
    HostMachine.StepOutcome engine.State → HostMachine.StepOutcome engine.State
  | .requested suspended request =>
      let replay : HostSession := {
        mode := .replay
        transcript
        cursor := suspended.host.cursor }
      match replay.resolve request with
      | .respond response _ =>
          match suspended.host.supply response with
          | .ok supplied =>
              HostMachine.stepWith engine prog gt fuel
                { suspended with host := supplied }
          | .error error =>
              HostMachine.unwindError
                { suspended with host := clearPending suspended.host }
                (HostMachine.protocolErrorAtom error)
      | .fail error =>
          HostMachine.unwindError
            { suspended with host := clearPending suspended.host }
            (HostMachine.protocolErrorAtom error)
      | .suspend pending _ =>
          HostMachine.unwindError
            { suspended with host := clearPending suspended.host }
            (HostMachine.protocolErrorAtom (.unavailable pending))
  | outcome => outcome

/-- Pure model of one recorded live step.  Suspension performs no PeTTa
    reduction: the fixed transcript supplies the response and the same step is
    resumed with the same fuel. -/
def recordedStepWith (engine : SubstEngine) (prog : Prog)
    (gt : GroundingTable) (transcript : List HostExchange) (fuel : Nat)
    (state : HostMachine.State engine.State) :
    HostMachine.StepOutcome engine.State :=
  completeRecordedStep engine prog gt transcript fuel
    (HostMachine.stepWith engine prog gt fuel state)

theorem unwindError_aligned {Binding : Type} (transcript : List HostExchange)
    (core : Conf Binding) (frames : List (HostMachine.Frame Binding))
    (liveTranscript : List HostExchange) (cursor : Nat) (error : Atom) :
    StepAligned transcript
      (HostMachine.unwindError {
        core, frames, host := {
          mode := .live, transcript := liveTranscript, cursor } } error)
      (HostMachine.unwindError {
        core, frames, host := {
          mode := .replay, transcript, cursor } } error) := by
  induction frames with
  | nil =>
      change StateAligned transcript
          { core := core, host := {
              mode := .live, transcript := liveTranscript, cursor } }
          { core := core, host := {
              mode := .replay, transcript, cursor } } ∧ error = error
      simp [StateAligned]
  | cons frame frames induction =>
      cases frame with
      | «catch» outer rest res binding =>
          change StateAligned transcript
            { core := { outer with
                cur := some (Goal.eq res error :: rest, binding)
                world := core.world
                counter := advanceCounterPastAtoms core.counter [error] }
              frames
              host := { mode := .live, transcript := liveTranscript, cursor } }
            { core := { outer with
                cur := some (Goal.eq res error :: rest, binding)
                world := core.world
                counter := advanceCounterPastAtoms core.counter [error] }
              frames
              host := { mode := .replay, transcript, cursor } }
          simp [StateAligned]
      | transaction outer rest tmpl binding => exact induction
      | softcut outer rest thn els tmpl binding => exact induction
      | findall outer rest res binding => exact induction
      | table outer key rest res binding => exact induction

theorem completeRecordedStep_unwindError (engine : SubstEngine)
    (prog : Prog) (gt : GroundingTable) (transcript : List HostExchange)
    (fuel : Nat) (core : Conf engine.State)
    (frames : List (HostMachine.Frame engine.State)) (host : HostSession)
    (error : Atom) :
    completeRecordedStep engine prog gt transcript fuel
        (HostMachine.unwindError { core, frames, host } error) =
      HostMachine.unwindError { core, frames, host } error := by
  induction frames with
  | nil => rfl
  | cons frame frames induction =>
      cases frame with
      | «catch» outer rest res binding => rfl
      | transaction outer rest tmpl binding =>
          simpa [HostMachine.unwindError, HostMachine.unwindFrames] using induction
      | softcut outer rest thn els tmpl binding =>
          simpa [HostMachine.unwindError, HostMachine.unwindFrames] using induction
      | findall outer rest res binding =>
          simpa [HostMachine.unwindError, HostMachine.unwindFrames] using induction
      | table outer key rest res binding =>
          simpa [HostMachine.unwindError, HostMachine.unwindFrames] using induction

abbrev fromCore {Binding : Type} :=
  HostMachine.fromCoreOutcome (Binding := Binding)

theorem fromCore_aligned {Binding : Type} (transcript : List HostExchange)
    (core : Conf Binding) (frames : List (HostMachine.Frame Binding))
    (liveTranscript : List HostExchange) (cursor : Nat)
    (outcome : SubstEngine.StepOutcomeWith Binding) :
    StepAligned transcript
      (fromCore { core, frames, host := {
        mode := .live, transcript := liveTranscript, cursor } } outcome)
      (fromCore { core, frames, host := {
        mode := .replay, transcript, cursor } } outcome) := by
  cases outcome with
  | progressed next =>
      simp [fromCore, HostMachine.fromCoreOutcome, StepAligned, StateAligned]
  | exhausted next =>
      simp [fromCore, HostMachine.fromCoreOutcome, StepAligned, StateAligned]
  | errored next error =>
      simpa [fromCore, HostMachine.fromCoreOutcome] using
        unwindError_aligned transcript next frames
        liveTranscript cursor error

theorem completeRecordedStep_fromCore_aligned (engine : SubstEngine)
    (prog : Prog) (gt : GroundingTable) (transcript : List HostExchange)
    (fuel : Nat) (core : Conf engine.State)
    (frames : List (HostMachine.Frame engine.State))
    (liveTranscript : List HostExchange) (cursor : Nat)
    (outcome : SubstEngine.StepOutcomeWith engine.State) :
    StepAligned transcript
      (completeRecordedStep engine prog gt transcript fuel
        (fromCore { core, frames, host := {
          mode := .live, transcript := liveTranscript, cursor } } outcome))
      (fromCore { core, frames, host := {
        mode := .replay, transcript, cursor } } outcome) := by
  cases outcome with
  | progressed next =>
      simpa [completeRecordedStep, fromCore, HostMachine.fromCoreOutcome] using
        fromCore_aligned transcript core
        frames liveTranscript cursor (.progressed next)
  | exhausted next =>
      simpa [completeRecordedStep, fromCore, HostMachine.fromCoreOutcome] using
        fromCore_aligned transcript core
        frames liveTranscript cursor (.exhausted next)
  | errored next error =>
      have aligned := unwindError_aligned transcript next frames liveTranscript
        cursor error
      unfold fromCore HostMachine.fromCoreOutcome
      cases left : HostMachine.unwindError
          { core := next, frames, host := {
            mode := .live, transcript := liveTranscript, cursor } } error <;>
        cases right : HostMachine.unwindError
          { core := next, frames, host := {
            mode := .replay, transcript, cursor } } error <;>
        simp_all [completeRecordedStep, StepAligned]

theorem completeRecordedStep_handlePyCall_aligned (engine : SubstEngine)
    (prog : Prog) (gt : GroundingTable) (transcript liveTranscript :
      List HostExchange) (fuel : Nat) (core : Conf engine.State)
    (frames : List (HostMachine.Frame engine.State)) (cursor : Nat)
    (binding : engine.State) (args : List Atom) (res : Atom)
    (rest : List Goal)
    (hcur : core.cur = some (Goal.bin "py-call" args res :: rest, binding))
    (hground : (engine.substMany binding args).1.all Metta.isGround = true) :
    StepAligned transcript
      (completeRecordedStep engine prog gt transcript (fuel + 1)
        (HostMachine.handlePyCall {
          core, frames, host := {
            mode := .live, transcript := liveTranscript, cursor } }
          core res rest (engine.substMany binding args).1
          (engine.substMany binding args).2))
      (HostMachine.handlePyCall {
        core, frames, host := {
          mode := .replay, transcript, cursor } }
        core res rest (engine.substMany binding args).1
        (engine.substMany binding args).2) := by
  cases hrequest : HostRequest.ofPyCallArgs
      (engine.substMany binding args).1 with
  | error message =>
      simpa [HostMachine.handlePyCall, hrequest,
        completeRecordedStep_unwindError] using
        unwindError_aligned transcript core frames liveTranscript cursor
          (HostMachine.marshallingErrorAtom message)
  | ok request =>
      cases hlocal : request.localResponse? with
      | some response =>
          cases response with
          | returned value =>
              simp [HostMachine.handlePyCall, hrequest, hlocal,
                completeRecordedStep, HostMachine.consumeResponse,
                StepAligned, StateAligned]
          | prologReturned answers =>
              simpa [HostMachine.handlePyCall, hrequest, hlocal,
                completeRecordedStep_unwindError,
                HostMachine.consumeResponse] using
                unwindError_aligned transcript core frames liveTranscript cursor
                  (HostMachine.marshallingErrorAtom
                    "Prolog response used outside a Prolog request")
          | failed =>
              simp [HostMachine.handlePyCall, hrequest, hlocal,
                completeRecordedStep, HostMachine.consumeResponse,
                StepAligned, StateAligned]
          | raised error =>
              simpa [HostMachine.handlePyCall, hrequest, hlocal,
                completeRecordedStep_unwindError,
                HostMachine.consumeResponse] using
                unwindError_aligned transcript core frames liveTranscript cursor
                  (HostMachine.pythonErrorAtom error)
      | none =>
          cases hentry : transcript[cursor]? with
          | none =>
              simpa [HostMachine.handlePyCall, hrequest, hlocal,
                completeRecordedStep, completeRecordedStep_unwindError,
                HostSession.resolve, hentry, clearPending] using
                unwindError_aligned transcript core frames liveTranscript cursor
                  (HostMachine.protocolErrorAtom
                    (.transcriptEnded cursor request))
          | some exchange =>
              rcases exchange with ⟨expected, response⟩
              by_cases hmatch :
                  ((Lean.toJson expected).compress ==
                    (Lean.toJson request).compress) = true
              · simp [HostMachine.handlePyCall, hrequest, hlocal,
                  completeRecordedStep, HostSession.resolve, hentry, hmatch,
                  HostSession.supply, HostMachine.stepWith,
                  HostMachine.consumeResponse, hcur, hground,
                  StepAligned, StateAligned]
                cases response with
                | returned value => simp
                | prologReturned answers =>
                    exact unwindError_aligned transcript core frames
                      (liveTranscript ++
                        [{ request, response := .prologReturned answers }])
                      (cursor + 1)
                      (HostMachine.marshallingErrorAtom
                        "Prolog response used outside a Prolog request")
                | failed => simp
                | raised error =>
                    exact unwindError_aligned transcript core frames
                      (liveTranscript ++
                        [{ request, response := .raised error }])
                      (cursor + 1) (HostMachine.pythonErrorAtom error)
              · simpa [HostMachine.handlePyCall, hrequest, hlocal,
                  completeRecordedStep, completeRecordedStep_unwindError,
                  HostSession.resolve, hentry, hmatch, clearPending] using
                  unwindError_aligned transcript core frames liveTranscript cursor
                    (HostMachine.protocolErrorAtom
                      (.transcriptMismatch cursor expected request))

theorem completeRecordedStep_handleReadLine_aligned (engine : SubstEngine)
    (prog : Prog) (gt : GroundingTable) (transcript liveTranscript :
      List HostExchange) (fuel : Nat) (core : Conf engine.State)
    (frames : List (HostMachine.Frame engine.State)) (cursor : Nat)
    (binding : engine.State) (args : List Atom) (res : Atom)
    (rest : List Goal)
    (hcur : core.cur = some (Goal.bin "readln!" args res :: rest, binding)) :
    StepAligned transcript
      (completeRecordedStep engine prog gt transcript (fuel + 1)
        (HostMachine.handleReadLine {
          core, frames, host := {
            mode := .live, transcript := liveTranscript, cursor } }
          core res rest (engine.substMany binding args).2))
      (HostMachine.handleReadLine {
        core, frames, host := {
          mode := .replay, transcript, cursor } }
        core res rest (engine.substMany binding args).2) := by
  cases hentry : transcript[cursor]? with
  | none =>
      simpa [HostMachine.handleReadLine, completeRecordedStep,
        completeRecordedStep_unwindError,
        HostSession.resolve, hentry, clearPending] using
        unwindError_aligned transcript core frames liveTranscript cursor
          (HostMachine.protocolErrorAtom
            (.transcriptEnded cursor HostRequest.readLine))
  | some exchange =>
      rcases exchange with ⟨expected, response⟩
      by_cases hmatch :
          ((Lean.toJson expected).compress ==
            (Lean.toJson HostRequest.readLine).compress) = true
      · simp [HostMachine.handleReadLine, completeRecordedStep,
          HostSession.resolve, hentry, hmatch, HostSession.supply,
          HostMachine.stepWith, HostMachine.consumeResponse, hcur,
          StepAligned, StateAligned]
        cases response with
        | returned value => simp
        | prologReturned answers =>
            exact unwindError_aligned transcript core frames
              (liveTranscript ++
                [{ request := HostRequest.readLine,
                   response := .prologReturned answers }])
              (cursor + 1)
              (HostMachine.marshallingErrorAtom
                "Prolog response used outside a Prolog request")
        | failed => simp
        | raised error =>
            exact unwindError_aligned transcript core frames
              (liveTranscript ++
                [{ request := HostRequest.readLine, response := .raised error }])
              (cursor + 1) (HostMachine.pythonErrorAtom error)
      · simpa [HostMachine.handleReadLine, completeRecordedStep,
          completeRecordedStep_unwindError,
          HostSession.resolve, hentry, hmatch, clearPending] using
          unwindError_aligned transcript core frames liveTranscript cursor
            (HostMachine.protocolErrorAtom
              (.transcriptMismatch cursor expected HostRequest.readLine))

theorem completeRecordedStep_handleClock_aligned (engine : SubstEngine)
    (prog : Prog) (gt : GroundingTable) (transcript liveTranscript :
      List HostExchange) (fuel : Nat) (core : Conf engine.State)
    (frames : List (HostMachine.Frame engine.State)) (cursor : Nat)
    (binding : engine.State) (args : List Atom) (res : Atom)
    (rest : List Goal)
    (hcur : core.cur = some (Goal.bin "get_time" args res :: rest, binding))
    (hvals : (engine.substMany binding args).1 = []) :
    StepAligned transcript
      (completeRecordedStep engine prog gt transcript (fuel + 1)
        (HostMachine.handleClock {
          core, frames, host := {
            mode := .live, transcript := liveTranscript, cursor } }
          core res rest (engine.substMany binding args).2))
      (HostMachine.handleClock {
        core, frames, host := {
          mode := .replay, transcript, cursor } }
        core res rest (engine.substMany binding args).2) := by
  let request : HostRequest := .effect .clock
  cases hentry : transcript[cursor]? with
  | none =>
      simpa [request, HostMachine.handleClock, completeRecordedStep,
        completeRecordedStep_unwindError, HostSession.resolve, hentry,
        clearPending] using
        unwindError_aligned transcript core frames liveTranscript cursor
          (HostMachine.protocolErrorAtom
            (.transcriptEnded cursor request))
  | some exchange =>
      rcases exchange with ⟨expected, response⟩
      by_cases hmatch :
          ((Lean.toJson expected).compress ==
            (Lean.toJson request).compress) = true
      · simp [request, HostMachine.handleClock, completeRecordedStep,
          HostSession.resolve, hentry, hmatch, HostSession.supply,
          HostMachine.stepWith, HostMachine.consumeResponse, hcur, hvals,
          StepAligned, StateAligned]
        cases response with
        | returned value => simp
        | prologReturned answers =>
            exact unwindError_aligned transcript core frames
              (liveTranscript ++
                [{ request, response := .prologReturned answers }])
              (cursor + 1)
              (HostMachine.marshallingErrorAtom
                "Prolog response used outside a Prolog request")
        | failed => simp
        | raised error =>
            exact unwindError_aligned transcript core frames
              (liveTranscript ++ [{ request, response := .raised error }])
              (cursor + 1) (HostMachine.pythonErrorAtom error)
      · simpa [request, HostMachine.handleClock, completeRecordedStep,
          completeRecordedStep_unwindError, HostSession.resolve, hentry,
          hmatch, clearPending] using
          unwindError_aligned transcript core frames liveTranscript cursor
            (HostMachine.protocolErrorAtom
              (.transcriptMismatch cursor expected request))

theorem completeRecordedStep_handlePrintLine_aligned (engine : SubstEngine)
    (prog : Prog) (gt : GroundingTable) (transcript liveTranscript :
      List HostExchange) (fuel : Nat) (core : Conf engine.State)
    (frames : List (HostMachine.Frame engine.State)) (cursor : Nat)
    (binding : engine.State) (args : List Atom) (res : Atom)
    (rest : List Goal) (value : Atom)
    (hcur : core.cur = some (Goal.bin "println!" args res :: rest, binding))
    (hvals : (engine.substMany binding args).1 = [value]) :
    StepAligned transcript
      (completeRecordedStep engine prog gt transcript (fuel + 1)
        (HostMachine.handlePrintLine {
          core, frames, host := {
            mode := .live, transcript := liveTranscript, cursor } }
          core value res rest (engine.substMany binding args).2))
      (HostMachine.handlePrintLine {
        core, frames, host := {
          mode := .replay, transcript, cursor } }
        core value res rest (engine.substMany binding args).2) := by
  let request : HostRequest := .effect (.printLine
    (Metta.Pretty.atom (unchainify 10000 value)))
  cases hentry : transcript[cursor]? with
  | none =>
      simpa [request, HostMachine.handlePrintLine, completeRecordedStep,
        completeRecordedStep_unwindError, HostSession.resolve, hentry,
        clearPending] using
        unwindError_aligned transcript core frames liveTranscript cursor
          (HostMachine.protocolErrorAtom
            (.transcriptEnded cursor request))
  | some exchange =>
      rcases exchange with ⟨expected, response⟩
      by_cases hmatch :
          ((Lean.toJson expected).compress ==
            (Lean.toJson request).compress) = true
      · simp [request, HostMachine.handlePrintLine, completeRecordedStep,
          HostSession.resolve, hentry, hmatch, HostSession.supply,
          HostMachine.stepWith, HostMachine.consumePrintLineResponse,
          hcur, hvals,
          HostMachine.hostDisabled, StepAligned, StateAligned]
        cases response with
        | returned value => simp
        | prologReturned answers =>
            exact unwindError_aligned transcript core frames
              (liveTranscript ++
                [{ request, response := .prologReturned answers }])
              (cursor + 1)
              (HostMachine.marshallingErrorAtom
                "Prolog response used outside a Prolog request")
        | failed => simp
        | raised error =>
            exact unwindError_aligned transcript core frames
              (liveTranscript ++ [{ request, response := .raised error }])
              (cursor + 1) (HostMachine.pythonErrorAtom error)
      · simpa [request, HostMachine.handlePrintLine, completeRecordedStep,
          completeRecordedStep_unwindError, HostSession.resolve, hentry,
          hmatch, clearPending] using
          unwindError_aligned transcript core frames liveTranscript cursor
            (HostMachine.protocolErrorAtom
              (.transcriptMismatch cursor expected request))

theorem completeRecordedStep_handleTranslatePredicate_aligned
    (engine : SubstEngine) (prog : Prog) (gt : GroundingTable)
    (transcript liveTranscript : List HostExchange) (fuel : Nat)
    (core : Conf engine.State)
    (frames : List (HostMachine.Frame engine.State)) (cursor : Nat)
    (binding : engine.State) (args : List Atom) (res : Atom) (rest : List Goal)
    (innerExpr : Atom) (functor : String) (ptArgs : List PrologTerm)
    (vars : List String)
    (hcur : core.cur =
      some (Goal.bin "translatePredicate" args res :: rest, binding))
    (hvals : (engine.substMany binding args).1 = [innerExpr])
    (hbuild : buildPrologCall innerExpr = some (functor, ptArgs, vars)) :
    StepAligned transcript
      (completeRecordedStep engine prog gt transcript (fuel + 1)
        (HostMachine.handleTranslatePredicate {
          core, frames, host := {
            mode := .live, transcript := liveTranscript, cursor } }
          core gt functor ptArgs vars res rest (engine.substMany binding args).2))
      (HostMachine.handleTranslatePredicate {
        core, frames, host := {
          mode := .replay, transcript, cursor } }
        core gt functor ptArgs vars res rest (engine.substMany binding args).2) := by
  cases hlocal : localPrologGoals? core.world gt functor ptArgs res rest with
  | some goals =>
      simp [HostMachine.handleTranslatePredicate, hlocal,
        completeRecordedStep, StepAligned, StateAligned]
  | none =>
      cases hentry : transcript[cursor]? with
      | none =>
          simpa [HostMachine.handleTranslatePredicate, hlocal,
            completeRecordedStep, completeRecordedStep_unwindError,
            HostSession.resolve, hentry, clearPending] using
            unwindError_aligned transcript core frames liveTranscript cursor
              (HostMachine.protocolErrorAtom
                (.transcriptEnded cursor
                  (HostRequest.ofPrologCall functor ptArgs vars)))
      | some exchange =>
          rcases exchange with ⟨expected, response⟩
          by_cases hmatch :
              ((Lean.toJson expected).compress ==
                (Lean.toJson
                  (HostRequest.ofPrologCall functor ptArgs vars)).compress) = true
          · simp [HostMachine.handleTranslatePredicate, hlocal,
              completeRecordedStep, HostSession.resolve, hentry, hmatch,
              HostSession.supply, HostMachine.stepWith, hcur, hvals, hbuild,
              StepAligned, StateAligned]
            cases response with
            | returned value =>
                exact unwindError_aligned transcript core frames
                  (liveTranscript ++
                    [{ request := HostRequest.ofPrologCall functor ptArgs vars,
                       response := .returned value }])
                  (cursor + 1)
                  (HostMachine.marshallingErrorAtom
                    "ordinary host response used for a Prolog request")
            | prologReturned answers => simp
            | failed => simp
            | raised error =>
                exact unwindError_aligned transcript core frames
                  (liveTranscript ++
                    [{ request := HostRequest.ofPrologCall functor ptArgs vars,
                       response := .raised error }])
                  (cursor + 1) (HostMachine.pythonErrorAtom error)
          · simpa [HostMachine.handleTranslatePredicate, hlocal,
              completeRecordedStep, completeRecordedStep_unwindError,
              HostSession.resolve, hentry, hmatch, clearPending] using
              unwindError_aligned transcript core frames liveTranscript cursor
                (HostMachine.protocolErrorAtom
                  (.transcriptMismatch cursor expected
                    (HostRequest.ofPrologCall functor ptArgs vars)))

theorem recordedStepWith_replay (engine : SubstEngine) (prog : Prog)
    (gt : GroundingTable) (transcript liveTranscript : List HostExchange)
    (fuel : Nat) (core : Conf engine.State)
    (frames : List (HostMachine.Frame engine.State)) (cursor : Nat) :
    StepAligned transcript
      (recordedStepWith engine prog gt transcript fuel {
        core, frames, host := {
          mode := .live, transcript := liveTranscript, cursor } })
      (HostMachine.stepWith engine prog gt fuel {
        core, frames, host := {
          mode := .replay, transcript, cursor } }) := by
  cases fuel with
  | zero =>
      simp [recordedStepWith, completeRecordedStep, HostMachine.stepWith,
        StepAligned, StateAligned]
  | succ fuel =>
      by_cases hdone : core.cur = none ∧ core.alts = []
      · cases frames <;>
          simp [recordedStepWith, completeRecordedStep, HostMachine.stepWith,
            hdone, StepAligned, StateAligned]
      · cases hcur : core.cur with
        | none =>
            have halts : core.alts ≠ [] := by
              intro empty
              exact hdone ⟨hcur, empty⟩
            have aligned := completeRecordedStep_fromCore_aligned engine prog gt
              transcript (fuel + 1) core frames liveTranscript cursor
              (engine.stepCleanWith prog gt fuel core)
            simpa [recordedStepWith, HostMachine.stepWith, hdone, hcur,
              halts, fromCore, HostMachine.fromCoreOutcome]
              using aligned
        | some current =>
            rcases current with ⟨goals, binding⟩
            cases goals with
            | nil =>
                have aligned := completeRecordedStep_fromCore_aligned engine prog gt
                  transcript (fuel + 1) core frames liveTranscript cursor
                  (engine.stepCleanWith prog gt fuel core)
                simpa [recordedStepWith, HostMachine.stepWith, hdone, hcur,
                  fromCore, HostMachine.fromCoreOutcome] using aligned
            | cons goal rest =>
                cases goal with
                | bin op args res =>
                    by_cases hop : op = "py-call"
                    · subst op
                      by_cases hground :
                          (engine.substMany binding args).1.all Metta.isGround = true
                      · simp [recordedStepWith, HostMachine.stepWith, hcur,
                          hground]
                        exact completeRecordedStep_handlePyCall_aligned engine
                          prog gt transcript liveTranscript fuel core
                          frames cursor binding args res rest hcur hground
                      · have aligned := completeRecordedStep_fromCore_aligned
                          engine prog gt transcript (fuel + 1) core frames
                          liveTranscript cursor
                          (engine.stepCleanWith prog gt fuel core)
                        simpa [recordedStepWith, HostMachine.stepWith, hdone, hcur,
                          hground, fromCore, HostMachine.fromCoreOutcome] using aligned
                    · by_cases hopr : op = "readln!"
                      · subst op
                        simp [recordedStepWith, HostMachine.stepWith, hcur]
                        exact completeRecordedStep_handleReadLine_aligned engine
                          prog gt transcript liveTranscript fuel core
                          frames cursor binding args res rest hcur
                      · by_cases hprint : op = "println!"
                        · subst op
                          cases hvals : (engine.substMany binding args).1 with
                          | nil =>
                            simpa [recordedStepWith, HostMachine.stepWith,
                              HostMachine.hostDisabled, hcur, hvals,
                              completeRecordedStep_unwindError] using
                              unwindError_aligned transcript core frames
                                liveTranscript cursor
                                (HostMachine.marshallingErrorAtom
                                  "println! arity")
                          | cons value tail =>
                            cases tail with
                            | nil =>
                              simp [recordedStepWith, HostMachine.stepWith,
                                HostMachine.hostDisabled, hcur, hvals]
                              exact completeRecordedStep_handlePrintLine_aligned
                                engine prog gt transcript liveTranscript fuel core
                                frames cursor binding args res rest value hcur hvals
                            | cons _ _ =>
                              simpa [recordedStepWith, HostMachine.stepWith,
                                HostMachine.hostDisabled, hcur, hvals,
                                completeRecordedStep_unwindError] using
                                unwindError_aligned transcript core frames
                                  liveTranscript cursor
                                  (HostMachine.marshallingErrorAtom
                                    "println! arity")
                        · by_cases hclock : op = "get_time"
                          · subst op
                            cases hvals : (engine.substMany binding args).1 with
                            | nil =>
                              simp [recordedStepWith, HostMachine.stepWith,
                                hcur, hvals]
                              exact completeRecordedStep_handleClock_aligned engine
                                prog gt transcript liveTranscript fuel core frames
                                cursor binding args res rest hcur hvals
                            | cons _ _ =>
                              simpa [recordedStepWith, HostMachine.stepWith,
                                hcur, hvals, completeRecordedStep_unwindError] using
                                unwindError_aligned transcript core frames
                                  liveTranscript cursor
                                  (HostMachine.marshallingErrorAtom
                                    "get_time arity")
                          · by_cases hopt : op = "translatePredicate"
                            · subst op
                              cases hvals : (engine.substMany binding args).1 with
                              | nil =>
                                simpa [recordedStepWith, HostMachine.stepWith,
                                  hcur, hvals, completeRecordedStep_unwindError] using
                                  unwindError_aligned transcript core frames
                                    liveTranscript cursor
                                    (HostMachine.marshallingErrorAtom
                                      "translatePredicate arity")
                              | cons innerExpr tl =>
                                cases tl with
                                | nil =>
                                  cases hbuild : buildPrologCall innerExpr with
                                  | none =>
                                    simpa [recordedStepWith, HostMachine.stepWith,
                                      hcur, hvals, hbuild,
                                      completeRecordedStep_unwindError] using
                                      unwindError_aligned transcript core frames
                                        liveTranscript cursor
                                        (HostMachine.marshallingErrorAtom
                                          s!"translatePredicate goal: {reprStr (deepUnchain innerExpr)}")
                                  | some fpv =>
                                    obtain ⟨functor, ptArgs, vars⟩ := fpv
                                    simp [recordedStepWith, HostMachine.stepWith,
                                      hcur, hvals, hbuild]
                                    exact
                                      completeRecordedStep_handleTranslatePredicate_aligned
                                        engine prog gt transcript liveTranscript fuel
                                        core frames cursor binding args res rest
                                        innerExpr functor ptArgs vars hcur hvals hbuild
                                | cons _ _ =>
                                  simpa [recordedStepWith, HostMachine.stepWith,
                                    hcur, hvals, completeRecordedStep_unwindError] using
                                    unwindError_aligned transcript core frames
                                      liveTranscript cursor
                                      (HostMachine.marshallingErrorAtom
                                        "translatePredicate arity")
                            · have aligned := completeRecordedStep_fromCore_aligned
                                engine prog gt transcript (fuel + 1) core frames
                                liveTranscript cursor
                                (engine.stepCleanWith prog gt fuel core)
                              simpa [recordedStepWith, HostMachine.stepWith, hdone,
                                hcur, hop, hopr, hprint, hclock, hopt, fromCore,
                                HostMachine.fromCoreOutcome] using aligned
                | catchg tmpl sub res =>
                    simp [recordedStepWith, completeRecordedStep,
                      HostMachine.stepWith, HostMachine.pushNested, hcur,
                      StepAligned, StateAligned]
                | transactiong tmpl sub =>
                    simp [recordedStepWith, completeRecordedStep,
                      HostMachine.stepWith, HostMachine.pushNested, hcur,
                      StepAligned, StateAligned]
                | softcut tmpl sub thn els =>
                    simp [recordedStepWith, completeRecordedStep,
                      HostMachine.stepWith, HostMachine.pushNested, hcur,
                      StepAligned, StateAligned]
                | findall tmpl sub res =>
                    simp [recordedStepWith, completeRecordedStep,
                      HostMachine.stepWith, HostMachine.pushNested, hcur,
                      StepAligned, StateAligned]
                | call function args res =>
                    by_cases htable :
                        core.world.canTableCall function
                          (engine.substMany binding args).1 = true
                    · cases hlookup : core.world.tableLookup
                          (tableKey function (engine.substMany binding args).1) with
                      | none =>
                          simp [recordedStepWith, completeRecordedStep,
                            HostMachine.stepWith, HostMachine.pushNested,
                            hcur, htable, hlookup, StepAligned, StateAligned]
                      | some value =>
                          have aligned := completeRecordedStep_fromCore_aligned
                            engine prog gt transcript (fuel + 1) core frames
                            liveTranscript cursor
                            (engine.stepCleanWith prog gt fuel core)
                          simpa [recordedStepWith, HostMachine.stepWith, hdone,
                            hcur, htable, hlookup, fromCore,
                            HostMachine.fromCoreOutcome] using aligned
                    · have aligned := completeRecordedStep_fromCore_aligned
                        engine prog gt transcript (fuel + 1) core frames
                        liveTranscript cursor
                        (engine.stepCleanWith prog gt fuel core)
                      simpa [recordedStepWith, HostMachine.stepWith, hdone, hcur,
                        htable, fromCore, HostMachine.fromCoreOutcome] using aligned
                | callDyn head args res =>
                    have aligned := completeRecordedStep_fromCore_aligned engine
                      prog gt transcript (fuel + 1) core frames liveTranscript
                      cursor (engine.stepCleanWith prog gt fuel core)
                    simpa [recordedStepWith, HostMachine.stepWith, hdone, hcur,
                      fromCore, HostMachine.fromCoreOutcome] using aligned
                | evalg value res =>
                    have aligned := completeRecordedStep_fromCore_aligned engine
                      prog gt transcript (fuel + 1) core frames liveTranscript
                      cursor (engine.stepCleanWith prog gt fuel core)
                    simpa [recordedStepWith, HostMachine.stepWith, hdone, hcur,
                      fromCore, HostMachine.fromCoreOutcome] using aligned
                | eq left right =>
                    have aligned := completeRecordedStep_fromCore_aligned engine
                      prog gt transcript (fuel + 1) core frames liveTranscript
                      cursor (engine.stepCleanWith prog gt fuel core)
                    simpa [recordedStepWith, HostMachine.stepWith, hdone, hcur,
                      fromCore, HostMachine.fromCoreOutcome] using aligned
                | compileAlias left right =>
                    have aligned := completeRecordedStep_fromCore_aligned engine
                      prog gt transcript (fuel + 1) core frames liveTranscript
                      cursor (engine.stepCleanWith prog gt fuel core)
                    simpa [recordedStepWith, HostMachine.stepWith, hdone, hcur,
                      fromCore, HostMachine.fromCoreOutcome] using aligned
                | cut =>
                    have aligned := completeRecordedStep_fromCore_aligned engine
                      prog gt transcript (fuel + 1) core frames liveTranscript
                      cursor (engine.stepCleanWith prog gt fuel core)
                    simpa [recordedStepWith, HostMachine.stepWith, hdone, hcur,
                      fromCore, HostMachine.fromCoreOutcome] using aligned
                | cutAt count =>
                    have aligned := completeRecordedStep_fromCore_aligned engine
                      prog gt transcript (fuel + 1) core frames liveTranscript
                      cursor (engine.stepCleanWith prog gt fuel core)
                    simpa [recordedStepWith, HostMachine.stepWith, hdone, hcur,
                      fromCore, HostMachine.fromCoreOutcome] using aligned
                | onceg tmpl sub res =>
                    have aligned := completeRecordedStep_fromCore_aligned engine
                      prog gt transcript (fuel + 1) core frames liveTranscript
                      cursor (engine.stepCleanWith prog gt fuel core)
                    simpa [recordedStepWith, HostMachine.stepWith, hdone, hcur,
                      fromCore, HostMachine.fromCoreOutcome] using aligned
                | amb branches res =>
                    have aligned := completeRecordedStep_fromCore_aligned engine
                      prog gt transcript (fuel + 1) core frames liveTranscript
                      cursor (engine.stepCleanWith prog gt fuel core)
                    simpa [recordedStepWith, HostMachine.stepWith, hdone, hcur,
                      fromCore, HostMachine.fromCoreOutcome] using aligned
                | spread value res =>
                    have aligned := completeRecordedStep_fromCore_aligned engine
                      prog gt transcript (fuel + 1) core frames liveTranscript
                      cursor (engine.stepCleanWith prog gt fuel core)
                    simpa [recordedStepWith, HostMachine.stepWith, hdone, hcur,
                      fromCore, HostMachine.fromCoreOutcome] using aligned
                | ite cond thn els res =>
                    have aligned := completeRecordedStep_fromCore_aligned engine
                      prog gt transcript (fuel + 1) core frames liveTranscript
                      cursor (engine.stepCleanWith prog gt fuel core)
                    simpa [recordedStepWith, HostMachine.stepWith, hdone, hcur,
                      fromCore, HostMachine.fromCoreOutcome] using aligned
                | smatch pattern =>
                    have aligned := completeRecordedStep_fromCore_aligned engine
                      prog gt transcript (fuel + 1) core frames liveTranscript
                      cursor (engine.stepCleanWith prog gt fuel core)
                    simpa [recordedStepWith, HostMachine.stepWith, hdone, hcur,
                      fromCore, HostMachine.fromCoreOutcome] using aligned
                | wact op args res =>
                    have aligned := completeRecordedStep_fromCore_aligned engine
                      prog gt transcript (fuel + 1) core frames liveTranscript
                      cursor (engine.stepCleanWith prog gt fuel core)
                    simpa [recordedStepWith, HostMachine.stepWith, hdone, hcur,
                      fromCore, HostMachine.fromCoreOutcome] using aligned

theorem recordedStepWith_of_aligned (engine : SubstEngine) (prog : Prog)
    (gt : GroundingTable) (transcript : List HostExchange) (fuel : Nat)
    (live replay : HostMachine.State engine.State)
    (aligned : StateAligned transcript live replay) :
    StepAligned transcript
      (recordedStepWith engine prog gt transcript fuel live)
      (HostMachine.stepWith engine prog gt fuel replay) := by
  rcases live with ⟨liveCore, liveFrames,
    ⟨liveMode, liveTranscript, liveCursor, livePending, liveReady⟩⟩
  rcases replay with ⟨replayCore, replayFrames,
    ⟨replayMode, replayTranscript, replayCursor, replayPending, replayReady⟩⟩
  simp only [StateAligned] at aligned
  rcases aligned with
    ⟨coreEq, framesEq, liveModeEq, replayModeEq, replayTranscriptEq,
      cursorEq, livePendingEq, liveReadyEq, replayPendingEq, replayReadyEq⟩
  subst replayCore
  subst replayFrames
  subst liveMode
  subst replayMode
  subst replayTranscript
  subst replayCursor
  subst livePending
  subst liveReady
  subst replayPending
  subst replayReady
  exact recordedStepWith_replay engine prog gt transcript liveTranscript fuel
    liveCore liveFrames liveCursor

def RunAligned (transcript : List HostExchange) {Binding : Type}
    (live replay : HostMachine.RunOutcome Binding) : Prop :=
  match live, replay with
  | .done left, .done right => StateAligned transcript left right
  | .limited left, .limited right => StateAligned transcript left right
  | .exhausted left, .exhausted right => StateAligned transcript left right
  | .errored left leftError, .errored right rightError =>
      StateAligned transcript left right ∧ leftError = rightError
  | _, _ => False

/-- Pure counterpart of the live IO driver for a fixed transcript.  Resolving
    a suspension consumes no semantic fuel; only the completed PeTTa step is
    charged. -/
def runRecordedWith (engine : SubstEngine) (prog : Prog)
    (gt : GroundingTable) (transcript : List HostExchange) :
    Nat → HostMachine.State engine.State → Option Nat →
      HostMachine.RunOutcome engine.State
  | 0, state, limit =>
      if state.frames.isEmpty && state.core.cur.isNone &&
          state.core.alts.isEmpty then
        .done state
      else if state.frames.isEmpty &&
          limit.any (fun maximum => state.core.answers.length ≥ maximum) then
        .limited state
      else
        .exhausted state
  | fuel + 1, state, limit =>
      if state.frames.isEmpty && state.core.cur.isNone &&
          state.core.alts.isEmpty then
        .done state
      else if state.frames.isEmpty &&
          limit.any (fun maximum => state.core.answers.length ≥ maximum) then
        .limited state
      else
        match recordedStepWith engine prog gt transcript (fuel + 1) state with
        | .progressed next =>
            runRecordedWith engine prog gt transcript fuel next limit
        | .requested next request => .requested next request (fuel + 1)
        | .exhausted done => .exhausted done
        | .errored done error => .errored done error

theorem runRecordedWith_replay (engine : SubstEngine) (prog : Prog)
    (gt : GroundingTable) (transcript : List HostExchange) :
    ∀ fuel live replay limit,
      StateAligned transcript live replay →
      RunAligned transcript
        (runRecordedWith engine prog gt transcript fuel live limit)
        (HostMachine.runWith engine prog gt fuel replay limit) := by
  intro fuel
  induction fuel with
  | zero =>
      intro live replay limit aligned
      rcases live with ⟨liveCore, liveFrames,
        ⟨liveMode, liveTranscript, liveCursor, livePending, liveReady⟩⟩
      rcases replay with ⟨replayCore, replayFrames,
        ⟨replayMode, replayTranscript, replayCursor, replayPending,
          replayReady⟩⟩
      simp only [StateAligned] at aligned
      rcases aligned with
        ⟨coreEq, framesEq, liveModeEq, replayModeEq, replayTranscriptEq,
          cursorEq, livePendingEq, liveReadyEq, replayPendingEq,
          replayReadyEq⟩
      subst replayCore
      subst replayFrames
      subst liveMode
      subst replayMode
      subst replayTranscript
      subst replayCursor
      subst livePending
      subst liveReady
      subst replayPending
      subst replayReady
      by_cases finished :
          (liveFrames = [] ∧ liveCore.cur = none) ∧ liveCore.alts = []
      · simp [runRecordedWith, HostMachine.runWith, finished, RunAligned,
          StateAligned]
      · by_cases reached :
            liveFrames = [] ∧
              Option.any (fun maximum =>
                decide (maximum ≤ liveCore.answers.length)) limit = true
        · have coreNotFinished :
              ¬(liveCore.cur = none ∧ liveCore.alts = []) := by
            intro coreFinished
            exact finished ⟨⟨reached.1, coreFinished.1⟩, coreFinished.2⟩
          simp [runRecordedWith, HostMachine.runWith, reached,
            coreNotFinished, RunAligned, StateAligned]
        · simp [runRecordedWith, HostMachine.runWith, finished, reached,
            RunAligned, StateAligned]
  | succ fuel induction =>
      intro live replay limit aligned
      have stepAligned := recordedStepWith_of_aligned engine prog gt transcript
        (fuel + 1) live replay aligned
      rcases live with ⟨liveCore, liveFrames,
        ⟨liveMode, liveTranscript, liveCursor, livePending, liveReady⟩⟩
      rcases replay with ⟨replayCore, replayFrames,
        ⟨replayMode, replayTranscript, replayCursor, replayPending,
          replayReady⟩⟩
      simp only [StateAligned] at aligned
      rcases aligned with
        ⟨coreEq, framesEq, liveModeEq, replayModeEq, replayTranscriptEq,
          cursorEq, livePendingEq, liveReadyEq, replayPendingEq,
          replayReadyEq⟩
      subst replayCore
      subst replayFrames
      subst liveMode
      subst replayMode
      subst replayTranscript
      subst replayCursor
      subst livePending
      subst liveReady
      subst replayPending
      subst replayReady
      by_cases finished :
          (liveFrames = [] ∧ liveCore.cur = none) ∧ liveCore.alts = []
      · simp [runRecordedWith, HostMachine.runWith,
          HostMachine.hostDisabled, finished, RunAligned, StateAligned]
      · by_cases reached :
            liveFrames = [] ∧
              Option.any (fun maximum =>
                decide (maximum ≤ liveCore.answers.length)) limit = true
        · have coreNotFinished :
              ¬(liveCore.cur = none ∧ liveCore.alts = []) := by
            intro coreFinished
            exact finished ⟨⟨reached.1, coreFinished.1⟩, coreFinished.2⟩
          simp [runRecordedWith, HostMachine.runWith,
            HostMachine.hostDisabled, reached, coreNotFinished, RunAligned,
            StateAligned]
        · simp [runRecordedWith, HostMachine.runWith,
            HostMachine.hostDisabled, finished, reached]
          cases liveStep : recordedStepWith engine prog gt transcript
              (fuel + 1) {
                core := liveCore
                frames := liveFrames
                host := {
                  mode := .live
                  transcript := liveTranscript
                  cursor := liveCursor } } <;>
            cases replayStep : HostMachine.stepWith engine prog gt (fuel + 1) {
                core := liveCore
                frames := liveFrames
                host := {
                  mode := .replay
                  transcript
                  cursor := liveCursor } } <;>
            simp [liveStep, replayStep, StepAligned] at stepAligned
          · exact induction _ _ limit stepAligned
          · exact stepAligned
          · exact stepAligned

inductive RunObservation (Binding : Type) where
  | done (state : HostMachine.ExecutionState Binding)
  | limited (state : HostMachine.ExecutionState Binding)
  | requested (state : HostMachine.ExecutionState Binding)
      (request : HostRequest) (fuelRemaining : Nat)
  | exhausted (state : HostMachine.ExecutionState Binding)
  | errored (state : HostMachine.ExecutionState Binding) (error : Atom)

def observeRun {Binding : Type} :
    HostMachine.RunOutcome Binding → RunObservation Binding
  | .done state => .done (HostMachine.observeState state)
  | .limited state => .limited (HostMachine.observeState state)
  | .requested state request remaining =>
      .requested (HostMachine.observeState state) request remaining
  | .exhausted state => .exhausted (HostMachine.observeState state)
  | .errored state error => .errored (HostMachine.observeState state) error

theorem StateAligned.observeState_eq {Binding : Type}
    {transcript : List HostExchange} {live replay : HostMachine.State Binding}
    (aligned : StateAligned transcript live replay) :
    HostMachine.observeState live = HostMachine.observeState replay := by
  rcases aligned with ⟨coreEq, framesEq, _⟩
  cases live
  cases replay
  simp_all [HostMachine.observeState]

theorem canonical_state_aligned {Binding : Type}
    (transcript liveTranscript : List HostExchange) (core : Conf Binding)
    (frames : List (HostMachine.Frame Binding)) (cursor : Nat) :
    StateAligned transcript
      { core, frames, host := {
          mode := .live, transcript := liveTranscript, cursor } }
      { core, frames, host := {
          mode := .replay, transcript, cursor } } := by
  simp [StateAligned]

theorem RunAligned.observeRun_eq {Binding : Type}
    {transcript : List HostExchange}
    {live replay : HostMachine.RunOutcome Binding}
    (aligned : RunAligned transcript live replay) :
    observeRun live = observeRun replay := by
  cases live <;> cases replay <;> simp [RunAligned] at aligned
  · simp [observeRun, StateAligned.observeState_eq aligned]
  · simp [observeRun, StateAligned.observeState_eq aligned]
  · simp [observeRun, StateAligned.observeState_eq aligned]
  · simp [observeRun, StateAligned.observeState_eq aligned.1, aligned.2]

/-- Whole-run replay theorem stated at the complete observable-machine level.
    `ExecutionState` retains answer order and multiplicity, alternatives,
    world effects, counters, and nested continuations; only trusted host-session
    bookkeeping is erased. -/
theorem runRecordedWith_replay_observation (engine : SubstEngine)
    (prog : Prog) (gt : GroundingTable) (transcript : List HostExchange)
    (fuel : Nat) (live replay : HostMachine.State engine.State)
    (limit : Option Nat) (aligned : StateAligned transcript live replay) :
    observeRun (runRecordedWith engine prog gt transcript fuel live limit) =
      observeRun (HostMachine.runWith engine prog gt fuel replay limit) :=
  RunAligned.observeRun_eq
    (runRecordedWith_replay engine prog gt transcript fuel live replay limit
      aligned)

theorem fixedTranscript_replay_observation (engine : SubstEngine)
    (prog : Prog) (gt : GroundingTable) (transcript liveTranscript :
      List HostExchange) (fuel : Nat) (core : Conf engine.State)
    (frames : List (HostMachine.Frame engine.State)) (cursor : Nat)
    (limit : Option Nat) :
    observeRun
        (runRecordedWith engine prog gt transcript fuel
          { core, frames, host := {
              mode := .live, transcript := liveTranscript, cursor } }
          limit) =
      observeRun
        (HostMachine.runWith engine prog gt fuel
          { core, frames, host := {
              mode := .replay, transcript, cursor } }
          limit) :=
  runRecordedWith_replay_observation engine prog gt transcript fuel _ _ limit
    (canonical_state_aligned transcript liveTranscript core frames cursor)

end HostReplay
end PLeaTTa
