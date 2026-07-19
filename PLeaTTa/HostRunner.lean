import PLeaTTa.HostMachine
import PLeaTTa.PythonWorker

namespace PLeaTTa

open Metta (Subst GroundingTable)

abbrev PythonModuleCatalog := List (String × System.FilePath)
abbrev PrologModuleCatalog := List (String × System.FilePath)

structure HostModuleCatalog where
  python : PythonModuleCatalog := []
  prolog : PrologModuleCatalog := []

private def modulePathFor (catalog : HostModuleCatalog) :
    HostRequest → Option System.FilePath
  | .importModule name => catalog.python.lookup name
  | .call _ _ => none
  | .readLine => none
  | .prologCall functor _ _ => catalog.prolog.lookup functor
  | .effect _ => none

private def executeLiveRequest (catalog : HostModuleCatalog)
    (worker : PythonWorker) : HostRequest → IO (HostResponse × PythonWorker)
  | .readLine => do
      let stdin ← IO.getStdin
      let line ← stdin.getLine
      let trimmed :=
        if line.endsWith "\n" then (line.dropEnd 1).toString else line
      pure (.returned (.string trimmed), worker)
  | .effect (.printLine text) => do
      let stdout ← IO.getStdout
      stdout.putStrLn text
      stdout.flush
      pure (.returned .none, worker)
  | request => worker.request request (modulePathFor catalog request)

def resolveReplayRequest (session : HostSession) (request : HostRequest) :
    Except HostProtocolError (HostResponse × HostSession) :=
  match session.resolve request with
  | .respond response next => .ok (response, next)
  | .fail error => .error error
  | .suspend request _ => .error (.unavailable request)

/-- Execute one explicit top-level host event through the same
    suspend/supply/resolve protocol used by machine-level `py-call`. -/
def resolveLiveRequest (catalog : HostModuleCatalog) (worker : PythonWorker)
    (session : HostSession) (request : HostRequest) :
    IO (HostResponse × HostSession × PythonWorker) := do
  match session.resolve request with
  | .respond response next => pure (response, next, worker)
  | .fail error =>
      throw (IO.userError s!"host request failed: {repr error}")
  | .suspend pending suspended =>
      let (response, worker) ← executeLiveRequest catalog worker pending
      let supplied ← match suspended.supply response with
        | .ok supplied => pure supplied
        | .error error =>
            throw (IO.userError s!"host response injection failed: {repr error}")
      match supplied.resolve request with
      | .respond response next => pure (response, next, worker)
      | .fail error =>
          throw (IO.userError s!"supplied host response failed: {repr error}")
      | .suspend pending _ =>
          throw (IO.userError s!"supplied host response remained pending: {repr pending}")

/-- Continue a live host run until completion, exhaustion, error, or fuel
    exhaustion.  Every response is injected through `HostSession.supply`, so
    live execution creates exactly the transcript replay consumes. -/
partial def continueLive (prog : Prog) (gt : GroundingTable)
    (catalog : HostModuleCatalog) (worker : PythonWorker)
    (checkpoint? : Option System.FilePath := none) :
    HostMachine.RunOutcome Subst →
      IO (HostMachine.RunOutcome Subst × PythonWorker)
  | .requested state request remaining => do
      let (response, worker) ← executeLiveRequest catalog worker request
      let supplied ← match state.host.supply response with
        | .ok supplied => pure supplied
        | .error error =>
            throw (IO.userError s!"host response injection failed: {repr error}")
      if let some checkpoint := checkpoint? then
        writeHostTranscript checkpoint supplied.transcript
      continueLive prog gt catalog worker checkpoint? <|
        HostMachine.resumePersistent prog gt remaining
          { state with host := supplied }
  | outcome => pure (outcome, worker)

def runLive (prog : Prog) (gt : GroundingTable) (catalog : HostModuleCatalog)
    (worker : PythonWorker) (fuel : Nat) (conf : Conf)
    (session : HostSession) (limit : Option Nat := none)
    (checkpoint? : Option System.FilePath := none) :
    IO (HostMachine.RunOutcome Subst × PythonWorker) :=
  continueLive prog gt catalog worker checkpoint? <|
    HostMachine.runPersistent prog gt fuel conf session limit

def runReplay (prog : Prog) (gt : GroundingTable) (fuel : Nat)
    (conf : Conf) (session : HostSession) (limit : Option Nat := none) :
    HostMachine.RunOutcome Subst :=
  HostMachine.runPersistent prog gt fuel conf session limit

/-- A transcript-prefix run stops immediately after the requested number of
    host responses have been consumed by the ordinary machine.  This is a
    verifier boundary for reactive programs; it neither changes their goals
    nor invents a language-level termination signal. -/
private def checkpointReached (exchangeLimit : Nat)
    (state : HostMachine.State SubstEngine.executablePersistent.State) : Bool :=
  state.host.cursor >= exchangeLimit && state.host.pending.isNone &&
    state.host.ready.isNone

private def continueReplayCheckpoint (prog : Prog)
    (gt : GroundingTable) (exchangeLimit : Nat) : Nat →
    HostMachine.State SubstEngine.executablePersistent.State →
    HostMachine.RunOutcome SubstEngine.executablePersistent.State
  | fuel, state =>
      if checkpointReached exchangeLimit state then
        .limited state
      else if state.frames.isEmpty && state.core.cur.isNone &&
          state.core.alts.isEmpty then
        .done state
      else match fuel with
      | 0 => .exhausted state
      | fuel + 1 =>
          match HostMachine.stepWith SubstEngine.executablePersistent prog gt
              (fuel + 1) state with
          | .progressed next =>
              continueReplayCheckpoint prog gt exchangeLimit fuel next
          | .requested next request =>
              .requested next request (fuel + 1)
          | .exhausted done => .exhausted done
          | .errored done error => .errored done error

/-- Replay exactly a finite prefix of a host transcript through the pure
    executable stepper. -/
def runReplayCheckpoint (prog : Prog) (gt : GroundingTable) (fuel : Nat)
    (conf : Conf) (session : HostSession) (exchangeLimit : Nat) :
    HostMachine.RunOutcome Subst :=
  let engine := SubstEngine.executablePersistent
  let initial : HostMachine.State engine.State := {
    core := SubstEngine.lift engine conf
    host := session }
  HostMachine.mapRunOutcome engine.denote <|
    continueReplayCheckpoint prog gt exchangeLimit fuel initial

private partial def continueLiveCheckpoint (prog : Prog)
    (gt : GroundingTable) (catalog : HostModuleCatalog)
    (exchangeLimit : Nat) (checkpoint? : Option System.FilePath) : Nat →
    HostMachine.State SubstEngine.executablePersistent.State → PythonWorker →
    IO (HostMachine.RunOutcome SubstEngine.executablePersistent.State ×
      PythonWorker)
  | fuel, state, worker => do
      if checkpointReached exchangeLimit state then
        pure (.limited state, worker)
      else if state.frames.isEmpty && state.core.cur.isNone &&
          state.core.alts.isEmpty then
        pure (.done state, worker)
      else match fuel with
      | 0 => pure (.exhausted state, worker)
      | fuel + 1 =>
          match HostMachine.stepWith SubstEngine.executablePersistent prog gt
              (fuel + 1) state with
          | .progressed next =>
              continueLiveCheckpoint prog gt catalog exchangeLimit checkpoint?
                fuel next worker
          | .requested next request => do
              let (response, worker) ← executeLiveRequest catalog worker request
              let supplied ← match next.host.supply response with
                | .ok supplied => pure supplied
                | .error error =>
                    throw (IO.userError
                      s!"host response injection failed: {repr error}")
              if let some checkpoint := checkpoint? then
                writeHostTranscript checkpoint supplied.transcript
              continueLiveCheckpoint prog gt catalog exchangeLimit checkpoint?
                (fuel + 1) { next with host := supplied } worker
          | .exhausted done => pure (.exhausted done, worker)
          | .errored done error => pure (.errored done error, worker)

/-- Execute exactly a finite prefix of a live host transcript.  Host waiting
    consumes no semantic fuel, matching `continueLive`; the checkpoint is
    reached only after the final response has been consumed by the machine. -/
def runLiveCheckpoint (prog : Prog) (gt : GroundingTable)
    (catalog : HostModuleCatalog) (worker : PythonWorker) (fuel : Nat)
    (conf : Conf) (session : HostSession) (exchangeLimit : Nat)
    (checkpoint? : Option System.FilePath := none) :
    IO (HostMachine.RunOutcome Subst × PythonWorker) := do
  let engine := SubstEngine.executablePersistent
  let initial : HostMachine.State engine.State := {
    core := SubstEngine.lift engine conf
    host := session }
  let (outcome, worker) ← continueLiveCheckpoint prog gt catalog exchangeLimit
    checkpoint? fuel initial worker
  pure (HostMachine.mapRunOutcome engine.denote outcome, worker)

end PLeaTTa
