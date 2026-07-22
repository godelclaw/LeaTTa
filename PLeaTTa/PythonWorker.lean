import PLeaTTa.HostProtocol
import Lean.Data.Json

namespace PLeaTTa

open Lean

def pythonWorkerStdio : IO.Process.StdioConfig where
  stdin := .piped
  stdout := .piped
  stderr := .inherit

structure PythonWorker where
  child : IO.Process.Child pythonWorkerStdio
  nextId : Nat := 0

namespace PythonWorker

def start (script : System.FilePath) (python : String := "python3") :
    IO PythonWorker := do
  let child ← IO.Process.spawn {
    cmd := python
    args := #[script.toString]
    stdin := .piped
    stdout := .piped
    stderr := .inherit
  }
  pure { child }

private def protocolFailure {α : Type} (worker : PythonWorker) (message : String) :
    IO α := do
  let exited ← worker.child.tryWait
  let suffix ← match exited with
    | none => pure ""
    | some code => pure s!"; worker exit {code}"
  throw (IO.userError (message ++ suffix))

/-- Execute one typed request against the persistent worker.  `modulePath?`
    is used only for a live import command and never enters the transcript. -/
def request (worker : PythonWorker) (hostRequest : HostRequest)
    (modulePath? : Option System.FilePath := none) :
    IO (HostResponse × PythonWorker) := do
  let command : HostCommand := {
    id := worker.nextId
    request := hostRequest
    modulePath? := modulePath?.map (·.toString)
  }
  worker.child.stdin.putStrLn (Lean.toJson command).compress
  worker.child.stdin.flush
  let line ← worker.child.stdout.getLine
  if line.isEmpty then
    protocolFailure worker "Python worker closed stdout"
  let reply ← match Json.parse line >>= Lean.fromJson? (α := HostReply) with
    | .ok reply => pure reply
    | .error error =>
        protocolFailure worker s!"invalid Python worker reply: {error}"
  if reply.id != worker.nextId then
    protocolFailure worker
      s!"Python worker reply id {reply.id} does not match {worker.nextId}"
  pure (reply.response, { worker with nextId := worker.nextId + 1 })

def stop (worker : PythonWorker) : IO Unit := do
  worker.child.kill
  discard worker.child.wait

end PythonWorker

def writeHostTranscript (path : System.FilePath)
    (transcript : List HostExchange) : IO Unit := do
  let pending : System.FilePath := ⟨path.toString ++ ".pending"⟩
  IO.FS.writeFile pending (Lean.toJson transcript).pretty
  IO.FS.rename pending path

def readHostTranscript (path : System.FilePath) : IO (List HostExchange) := do
  let source ← IO.FS.readFile path
  match Json.parse source >>= Lean.fromJson? (α := List HostExchange) with
  | .ok transcript => pure transcript
  | .error error => throw (IO.userError s!"invalid host transcript: {error}")

end PLeaTTa
