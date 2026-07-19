import PLeaTTa.PythonWorker

open PLeaTTa

private def expect (actual expected : HostResponse) (label : String) : IO Unit :=
  if actual == expected then pure ()
  else throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")

def main (args : List String) : IO UInt32 := do
  let [script, fixture] := args
    | throw (IO.userError "expected WORKER.py FIXTURE.py")
  let mut worker ← PythonWorker.start ⟨script⟩
  let (length, next) ← worker.request (.call "len"
    [.list [.integer 1, .integer 2, .integer 3]])
  worker := next
  expect length (.returned (.integer 3)) "list length"

  let (object, next) ← worker.request (.call "types.SimpleNamespace" [])
  worker := next
  let handle ← match object with
    | .returned (.handle id) => pure id
    | other => throw (IO.userError s!"constructor did not return a handle: {repr other}")
  let (setResult, next) ← worker.request
    (.call "setattr" [.handle handle, .string "answer", .integer 42])
  worker := next
  expect setResult (.returned .none) "setattr"
  let (getResult, next) ← worker.request
    (.call "getattr" [.handle handle, .string "answer"])
  worker := next
  expect getResult (.returned (.integer 42)) "getattr"

  let (missing, next) ← worker.request
    (.call "getattr" [.handle handle, .string "missing"])
  worker := next
  match missing with
  | .raised error =>
      if error.kind != "AttributeError" then
        throw (IO.userError s!"wrong exception type: {error.kind}")
  | other => throw (IO.userError s!"missing attribute succeeded: {repr other}")

  let (imported, next) ← worker.request
    (.importModule "python_import_file") (some ⟨fixture⟩)
  worker := next
  expect imported (.returned (.string "true")) "module import"
  let (sum, next) ← worker.request
    (.call "python_import_file.add" [.integer 10, .integer 20])
  worker := next
  expect sum (.returned (.integer 30)) "imported add"

  PythonWorker.stop worker
  IO.println "python worker smoke: PASS"
  pure 0
