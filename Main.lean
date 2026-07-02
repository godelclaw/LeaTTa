/-
Module: Main
Layer: Executable
Purpose: The runnable LeaTTa entry point. It runs the minimal MeTTa interpreter and stdlib on a
  program, with CLI modes for a built-in demo, running a `.metta` file (`--file` / `--min-file`),
  running a program string (`--min`), running a test file's `!`-assertions as an oracle report
  (`--oracle`), and running an external MeTTaIL dialect file (`--mettail FILE --term TERM`). It also
  resolves and transitively loads `import!` modules, handling both the plain sibling-file form and the
  namespaced `register-module!` form, matching Hyperon's module system. File reading is the only IO;
  the `import!` instruction itself is pure.
Imports: MettaHyperonFull.Minimal.Stdlib, MeTTaIL.Runtime.LanguageFile
Trusted boundary: none
Main exports: main; the helpers demoSource, resolveImport, loadImportsFuel, loadImports.
Open obligations: none
-/
import MettaHyperonFull.Minimal.Stdlib
import MeTTaIL.Runtime.LanguageFile

open Metta
open Metta.Runtime
open Metta.Minimal

def parseFuelArg (s : String) : Except String Nat :=
  match s.toNat? with
  | some n => .ok n
  | none => .error ("invalid fuel `" ++ s ++ "`")

def runMeTTaILFile (path term : String) (fuel : Nat) : IO UInt32 := do
  let src ← IO.FS.readFile path
  match MeTTaIL.LanguageFile.runSource src fuel term with
  | .ok (some out) =>
      IO.println out
      pure 0
  | .ok none =>
      IO.eprintln "MeTTaIL term did not parse"
      pure 1
  | .error msg =>
      IO.eprintln msg
      pure 1

def runMeTTaILFileWithFuelArg (path term fuelRaw : String) : IO UInt32 :=
  match parseFuelArg fuelRaw with
  | .ok fuel => runMeTTaILFile path term fuel
  | .error msg => do
      IO.eprintln msg
      pure 1

/-- A short demo program used when LeaTTa is invoked with no arguments. -/
def demoSource : String := "(= (double $x) ($x $x)) !(double Bob)"

/-- Resolve an `import!` name to a file path, given the module catalog and the importing file's
    directory. Two forms are handled:
    * a plain name `c2_spaces_kb` resolves to the sibling file `c2_spaces_kb.metta`;
    * a namespaced name `chaining:dtl:utils` resolves to `<root>/dtl/utils.metta`, where `<root>`
      is the path registered for module `chaining` by `register-module!`.
    The `:` separator and `register-module!` catalog match Hyperon's module system. -/
def resolveImport (catalog : Std.HashMap String System.FilePath) (dir : System.FilePath)
    (libRoot : System.FilePath) (name : String) : Option System.FilePath :=
  -- PeTTa's `(library lib_x)` form (keyed "library lib_x" by `importName?`):
  -- resolve against the PeTTa lib root (PETTA_LIB_ROOT env, or ~/repos/PeTTa/lib).
  if name.startsWith "library " then
    some (libRoot.join ⟨(name.drop "library ".length).toString ++ ".metta"⟩)
  -- Path-shaped names (PeTTa style): absolute paths pass through; relative
  -- paths resolve against the importing file's directory; `.metta` is
  -- appended only when missing.
  else if name.startsWith "/" || (name.splitOn "/").length > 1 then
    let withExt := if name.endsWith ".metta" then name else name ++ ".metta"
    some (dir.join ⟨withExt⟩)
  else
  match name.splitOn ":" with
  | [] => none
  | [single] => some (dir.join ⟨single ++ ".metta"⟩)
  | mod :: segs => (catalog.get? mod).map fun root =>
      ⟨(segs.foldl (fun acc s => acc ++ "/" ++ s) (toString root)) ++ ".metta"⟩

/-- Recursively load all modules reachable via `import!`, up to `fuel` levels deep. `catalog0` maps
    module names to their root paths (from `register-module!`). `visited` guards against import
    cycles. Missing or unparsable modules are silently skipped. Returns the accumulated
    `name → atoms` map that the pure interpreter consults when it encounters `import!`. -/
def loadImportsFuel (libRoot : System.FilePath) :
    Nat → Std.HashMap String System.FilePath → List String → System.FilePath →
    List Atom → Std.HashMap String (List Atom) → IO (Std.HashMap String (List Atom))
  | 0, _, _, _, _, acc => pure acc
  | fuel + 1, catalog0, visited, dir, atoms, acc => do
      -- Extend the catalog with any `register-module!` roots declared in this file.
      let catalog := (collectModuleRoots atoms).foldl (fun (c : Std.HashMap String System.FilePath) p =>
          let abs := dir.join ⟨p⟩
          c.insert (abs.fileName.getD p) abs) catalog0
      (collectImports atoms).foldlM (init := acc) fun m name => do
        if visited.contains name then pure m
        else match resolveImport catalog dir libRoot name with
          | none => pure m
          | some fp =>
              if ← fp.pathExists then
                match parseProgram (← IO.FS.readFile fp) with
                | Except.ok fatoms =>
                    loadImportsFuel libRoot fuel catalog (name :: visited) (fp.parent.getD dir) fatoms
                      (m.insert name fatoms)
                | Except.error _ => pure m
              else pure m

/-- Load all modules a program imports, transitively. Returns the `name → atoms` map for `import!`.
    IO is limited to reading files; the `import!` instruction itself is pure. The PeTTa
    `(library X)` root comes from `PETTA_LIB_ROOT`, defaulting to `~/repos/PeTTa/lib`. -/
def loadImports (path : String) (src : String) : IO (Std.HashMap String (List Atom)) := do
  let dir := (System.FilePath.mk path).parent.getD (System.FilePath.mk ".")
  let libRoot ← do
    match ← IO.getEnv "PETTA_LIB_ROOT" with
    | some r => pure (System.FilePath.mk r)
    | none =>
        let home := (← IO.getEnv "HOME").getD "."
        pure (System.FilePath.mk home / "repos" / "PeTTa" / "lib")
  match parseProgram src with
  | Except.error _ => pure Std.HashMap.emptyWithCapacity
  | Except.ok atoms => loadImportsFuel libRoot 64 Std.HashMap.emptyWithCapacity [] dir atoms Std.HashMap.emptyWithCapacity

/-- CLI entry point for LeaTTa. Runs on the minimal MeTTa interpreter and stdlib (`Minimal/`).
    * no arguments: run the demo program;
    * `--file PATH` / `--min-file PATH`: run a `.metta` file;
    * `--min PROGRAM`: run a program string;
    * `--mettail PATH --term TERM [--fuel N]`: run `TERM` with a MeTTaIL dialect file;
    * `--oracle PATH`: run a test file's `!`-assertions and report how many evaluate to `()`.
    A leading/anywhere `--petta` flag selects the native-PeTTa evaluation profile
    (`Metta.pettaProfile`) for the minimal-interpreter modes.
    An earlier `Runtime.CLI` four-register runner was retired; see `MettaHyperonFull.lean`. -/
def dispatch (profile : Metta.EvalProfile) : List String → IO UInt32
  | ["--file", path] | ["--min-file", path] => do
      let src ← IO.FS.readFile path
      let imports ← loadImports path src
      IO.println (runMinimalSource src (imports := imports) (profile := profile))
      pure 0
  | ["--oracle", path] => do
      -- Run every `!`-assertion through the minimal interpreter in file order.
      -- An assertion passes iff it evaluates to the unit atom `()`.
      let src ← IO.FS.readFile path
      let imports ← loadImports path src
      IO.println (oracleReport src (imports := imports) (profile := profile))
      pure 0
  | "--min" :: rest => do
      IO.println (runMinimalSource (" ".intercalate rest) (profile := profile))
      pure 0
  | ["--mettail", path, "--term", term] =>
      runMeTTaILFile path term 256
  | ["--mettail", path, "--term", term, "--fuel", fuel] =>
      runMeTTaILFileWithFuelArg path term fuel
  | ["--mettail", path, "--fuel", fuel, "--term", term] =>
      runMeTTaILFileWithFuelArg path term fuel
  | "--mettail" :: _ => do
      IO.eprintln "usage: LeaTTa --mettail FILE --term TERM [--fuel N]"
      pure 1
  | [] => do
      IO.println (runMinimalSource demoSource)
      pure 0
  | args => do
      IO.println (runMinimalSource (" ".intercalate args) (profile := profile))
      pure 0

def main (args : List String) : IO UInt32 :=
  let profile := if args.contains "--petta" then Metta.pettaProfile else Metta.heProfile
  dispatch profile (args.filter (· != "--petta"))
