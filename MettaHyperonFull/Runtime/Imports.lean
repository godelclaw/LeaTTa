-- SPDX-License-Identifier: Apache-2.0

/-
Import resolution shared by the LeaTTa and pleatta executables: pre-read a
program's `import!` targets (transitively, cycle-guarded) into a
`name -> atoms` map at the IO layer; the pure interpreters consult the map.
Factored out of Main.lean unchanged.
-/
import MettaHyperonFull.Minimal.Stdlib

open Metta
open Metta.Runtime
open Metta.Minimal

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
                match parseFile (← IO.FS.readFile fp) with
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
  match parseFile src with
  | Except.error _ => pure Std.HashMap.emptyWithCapacity
  | Except.ok atoms => loadImportsFuel libRoot 64 Std.HashMap.emptyWithCapacity [] dir atoms Std.HashMap.emptyWithCapacity
