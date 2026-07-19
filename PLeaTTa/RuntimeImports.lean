import PLeaTTa.Compile
import PLeaTTa.HostRunner
import PLeaTTa.Builtins
import MettaHyperonFull.Runtime.Parser

namespace PLeaTTa

open Metta (Atom Ground)

structure RuntimeImportResult where
  forms : List SourceForm
  pythonModules : PythonModuleCatalog
  prologModules : PrologModuleCatalog

private inductive ImportTarget where
  | path (value : String)
  | library (namespaceName : String) (path? : Option String)

private def atomText? : Atom → Option String
  | .sym value => some value
  | .gnd (.str value) => some value
  | _ => none

private def importTarget? : Atom → Option ImportTarget
  | .sym value => some (.path value)
  | .gnd (.str value) => some (.path value)
  | .expr [.sym "library", namespaceAtom] =>
      .library <$> atomText? namespaceAtom <*> pure none
  | .expr [.sym "library", namespaceAtom, path] =>
      .library <$> atomText? namespaceAtom <*> (some <$> atomText? path)
  | _ => none

private def importDirective? : Atom → Option ImportTarget
  | .expr [.sym "!", .expr [.sym "import!", _space, target]] =>
      importTarget? target
  | _ => none

private def prologRegistrations? : Atom → Option (List String)
  | .expr [.sym "!",
      .expr [.sym "import_prolog_function", function]] =>
      some (atomText? function).toList
  | .expr [.sym "!",
      .expr [.sym "import_prolog_functions_from_file", _path,
        .expr functions]] =>
      some (functions.filterMap atomText?)
  | _ => none

private def prologFileRegistration? : Atom →
    Option (ImportTarget × List String)
  | .expr [.sym "!",
      .expr [.sym "import_prolog_functions_from_file", path,
        .expr functions]] => do
      let target ← importTarget? path
      pure (target, functions.filterMap atomText?)
  | _ => none

private def registeredHostFunctionAvailable (name : String) : Bool :=
  (Metta.GroundingTable.lookup pleattaTable name).isSome

/-- Explain top-level effect directives that the runtime cannot yet execute.
    This check runs after recognized static imports, so a remaining `import!`
    necessarily has a computed or malformed target. -/
def unsupportedRuntimeDirective? : Atom → Option String
  | atom@(.expr [.sym "!", .expr (.sym "import_prolog_function" :: _)]) =>
      if (prologRegistrations? atom).any
          (·.all registeredHostFunctionAvailable) then none
      else some "import_prolog_function names an unavailable host operation"
  | atom@(.expr [.sym "!",
      .expr (.sym "import_prolog_functions_from_file" :: _)]) =>
      if (prologRegistrations? atom).any
          (·.all registeredHostFunctionAvailable) then none
      else some "import_prolog_functions_from_file names an unavailable host operation"
  | atom@(.expr [.sym "!", .expr (.sym "import!" :: _)]) =>
      if (importDirective? atom).isSome then none
      else some "computed or malformed import! target is unsupported"
  | .expr [.sym "!", .expr (.sym "export!" :: _)] =>
      some "export! requires the persistent-space host bridge"
  | .expr [.sym "!", .expr (.sym "translatePredicate" :: _)] =>
      some "translatePredicate requires the Prolog host bridge"
  | _ => none

private def repositoryName (url : String) : String :=
  let slashLeaf := (url.splitOn "/").reverse.head?.getD url
  let leaf := (slashLeaf.splitOn ":").reverse.head?.getD slashLeaf
  if leaf.endsWith ".git" then (leaf.dropEnd 4).toString else leaf

private def gitImportRepo? : Atom → Option String
  | .expr [.sym "!", .expr (.sym "git-import!" :: url :: _)] =>
      repositoryName <$> atomText? url
  | _ => none

private def hasKnownExtension (path : String) : Bool :=
  path.endsWith ".metta" || path.endsWith ".py" || path.endsWith ".pl"

private def withDefaultExtension (path : String) : String :=
  if hasKnownExtension path then path else path ++ ".metta"

private def stripCurrentPrefix (path : String) : String :=
  if path.startsWith "./" then (path.drop 2).toString else path

private def normalizeBangs : List Atom → List Atom
  | Atom.sym "!" :: atom :: rest =>
      Atom.expr [Atom.sym "!", atom] :: normalizeBangs rest
  | atom :: rest => atom :: normalizeBangs rest
  | [] => []

private def resolvePath (dir : System.FilePath) (value : String) :
    System.FilePath :=
  let path := withDefaultExtension value
  if path.startsWith "/" then ⟨path⟩ else dir / stripCurrentPrefix path

/-- Candidate import paths in priority order. A sibling file resolves against
    the importing file's directory, while paths written from a library root
    (for example `./src/skills.pl`) resolve against the root that supplied the
    imported module. The entry-program and pinned-PeTTa roots remain fallbacks.
    `pickExisting` selects the first candidate that exists on disk. -/
private def resolveTargetCandidates (catalog : List (String × System.FilePath))
    (pettaLibRoot programRoot sourceRoot dir : System.FilePath) :
    ImportTarget → Except String (List System.FilePath)
  | .path value =>
      .ok [resolvePath dir value,
           resolvePath sourceRoot value,
           resolvePath programRoot value,
           resolvePath (pettaLibRoot.parent.getD dir) value]
  | .library namespaceName none =>
      .ok [pettaLibRoot / withDefaultExtension namespaceName]
  | .library namespaceName (some path) =>
      match catalog.lookup namespaceName with
      | some root => .ok [root / stripCurrentPrefix (withDefaultExtension path)]
      | none => .error s!"no pre-provisioned library root for {namespaceName}"

/-- PeTTa executes `import_prolog_functions_from_file` through `exists_file`
    and `consult` in the owning source tree's working directory.  A nested
    MeTTa module therefore does not rebase the Prolog filename to its own
    directory.  Keep that rule distinct from ordinary `import!`, whose path
    imports remain sibling-relative. -/
private def resolvePrologTargetCandidates
    (catalog : List (String × System.FilePath))
    (pettaLibRoot programRoot sourceRoot dir : System.FilePath) :
    ImportTarget → Except String (List System.FilePath)
  | .path value =>
      .ok [resolvePath sourceRoot value,
           resolvePath programRoot value,
           resolvePath (pettaLibRoot.parent.getD dir) value]
  | target =>
      resolveTargetCandidates catalog pettaLibRoot programRoot sourceRoot dir
        target

/-- The stable source root inherited by a module loaded through `target`.
    Ordinary path imports remain in the current source tree. A named library
    carries its catalog root, and PeTTa's built-in library namespace carries
    the checkout root containing `lib/`. -/
private def sourceRootForTarget
    (catalog : List (String × System.FilePath))
    (pettaLibRoot currentRoot : System.FilePath) :
    ImportTarget → System.FilePath
  | .path _ => currentRoot
  | .library _ none => pettaLibRoot.parent.getD currentRoot
  | .library namespaceName (some _) =>
      catalog.lookup namespaceName |>.getD currentRoot

private def initialCatalog (program : System.FilePath) :
    IO (List (String × System.FilePath)) := do
  let programDir := program.parent.getD ⟨"."⟩
  let localRoots := match programDir.fileName with
    | some name => [(name, programDir)]
    | none => []
  let configured := match ← IO.getEnv "PLEATTA_LIBRARY_PATH" with
    | none => []
    | some source => source.splitOn ":" |>.filterMap fun value =>
        if value.isEmpty then none
        else
          let root : System.FilePath := ⟨value⟩
          root.fileName.map fun name => (name, root)
  pure (configured ++ localRoots)

private def pettaLibraryRoot : IO System.FilePath := do
  match ← IO.getEnv "PETTA_LIB_ROOT" with
  | some root => pure ⟨root⟩
  | none =>
      let home := (← IO.getEnv "HOME").getD "."
      pure (⟨home⟩ / "repos" / "PeTTa" / "lib")

private abbrev ImportM := ExceptT String IO

private def readModule (path : System.FilePath) : ImportM (List Atom) := do
  if !(← path.pathExists) then
    throw s!"import target does not exist: {path}"
  let source ← IO.FS.readFile path
  match Metta.Runtime.parseProgram source with
  | .ok atoms => pure atoms
  | .error error => throw s!"cannot parse imported module {path}: {error}"

/-- Select the first candidate import path that exists on disk. If none exist,
    return the primary (file-directory) candidate so the "import target does not
    exist" error names the expected location exactly as before. -/
private def pickExisting (candidates : List System.FilePath) :
    ImportM System.FilePath := do
  for candidate in candidates do
    if ← candidate.pathExists then
      return candidate
  pure (candidates.head?.getD ⟨"."⟩)

private partial def expandForms
    (catalog : List (String × System.FilePath))
    (pettaLibRoot programRoot sourceRoot dir : System.FilePath) (fuel : Nat)
    (visited : List String) (observable : Bool)
    (pythonModules : PythonModuleCatalog)
    (prologModules : PrologModuleCatalog) (atoms : List Atom) :
    ImportM (List SourceForm × PythonModuleCatalog ×
      PrologModuleCatalog × List String) := do
  match atoms with
  | [] => pure ([], pythonModules, prologModules, visited)
  | atom :: rest =>
      match gitImportRepo? atom with
      | some repository =>
          let some root := catalog.lookup repository
            | throw s!"git import requires pre-provisioned library root for {repository}"
          if !(← root.pathExists) then
            throw s!"pre-provisioned library root does not exist for {repository}"
          let success := SourceForm.atom
            (Atom.expr [Atom.sym "!", trueA]) observable
          let (tail, pyModules, plModules, visited) ←
            expandForms catalog pettaLibRoot programRoot sourceRoot dir fuel
              visited observable pythonModules prologModules rest
          pure (success :: tail, pyModules, plModules, visited)
      | none => match importDirective? atom with
        | none =>
            match prologFileRegistration? atom with
            | some (target, functions) =>
                if functions.isEmpty then
                  throw "import_prolog_functions_from_file names no functions"
                let candidates ← liftExcept <|
                  resolvePrologTargetCandidates catalog pettaLibRoot programRoot
                    sourceRoot dir target
                let path ← pickExisting candidates
                if !(← path.pathExists) then
                  throw s!"Prolog import target does not exist: {path}"
                if !(path.toString.endsWith ".pl") then
                  throw s!"Prolog import target is not a .pl file: {path}"
                let hostFunctions := functions.filter (fun function =>
                  importedPrologHostBacked function ||
                    !registeredHostFunctionAvailable function)
                let registered := hostFunctions.foldl (fun modules function =>
                  (function, path) ::
                    modules.filter (fun entry => entry.1 != function))
                  prologModules
                let (tail, pyModules, plModules, visited) ←
                  expandForms catalog pettaLibRoot programRoot sourceRoot dir
                    fuel visited observable pythonModules registered rest
                pure (.prologRegister hostFunctions observable :: tail,
                  pyModules, plModules, visited)
            | none =>
              match prologRegistrations? atom with
              | some functions =>
                  let unavailable :=
                    functions.filter (!registeredHostFunctionAvailable ·)
                  if !unavailable.isEmpty then
                    throw s!"unavailable imported host operations: {unavailable}"
                  let success := SourceForm.atom
                    (Atom.expr [Atom.sym "!", trueA]) observable
                  let (tail, pyModules, plModules, visited) ←
                    expandForms catalog pettaLibRoot programRoot sourceRoot dir
                      fuel visited observable pythonModules prologModules rest
                  pure (success :: tail, pyModules, plModules, visited)
              | none =>
                  if let some error := unsupportedRuntimeDirective? atom then
                    throw error
                  let (tail, pyModules, plModules, visited) ←
                    expandForms catalog pettaLibRoot programRoot sourceRoot dir
                      fuel visited observable pythonModules prologModules rest
                  pure (.atom atom observable :: tail, pyModules, plModules,
                    visited)
        | some target =>
          if fuel = 0 then throw "import nesting limit exhausted"
          let candidates ←
            liftExcept (resolveTargetCandidates catalog pettaLibRoot
              programRoot sourceRoot dir target)
          let path ← pickExisting candidates
          let importedSourceRoot :=
            sourceRootForTarget catalog pettaLibRoot sourceRoot target
          let key := path.toString
          if key.endsWith ".py" then
            if !(← path.pathExists) then
              throw s!"Python import target does not exist: {path}"
            let some moduleName := path.fileStem
              | throw s!"Python import has no module name: {path}"
            let modules := (moduleName, path) ::
              pythonModules.filter (fun entry => entry.1 != moduleName)
            let (tail, modules, plModules, visited) ←
              expandForms catalog pettaLibRoot programRoot sourceRoot dir fuel
                visited observable modules prologModules rest
            pure ([.importBegin, .hostImport moduleName false,
              .importEnd observable] ++ tail, modules, plModules, visited)
          else if key.endsWith ".metta" then
            let (imported, modules, plModules, visited, alreadyLoaded) ←
              if visited.contains key then
                pure ([], pythonModules, prologModules, visited, true)
              else
                let importedAtoms ← readModule path
                let (forms, modules, plModules, visited) ←
                  expandForms catalog pettaLibRoot programRoot
                    importedSourceRoot (path.parent.getD dir) (fuel - 1)
                    (key :: visited) false pythonModules prologModules
                    (normalizeBangs importedAtoms)
                pure (forms, modules, plModules, visited, false)
            let (tail, modules, plModules, visited) ←
              expandForms catalog pettaLibRoot programRoot sourceRoot dir fuel
                visited observable modules plModules rest
            if alreadyLoaded then
              let success := SourceForm.atom
                (Atom.expr [Atom.sym "!", trueA]) observable
              pure (success :: tail, modules, plModules, visited)
            else
              pure ([.importBegin] ++ imported ++
                [.importEnd observable] ++ tail, modules, plModules, visited)
          else
            throw s!"unsupported import target: {path}"

/-- Resolve and flatten MeTTa modules in source order. Imported initializers
    execute but are non-observable; Python modules become explicit host events
    and their filesystem paths remain solely in the runtime catalog. -/
def loadRuntimeImports (program : System.FilePath) (atoms : List Atom) :
    IO (Except String RuntimeImportResult) := do
  let catalog ← initialCatalog program
  let libRoot ← pettaLibraryRoot
  let dir := program.parent.getD ⟨"."⟩
  let expanded ←
    expandForms catalog libRoot dir dir dir 64 [program.toString] true [] []
      (normalizeBangs atoms)
  pure <| expanded.map fun (forms, pythonModules, prologModules, _) =>
    { forms, pythonModules, prologModules }

def SourceForm.seedAtoms : SourceForm → List Atom
  | .atom value _ => [value]
  | .hostImport _ _ => []
  | .prologRegister _ _ => []
  | .importBegin | .importEnd _ => []

end PLeaTTa
