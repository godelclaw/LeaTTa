-- SPDX-License-Identifier: Apache-2.0

/-
pleatta — core PeTTa via its own semantics: compile to clauses, run the SLD
machine. CLI-compatible with LeaTTa's `--file` contract (one `[a, b, c]`
result line) so the differential harness can drive both engines.

Exit 2 with `PLEATTA-NOCOMPILE: <reason>` = the file uses forms outside the
current compile equations (a spec gap, listed loudly; the harness may fall
back to the rewriting kernel for such files, counted visibly).
-/
import PLeaTTa.Compile
import PLeaTTa.Machine
import PLeaTTa.SubstMachine
import PLeaTTa.HostRunner
import PLeaTTa.HostProvenance
import PLeaTTa.RuntimeImports
import PLeaTTa.Trace
import MettaHyperonFull.Runtime.Parser
import MettaHyperonFull.Core.Pretty
import PLeaTTa.Builtins

open PLeaTTa
open Metta (Atom Subst)

inductive HostCliMode where
  | disabled
  | live (transcriptOut : System.FilePath)
  | replay (transcriptIn : System.FilePath)
  | liveCheckpoint (transcriptOut : System.FilePath) (exchanges : Nat)
  | replayCheckpoint (transcriptIn : System.FilePath) (exchanges : Nat)

private def HostCliMode.checkpointLimit? : HostCliMode → Option Nat
  | .liveCheckpoint _ exchanges => some exchanges
  | .replayCheckpoint _ exchanges => some exchanges
  | _ => none

private def HostCliMode.isReplay : HostCliMode → Bool
  | .replay _ | .replayCheckpoint _ _ => true
  | _ => false

/-- Reproduce only console-output events consumed by a replayed query.  The
    pure machine still performs no IO; the CLI projects recorded output after
    the query step and before the aggregate answer line. -/
private def emitReplayPrintLines (transcript : List HostExchange)
    (start stop : Nat) : IO Unit := do
  for exchange in (transcript.drop start).take (stop - start) do
    match exchange.request with
    | .effect (.printLine text) => IO.println text
    | _ => pure ()

private def hostOutcomeParts : HostMachine.RunOutcome Subst →
    Conf × Bool × Option Atom × HostSession
  | .done state => (state.core, false, none, state.host)
  | .limited state => (state.core, false, none, state.host)
  | .requested state request _ =>
      (state.core, false,
        some (HostMachine.errorAtom "protocol"
          s!"unhandled host request: {repr request}"), state.host)
  | .exhausted state => (state.core, true, none, state.host)
  | .errored state error => (state.core, false, some error, state.host)

private def installSourceClauseBatch (world : PWorld)
    (pendingClauses : List (String × Clause))
    (pendingClauseKeys : List String) : PWorld :=
  let sourceClauses := pendingClauses.reverse
  let sourceKeys := pendingClauseKeys.reverse
  let priorKeys := world.effectiveProgClauseKeys
  let withClauses := world.replaceProgClauses
    (world.progClauses ++ sourceClauses)
  { withClauses with progClauseKeys := priorKeys ++ sourceKeys }

def guardUnsupported (src : String) : Except String Unit := do
  let bad := ["(pragma!", "(quote-eval"]
  for b in bad do
    if (src.splitOn b).length > 1 then
      throw s!"uses {b} (outside v1 compile equations)"
  .ok ()

mutual
/-- CLI-only profiler: execute the machine, counting nested `softcut` and
    `findall` sub-runs that the ordinary `step` performs internally, and
    retain the peak active substitution size seen along the run. -/
partial def runCount (prog : Prog) (gt : Metta.GroundingTable) (fuel : Nat)
    (c : Conf) (limit : Option Nat) : Conf × Nat × Nat :=
  let activeSubst := match c.cur with
    | some (_, b) => b.length
    | none => 0
  match fuel with
  | 0 => (c, 0, activeSubst)
  | fuel + 1 =>
      if c.cur.isNone && c.alts.isEmpty then (c, 0, activeSubst)
      else if limit.any (fun l => c.answers.length ≥ l) then
        (c, 0, activeSubst)
      else
        let (c', nested, nestedMaxSubst) := stepCount prog gt fuel c
        let (d, n, tailMaxSubst) := runCount prog gt fuel c' limit
        (d, n + nested + 1,
          max activeSubst (max nestedMaxSubst tailMaxSubst))

partial def stepCount (prog : Prog) (gt : Metta.GroundingTable)
    (fuel : Nat) (c : Conf) : Conf × Nat × Nat :=
  match c.cur with
  | some (Goal.transactiong tmpl sub :: rest, b) =>
      let txSub := transactionSub tmpl sub
      let subConf : Conf :=
        { cur := some (txSub, b), alts := [], world := c.world,
          counter := c.counter, qterm := tmpl,
          barriers := resetBarrierCache c.barriers }
      let (d, subSteps, maxSubst) := runCount prog gt fuel subConf none
      let next :=
        if d.answers.isEmpty then
          pull { c with cur := none, world := c.world, counter := d.counter }
        else
          pull { c with cur := none, world := d.world, counter := d.counter,
                        alts := d.answerValues.map (fun inst =>
                          Alt.br (Goal.eq tmpl inst :: rest) b) ++ c.alts }
      (next, subSteps, maxSubst)
  | some (Goal.softcut tmpl sub thn els :: rest, b) =>
      let subConf : Conf :=
        { cur := some (sub, b), alts := [], world := c.world,
          counter := c.counter, qterm := tmpl,
          barriers := resetBarrierCache c.barriers }
      let (d, subSteps, maxSubst) := runCount prog gt fuel subConf none
      let next :=
        if d.answers.isEmpty then
          { c with cur := some (els ++ rest, b),
                   world := d.world, counter := d.counter }
        else
          PLeaTTa.pull { c with cur := none,
                                world := d.world, counter := d.counter,
                                alts := d.answerValues.map (fun inst =>
                                  Alt.br (Goal.eq tmpl inst :: thn ++ rest) b)
                                  ++ c.alts }
      (next, subSteps, maxSubst)
  | some (Goal.findall tmpl sub res :: rest, b) =>
      let subConf : Conf :=
        { cur := some (sub, b), alts := [], world := c.world,
          counter := c.counter, qterm := tmpl,
          barriers := resetBarrierCache c.barriers }
      let (subDone, subSteps, maxSubst) := runCount prog gt fuel subConf none
      let items := chainOf subDone.answerValues
      ({ c with cur := some (Goal.eq res items :: rest, b),
                world := subDone.world, counter := subDone.counter },
       subSteps, maxSubst)
  | _ => (PLeaTTa.step prog gt fuel c, 0, 0)
end

private def goalSummary : Goal → String
  | .call f args _ => s!"call:{f}/{args.length}"
  | .bin op args _ => s!"builtin:{op}/{args.length}"
  | .callDyn _ args _ => s!"dynamic-call/{args.length}"
  | .evalg _ _ => "eval"
  | .catchg _ _ _ => "catch"
  | .softcut _ _ _ _ => "softcut"
  | .eq _ _ => "unify"
  | .cut => "cut"
  | .cutAt _ => "cut-at"
  | .findall _ _ _ => "findall"
  | .onceg _ _ _ => "once"
  | .transactiong _ _ => "transaction"
  | .amb branches _ => s!"amb/{branches.length}"
  | .spread _ _ => "spread"
  | .ite _ _ _ _ => "if"
  | .smatch _ => "space-match"
  | .wact op args _ => s!"world-action:{op}/{args.length}"

private def stallSummary (c : Conf) : String :=
  match c.cur with
  | some (Goal.eq left right :: _, b) =>
      let vals := [left, right].map fun atom =>
        unchainify 1000 (subst b atom)
      s!"unify:{Metta.Pretty.atoms vals}"
  | some (Goal.bin op args _ :: _, b) =>
      let vals := args.map (fun a => unchainify 1000 (subst b a))
      s!"builtin:{op}/{args.length}:{Metta.Pretty.atoms vals}"
  | some (g :: _, _) => goalSummary g
  | some ([], _) => "pull"
  | none => "none"

private structure HostProfileResult where
  outcome : HostMachine.RunOutcome
    SubstEngine.executablePersistent.State
  steps : Nat
  maxActive : Nat
  maxDepth : Nat

private def persistentBindingSizes
    (binding : SubstEngine.executablePersistent.State) : Nat × Nat :=
  let runtimeState := binding.1.1
  (runtimeState.active.size, runtimeState.memo.depth)

private def persistentConfSizes
    (core : Conf SubstEngine.executablePersistent.State) : Nat × Nat :=
  let initial := match core.cur with
    | some (_, binding) => persistentBindingSizes binding
    | none => (0, 0)
  core.alts.foldl (fun current alt =>
    match alt with
    | .barrier => current
    | .br _ binding =>
        let sizes := persistentBindingSizes binding
        (max current.1 sizes.1, max current.2 sizes.2)) initial

private def hostProfileCheckpointReached (exchangeLimit? : Option Nat)
    (state : HostMachine.State SubstEngine.executablePersistent.State) : Bool :=
  exchangeLimit?.any (fun exchangeLimit =>
    state.host.cursor >= exchangeLimit && state.host.pending.isNone &&
      state.host.ready.isNone)

/-- CLI-only replay profiler.  It executes the same persistent host stepper,
counting semantic steps and reading only O(1) representation counters; it
does not force the proof-facing substitution denotation while sampling. -/
private def runHostProfile (prog : Prog)
    (gt : Metta.GroundingTable) (exchangeLimit? : Option Nat := none) : Nat →
    HostMachine.State SubstEngine.executablePersistent.State →
    Nat → Nat → Nat → HostProfileResult
  | fuel, state, steps, maxActive, maxDepth =>
      let sizes := persistentConfSizes state.core
      let maxActive := max maxActive sizes.1
      let maxDepth := max maxDepth sizes.2
      if hostProfileCheckpointReached exchangeLimit? state then
        { outcome := .limited state, steps, maxActive, maxDepth }
      else if state.frames.isEmpty && state.core.cur.isNone &&
          state.core.alts.isEmpty then
        { outcome := .done state, steps, maxActive, maxDepth }
      else match fuel with
      | 0 => { outcome := .exhausted state, steps, maxActive, maxDepth }
      | fuel + 1 =>
          match HostMachine.stepWith SubstEngine.executablePersistent prog gt
              (fuel + 1) state with
          | .progressed next =>
              runHostProfile prog gt exchangeLimit? fuel next (steps + 1)
                maxActive maxDepth
          | .requested next request =>
              { outcome := .requested next request (fuel + 1)
                steps, maxActive, maxDepth }
          | .exhausted done =>
              { outcome := .exhausted done, steps := steps + 1,
                maxActive, maxDepth }
          | .errored done error =>
              { outcome := .errored done error, steps := steps + 1,
                maxActive, maxDepth }

/-- PeTTa exposes SWI's launch vector through `argv/2`: index zero is the
    program path, later entries are program arguments, numeric atoms are
    converted to numbers, and an absent index simply has no answer.
    [SPEC metta.pl:273]  Keeping the vector in a per-run grounding makes it
    explicit input to both live execution and deterministic replay. -/
private def argvAtom (value : String) : Atom :=
  match Metta.Runtime.parseInt? value with
  | some number => .gnd (.int number)
  | none =>
      match Metta.Runtime.parseFloat? value with
      | some number => .gnd (.float number)
      | none => .sym value

private def argvGrounding (values : List String) : Metta.Grounding :=
  { name := "argv"
    mode := .evalArgs
    typeSig := none
    impl := fun args =>
      match args with
      | [.gnd (.int index)] =>
          if index < 0 then .ok []
          else
            match values[index.toNat]? with
            | some value => .ok [argvAtom value]
            | none => .ok []
      | _ => .incorrectArgument "argv" }

private def runProgramMain (args : List String) : IO UInt32 := do
  let usage :=
    "usage: pleatta --file <program.metta> [budget] [-- program-args...] | pleatta --host-live <program.metta> <transcript.json> [budget] [-- program-args...] | pleatta --host-replay <program.metta> <transcript.json> [budget] [-- program-args...] | pleatta --host-live-prefix <program.metta> <transcript.json> <exchanges> <budget> [-- program-args...] | pleatta --host-replay-prefix <program.metta> <transcript.json> <exchanges> <budget> [-- program-args...] | pleatta --host-profile-prefix <program.metta> <transcript.json> <exchanges> <budget> [-- program-args...] | pleatta --host-profile <program.metta> <transcript.json> [budget] [-- program-args...] | pleatta --host-provenance <transcript.json> | pleatta --trace <program.metta> <outdir> [budget] | pleatta --profile <program.metta> [fuel]"
  let (path?, traceDir?, profile?, budget?, hostMode, programArgs) := match args with
    | "--file" :: p :: b :: "--" :: rest =>
        match b.toNat? with
        | some n => (some p, none, false, some n, HostCliMode.disabled, rest)
        | none => (none, none, false, none, HostCliMode.disabled, [])
    | "--file" :: p :: "--" :: rest =>
        (some p, none, false, some 4000000, HostCliMode.disabled, rest)
    | ["--file", p] =>
        (some p, none, false, some 4000000, HostCliMode.disabled, [])
    | ["--file", p, b] =>
        match b.toNat? with
        | some n => (some p, none, false, some n, HostCliMode.disabled, [])
        | none => (none, none, false, none, HostCliMode.disabled, [])
    | "--host-live-prefix" :: p :: transcript :: exchanges :: b :: "--" :: rest =>
        match exchanges.toNat?, b.toNat? with
        | some count, some n => (some p, none, false, some n,
            HostCliMode.liveCheckpoint ⟨transcript⟩ count, rest)
        | _, _ => (none, none, false, none, HostCliMode.disabled, [])
    | ["--host-live-prefix", p, transcript, exchanges, b] =>
        match exchanges.toNat?, b.toNat? with
        | some count, some n => (some p, none, false, some n,
            HostCliMode.liveCheckpoint ⟨transcript⟩ count, [])
        | _, _ => (none, none, false, none, HostCliMode.disabled, [])
    | "--host-replay-prefix" :: p :: transcript :: exchanges :: b :: "--" :: rest =>
        match exchanges.toNat?, b.toNat? with
        | some count, some n => (some p, none, false, some n,
            HostCliMode.replayCheckpoint ⟨transcript⟩ count, rest)
        | _, _ => (none, none, false, none, HostCliMode.disabled, [])
    | ["--host-replay-prefix", p, transcript, exchanges, b] =>
        match exchanges.toNat?, b.toNat? with
        | some count, some n => (some p, none, false, some n,
            HostCliMode.replayCheckpoint ⟨transcript⟩ count, [])
        | _, _ => (none, none, false, none, HostCliMode.disabled, [])
    | "--host-profile-prefix" :: p :: transcript :: exchanges :: b :: "--" :: rest =>
        match exchanges.toNat?, b.toNat? with
        | some count, some n => (some p, none, true, some n,
            HostCliMode.replayCheckpoint ⟨transcript⟩ count, rest)
        | _, _ => (none, none, false, none, HostCliMode.disabled, [])
    | ["--host-profile-prefix", p, transcript, exchanges, b] =>
        match exchanges.toNat?, b.toNat? with
        | some count, some n => (some p, none, true, some n,
            HostCliMode.replayCheckpoint ⟨transcript⟩ count, [])
        | _, _ => (none, none, false, none, HostCliMode.disabled, [])
    | "--host-live" :: p :: transcript :: b :: "--" :: rest =>
        match b.toNat? with
        | some n => (some p, none, false, some n,
            HostCliMode.live ⟨transcript⟩, rest)
        | none => (none, none, false, none, HostCliMode.disabled, [])
    | "--host-live" :: p :: transcript :: "--" :: rest =>
        (some p, none, false, some 4000000,
          HostCliMode.live ⟨transcript⟩, rest)
    | ["--host-live", p, transcript] =>
        (some p, none, false, some 4000000,
          HostCliMode.live ⟨transcript⟩, [])
    | ["--host-live", p, transcript, b] =>
        match b.toNat? with
        | some n => (some p, none, false, some n,
            HostCliMode.live ⟨transcript⟩, [])
        | none => (none, none, false, none, HostCliMode.disabled, [])
    | "--host-replay" :: p :: transcript :: b :: "--" :: rest =>
        match b.toNat? with
        | some n => (some p, none, false, some n,
            HostCliMode.replay ⟨transcript⟩, rest)
        | none => (none, none, false, none, HostCliMode.disabled, [])
    | "--host-replay" :: p :: transcript :: "--" :: rest =>
        (some p, none, false, some 4000000,
          HostCliMode.replay ⟨transcript⟩, rest)
    | ["--host-replay", p, transcript] =>
        (some p, none, false, some 4000000,
          HostCliMode.replay ⟨transcript⟩, [])
    | ["--host-replay", p, transcript, b] =>
        match b.toNat? with
        | some n => (some p, none, false, some n,
            HostCliMode.replay ⟨transcript⟩, [])
        | none => (none, none, false, none, HostCliMode.disabled, [])
    | "--host-profile" :: p :: transcript :: b :: "--" :: rest =>
        match b.toNat? with
        | some n => (some p, none, true, some n,
            HostCliMode.replay ⟨transcript⟩, rest)
        | none => (none, none, false, none, HostCliMode.disabled, [])
    | "--host-profile" :: p :: transcript :: "--" :: rest =>
        (some p, none, true, some 400000,
          HostCliMode.replay ⟨transcript⟩, rest)
    | ["--host-profile", p, transcript] =>
        (some p, none, true, some 400000,
          HostCliMode.replay ⟨transcript⟩, [])
    | ["--host-profile", p, transcript, b] =>
        match b.toNat? with
        | some n => (some p, none, true, some n,
            HostCliMode.replay ⟨transcript⟩, [])
        | none => (none, none, false, none, HostCliMode.disabled, [])
    | ["--trace", p, d] =>
        (some p, some d, false, some 4000000, HostCliMode.disabled, [])
    | ["--trace", p, d, b] =>
        match b.toNat? with
        | some n => (some p, some d, false, some n, HostCliMode.disabled, [])
        | none => (none, none, false, none, HostCliMode.disabled, [])
    | ["--profile", p] =>
        (some p, none, true, some 400000, HostCliMode.disabled, [])
    | ["--profile", p, f] =>
        match f.toNat? with
        | some n => (some p, none, true, some n, HostCliMode.disabled, [])
        | none => (none, none, false, none, HostCliMode.disabled, [])
    | [p] => (some p, none, false, some 3000000, HostCliMode.disabled, [])
    | _ => (none, none, false, none, HostCliMode.disabled, [])
  let some path := path? | do
    IO.eprintln usage; return 2
  let budget := budget?.getD 4000000
  let src ← IO.FS.readFile path
  match Metta.Runtime.parseFile src with
  | .error e => IO.eprintln s!"PLEATTA-NOCOMPILE: parse error: {e}"; return 2
  | .ok atoms0 =>
    let importAttempt ← loadRuntimeImports ⟨path⟩ atoms0
    let .ok importResult := importAttempt | do
      let .error error := importAttempt | unreachable!
      IO.eprintln s!"PLEATTA-NOCOMPILE: {error}"
      return 2
    let forms := importResult.forms
    let hostCatalog : HostModuleCatalog := {
      python := importResult.pythonModules
      prolog := importResult.prologModules }
    let atoms := forms.flatMap SourceForm.seedAtoms
    match guardUnsupported src with
    | .error e => IO.eprintln s!"PLEATTA-NOCOMPILE: {e}"; return 2
    | .ok () =>
    let groundingTable := argvGrounding (path :: programArgs) :: pleattaTable
    let isBin := fun (s : String) =>
      (groundingTable.map (·.name)).contains s
    let preAtoms := (Metta.Runtime.parseFile preludeSrc).toOption.getD []
    let preForms := preAtoms.map (SourceForm.atom · true)
    let preEventCount ←
      match compileProgramSequentialForms isBin preForms with
      | .error e => IO.eprintln s!"PLEATTA-NOCOMPILE: prelude: {e}"; return 2
      | .ok (_, evs) => pure evs.length
    match compileProgramSequentialForms isBin (preForms ++ forms) with
    | .error e => IO.eprintln s!"PLEATTA-NOCOMPILE: {e}"; return 2
    | .ok (prog, events) =>
      let staticArities := prog.clauses.map (fun (f, c) => (f, c.params.length))
      let mut world : PWorld :=
        ({ knownHeads := (prog.clauses.map (·.1)).eraseDups,
           knownArities := staticArities } : PWorld).reindexSpaces.reindexClauses
      let (initialHost, initialWorker) ← match hostMode with
        | .disabled => pure (({} : HostSession), none)
        | .replay transcriptPath =>
            pure (HostSession.replay (← readHostTranscript transcriptPath), none)
        | .replayCheckpoint transcriptPath _ =>
            pure (HostSession.replay (← readHostTranscript transcriptPath), none)
        | .live _ =>
            let workerPath := (← IO.getEnv "PLEATTA_PY_WORKER").getD
              "scripts/pleatta-python-worker.py"
            let python := (← IO.getEnv "PLEATTA_PYTHON").getD "python3"
            pure (HostSession.live,
              some (← PythonWorker.start ⟨workerPath⟩ python))
        | .liveCheckpoint _ _ =>
            let workerPath := (← IO.getEnv "PLEATTA_PY_WORKER").getD
              "scripts/pleatta-python-worker.py"
            let python := (← IO.getEnv "PLEATTA_PYTHON").getD "python3"
            pure (HostSession.live,
              some (← PythonWorker.start ⟨workerPath⟩ python))
      let mut hostSession := initialHost
      let mut pythonWorker? := initialWorker
      -- Consecutive source clauses are not observable until the next query.
      -- Accumulate them newest-first and install the whole source-order batch
      -- once at that boundary, avoiding quadratic `progClauses ++ [entry]`
      -- construction while preserving sequential top-level visibility.
      let mut pendingClauses : List (String × Clause) := []
      let mut pendingClauseKeys : List String := []
      let sourceHighWater := resolutionSeedHighWaterAtoms (preAtoms ++ atoms)
      let mut counter := max 1000000 sourceHighWater
      let mut results : List Atom := []
      let mut perBang : List (List Atom) := []
      let mut queries : List (List Goal × Atom) := []
      let mut totalSteps := 0
      let mut exhausted := false
      let mut runtimeError : Option Atom := none
      let mut checkpointed := false
      let mut importDepth := 0
      let mut skippingImportDepth : Option Nat := none
      let mut qi := 0
      let mut ei := 0
      for ev in events do
        if runtimeError.isSome || checkpointed then continue
        let visible := ei ≥ preEventCount
        ei := ei + 1
        if skippingImportDepth.isSome then
          match ev with
          | .importBegin =>
              importDepth := importDepth + 1
              continue
          | .importEnd _ =>
              let closesFailedImport := skippingImportDepth == some importDepth
              importDepth := importDepth - 1
              if closesFailedImport then skippingImportDepth := none
              continue
          | _ => continue
        match ev with
        | TopEvent.importBegin =>
            importDepth := importDepth + 1
        | TopEvent.importEnd observable =>
            if !pendingClauses.isEmpty then
              world := installSourceClauseBatch world pendingClauses
                pendingClauseKeys
              pendingClauses := []
              pendingClauseKeys := []
            importDepth := importDepth - 1
            if visible && observable then
              results := results ++ [trueA]
              perBang := perBang ++ [[trueA]]
              queries := queries ++ [([], trueA)]
              qi := qi + 1
        | TopEvent.fact a =>
            if visible then
              world := world.addAtom selfSpace (chainify a)
        | TopEvent.typeDecl subj ty =>
            world :=
              if visible then
                { world.addAtom selfSpace
                    (chainify (Atom.expr [Atom.sym ":", subj, ty])) with
                  typeDecls := world.typeDecls ++ [(subj, ty)] }
              else
                { world with typeDecls := world.typeDecls ++ [(subj, ty)] }
        | TopEvent.clause src f c =>
            let world' :=
              if visible then world.addAtom selfSpace (chainify src)
              else world
            world := world'.captureMeta src c
            pendingClauses := (f, c) :: pendingClauses
            pendingClauseKeys := clauseAlphaKey c :: pendingClauseKeys
        | TopEvent.tabled f arity observable =>
            world := { world with
              tabledArities := (f, arity) ::
                (world.tabledArities.filter (fun p =>
                  !(p.1 == f && p.2 == arity))) }
            if visible && observable then
              results := results ++ [trueA]
              perBang := perBang ++ [[trueA]]
              qi := qi + 1
        | TopEvent.prologRegister functions observable =>
            world := { world with
              prologFunctions :=
                (world.prologFunctions ++ functions).eraseDups }
            if visible && observable then
              results := results ++ [trueA]
              perBang := perBang ++ [[trueA]]
              queries := queries ++ [([], trueA)]
              qi := qi + 1
        | TopEvent.hostImport moduleName observable =>
            if !pendingClauses.isEmpty then
              world := installSourceClauseBatch world pendingClauses
                pendingClauseKeys
              pendingClauses := []
              pendingClauseKeys := []
            let request := HostRequest.importModule moduleName
            let (response?, nextHost, nextWorker, fatal?) ← match hostMode with
              | .disabled =>
                  pure (none, hostSession, pythonWorker?,
                    some (HostMachine.protocolErrorAtom (.unavailable request)))
              | .replay _ =>
                  match resolveReplayRequest hostSession request with
                  | .ok (response, next) =>
                      pure (some response, next, pythonWorker?, none)
                  | .error error =>
                      pure (none, hostSession, pythonWorker?,
                        some (HostMachine.protocolErrorAtom error))
              | .replayCheckpoint _ _ =>
                  match resolveReplayRequest hostSession request with
                  | .ok (response, next) =>
                      pure (some response, next, pythonWorker?, none)
                  | .error error =>
                      pure (none, hostSession, pythonWorker?,
                        some (HostMachine.protocolErrorAtom error))
              | .live _ =>
                  match pythonWorker? with
                  | none =>
                      pure (none, hostSession, none,
                        some (HostMachine.errorAtom "protocol"
                          "Python worker is not running"))
                  | some worker =>
                      let (response, next, worker) ←
                        resolveLiveRequest hostCatalog worker
                          hostSession request
                      pure (some response, next, some worker, none)
              | .liveCheckpoint _ _ =>
                  match pythonWorker? with
                  | none =>
                      pure (none, hostSession, none,
                        some (HostMachine.errorAtom "protocol"
                          "Python worker is not running"))
                  | some worker =>
                      let (response, next, worker) ←
                        resolveLiveRequest hostCatalog worker
                          hostSession request
                      pure (some response, next, some worker, none)
            hostSession := nextHost
            pythonWorker? := nextWorker
            if hostMode.checkpointLimit?.any
                (fun limit => hostSession.cursor >= limit) then
              checkpointed := true
            match fatal? with
            | some error =>
                if importDepth = 0 then runtimeError := some error
                else skippingImportDepth := some importDepth
            | none =>
                match response? with
                | some (.raised error) =>
                    let atom := HostMachine.pythonErrorAtom error
                    if importDepth = 0 then runtimeError := some atom
                    else skippingImportDepth := some importDepth
                | some (.returned _) =>
                    if visible && observable then
                      results := results ++ [trueA]
                      perBang := perBang ++ [[trueA]]
                      queries := queries ++ [([], trueA)]
                      qi := qi + 1
                | some (.prologReturned _) =>
                    let atom := HostMachine.marshallingErrorAtom
                      "Prolog response used for a module import"
                    if importDepth = 0 then runtimeError := some atom
                    else skippingImportDepth := some importDepth
                | some .failed =>
                    let atom := HostMachine.errorAtom "protocol"
                      "host import failed"
                    if importDepth = 0 then runtimeError := some atom
                    else skippingImportDepth := some importDepth
                | none =>
                    let atom := HostMachine.errorAtom "protocol"
                      "host import produced no response"
                    if importDepth = 0 then runtimeError := some atom
                    else skippingImportDepth := some importDepth
        | TopEvent.query goals qterm observable =>
            if !pendingClauses.isEmpty then
              world := installSourceClauseBatch world pendingClauses
                pendingClauseKeys
              pendingClauses := []
              pendingClauseKeys := []
            let (profileWorld, profileGoals) :=
              specializeGoals (specializationIsBin groundingTable)
                specializationBuildFuel world goals
            world := profileWorld
            if visible && observable then
              queries := queries ++ [(profileGoals, qterm)]
            let unseededConf : Conf :=
              { cur := some (profileGoals, []), alts := [],
                world, counter, qterm, barriers := some 0 }
            let counterSeed :=
              max counter (resolutionLiveHighWater unseededConf)
            let conf : Conf := { unseededConf with counter := counterSeed }
            let hostCursorBefore := hostSession.cursor
            let (done, steps, maxSubst, incomplete, fatal,
                nextHost, nextWorker) ← match hostMode with
              | .disabled =>
                  let execution :=
                    if profile? then
                      let (_, s, peakSubst) :=
                        runCount prog groundingTable budget conf none
                      match PLeaTTa.SubstEngine.runPersistentClean prog
                          groundingTable budget conf none with
                      | .done d => (d, s, peakSubst, false, none)
                      | .limited d => (d, s, peakSubst, false, none)
                      | .exhausted d => (d, s, peakSubst, true, none)
                      | .errored d err =>
                          (d, s, peakSubst, false, some err)
                    else
                      match PLeaTTa.SubstEngine.runPersistentClean prog
                          groundingTable budget conf none with
                      | .done d => (d, 0, 0, false, none)
                      | .limited d => (d, 0, 0, false, none)
                      | .exhausted d => (d, 0, 0, true, none)
                      | .errored d err => (d, 0, 0, false, some err)
                  pure (execution.1, execution.2.1, execution.2.2.1,
                    execution.2.2.2.1, execution.2.2.2.2,
                    hostSession, pythonWorker?)
              | .replay _ =>
                  if profile? then
                    let engine := SubstEngine.executablePersistent
                    let initial : HostMachine.State engine.State := {
                      core := SubstEngine.lift engine conf
                      host := hostSession }
                    let profiled := runHostProfile prog groundingTable none
                      budget initial 0 0 0
                    IO.println s!"HOST_PROFILE q{qi} steps={profiled.steps} maxActive={profiled.maxActive} maxDepth={profiled.maxDepth}"
                    let parts := hostOutcomeParts <|
                      HostMachine.mapRunOutcome engine.denote profiled.outcome
                    pure (parts.1, profiled.steps, profiled.maxActive,
                      parts.2.1, parts.2.2.1, parts.2.2.2, pythonWorker?)
                  else
                    let parts := hostOutcomeParts <|
                      runReplay prog groundingTable budget conf hostSession
                    pure (parts.1, 0, 0, parts.2.1, parts.2.2.1,
                      parts.2.2.2, pythonWorker?)
              | .replayCheckpoint _ exchangeLimit =>
                  if profile? then
                    let engine := SubstEngine.executablePersistent
                    let initial : HostMachine.State engine.State := {
                      core := SubstEngine.lift engine conf
                      host := hostSession }
                    let profiled := runHostProfile prog groundingTable
                      (some exchangeLimit) budget initial 0 0 0
                    IO.println s!"HOST_PROFILE q{qi} steps={profiled.steps} maxActive={profiled.maxActive} maxDepth={profiled.maxDepth}"
                    let parts := hostOutcomeParts <|
                      HostMachine.mapRunOutcome engine.denote profiled.outcome
                    pure (parts.1, profiled.steps, profiled.maxActive,
                      parts.2.1, parts.2.2.1, parts.2.2.2, pythonWorker?)
                  else
                    let parts := hostOutcomeParts <|
                      runReplayCheckpoint prog groundingTable budget conf
                        hostSession exchangeLimit
                    pure (parts.1, 0, 0, parts.2.1, parts.2.2.1,
                      parts.2.2.2, pythonWorker?)
              | .live _ =>
                  match pythonWorker? with
                  | none =>
                      pure (conf, 0, 0, false,
                        some (HostMachine.errorAtom "protocol"
                          "Python worker is not running"), hostSession, none)
                  | some worker =>
                      let (outcome, worker) ←
                        runLive prog groundingTable hostCatalog
                          worker budget conf hostSession none
                          (match hostMode with
                            | .live transcriptPath => some transcriptPath
                            | _ => none)
                      let parts := hostOutcomeParts outcome
                      pure (parts.1, 0, 0, parts.2.1, parts.2.2.1,
                        parts.2.2.2, some worker)
              | .liveCheckpoint transcriptPath exchangeLimit =>
                  match pythonWorker? with
                  | none =>
                      pure (conf, 0, 0, false,
                        some (HostMachine.errorAtom "protocol"
                          "Python worker is not running"), hostSession, none)
                  | some worker =>
                      let (outcome, worker) ←
                        runLiveCheckpoint prog groundingTable
                          hostCatalog worker budget conf
                          hostSession exchangeLimit (some transcriptPath)
                      let parts := hostOutcomeParts outcome
                      pure (parts.1, 0, 0, parts.2.1, parts.2.2.1,
                        parts.2.2.2, some worker)
            if hostMode.isReplay then
              emitReplayPrintLines nextHost.transcript hostCursorBefore
                nextHost.cursor
            hostSession := nextHost
            pythonWorker? := nextWorker
            if hostMode.checkpointLimit?.any
                (fun limit => hostSession.cursor >= limit) then
              checkpointed := true
            match fatal with
            | some err =>
                if importDepth = 0 then runtimeError := some err
                else skippingImportDepth := some importDepth
            | none =>
                if profile? then
                  totalSteps := totalSteps + steps
                  let doneNow := !incomplete
                  exhausted := exhausted || incomplete
                  let stalled := if incomplete then stallSummary done else "none"
                  let (pendingGoals, substSize) := match done.cur with
                    | some (gs, b) => (gs.length, b.length)
                    | none => (0, 0)
                  let maxAltSubst := done.alts.foldl (fun n alt =>
                    match alt with
                    | .br _ b => Nat.max n b.length
                    | .barrier => n) 0
                  if visible && observable then
                    IO.println s!"PROFILE q{qi} steps={steps} answers={done.answers.length} done={doneNow} stalled={stalled} goals={pendingGoals} subst={substSize} maxSubst={maxSubst} alts={done.alts.length} maxAltSubst={maxAltSubst} selfAtoms={done.world.selfAtoms.length} clauses={done.world.progClauses.length} counter={done.counter}"
                else if incomplete then
                  exhausted := true
                if visible && observable then
                  results := results ++ done.answerValues
                  perBang := perBang ++ [done.answerValues]
                  qi := qi + 1
                world := done.world
                counter := done.counter
      match hostMode with
      | .live transcriptPath =>
          writeHostTranscript transcriptPath hostSession.transcript
      | .liveCheckpoint transcriptPath _ =>
          writeHostTranscript transcriptPath hostSession.transcript
      | _ => pure ()
      if let some worker := pythonWorker? then
        PythonWorker.stop worker
      if let some err := runtimeError then
        IO.eprintln s!"PLEATTA-ERROR: {Metta.Pretty.atom (unchainify 10000 err)}"
        return 2
      match hostMode with
      | .replay _ | .replayCheckpoint _ _ =>
        if hostSession.cursor != hostSession.transcript.length then
          IO.eprintln s!"PLEATTA-ERROR: replay consumed {hostSession.cursor} of {hostSession.transcript.length} host exchanges"
          return (2 : UInt32)
      | _ => pure ()
      if checkpointed then
        IO.println s!"HOST_CHECKPOINT exchanges={hostSession.cursor}"
      if exhausted && !profile? then
        IO.eprintln "PLeaTTa: fuel exhausted before a semantics-licensed result; increase fuel or simplify the program"
        return 2
      if profile? then
        IO.println s!"PROFILE total_steps={totalSteps} answers={results.length} exhausted={exhausted}"
        return 0
      match traceDir? with
      | none =>
          IO.println (Metta.Pretty.atoms (results.map (unchainify 10000)))
          return 0
      | some outdir =>
          -- project once (initial space), then re-derive each answer
          let traceSelf := world.atomsOf selfSpace
          let (wcs, qrels, traceEnv) := Trace.projectProg prog traceSelf queries
          let base := (System.FilePath.mk path).fileStem.getD "trace"
          let mut i := 0
          let mut ok := 0
          let mut tot := 0
          for ((qrel, _), answers) in qrels.zip perBang do
            let mut j := 0
            for ans in answers do
              tot := tot + 1
              match (← Trace.traceAnswer wcs traceEnv qrel ans budget) with
              | some txt =>
                  IO.FS.writeFile ⟨s!"{outdir}/{base}-q{i}-{j}.sexp"⟩ txt
                  ok := ok + 1
              | none =>
                  IO.println s!"NOTRACE q{i} answer {j}"
              j := j + 1
            i := i + 1
          IO.println s!"TRACED {ok}/{tot}"
          return 0

def main (args : List String) : IO UInt32 :=
  match args with
  | ["--host-provenance", transcriptPath] => do
      let transcript ← readHostTranscript ⟨transcriptPath⟩
      IO.println (HostProvenanceSummary.renderTranscript transcript)
      return 0
  | _ => runProgramMain args
