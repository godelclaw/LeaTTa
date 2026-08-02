import PLeaTTa.HostProtocol
import PLeaTTa.SubstMachine

namespace PLeaTTa
namespace HostMachine

open Metta (Atom GroundingTable Subst)
open SubstEngine

-- Host refinement is stated over the concrete denotation of the reference
-- engine.  Keep that engine opaque globally, while allowing this module to
-- normalize its record projections during proof elaboration.
set_option allowUnsafeReducibility true
attribute [local reducible] SubstEngine.reference

/-- Reified callers for the nested evaluations that the ordinary clean
    executor runs recursively.  Reification lets a Python request suspend at
    any depth without hiding IO in a pure function. -/
inductive Frame (State : Type) where
  | transaction (outer : Conf State) (rest : List Goal) (tmpl : Atom)
      (state : State)
  | softcut (outer : Conf State) (rest thn els : List Goal) (tmpl : Atom)
      (state : State)
  | findall (outer : Conf State) (rest : List Goal) (res : Atom)
      (state : State)
  | table (outer : Conf State) (key : Atom) (rest : List Goal) (res : Atom)
      (state : State)

structure State (Binding : Type) where
  core : Conf Binding
  frames : List (Frame Binding) := []
  host : HostSession := {}

inductive StepOutcome (Binding : Type) where
  | progressed (state : State Binding)
  | requested (state : State Binding) (request : HostRequest)
  | exhausted (state : State Binding)
  | errored (state : State Binding) (error : Atom)

inductive RunOutcome (Binding : Type) where
  | done (state : State Binding)
  | limited (state : State Binding)
  | requested (state : State Binding) (request : HostRequest)
      (fuelRemaining : Nat)
  | exhausted (state : State Binding)
  | errored (state : State Binding) (error : Atom)

/-- The complete machine observation after erasing only trusted-host session
    bookkeeping.  It retains answers, alternatives, world effects, counter,
    nested continuations, and therefore value order and multiplicity. -/
structure ExecutionState (Binding : Type) where
  core : Conf Binding
  frames : List (Frame Binding)

def observeState {Binding : Type} (state : State Binding) :
    ExecutionState Binding :=
  { core := state.core, frames := state.frames }

inductive StepObservation (Binding : Type) where
  | progressed (state : ExecutionState Binding)
  | requested (state : ExecutionState Binding) (request : HostRequest)
  | exhausted (state : ExecutionState Binding)
  | errored (state : ExecutionState Binding) (error : Atom)

def observeStep {Binding : Type} :
    StepOutcome Binding → StepObservation Binding
  | .progressed state => .progressed (observeState state)
  | .requested state request => .requested (observeState state) request
  | .exhausted state => .exhausted (observeState state)
  | .errored state error => .errored (observeState state) error

def errorAtom (kind message : String) : Atom :=
  chainOf [Atom.sym "Error",
    chainOf [Atom.sym "python_error", Atom.sym kind],
    Atom.gnd (.str message)]

def protocolErrorAtom (error : HostProtocolError) : Atom :=
  errorAtom "protocol" (reprStr error)

def marshallingErrorAtom (message : String) : Atom :=
  errorAtom "type_error" message

/-- Reify typed Prolog exceptions produced by host-effect implementations.
    The free context variable matches the implementation-supplied context in
    pinned SWI modulo alpha-renaming. Other worker exceptions retain the
    explicit Python-boundary wrapper. -/
def pythonErrorAtom (error : HostError) : Atom :=
  if error.kind == "existence_error:source_sink" then
    chainOf [Atom.sym "Error",
      chainOf [Atom.sym "existence_error", Atom.sym "source_sink",
        Atom.gnd (.str error.message)],
      Atom.var "_hostErrorContext"]
  else
    errorAtom error.kind error.message

def finishFrame {Binding : Type} (done : Conf Binding) :
    Frame Binding → Conf Binding
  | .transaction outer rest tmpl state =>
      finishTransaction outer done rest tmpl state
  | .softcut outer rest thn els tmpl state =>
      finishSoftcut outer done rest thn els tmpl state
  | .findall outer rest res state => finishFindall outer done rest res state
  | .table outer key rest res state => finishTable outer done key rest res state

/-- Restore a suspended caller while retaining the world and allocation
    high-water reached by a non-transactional nested evaluation.  Control,
    answers, and alternatives are backtrackable caller state. -/
def restoreCallerForError {Binding : Type} (caller current : Conf Binding) :
    Conf Binding :=
  { caller with world := current.world, counter := current.counter }

@[simp] theorem mapConf_restoreCallerForError {Source Target : Type}
    (map : Source → Target) (caller current : Conf Source) :
    SubstEngine.mapConf map (restoreCallerForError caller current) =
      restoreCallerForError (SubstEngine.mapConf map caller)
        (SubstEngine.mapConf map current) := by
  rfl

/-- An exception aborts a transaction just as ordinary failure does: restore
    the caller world, but never rewind the global fresh-name high-water. -/
def restoreTransactionCallerForError {Binding : Type}
    (caller current : Conf Binding) : Conf Binding :=
  { caller with counter := current.counter }

@[simp] theorem mapConf_restoreTransactionCallerForError
    {Source Target : Type} (map : Source → Target)
    (caller current : Conf Source) :
    SubstEngine.mapConf map
        (restoreTransactionCallerForError caller current) =
      restoreTransactionCallerForError (SubstEngine.mapConf map caller)
        (SubstEngine.mapConf map current) := by
  rfl

/-- Propagate an error through suspended nested evaluations.  At every level
    the certified core gets the first opportunity to consume the exception at
    its nearest active streaming-catch delimiter.  If no delimiter is active,
    the nested frame is discarded, its caller control is restored, persistent
    state is threaded forward, and unwinding continues outward. -/
def unwindFrames {Binding : Type} (core : Conf Binding)
    (host : HostSession) : List (Frame Binding) → Atom → StepOutcome Binding
  | frames, error =>
      match catchErrorSuccessor? core error with
      | some caught => .progressed { core := caught, frames, host }
      | none =>
          match frames with
          | [] => .errored { core, host } error
          | .transaction outer _ _ _ :: rest =>
              unwindFrames
                (restoreTransactionCallerForError outer core) host rest error
          | .softcut outer _ _ _ _ _ :: rest =>
              unwindFrames (restoreCallerForError outer core) host rest error
          | .findall outer _ _ _ :: rest =>
              unwindFrames (restoreCallerForError outer core) host rest error
          | .table outer _ _ _ _ :: rest =>
              unwindFrames (restoreCallerForError outer core) host rest error

private def transactionRollbackOuter : Conf Unit :=
  { cur := none
    alts := []
    world := {}
    counter := 3
    qterm := Atom.sym "query" }

private def transactionRollbackInner : Conf Unit :=
  { transactionRollbackOuter with
    world := { transactionRollbackOuter.world with
      selfAtoms := [Atom.sym "transient"] }
    counter := 11 }

private def transactionRollbackHost : HostSession := {}

/-- Ordinary failure and an escaping exception both discard a transaction's
    world mutation.  The exception path nevertheless retains the advanced
    allocation counter, so rollback cannot reissue fresh names. -/
theorem transaction_failure_and_escaping_exception_rollback_witness :
    let failed := finishTransaction transactionRollbackOuter
      transactionRollbackInner [] (Atom.sym "result") ()
    let escaped := unwindFrames transactionRollbackInner
      transactionRollbackHost
      [.transaction transactionRollbackOuter [] (Atom.sym "result") ()]
      (Atom.sym "boom")
    failed.world = transactionRollbackOuter.world ∧
      failed.counter = transactionRollbackInner.counter ∧
      escaped = .errored
        { core := restoreTransactionCallerForError transactionRollbackOuter
            transactionRollbackInner
          host := transactionRollbackHost }
        (Atom.sym "boom") ∧
      transactionRollbackInner.world.selfAtoms = [Atom.sym "transient"] := by
  simp [transactionRollbackOuter, transactionRollbackInner,
    transactionRollbackHost, finishTransaction, pull, pullAuxTracked,
    pullAux, unwindFrames, catchErrorSuccessor?, splitCatchActive,
    restoreTransactionCallerForError]

def unwindError {Binding : Type} (state : State Binding)
    (error : Atom) : StepOutcome Binding :=
  unwindFrames state.core state.host state.frames error

def consumeResponse {Binding : Type} (state : State Binding)
    (core : Conf Binding) (rest : List Goal) (res : Atom)
    (binding : Binding) (response : HostResponse)
    (session : HostSession) : StepOutcome Binding :=
  match response with
  | .returned value =>
      .progressed { state with
        core := enqueueHostAnswers core [value.toAtom] rest res binding
        host := session }
  | .prologReturned _ =>
      unwindError { state with core, host := session }
        (marshallingErrorAtom "Prolog response used outside a Prolog request")
  | .failed =>
      .progressed { state with
        core := pull { core with cur := none }
        host := session }
  | .raised error =>
      unwindError { state with core, host := session } (pythonErrorAtom error)

private theorem observe_unwindFrames_host_independent {Binding : Type}
    (core : Conf Binding) (frames : List (Frame Binding)) (error : Atom)
    (left right : HostSession) :
    observeStep (unwindFrames core left frames error) =
      observeStep (unwindFrames core right frames error) := by
  induction frames generalizing core with
  | nil =>
      unfold unwindFrames
      cases catchErrorSuccessor? core error <;> rfl
  | cons frame frames induction =>
      unfold unwindFrames
      cases found : catchErrorSuccessor? core error with
      | some caught => rfl
      | none =>
          cases frame with
          | transaction outer _ _ _ =>
              exact induction
                (core := restoreTransactionCallerForError outer core)
          | softcut outer _ _ _ _ _ =>
              exact induction (core := restoreCallerForError outer core)
          | findall outer _ _ _ =>
              exact induction (core := restoreCallerForError outer core)
          | table outer _ _ _ _ =>
              exact induction (core := restoreCallerForError outer core)

/-- Once a fixed host response has been accepted, all observable machine
    state is independent of whether that response came from live IO or a
    replay transcript. -/
theorem consumeResponse_observation_host_independent {Binding : Type}
    (state : State Binding) (core : Conf Binding) (rest : List Goal)
    (res : Atom) (binding : Binding) (response : HostResponse)
    (leftState rightState leftResult rightResult : HostSession) :
    observeStep
        (consumeResponse { state with host := leftState }
          core rest res binding response leftResult) =
      observeStep
        (consumeResponse { state with host := rightState }
          core rest res binding response rightResult) := by
  cases response with
  | returned value => rfl
  | prologReturned answers =>
      unfold consumeResponse unwindError
      exact observe_unwindFrames_host_independent core state.frames
        (marshallingErrorAtom "Prolog response used outside a Prolog request")
        leftResult rightResult
  | failed => rfl
  | raised error =>
      unfold consumeResponse unwindError
      exact observe_unwindFrames_host_independent core state.frames
        (pythonErrorAtom error) leftResult rightResult

def handlePyCall {Binding : Type} (state : State Binding)
    (core : Conf Binding) (res : Atom) (rest : List Goal)
    (values : List Atom) (next : Binding) : StepOutcome Binding :=
  match HostRequest.ofPyCallArgs values with
  | .error message =>
      unwindError state (marshallingErrorAtom message)
  | .ok request =>
      match request.localResponse? with
      | some response =>
          consumeResponse state core rest res next response state.host
      | none =>
          match state.host.resolve request with
          | .respond response session =>
              consumeResponse state core rest res next response session
          | .suspend pending session =>
              .requested { state with host := session } pending
          | .fail error => unwindError state (protocolErrorAtom error)

/-- Stdin (`readln!`) goes through the same suspend/supply/resolve host protocol
    as `py-call`; the request carries no arguments and the response is the line
    read. Live mode reads one process-stdin line; replay consumes the recorded
    transcript entry. -/
def handleReadLine {Binding : Type} (state : State Binding)
    (core : Conf Binding) (res : Atom) (rest : List Goal)
    (next : Binding) : StepOutcome Binding :=
  match state.host.resolve HostRequest.readLine with
  | .respond response session =>
      consumeResponse state core rest res next response session
  | .suspend pending session =>
      .requested { state with host := session } pending
  | .fail error => unwindError state (protocolErrorAtom error)

/-- A successful console write has the certified PeTTa value `True`; the host
    acknowledgment cannot choose a language-level result. -/
def consumePrintLineResponse {Binding : Type} (state : State Binding)
    (core : Conf Binding) (res : Atom) (rest : List Goal)
    (binding : Binding) (response : HostResponse)
    (session : HostSession) : StepOutcome Binding :=
  match response with
  | .returned _ =>
      .progressed { state with
        core := { core with
          cur := some (Goal.eq res (Atom.sym "True") :: rest, binding) }
        host := session }
  | .prologReturned _ =>
      unwindError { state with core, host := session }
        (marshallingErrorAtom "Prolog response used outside a Prolog request")
  | .failed =>
      .progressed { state with
        core := pull { core with cur := none }
        host := session }
  | .raised error =>
      unwindError { state with core, host := session } (pythonErrorAtom error)

/-- Console output is an explicit host effect in live/replay modes.  The
    request records PeTTa's `swrite` rendering; a successful response is only
    an acknowledgment. -/
def handlePrintLine {Binding : Type} (state : State Binding)
    (core : Conf Binding) (value res : Atom) (rest : List Goal)
    (next : Binding) : StepOutcome Binding :=
  let text := Metta.Pretty.atom (unchainify 10000 value)
  match state.host.resolve (.effect (.printLine text)) with
  | .respond response session =>
      consumePrintLineResponse state core res rest next response session
  | .suspend pending session =>
      .requested { state with host := session } pending
  | .fail error => unwindError state (protocolErrorAtom error)

/-- Wall-clock reads are explicit host requests.  Live execution records the
    returned instant; replay consumes that value without consulting a clock. -/
def handleClock {Binding : Type} (state : State Binding)
    (core : Conf Binding) (res : Atom) (rest : List Goal)
    (next : Binding) : StepOutcome Binding :=
  match state.host.resolve (.effect .clock) with
  | .respond response session =>
      consumeResponse state core rest res next response session
  | .suspend pending session =>
      .requested { state with host := session } pending
  | .fail error => unwindError state (protocolErrorAtom error)

/-- Decode one typed Prolog answer substitution into equality goals that bind
    those variables in the machine.  Binding order remains observable. -/
def prologBindingGoals (answer : PrologAnswer) : List Goal :=
  answer.map fun binding =>
    Goal.eq (Atom.var binding.name) binding.value.toAtom

/-- Continue the enclosing PeTTa computation after one successful Prolog
    answer. -/
def prologAnswerGoals (answer : PrologAnswer) (res : Atom)
    (rest : List Goal) : List Goal :=
  prologBindingGoals answer ++ Goal.eq res (Atom.sym "True") :: rest

/-- Turn the complete ordered Prolog answer bag into machine alternatives.
    `List.map` preserves both clause order and duplicate multiplicity. -/
def prologAnswerBranches {Binding : Type} (answers : List PrologAnswer)
    (res : Atom) (rest : List Goal) (binding : Binding) : List (Alt Binding) :=
  answers.map fun answer => Alt.br (prologAnswerGoals answer res rest) binding

@[simp] theorem prologAnswerBranches_length {Binding : Type}
    (answers : List PrologAnswer) (res : Atom) (rest : List Goal)
    (binding : Binding) :
    (prologAnswerBranches answers res rest binding).length = answers.length := by
  simp [prologAnswerBranches]

@[simp] theorem prologAnswerBranches_map {Source Target : Type}
    (map : Source → Target) (answers : List PrologAnswer) (res : Atom)
    (rest : List Goal) (binding : Source) :
    (prologAnswerBranches answers res rest binding).map
        (SubstEngine.mapAlt map) =
      prologAnswerBranches answers res rest (map binding) := by
  simp [prologAnswerBranches, SubstEngine.mapAlt]

/-- `translatePredicate` runs a Prolog goal at the trusted SWI boundary and
    unifies the returned answer substitution back into the machine: each bound
    variable becomes an equality goal, then the call itself yields `True`.  The
    goal already has the current bindings substituted in. -/
def handleTranslatePredicate {Binding : Type} (state : State Binding)
    (core : Conf Binding) (gt : GroundingTable) (functor : String)
    (ptArgs : List PrologTerm)
    (vars : List String) (res : Atom) (rest : List Goal)
    (next : Binding) : StepOutcome Binding :=
  match localPrologGoals? core.world gt functor ptArgs res rest with
  | some goals =>
      .progressed { state with core := { core with cur := some (goals, next) } }
  | none =>
      match state.host.resolve (HostRequest.ofPrologCall functor ptArgs vars) with
      | .respond (.prologReturned answers) session =>
          .progressed { state with
            core := pull { core with
              cur := none
              alts := prologAnswerBranches answers res rest next ++ core.alts }
            host := session }
      | .respond (.returned _) session =>
          unwindError { state with host := session }
            (marshallingErrorAtom
              "ordinary host response used for a Prolog request")
      | .respond .failed session =>
          .progressed { state with
            core := pull { core with cur := none }
            host := session }
      | .respond (.raised error) session =>
          unwindError { state with host := session } (pythonErrorAtom error)
      | .suspend pending session =>
          .requested { state with host := session } pending
      | .fail error => unwindError state (protocolErrorAtom error)

/-- A live response already supplied for the pending call and the matching
    replay entry induce exactly the same complete machine observation. -/
theorem live_ready_replay_handlePyCall_observation {Binding : Type}
    (state : State Binding) (core : Conf Binding) (res : Atom)
    (rest : List Goal) (values : List Atom) (binding : Binding)
    (request : HostRequest) (response : HostResponse)
    (hrequest : HostRequest.ofPyCallArgs values = .ok request) :
    let exchange : HostExchange := { request, response }
    let liveReady : HostSession := {
      mode := .live
      transcript := [exchange]
      pending := some request
      ready := some response }
    let replayReady : HostSession := .replay [exchange]
    observeStep
        (handlePyCall { state with host := liveReady }
          core res rest values binding) =
      observeStep
        (handlePyCall { state with host := replayReady }
          core res rest values binding) := by
  dsimp only
  let liveInitial : HostSession := {
    mode := .live
    transcript := [{ request, response }]
    pending := some request
    ready := some response }
  let liveNext : HostSession := {
    mode := .live
    transcript := [{ request, response }]
    cursor := 1 }
  let replayInitial : HostSession := .replay [{ request, response }]
  let replayNext : HostSession := {
    mode := .replay
    transcript := [{ request, response }]
    cursor := 1 }
  have hlive : liveInitial.resolve request =
      .respond response liveNext := by
    simp [liveInitial, liveNext, HostSession.resolve]
  have hreplay : replayInitial.resolve request =
      .respond response replayNext := by
    exact HostSession.resolve_replay_entry
      [{ request, response }] 0 request response rfl
  change observeStep
      (handlePyCall { state with host := liveInitial }
        core res rest values binding) =
    observeStep
      (handlePyCall { state with host := replayInitial }
        core res rest values binding)
  unfold handlePyCall
  simp only [hrequest]
  cases hlocal : request.localResponse? with
  | some localResponse =>
      exact consumeResponse_observation_host_independent state core rest res
        binding localResponse
        liveInitial replayInitial liveInitial replayInitial
  | none =>
      rw [hlive, hreplay]
      exact consumeResponse_observation_host_independent state core rest res
        binding response
        liveInitial replayInitial liveNext replayNext

/-- The live/replay response equivalence holds at every transcript position
    and is independent of the already-recorded live prefix.  This is the
    compositional form used for multi-request transcript replay. -/
theorem live_ready_replay_handlePyCall_observation_at {Binding : Type}
    (state : State Binding) (core : Conf Binding) (res : Atom)
    (rest : List Goal) (values : List Atom) (binding : Binding)
    (request : HostRequest) (response : HostResponse)
    (liveTranscript transcript : List HostExchange) (cursor : Nat)
    (hrequest : HostRequest.ofPyCallArgs values = .ok request)
    (hentry : transcript[cursor]? = some { request, response }) :
    let liveReady : HostSession := {
      mode := .live
      transcript := liveTranscript
      cursor
      pending := some request
      ready := some response }
    let replayReady : HostSession := {
      mode := .replay
      transcript
      cursor }
    observeStep
        (handlePyCall { state with host := liveReady }
          core res rest values binding) =
      observeStep
        (handlePyCall { state with host := replayReady }
          core res rest values binding) := by
  dsimp only
  let liveInitial : HostSession := {
    mode := .live
    transcript := liveTranscript
    cursor
    pending := some request
    ready := some response }
  let liveNext : HostSession := {
    mode := .live
    transcript := liveTranscript
    cursor := cursor + 1 }
  let replayInitial : HostSession := {
    mode := .replay
    transcript
    cursor }
  let replayNext : HostSession := {
    mode := .replay
    transcript
    cursor := cursor + 1 }
  have hlive : liveInitial.resolve request =
      .respond response liveNext := by
    simp [liveInitial, liveNext, HostSession.resolve]
  have hreplay : replayInitial.resolve request =
      .respond response replayNext := by
    exact HostSession.resolve_replay_entry
      transcript cursor request response hentry
  change observeStep
      (handlePyCall { state with host := liveInitial }
        core res rest values binding) =
    observeStep
      (handlePyCall { state with host := replayInitial }
        core res rest values binding)
  unfold handlePyCall
  simp only [hrequest]
  cases hlocal : request.localResponse? with
  | some localResponse =>
      exact consumeResponse_observation_host_independent state core rest res
        binding localResponse
        liveInitial replayInitial liveInitial replayInitial
  | none =>
      rw [hlive, hreplay]
      exact consumeResponse_observation_host_independent state core rest res
        binding response
        liveInitial replayInitial liveNext replayNext

def pushNested {Binding : Type} (state : State Binding)
    (nested : Conf Binding) (frame : Frame Binding) : StepOutcome Binding :=
  .progressed { state with core := nested, frames := frame :: state.frames }

def fromCoreOutcome {Binding : Type} (state : State Binding) :
    StepOutcomeWith Binding → StepOutcome Binding
  | .progressed core => .progressed { state with core }
  | .exhausted core => .exhausted { state with core }
  | .errored core error => unwindError { state with core } error

private def fromCoreRunOutcome {Binding : Type} (host : HostSession) :
    RunOutcomeWith Binding → RunOutcome Binding
  | .done core => .done { core, host }
  | .limited core => .limited { core, host }
  | .exhausted core => .exhausted { core, host }
  | .errored core error => .errored { core, host } error

def hostDisabled : HostMode → Bool
  | .disabled => true
  | _ => false

/-- One pure host-aware step.  Ordinary reductions are delegated to the
    proved clean machine; only nested-run scheduling and `py-call` suspension
    are handled here. -/
def stepWith (engine : SubstEngine) (prog : Prog) (gt : GroundingTable) :
    Nat → State engine.State → StepOutcome engine.State
  | 0, state => .exhausted state
  | fuel + 1, state =>
      let core := state.core
      if core.cur.isNone && core.alts.isEmpty then
        match state.frames with
        | [] => .progressed state
        | frame :: frames =>
            .progressed { state with
              core := finishFrame core frame
              frames }
      else
        match core.cur with
        | some (Goal.bin "py-call" args res :: rest, binding) =>
            let argsResult := engine.substMany binding args
            let values := argsResult.1
            if values.all Metta.isGround then
              handlePyCall state core res rest values argsResult.2
            else
              fromCoreOutcome state
                (SubstEngine.stepCleanWith engine prog gt fuel core)
        | some (Goal.bin "readln!" args res :: rest, binding) =>
            let argsResult := engine.substMany binding args
            handleReadLine state core res rest argsResult.2
        | some (Goal.bin "println!" args res :: rest, binding) =>
            if hostDisabled state.host.mode then
              fromCoreOutcome state
                (SubstEngine.stepCleanWith engine prog gt fuel core)
            else
              let argsResult := engine.substMany binding args
              match argsResult.1 with
              | [value] =>
                  handlePrintLine state core value res rest argsResult.2
              | _ => unwindError state
                  (marshallingErrorAtom "println! arity")
        | some (Goal.bin "get_time" args res :: rest, binding) =>
            let argsResult := engine.substMany binding args
            match argsResult.1 with
            | [] => handleClock state core res rest argsResult.2
            | _ => unwindError state (marshallingErrorAtom "get_time arity")
        | some (Goal.bin "translatePredicate" args res :: rest, binding) =>
            let argsResult := engine.substMany binding args
            match argsResult.1 with
            | [innerExpr] =>
                match buildPrologCall innerExpr with
                | some (functor, ptArgs, vars) =>
                    handleTranslatePredicate state core gt functor ptArgs vars res
                      rest argsResult.2
                | none =>
                    unwindError state (marshallingErrorAtom
                      s!"translatePredicate goal: {reprStr (deepUnchain innerExpr)}")
            | _ => unwindError state (marshallingErrorAtom "translatePredicate arity")
        | some (Goal.catchg tmpl sub res :: rest, binding) =>
            fromCoreOutcome state
              (SubstEngine.stepCleanWith engine prog gt fuel core)
        | some (Goal.transactiong tmpl sub :: rest, binding) =>
            pushNested state
              (subConfOfWith engine core (transactionSub tmpl sub) binding tmpl)
              (.transaction core rest tmpl binding)
        | some (Goal.softcut tmpl sub thn els :: rest, binding) =>
            pushNested state (subConfOfWith engine core sub binding tmpl)
              (.softcut core rest thn els tmpl binding)
        | some (Goal.findall tmpl sub res :: rest, binding) =>
            pushNested state (subConfOfWith engine core sub binding tmpl)
              (.findall core rest res binding)
        | some (Goal.call function args res :: rest, binding) =>
            let argsResult := engine.substMany binding args
            let values := argsResult.1
            let next := argsResult.2
            let key := tableKey function values
            if core.world.canTableCall function values then
              match core.world.tableLookup key with
              | some _ =>
                  fromCoreOutcome state
                    (SubstEngine.stepCleanWith engine prog gt fuel core)
              | none =>
                  let result := tableFresh core
                  pushNested state
                    (tableSubConfOfWith engine core function values result key)
                    (.table core key rest res next)
            else
              fromCoreOutcome state
                (SubstEngine.stepCleanWith engine prog gt fuel core)
        | _ =>
            fromCoreOutcome state
              (SubstEngine.stepCleanWith engine prog gt fuel core)

/-- Fuel-bounded pure execution.  Live mode returns at the first request with
    the exact remaining fuel; replay mode consumes transcript entries without
    leaving the pure executor. -/
def runWith (engine : SubstEngine) (prog : Prog) (gt : GroundingTable) :
    Nat → State engine.State → Option Nat → RunOutcome engine.State
  | 0, state, limit =>
      if state.frames.isEmpty && state.core.cur.isNone && state.core.alts.isEmpty then
        .done state
      else if state.frames.isEmpty &&
          limit.any (fun maximum => state.core.answers.length ≥ maximum) then
        .limited state
      else
        .exhausted state
  | fuel + 1, state, limit =>
      if hostDisabled state.host.mode && state.frames.isEmpty then
        fromCoreRunOutcome state.host
          (SubstEngine.runCleanWith engine prog gt (fuel + 1) state.core limit)
      else if state.frames.isEmpty && state.core.cur.isNone && state.core.alts.isEmpty then
        .done state
      else if state.frames.isEmpty &&
          limit.any (fun maximum => state.core.answers.length ≥ maximum) then
        .limited state
      else
        match stepWith engine prog gt (fuel + 1) state with
        | .progressed next => runWith engine prog gt fuel next limit
        -- Waiting for trusted IO is not a PeTTa reduction. Preserve the
        -- current fuel so live resume and transcript replay consume exactly
        -- the same semantic-step budget.
        | .requested next request => .requested next request (fuel + 1)
        | .exhausted done => .exhausted done
        | .errored done error => .errored done error

def mapFrame {Source Target : Type} (map : Source → Target) :
    Frame Source → Frame Target
  | .transaction outer rest tmpl state =>
      .transaction (mapConf map outer) rest tmpl (map state)
  | .softcut outer rest thn els tmpl state =>
      .softcut (mapConf map outer) rest thn els tmpl (map state)
  | .findall outer rest res state =>
      .findall (mapConf map outer) rest res (map state)
  | .table outer key rest res state =>
      .table (mapConf map outer) key rest res (map state)

def mapState {Source Target : Type} (map : Source → Target)
    (state : State Source) : State Target :=
  { core := mapConf map state.core
    frames := state.frames.map (mapFrame map)
    host := state.host }

def mapStepOutcome {Source Target : Type} (map : Source → Target) :
    StepOutcome Source → StepOutcome Target
  | .progressed state => .progressed (mapState map state)
  | .requested state request => .requested (mapState map state) request
  | .exhausted state => .exhausted (mapState map state)
  | .errored state error => .errored (mapState map state) error

theorem mapConf_finishFrame {Source Target : Type} (map : Source → Target)
    (done : Conf Source) (frame : Frame Source) :
    SubstEngine.mapConf map (finishFrame done frame) =
      finishFrame (SubstEngine.mapConf map done) (mapFrame map frame) := by
  cases frame <;>
    simp only [finishFrame, mapFrame,
      SubstEngine.mapConf_finishTransaction,
      SubstEngine.mapConf_finishSoftcut,
      SubstEngine.mapConf_finishFindall,
      SubstEngine.mapConf_finishTable]

theorem mapStepOutcome_unwindFrames {Source Target : Type}
    (map : Source → Target) (core : Conf Source) (host : HostSession)
    (frames : List (Frame Source)) (error : Atom) :
    mapStepOutcome map (unwindFrames core host frames error) =
      unwindFrames (SubstEngine.mapConf map core) host
        (frames.map (mapFrame map)) error := by
  induction frames generalizing core with
  | nil =>
      simp only [List.map_nil]
      unfold unwindFrames
      rw [← SubstEngine.mapConf_catchErrorSuccessor]
      cases catchErrorSuccessor? core error <;> rfl
  | cons frame frames induction =>
      simp only [List.map_cons]
      unfold unwindFrames
      rw [← SubstEngine.mapConf_catchErrorSuccessor]
      cases found : catchErrorSuccessor? core error with
      | some caught => rfl
      | none =>
          cases frame with
          | transaction outer _ _ _ =>
              simp only [Option.map_none, mapFrame,
                mapConf_restoreTransactionCallerForError]
              exact induction
                (core := restoreTransactionCallerForError outer core)
          | softcut outer _ _ _ _ _ =>
              simp only [Option.map_none, mapFrame,
                mapConf_restoreCallerForError]
              exact induction (core := restoreCallerForError outer core)
          | findall outer _ _ _ =>
              simp only [Option.map_none, mapFrame,
                mapConf_restoreCallerForError]
              exact induction (core := restoreCallerForError outer core)
          | table outer _ _ _ _ =>
              simp only [Option.map_none, mapFrame,
                mapConf_restoreCallerForError]
              exact induction (core := restoreCallerForError outer core)

theorem mapStepOutcome_consumeResponse {Source Target : Type}
    (map : Source → Target) (state : State Source) (core : Conf Source)
    (rest : List Goal) (res : Atom) (binding : Source)
    (response : HostResponse) (session : HostSession) :
    mapStepOutcome map
        (consumeResponse state core rest res binding response session) =
      consumeResponse (mapState map state) (SubstEngine.mapConf map core)
        rest res (map binding) response session := by
  cases response with
  | returned value =>
      simp [consumeResponse, mapStepOutcome, mapState,
        SubstEngine.mapConf_enqueueHostAnswers]
  | prologReturned answers =>
      unfold consumeResponse unwindError
      exact mapStepOutcome_unwindFrames map core session state.frames
        (marshallingErrorAtom "Prolog response used outside a Prolog request")
  | failed =>
      simp only [consumeResponse, mapStepOutcome, mapState]
      rw [SubstEngine.mapConf_pull, SubstEngine.mapConf_setCurNone]
  | raised error =>
      unfold consumeResponse unwindError
      exact mapStepOutcome_unwindFrames map core session state.frames
        (pythonErrorAtom error)

theorem mapStepOutcome_handlePyCall {Source Target : Type}
    (map : Source → Target) (state : State Source) (core : Conf Source)
    (res : Atom) (rest : List Goal) (values : List Atom) (binding : Source) :
    mapStepOutcome map (handlePyCall state core res rest values binding) =
      handlePyCall (mapState map state) (SubstEngine.mapConf map core)
        res rest values (map binding) := by
  unfold handlePyCall
  cases requestResult : HostRequest.ofPyCallArgs values with
  | error message =>
      simp only [mapState]
      unfold unwindError
      exact mapStepOutcome_unwindFrames map state.core state.host state.frames
        (marshallingErrorAtom message)
  | ok request =>
      simp only [mapState]
      cases hlocal : request.localResponse? with
      | some response =>
          exact mapStepOutcome_consumeResponse map state core rest res
            binding response state.host
      | none =>
          cases decision : state.host.resolve request with
          | respond response session =>
              exact mapStepOutcome_consumeResponse map state core rest res
                binding response session
          | suspend pending session => simp [mapStepOutcome, mapState]
          | fail error =>
              unfold unwindError
              exact mapStepOutcome_unwindFrames map state.core state.host state.frames
                (protocolErrorAtom error)

theorem mapStepOutcome_handleReadLine {Source Target : Type}
    (map : Source → Target) (state : State Source) (core : Conf Source)
    (res : Atom) (rest : List Goal) (binding : Source) :
    mapStepOutcome map (handleReadLine state core res rest binding) =
      handleReadLine (mapState map state) (SubstEngine.mapConf map core)
        res rest (map binding) := by
  unfold handleReadLine
  simp only [mapState]
  cases decision : state.host.resolve HostRequest.readLine with
  | respond response session =>
      exact mapStepOutcome_consumeResponse map state core rest res
        binding response session
  | suspend pending session => simp [mapStepOutcome, mapState]
  | fail error =>
      unfold unwindError
      exact mapStepOutcome_unwindFrames map state.core state.host state.frames
        (protocolErrorAtom error)

theorem mapStepOutcome_consumePrintLineResponse {Source Target : Type}
    (map : Source → Target) (state : State Source) (core : Conf Source)
    (res : Atom) (rest : List Goal) (binding : Source)
    (response : HostResponse) (session : HostSession) :
    mapStepOutcome map
        (consumePrintLineResponse state core res rest binding response session) =
      consumePrintLineResponse (mapState map state)
        (SubstEngine.mapConf map core) res rest (map binding) response session := by
  cases response with
  | returned value =>
      simp only [consumePrintLineResponse, mapStepOutcome, mapState]
      rw [SubstEngine.mapConf_setCurSome]
  | prologReturned answers =>
      unfold consumePrintLineResponse unwindError
      exact mapStepOutcome_unwindFrames map core session state.frames
        (marshallingErrorAtom "Prolog response used outside a Prolog request")
  | failed =>
      simp only [consumePrintLineResponse, mapStepOutcome, mapState]
      rw [SubstEngine.mapConf_pull, SubstEngine.mapConf_setCurNone]
  | raised error =>
      unfold consumePrintLineResponse unwindError
      exact mapStepOutcome_unwindFrames map core session state.frames
        (pythonErrorAtom error)

theorem mapStepOutcome_handlePrintLine {Source Target : Type}
    (map : Source → Target) (state : State Source) (core : Conf Source)
    (value res : Atom) (rest : List Goal) (binding : Source) :
    mapStepOutcome map
        (handlePrintLine state core value res rest binding) =
      handlePrintLine (mapState map state) (SubstEngine.mapConf map core)
        value res rest (map binding) := by
  unfold handlePrintLine
  simp only [mapState]
  cases decision : state.host.resolve
      (.effect (.printLine (Metta.Pretty.atom (unchainify 10000 value)))) with
  | respond response session =>
      exact mapStepOutcome_consumePrintLineResponse map state core res rest
        binding response session
  | suspend pending session => simp [mapStepOutcome, mapState]
  | fail error =>
      unfold unwindError
      exact mapStepOutcome_unwindFrames map state.core state.host state.frames
        (protocolErrorAtom error)

theorem mapStepOutcome_handleClock {Source Target : Type}
    (map : Source → Target) (state : State Source) (core : Conf Source)
    (res : Atom) (rest : List Goal) (binding : Source) :
    mapStepOutcome map (handleClock state core res rest binding) =
      handleClock (mapState map state) (SubstEngine.mapConf map core)
        res rest (map binding) := by
  unfold handleClock
  simp only [mapState]
  cases decision : state.host.resolve (.effect .clock) with
  | respond response session =>
      exact mapStepOutcome_consumeResponse map state core rest res
        binding response session
  | suspend pending session => simp [mapStepOutcome, mapState]
  | fail error =>
      unfold unwindError
      exact mapStepOutcome_unwindFrames map state.core state.host state.frames
        (protocolErrorAtom error)

theorem mapStepOutcome_handleTranslatePredicate {Source Target : Type}
    (map : Source → Target) (state : State Source) (core : Conf Source)
    (gt : GroundingTable) (functor : String) (ptArgs : List PrologTerm)
    (vars : List String)
    (res : Atom) (rest : List Goal) (binding : Source) :
    mapStepOutcome map
        (handleTranslatePredicate state core gt functor ptArgs vars res rest binding) =
      handleTranslatePredicate (mapState map state) (SubstEngine.mapConf map core)
        gt functor ptArgs vars res rest (map binding) := by
  unfold handleTranslatePredicate
  simp only [mapState]
  have mappedLocal :
      localPrologGoals? (SubstEngine.mapConf map core).world gt functor ptArgs
          res rest =
        localPrologGoals? core.world gt functor ptArgs res rest := by
    rfl
  rw [mappedLocal]
  cases hlocal : localPrologGoals? core.world gt functor ptArgs res rest with
  | some goals => simp [mapStepOutcome, mapState, SubstEngine.mapConf]
  | none =>
      cases decision :
          state.host.resolve (HostRequest.ofPrologCall functor ptArgs vars) with
      | respond response session =>
          cases response with
          | returned value =>
              unfold unwindError
              exact mapStepOutcome_unwindFrames map state.core session state.frames _
          | prologReturned answers =>
              simp only [mapStepOutcome, mapState]
              rw [SubstEngine.mapConf_pull]
              simp [SubstEngine.mapConf, List.map_append]
          | failed =>
              simp only [mapStepOutcome, mapState]
              rw [SubstEngine.mapConf_pull, SubstEngine.mapConf_setCurNone]
          | raised error =>
              unfold unwindError
              exact mapStepOutcome_unwindFrames map state.core session state.frames _
      | suspend pending session => simp [mapStepOutcome, mapState]
      | fail error =>
          unfold unwindError
          exact mapStepOutcome_unwindFrames map state.core state.host state.frames _

theorem mapStepOutcome_fromCoreOutcome {Source Target : Type}
    (map : Source → Target) (state : State Source)
    (outcome : SubstEngine.StepOutcomeWith Source) :
    mapStepOutcome map (fromCoreOutcome state outcome) =
      fromCoreOutcome (mapState map state)
        (SubstEngine.mapStepOutcome map outcome) := by
  cases outcome with
  | progressed core => rfl
  | exhausted core => rfl
  | errored core error =>
      unfold fromCoreOutcome unwindError
      exact mapStepOutcome_unwindFrames map core state.host state.frames error

theorem mapStepOutcome_pushNested {Source Target : Type}
    (map : Source → Target) (state : State Source) (nested : Conf Source)
    (frame : Frame Source) :
    mapStepOutcome map (pushNested state nested frame) =
      pushNested (mapState map state) (SubstEngine.mapConf map nested)
        (mapFrame map frame) := by
  rfl

theorem checked_fromCoreOutcome_step_simulation (engine : SubstEngine)
    (prog : Prog) (gt : GroundingTable) (fuel : Nat)
    (state : State (SubstEngine.checked engine).State) :
    mapStepOutcome (SubstEngine.checked engine).denote
        (fromCoreOutcome state
          (SubstEngine.stepCleanWith (SubstEngine.checked engine)
            prog gt fuel state.core)) =
      fromCoreOutcome
        (mapState (SubstEngine.checked engine).denote state)
        (SubstEngine.stepCleanWith SubstEngine.reference prog gt fuel
          (SubstEngine.mapConf (SubstEngine.checked engine).denote
            state.core)) := by
  rw [mapStepOutcome_fromCoreOutcome]
  rw [(SubstEngine.checked_clean_run_step_simulation
    engine prog gt fuel).2 state.core]
  rfl

/-- The host-aware executable step over a proof-carrying substitution engine
    denotes exactly the list-substitution host step, including suspension,
    accepted responses, nested continuations, errors, answers, and world
    effects. -/
theorem checked_stepWith_simulation (engine : SubstEngine) (prog : Prog)
    (gt : GroundingTable) (fuel : Nat)
    (state : State (SubstEngine.checked engine).State) :
    mapStepOutcome (SubstEngine.checked engine).denote
        (stepWith (SubstEngine.checked engine) prog gt fuel state) =
      stepWith SubstEngine.reference prog gt fuel
        (mapState (Target := Subst)
          (SubstEngine.checked engine).denote state) := by
  cases state with
  | mk core frames host =>
    cases core with
    | mk cur alts world counter qterm answers answerKeys
        answerKeys_sound barriers =>
      let source : State (SubstEngine.checked engine).State := {
        core := {
          cur
          alts
          world
          counter
          qterm
          answers
          answerKeys
          answerKeys_sound
          barriers }
        frames
        host }
      change mapStepOutcome (SubstEngine.checked engine).denote
          (stepWith (SubstEngine.checked engine) prog gt fuel source) =
        stepWith SubstEngine.reference prog gt fuel
          (mapState (SubstEngine.checked engine).denote source)
      cases fuel with
      | zero => rfl
      | succ fuel =>
        cases cur with
        | none =>
          cases alts with
          | nil =>
            cases frames with
            | nil => rfl
            | cons frame rest =>
              have mappedFinish := mapConf_finishFrame
                (SubstEngine.checked engine).denote source.core frame
              simpa [stepWith, source, mapState, SubstEngine.mapConf,
                mapStepOutcome] using
                  congrArg (fun core => StepOutcome.progressed {
                    core
                    frames := rest.map
                      (mapFrame (SubstEngine.checked engine).denote)
                    host }) mappedFinish
          | cons alt tail =>
            simpa [stepWith, source, mapState, SubstEngine.mapConf] using
              checked_fromCoreOutcome_step_simulation
                engine prog gt fuel source
        | some branch =>
          rcases branch with ⟨goals, binding⟩
          cases goals with
          | nil =>
            simpa [stepWith, source, mapState, SubstEngine.mapConf] using
              checked_fromCoreOutcome_step_simulation
                engine prog gt fuel source
          | cons goal rest =>
            cases goal with
            | bin op args res =>
              by_cases pycall : op = "py-call"
              · subst op
                cases result : (SubstEngine.checked engine).substMany
                    binding args with
                | mk values next =>
                  have valuesEq :=
                    (SubstEngine.checked engine).substMany_value
                      binding args True.intro
                  have nextEq :=
                    (SubstEngine.checked engine).substMany_denote
                      binding args True.intro
                  simp only [result] at valuesEq nextEq
                  by_cases ground : values.all Metta.isGround
                  · have allGround := List.all_eq_true.mp ground
                    have mappedGround :
                        ∀ x ∈ args,
                          Metta.isGround
                            (PLeaTTa.subst
                              ((SubstEngine.checked engine).denote binding)
                              x) = true := by
                      intro x member
                      apply allGround
                      rw [valuesEq]
                      exact List.mem_map.mpr ⟨x, member, rfl⟩
                    have mapped := mapStepOutcome_handlePyCall
                      (SubstEngine.checked engine).denote source source.core
                      res rest values next
                    simp [stepWith, source, result, valuesEq,
                      SubstEngine.referenceSubstMany, mapState,
                      SubstEngine.mapConf]
                    rw [if_pos mappedGround, if_pos mappedGround]
                    simpa [source, valuesEq, nextEq, mapState,
                      SubstEngine.mapConf] using mapped
                  · have notAllGround :
                        ¬ ∀ x ∈ values, Metta.isGround x = true := by
                      intro allGround
                      exact ground (List.all_eq_true.mpr allGround)
                    have notMappedGround :
                        ¬ ∀ x ∈ args,
                          Metta.isGround
                            (PLeaTTa.subst
                              ((SubstEngine.checked engine).denote binding)
                              x) = true := by
                      intro mappedGround
                      apply notAllGround
                      intro x member
                      rw [valuesEq] at member
                      rcases List.mem_map.mp member with ⟨atom, present, rfl⟩
                      exact mappedGround atom present
                    have delegated :=
                      checked_fromCoreOutcome_step_simulation
                        engine prog gt fuel source
                    simp [stepWith, source, result, valuesEq,
                      SubstEngine.referenceSubstMany, mapState,
                      SubstEngine.mapConf]
                    rw [if_neg notMappedGround, if_neg notMappedGround]
                    exact delegated
              · by_cases readln : op = "readln!"
                · subst op
                  cases result : (SubstEngine.checked engine).substMany
                      binding args with
                  | mk values next =>
                    have nextEq :=
                      (SubstEngine.checked engine).substMany_denote
                        binding args True.intro
                    simp only [result] at nextEq
                    have mapped := mapStepOutcome_handleReadLine
                      (SubstEngine.checked engine).denote source source.core
                      res rest next
                    simp [stepWith, source, result,
                      SubstEngine.referenceSubstMany, mapState,
                      SubstEngine.mapConf]
                    simpa [source, nextEq, mapState,
                      SubstEngine.mapConf] using mapped
                · by_cases printLine : op = "println!"
                  · subst op
                    by_cases disabled : hostDisabled source.host.mode = true
                    · simpa [stepWith, source, disabled, mapState,
                        SubstEngine.mapConf] using
                        checked_fromCoreOutcome_step_simulation
                          engine prog gt fuel source
                    · cases result : (SubstEngine.checked engine).substMany
                          binding args with
                      | mk values next =>
                        have valuesEq :=
                          (SubstEngine.checked engine).substMany_value
                            binding args True.intro
                        have nextEq :=
                          (SubstEngine.checked engine).substMany_denote
                            binding args True.intro
                        simp only [result] at valuesEq nextEq
                        cases values with
                        | nil =>
                          simp [stepWith, source, disabled, result, ← valuesEq,
                            SubstEngine.referenceSubstMany, mapState,
                            SubstEngine.mapConf]
                          unfold unwindError
                          exact mapStepOutcome_unwindFrames
                            (SubstEngine.checked engine).denote source.core
                            source.host source.frames _
                        | cons value tail =>
                          cases tail with
                          | nil =>
                            have mapped := mapStepOutcome_handlePrintLine
                              (SubstEngine.checked engine).denote source
                              source.core value res rest next
                            simp [stepWith, source, disabled, result, ← valuesEq,
                              SubstEngine.referenceSubstMany, mapState,
                              SubstEngine.mapConf]
                            simpa [source, nextEq, mapState,
                              SubstEngine.mapConf] using mapped
                          | cons _ _ =>
                            simp [stepWith, source, disabled, result, ← valuesEq,
                              SubstEngine.referenceSubstMany, mapState,
                              SubstEngine.mapConf]
                            unfold unwindError
                            exact mapStepOutcome_unwindFrames
                              (SubstEngine.checked engine).denote source.core
                              source.host source.frames _
                  · by_cases getTime : op = "get_time"
                    · subst op
                      cases result : (SubstEngine.checked engine).substMany
                          binding args with
                      | mk values next =>
                        have valuesEq :=
                          (SubstEngine.checked engine).substMany_value
                            binding args True.intro
                        have nextEq :=
                          (SubstEngine.checked engine).substMany_denote
                            binding args True.intro
                        simp only [result] at valuesEq nextEq
                        cases values with
                        | nil =>
                          have mapped := mapStepOutcome_handleClock
                            (SubstEngine.checked engine).denote source source.core
                            res rest next
                          simp [stepWith, source, result, ← valuesEq,
                            SubstEngine.referenceSubstMany, mapState,
                            SubstEngine.mapConf]
                          simpa [source, nextEq, mapState,
                            SubstEngine.mapConf] using mapped
                        | cons _ _ =>
                          simp [stepWith, source, result, ← valuesEq,
                            SubstEngine.referenceSubstMany, mapState,
                            SubstEngine.mapConf]
                          unfold unwindError
                          exact mapStepOutcome_unwindFrames
                            (SubstEngine.checked engine).denote source.core
                            source.host source.frames _
                    · by_cases translatePred : op = "translatePredicate"
                      · subst op
                        cases result : (SubstEngine.checked engine).substMany
                            binding args with
                        | mk values next =>
                          have valuesEq :=
                            (SubstEngine.checked engine).substMany_value
                              binding args True.intro
                          have nextEq :=
                            (SubstEngine.checked engine).substMany_denote
                              binding args True.intro
                          simp only [result] at valuesEq nextEq
                          cases values with
                          | nil =>
                            simp [stepWith, source, result, ← valuesEq,
                                SubstEngine.referenceSubstMany, mapState,
                                SubstEngine.mapConf]
                            unfold unwindError
                            exact mapStepOutcome_unwindFrames
                              (SubstEngine.checked engine).denote source.core
                              source.host source.frames _
                          | cons innerExpr tl =>
                            cases tl with
                            | nil =>
                              cases hbuild : buildPrologCall innerExpr with
                              | none =>
                                simp [stepWith, source, result, ← valuesEq, hbuild,
                                  SubstEngine.referenceSubstMany, mapState,
                                  SubstEngine.mapConf]
                                unfold unwindError
                                exact mapStepOutcome_unwindFrames
                                  (SubstEngine.checked engine).denote source.core
                                  source.host source.frames _
                              | some fpv =>
                                obtain ⟨functor, ptArgs, vars⟩ := fpv
                                have mapped :=
                                  mapStepOutcome_handleTranslatePredicate
                                    (SubstEngine.checked engine).denote source
                                    source.core gt functor ptArgs vars res rest next
                                simp [stepWith, source, result, ← valuesEq, hbuild,
                                  SubstEngine.referenceSubstMany, mapState,
                                  SubstEngine.mapConf]
                                simpa [source, nextEq, mapState,
                                  SubstEngine.mapConf] using mapped
                            | cons _ _ =>
                              simp [stepWith, source, result, ← valuesEq,
                                SubstEngine.referenceSubstMany, mapState,
                                SubstEngine.mapConf]
                              unfold unwindError
                              exact mapStepOutcome_unwindFrames
                                (SubstEngine.checked engine).denote source.core
                                source.host source.frames _
                      · simpa [stepWith, source, pycall, readln, printLine,
                        getTime, translatePred,
                        mapState, SubstEngine.mapConf] using
                          checked_fromCoreOutcome_step_simulation
                            engine prog gt fuel source
            | catchg tmpl sub res =>
              simpa [stepWith, source, mapState, SubstEngine.mapConf] using
                checked_fromCoreOutcome_step_simulation
                  engine prog gt fuel source
            | catchExit template result =>
              simpa [stepWith, source, mapState, SubstEngine.mapConf] using
                checked_fromCoreOutcome_step_simulation
                  engine prog gt fuel source
            | transactiong tmpl sub =>
              have nestedEq := SubstEngine.erase_subConfOfWith
                (SubstEngine.checked engine) source.core
                (transactionSub tmpl sub) binding tmpl
              unfold SubstEngine.erase at nestedEq
              have mapped := mapStepOutcome_pushNested
                (SubstEngine.checked engine).denote source
                (SubstEngine.subConfOfWith (SubstEngine.checked engine)
                  source.core (transactionSub tmpl sub) binding tmpl)
                (.transaction source.core rest tmpl binding)
              simpa [stepWith, source, mapState, mapFrame, nestedEq] using mapped
            | softcut tmpl sub thn els =>
              have nestedEq := SubstEngine.erase_subConfOfWith
                (SubstEngine.checked engine) source.core sub binding tmpl
              unfold SubstEngine.erase at nestedEq
              have mapped := mapStepOutcome_pushNested
                (SubstEngine.checked engine).denote source
                (SubstEngine.subConfOfWith (SubstEngine.checked engine)
                  source.core sub binding tmpl)
                (.softcut source.core rest thn els tmpl binding)
              simpa [stepWith, source, mapState, mapFrame, nestedEq] using mapped
            | findall tmpl sub res =>
              have nestedEq := SubstEngine.erase_subConfOfWith
                (SubstEngine.checked engine) source.core sub binding tmpl
              unfold SubstEngine.erase at nestedEq
              have mapped := mapStepOutcome_pushNested
                (SubstEngine.checked engine).denote source
                (SubstEngine.subConfOfWith (SubstEngine.checked engine)
                  source.core sub binding tmpl)
                (.findall source.core rest res binding)
              simpa [stepWith, source, mapState, mapFrame, nestedEq] using mapped
            | call function args res =>
              cases result : (SubstEngine.checked engine).substMany
                  binding args with
              | mk values next =>
                have valuesEq :=
                  (SubstEngine.checked engine).substMany_value
                    binding args True.intro
                have nextEq :=
                  (SubstEngine.checked engine).substMany_denote
                    binding args True.intro
                simp only [result] at valuesEq nextEq
                by_cases tabled : source.core.world.canTableCall function values
                · have mappedTabled :
                      world.canTableCall function
                        (args.map (PLeaTTa.subst
                          ((SubstEngine.checked engine).denote binding))) =
                        true := by
                    change world.canTableCall function values = true at tabled
                    rw [← valuesEq]
                    exact tabled
                  cases lookup : source.core.world.tableLookup
                      (tableKey function values) with
                  | some tableAnswers =>
                    have mappedLookup :
                        world.tableLookup
                            (tableKey function
                              (args.map (PLeaTTa.subst
                                ((SubstEngine.checked engine).denote
                                  binding)))) =
                          some tableAnswers := by
                      change world.tableLookup (tableKey function values) =
                        some tableAnswers at lookup
                      rw [← valuesEq]
                      exact lookup
                    have delegated :=
                      checked_fromCoreOutcome_step_simulation
                        engine prog gt fuel source
                    simp [stepWith, source, result, valuesEq, mappedLookup,
                      SubstEngine.referenceSubstMany, mapState,
                      SubstEngine.mapConf]
                    simpa [source, mapState, SubstEngine.mapConf] using
                      delegated
                  | none =>
                    have mappedLookup :
                        world.tableLookup
                            (tableKey function
                              (args.map (PLeaTTa.subst
                                ((SubstEngine.checked engine).denote
                                  binding)))) = none := by
                      change world.tableLookup (tableKey function values) =
                        none at lookup
                      rw [← valuesEq]
                      exact lookup
                    have nestedEq := SubstEngine.erase_tableSubConfOfWith
                      (SubstEngine.checked engine) source.core function
                      values (tableFresh source.core)
                      (tableKey function values)
                    unfold SubstEngine.erase at nestedEq
                    have mapped := mapStepOutcome_pushNested
                      (SubstEngine.checked engine).denote source
                      (SubstEngine.tableSubConfOfWith
                        (SubstEngine.checked engine) source.core function
                        values (tableFresh source.core)
                        (tableKey function values))
                      (.table source.core (tableKey function values)
                        rest res next)
                    rw [nestedEq] at mapped
                    simp [stepWith, source, result, valuesEq, mappedLookup,
                      SubstEngine.referenceSubstMany, mapState,
                      SubstEngine.mapConf]
                    rw [if_pos mappedTabled, if_pos mappedTabled]
                    simpa [source, valuesEq, nextEq, mapState, mapFrame,
                      tableFresh] using mapped
                · have notMappedTabled :
                      ¬ world.canTableCall function
                        (args.map (PLeaTTa.subst
                          ((SubstEngine.checked engine).denote binding))) =
                          true := by
                    intro mappedTabled
                    apply tabled
                    change world.canTableCall function values = true
                    rw [valuesEq]
                    exact mappedTabled
                  have delegated := checked_fromCoreOutcome_step_simulation
                    engine prog gt fuel source
                  simp [stepWith, source, result, valuesEq,
                    SubstEngine.referenceSubstMany, mapState,
                    SubstEngine.mapConf]
                  rw [if_neg notMappedTabled, if_neg notMappedTabled]
                  simpa [source, mapState, SubstEngine.mapConf] using delegated
            | callDyn head args res =>
              simpa [stepWith, source, mapState, SubstEngine.mapConf] using
                checked_fromCoreOutcome_step_simulation engine prog gt fuel source
            | evalg value res =>
              simpa [stepWith, source, mapState, SubstEngine.mapConf] using
                checked_fromCoreOutcome_step_simulation engine prog gt fuel source
            | eq left right =>
              simpa [stepWith, source, mapState, SubstEngine.mapConf] using
                checked_fromCoreOutcome_step_simulation engine prog gt fuel source
            | compileAlias left right =>
              simpa [stepWith, source, mapState, SubstEngine.mapConf] using
                checked_fromCoreOutcome_step_simulation engine prog gt fuel source
            | cut =>
              simpa [stepWith, source, mapState, SubstEngine.mapConf] using
                checked_fromCoreOutcome_step_simulation engine prog gt fuel source
            | cutAt count =>
              simpa [stepWith, source, mapState, SubstEngine.mapConf] using
                checked_fromCoreOutcome_step_simulation engine prog gt fuel source
            | onceg tmpl sub res =>
              simpa [stepWith, source, mapState, SubstEngine.mapConf] using
                checked_fromCoreOutcome_step_simulation engine prog gt fuel source
            | amb branches res =>
              simpa [stepWith, source, mapState, SubstEngine.mapConf] using
                checked_fromCoreOutcome_step_simulation engine prog gt fuel source
            | spread value res =>
              simpa [stepWith, source, mapState, SubstEngine.mapConf] using
                checked_fromCoreOutcome_step_simulation engine prog gt fuel source
            | ite cond thn els res =>
              simpa [stepWith, source, mapState, SubstEngine.mapConf] using
                checked_fromCoreOutcome_step_simulation engine prog gt fuel source
            | smatch pattern =>
              simpa [stepWith, source, mapState, SubstEngine.mapConf] using
                checked_fromCoreOutcome_step_simulation engine prog gt fuel source
            | wact op args res =>
              simpa [stepWith, source, mapState, SubstEngine.mapConf] using
                checked_fromCoreOutcome_step_simulation engine prog gt fuel source

def mapRunOutcome {Source Target : Type} (map : Source → Target) :
    RunOutcome Source → RunOutcome Target
  | .done state => .done (mapState map state)
  | .limited state => .limited (mapState map state)
  | .requested state request remaining =>
      .requested (mapState map state) request remaining
  | .exhausted state => .exhausted (mapState map state)
  | .errored state error => .errored (mapState map state) error

theorem mapRunOutcome_fromCoreRunOutcome {Source Target : Type}
    (map : Source → Target) (host : HostSession)
    (outcome : SubstEngine.RunOutcomeWith Source) :
    mapRunOutcome map (fromCoreRunOutcome host outcome) =
      fromCoreRunOutcome host (SubstEngine.mapRunOutcome map outcome) := by
  cases outcome <;> rfl

/-- Complete fuel-bounded host execution over a checked substitution engine
    denotes the reference host execution, preserving termination class,
    request and remaining fuel, answers, alternatives, world effects, and
    nested continuations. -/
theorem checked_runWith_simulation (engine : SubstEngine) (prog : Prog)
    (gt : GroundingTable) :
    ∀ fuel (state : State (SubstEngine.checked engine).State) limit,
      mapRunOutcome (SubstEngine.checked engine).denote
          (runWith (SubstEngine.checked engine) prog gt fuel state limit) =
        runWith SubstEngine.reference prog gt fuel
          (mapState (Target := Subst)
            (SubstEngine.checked engine).denote state) limit := by
  intro fuel
  induction fuel with
  | zero =>
      intro state limit
      let mapped := mapState (Target := Subst)
        (SubstEngine.checked engine).denote state
      have mappedFinished :
          (mapped.frames.isEmpty && mapped.core.cur.isNone &&
              mapped.core.alts.isEmpty) =
            (state.frames.isEmpty && state.core.cur.isNone &&
              state.core.alts.isEmpty) := by
        simp [mapped, mapState, SubstEngine.mapConf]
      have mappedReached :
          (mapped.frames.isEmpty &&
              limit.any (fun maximum =>
                mapped.core.answers.length ≥ maximum)) =
            (state.frames.isEmpty &&
              limit.any (fun maximum =>
                state.core.answers.length ≥ maximum)) := by
        simp [mapped, mapState, SubstEngine.mapConf]
      by_cases finished :
          state.frames.isEmpty && state.core.cur.isNone &&
            state.core.alts.isEmpty
      · simp [runWith, finished, mappedFinished, mapped, mapRunOutcome]
      · by_cases reached :
            state.frames.isEmpty &&
              limit.any (fun maximum =>
                state.core.answers.length ≥ maximum)
        · simp [runWith, finished, reached, mappedFinished, mappedReached,
            mapped, mapRunOutcome]
        · simp [runWith, finished, reached, mappedFinished, mappedReached,
            mapped, mapRunOutcome]
  | succ fuel induction =>
      intro state limit
      let mapped := mapState (Target := Subst)
        (SubstEngine.checked engine).denote state
      have mappedDirect :
          (hostDisabled mapped.host.mode && mapped.frames.isEmpty) =
            (hostDisabled state.host.mode && state.frames.isEmpty) := by
        simp [mapped, mapState]
      have mappedFinished :
          (mapped.frames.isEmpty && mapped.core.cur.isNone &&
              mapped.core.alts.isEmpty) =
            (state.frames.isEmpty && state.core.cur.isNone &&
              state.core.alts.isEmpty) := by
        simp [mapped, mapState, SubstEngine.mapConf]
      have mappedReached :
          (mapped.frames.isEmpty &&
              limit.any (fun maximum =>
                mapped.core.answers.length ≥ maximum)) =
            (state.frames.isEmpty &&
              limit.any (fun maximum =>
                state.core.answers.length ≥ maximum)) := by
        simp [mapped, mapState, SubstEngine.mapConf]
      by_cases direct :
          hostDisabled state.host.mode && state.frames.isEmpty
      · have coreRun :=
          (SubstEngine.checked_clean_run_step_simulation
            engine prog gt (fuel + 1)).1 state.core limit
        unfold SubstEngine.erase at coreRun
        have delegated :
            mapRunOutcome (SubstEngine.checked engine).denote
                (fromCoreRunOutcome state.host
                  (SubstEngine.runCleanWith (SubstEngine.checked engine)
                    prog gt (fuel + 1) state.core limit)) =
              fromCoreRunOutcome state.host
                (SubstEngine.runCleanWith SubstEngine.reference
                  prog gt (fuel + 1)
                  (SubstEngine.mapConf
                    (SubstEngine.checked engine).denote state.core)
                  limit) := by
          rw [mapRunOutcome_fromCoreRunOutcome, coreRun]
        simpa [runWith, direct, mappedDirect, mapped, mapState,
          SubstEngine.mapConf] using delegated
      · by_cases finished :
            state.frames.isEmpty && state.core.cur.isNone &&
              state.core.alts.isEmpty
        · simp [runWith, direct, mappedDirect, finished, mappedFinished, mapped,
            mapRunOutcome]
        · by_cases reached :
              state.frames.isEmpty &&
                limit.any (fun maximum =>
                  state.core.answers.length ≥ maximum)
          · simp [runWith, direct, mappedDirect, finished, reached, mappedFinished,
              mappedReached, mapped, mapRunOutcome]
          · have stepEq := checked_stepWith_simulation
                engine prog gt (fuel + 1) state
            cases stepped : stepWith (SubstEngine.checked engine)
                prog gt (fuel + 1) state with
            | progressed next =>
                rw [stepped] at stepEq
                have referenceStep :
                    stepWith SubstEngine.reference prog gt (fuel + 1) mapped =
                      .progressed (mapState
                        (SubstEngine.checked engine).denote next) := by
                  exact stepEq.symm
                simpa [runWith, direct, mappedDirect, finished, reached, mappedFinished,
                  mappedReached, mapped, stepped, referenceStep] using
                    induction next limit
            | requested next request =>
                rw [stepped] at stepEq
                have referenceStep :
                    stepWith SubstEngine.reference prog gt (fuel + 1) mapped =
                      .requested
                        (mapState (SubstEngine.checked engine).denote next)
                        request := by
                  exact stepEq.symm
                simp [runWith, direct, mappedDirect, finished, reached, mappedFinished,
                  mappedReached, mapped, stepped, referenceStep,
                  mapRunOutcome]
            | exhausted done =>
                rw [stepped] at stepEq
                have referenceStep :
                    stepWith SubstEngine.reference prog gt (fuel + 1) mapped =
                      .exhausted
                        (mapState (SubstEngine.checked engine).denote done) := by
                  exact stepEq.symm
                simp [runWith, direct, mappedDirect, finished, reached, mappedFinished,
                  mappedReached, mapped, stepped, referenceStep,
                  mapRunOutcome]
            | errored done error =>
                rw [stepped] at stepEq
                have referenceStep :
                    stepWith SubstEngine.reference prog gt (fuel + 1) mapped =
                      .errored
                        (mapState (SubstEngine.checked engine).denote done)
                        error := by
                  exact stepEq.symm
                simp [runWith, direct, mappedDirect, finished, reached, mappedFinished,
                  mappedReached, mapped, stepped, referenceStep,
                  mapRunOutcome]

def runPersistent (prog : Prog) (gt : GroundingTable) (fuel : Nat)
    (conf : Conf) (host : HostSession) (limit : Option Nat := none) :
    RunOutcome Subst :=
  let engine := executablePersistent
  let initial : State engine.State := {
    core := lift engine conf
    host }
  mapRunOutcome engine.denote (runWith engine prog gt fuel initial limit)

def resumePersistent (prog : Prog) (gt : GroundingTable) (fuel : Nat)
    (state : State Subst) (limit : Option Nat := none) : RunOutcome Subst :=
  let engine := executablePersistent
  mapRunOutcome engine.denote <|
    runWith engine prog gt fuel (mapState engine.ofDenote state) limit

theorem runWith_disabled (engine : SubstEngine) (prog : Prog)
    (gt : GroundingTable) (fuel : Nat) (core : Conf engine.State)
    (limit : Option Nat) :
    runWith engine prog gt (fuel + 1) { core, host := {} } limit =
      fromCoreRunOutcome ({} : HostSession)
        (SubstEngine.runCleanWith engine prog gt (fuel + 1) core limit) := by
  rfl

end HostMachine
end PLeaTTa
