import PLeaTTa.Chain
import Lean.Data.Json

namespace PLeaTTa

open Metta (Atom Ground)
open Lean (FromJson ToJson)

/-- Values that may cross the trusted Python boundary.  The constructors keep
    Janus distinctions that ordinary JSON erases, notably tuples, `None`, and
    opaque object identity. -/
inductive HostValue where
  | integer (value : Int)
  /-- IEEE-754 bits preserve NaN payloads, infinities, and signed zero while
      keeping transcript request equality reflexive. -/
  | floating (bits : UInt64)
  | string (value : String)
  | boolean (value : Bool)
  | none
  | list (items : List HostValue)
  | tuple (items : List HostValue)
  | mapping (items : List (String × HostValue))
  | handle (id : Nat)
  /-- An opaque non-Python host resource.  The kind prevents a file handle
      from being confused with a Python object while the numeric identity is
      stable enough to record and replay. -/
  | resource (kind : String) (id : Nat)
  deriving Repr, BEq, Inhabited

deriving instance Lean.ToJson for HostValue
deriving instance Lean.FromJson for HostValue

/-- A Prolog term for the trusted SWI host boundary.  Unlike `HostValue` (which
    is Python/Janus-oriented), this faithfully carries logic VARIABLES, atoms and
    compounds so a `translatePredicate` goal can be sent with unbound arguments
    and its answer substitution returned. -/
inductive PrologTerm where
  | var (name : String)
  | int (value : Int)
  | floating (bits : UInt64)
  | atom (name : String)
  | str (value : String)
  | list (items : List PrologTerm)
  | compound (functor : String) (args : List PrologTerm)
  | resource (kind : String) (id : Nat)
  deriving Repr, BEq, Inhabited

deriving instance Lean.ToJson for PrologTerm
deriving instance Lean.FromJson for PrologTerm

/-- One variable binding in a Prolog answer.  A structure, rather than a
Python-oriented mapping entry, keeps the Prolog term type visible in the JSON
protocol and preserves binding order. -/
structure PrologBinding where
  name : String
  value : PrologTerm
  deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- One answer substitution.  The outer response is a list of these answers,
so clause order and duplicate multiplicity remain observable. -/
abbrev PrologAnswer := List PrologBinding

mutual

/-- Decode a typed Prolog value into the executable Atom representation.
Lists and compounds use the same internal chain encoding as compiled PeTTa
values; atoms and strings remain distinct. -/
def PrologTerm.toAtom : PrologTerm → Atom
  | .var name => .var name
  | .int value => .gnd (.int value)
  | .floating bits => .gnd (.float (Float.ofBits bits))
  | .atom name => .sym name
  | .str value => .gnd (.str value)
  | .list items => chainOf (prologTermsToAtoms items)
  | .compound functor args =>
      chainOf (.sym functor :: prologTermsToAtoms args)
  | .resource kind id => .gnd (.external kind (toString id))
termination_by structural term => term

def prologTermsToAtoms : List PrologTerm → List Atom
  | [] => []
  | term :: terms => term.toAtom :: prologTermsToAtoms terms
termination_by structural terms => terms

end

/-- Marshal a PLeaTTa atom into a Prolog term for a `translatePredicate` goal.
    Variables and compounds are preserved; unsupported grounds fail. -/
partial def atomToPrologTerm : Atom → Option PrologTerm
  | .var name => some (.var name)
  | .gnd (.int v) => some (.int v)
  | .gnd (.float v) => some (.floating v.toBits)
  | .gnd (.str v) => some (.str v)
  | .gnd (.external kind payload) =>
      payload.toNat?.map (PrologTerm.resource kind)
  | .sym name => some (.atom name)
  | .expr [] => some (.list [])
  | .expr (.sym f :: args) =>
      (args.mapM atomToPrologTerm).map (PrologTerm.compound f)
  | .expr items => (items.mapM atomToPrologTerm).map PrologTerm.list
  | _ => none

/-- Distinct variable names occurring in an atom (the answer keys to request). -/
partial def prologVars : Atom → List String
  | .var name => [name]
  | .expr items => (items.flatMap prologVars).eraseDups
  | _ => []

/-- Reverse `chainify`: decode nested `#c`/`#nil` cons-chains back to surface
    exprs.  The compiler stores a `translatePredicate` argument as chained data
    (`(#c is (#c $x (#c 2 #nil)))`), so it must be unchained before it parses as
    the Prolog goal `(is $x 2)`. -/
partial def deepUnchain (a : Atom) : Atom :=
  match chainListM a with
  | some elems => Atom.expr (elems.map deepUnchain)
  | none => a

/-- Parse a `translatePredicate` argument `(functor a b ...)` into the Prolog
    call components (functor, marshalled arguments, requested variable names).
    The argument arrives chained, so unchain it first.  Returns `none` for a
    non-goal or an unmarshallable argument. -/
def buildPrologCall (innerExpr : Atom) :
    Option (String × List PrologTerm × List String) :=
  let decoded := deepUnchain innerExpr
  let goal := match decoded with
    | .expr [.sym "Predicate", wrapped] => deepUnchain wrapped
    | other => other
  match goal with
  | e@(.expr (.sym functor :: goalArgs)) =>
      (goalArgs.mapM atomToPrologTerm).map
        (fun ptArgs => (functor, ptArgs, prologVars e))
  | _ => none

/-- Decode the value produced by PeTTa's `Predicate` constructor and build
    the corresponding typed Prolog call. -/
def buildCallPredicate (predicate : Atom) :
    Option (String × List PrologTerm × List String) :=
  match deepUnchain predicate with
  | .expr [.sym "Predicate", _] => buildPrologCall predicate
  | _ => none

structure HostError where
  kind : String
  message : String
  deriving Repr, BEq, Inhabited, ToJson, FromJson

inductive HostResponse where
  | returned (value : HostValue)
  | prologReturned (answers : List PrologAnswer)
  | failed
  | raised (error : HostError)
  deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- Numeric host arguments retain exact float bits for transcript equality. -/
inductive HostNumber where
  | integer (value : Int)
  | floating (bits : UInt64)
  deriving Repr, BEq, Inhabited, ToJson, FromJson

def HostNumber.ofPrologTerm : PrologTerm → Option HostNumber
  | .int value => some (.integer value)
  | .floating bits => some (.floating bits)
  | _ => none

inductive HostFileMode where
  | read
  | write
  | append
  deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- Explicit effects needed by PeTTa programs at the trusted host boundary.
    File paths are logical paths; the live driver resolves them beneath its
    configured root.  Replay never touches the filesystem or clock. -/
inductive HostEffect where
  | printLine (text : String)
  | clock
  | sleep (duration : HostNumber)
  | fileExists (path : String)
  | fileRead (path : String) (resultVar : String)
  | fileOpen (path : String) (mode : HostFileMode) (resultVar : String)
  | fileWrite (handle : Nat) (text : String)
  | fileNewline (handle : Nat)
  | fileClose (handle : Nat)
  | formatTime (format : String) (stamp : Option HostNumber)
      (resultVar : String)
  deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- Logical host requests contain no filesystem paths or credentials.  The IO
    driver resolves a module name through its runtime-only module catalog. -/
inductive HostRequest where
  | call (spec : String) (args : List HostValue)
  | importModule (name : String)
  | readLine
  | prologCall (functor : String) (args : List PrologTerm) (vars : List String)
  | effect (operation : HostEffect)
  deriving Repr, BEq, Inhabited, ToJson, FromJson

private def prologText : PrologTerm → Option String
  | .str value => some value
  | .atom value => some value
  | .int value => some (toString value)
  | .floating bits => some (toString (Float.ofBits bits))
  | _ => none

private def prologVar : PrologTerm → Option String
  | .var name => some name
  | _ => none

private def prologFileMode : PrologTerm → Option HostFileMode
  | .atom "read" => some .read
  | .atom "write" => some .write
  | .atom "append" => some .append
  | .str "read" => some .read
  | .str "write" => some .write
  | .str "append" => some .append
  | _ => none

private def prologFileHandle : PrologTerm → Option Nat
  | .resource "file" id => some id
  | _ => none

private def formatResultVar : PrologTerm → Option String
  | .compound "Predicate" [.compound "string" [.var name]] => some name
  | _ => none

private def formatStamp : PrologTerm → Option (Option HostNumber)
  | .compound "get_time" [] => some none
  | value => HostNumber.ofPrologTerm value |>.map some

/-- Recognize the effectful Prolog forms whose state must be represented in
    the typed host protocol.  Every other goal remains an ordinary bounded
    Prolog request. -/
def HostRequest.ofPrologCall (functor : String) (args : List PrologTerm)
    (vars : List String) : HostRequest :=
  match functor, args with
  | "sleep", [duration] =>
      match HostNumber.ofPrologTerm duration with
      | some value => .effect (.sleep value)
      | none => .prologCall functor args vars
  | "exists_file", [path] =>
      match prologText path with
      | some value => .effect (.fileExists value)
      | none => .prologCall functor args vars
  | "read_file_to_string", [path, result, _options] =>
      match prologText path, prologVar result with
      | some value, some resultVar => .effect (.fileRead value resultVar)
      | _, _ => .prologCall functor args vars
  | "open", [path, mode, result] =>
      match prologText path, prologFileMode mode, prologVar result with
      | some value, some fileMode, some resultVar =>
          .effect (.fileOpen value fileMode resultVar)
      | _, _, _ => .prologCall functor args vars
  | "write", [handle, value] =>
      match prologFileHandle handle, prologText value with
      | some id, some text => .effect (.fileWrite id text)
      | _, _ => .prologCall functor args vars
  | "nl", [handle] =>
      match prologFileHandle handle with
      | some id => .effect (.fileNewline id)
      | none => .prologCall functor args vars
  | "close", [handle] =>
      match prologFileHandle handle with
      | some id => .effect (.fileClose id)
      | none => .prologCall functor args vars
  | "format_time", [result, format, stamp] =>
      match formatResultVar result, prologText format, formatStamp stamp with
      | some resultVar, some format, some stamp =>
          .effect (.formatTime format stamp resultVar)
      | _, _, _ => .prologCall functor args vars
  | _, _ => .prologCall functor args vars

/-- Exact, effect-free Python fragments evaluated inside the pure executor.
    Unsupported values deliberately fall back to the real host instead of
    approximating Python's representation or overloaded addition. -/
def HostRequest.localResponse? : HostRequest → Option HostResponse
  | .call "str" [.string value] => some (.returned (.string value))
  | .call "str" [.integer value] =>
      some (.returned (.string (toString value)))
  | .call "str" [.boolean true] => some (.returned (.string "True"))
  | .call "str" [.boolean false] => some (.returned (.string "False"))
  | .call "str" [.none] => some (.returned (.string "None"))
  | .call "operator.add" [.string left, .string right] =>
      some (.returned (.string (left ++ right)))
  | .call "operator.add" [.integer left, .integer right] =>
      some (.returned (.integer (left + right)))
  | _ => none

structure HostExchange where
  request : HostRequest
  response : HostResponse
  deriving Repr, BEq, Inhabited, ToJson, FromJson

inductive HostMode where
  | disabled
  | live
  | replay
  deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- Pure state at the host boundary.  A live request first becomes `pending`;
    the IO driver supplies its response; the pure machine then consumes that
    response exactly as replay consumes the next transcript entry. -/
structure HostSession where
  mode : HostMode := .disabled
  transcript : List HostExchange := []
  cursor : Nat := 0
  pending : Option HostRequest := none
  ready : Option HostResponse := none
  deriving Repr, BEq, Inhabited, ToJson, FromJson

inductive HostProtocolError where
  | unavailable (request : HostRequest)
  | transcriptEnded (position : Nat) (request : HostRequest)
  | transcriptMismatch (position : Nat) (expected actual : HostRequest)
  | pendingMismatch (expected actual : HostRequest)
  | responseWithoutRequest
  | responseAlreadySupplied (request : HostRequest)
  deriving Repr, BEq, Inhabited

inductive HostDecision where
  | respond (response : HostResponse) (session : HostSession)
  | suspend (request : HostRequest) (session : HostSession)
  | fail (error : HostProtocolError)
  deriving Repr, BEq, Inhabited

def HostSession.replay (transcript : List HostExchange) : HostSession :=
  { mode := .replay, transcript }

def HostSession.live : HostSession :=
  { mode := .live }

/-- Resolve a request without performing IO.  Replay consumes a matching
    transcript entry; live mode either suspends or consumes a response that
    the driver supplied for the same pending request. -/
def HostSession.resolve (session : HostSession)
    (request : HostRequest) : HostDecision :=
  match session.mode with
  | .disabled => .fail (.unavailable request)
  | .replay =>
      match session.transcript[session.cursor]? with
      | none => .fail (.transcriptEnded session.cursor request)
      | some exchange =>
          if (Lean.toJson exchange.request).compress ==
              (Lean.toJson request).compress then
            .respond exchange.response
              { session with cursor := session.cursor + 1 }
          else
            .fail (.transcriptMismatch session.cursor exchange.request request)
  | .live =>
      match session.pending, session.ready with
      | none, none =>
          .suspend request { session with pending := some request }
      | some expected, none =>
          if (Lean.toJson expected).compress ==
              (Lean.toJson request).compress then
            .suspend request session
          else .fail (.pendingMismatch expected request)
      | some expected, some response =>
          if (Lean.toJson expected).compress ==
              (Lean.toJson request).compress then
            .respond response
              { session with
                  cursor := session.cursor + 1
                  pending := none
                  ready := none }
          else .fail (.pendingMismatch expected request)
      | none, some _ => .fail .responseWithoutRequest

/-- The only live-IO injection point.  Supplying a response also appends the
    exact request/response pair to the replayable transcript. -/
def HostSession.supply (session : HostSession)
    (response : HostResponse) : Except HostProtocolError HostSession :=
  match session.mode, session.pending, session.ready with
  | .live, some request, none =>
      .ok { session with
        transcript := session.transcript ++ [{ request, response }]
        ready := some response }
  | .live, some request, some _ =>
      .error (.responseAlreadySupplied request)
  | _, _, _ => .error .responseWithoutRequest

mutual

/-- Convert a host value to the internal atom corresponding to Janus' default
    Python-to-Prolog conversion. -/
def HostValue.toAtom : HostValue → Atom
  | .integer value => Atom.gnd (.int value)
  | .floating bits => Atom.gnd (.float (Float.ofBits bits))
  | .string value => Atom.sym value
  | .boolean true => Atom.expr [Atom.sym "@", Atom.sym "true"]
  | .boolean false => Atom.expr [Atom.sym "@", Atom.sym "false"]
  | .none => Atom.expr [Atom.sym "@", Atom.sym "none"]
  | .list items => chainOf (hostValuesToAtoms items)
  | .tuple items => Atom.expr (Atom.sym "-" :: hostValuesToAtoms items)
  | .mapping items =>
      Atom.expr (Atom.sym "dict" :: Atom.sym "py" :: hostMappingToAtoms items)
  | .handle id => Atom.gnd (.external "python" (toString id))
  | .resource kind id => Atom.gnd (.external kind (toString id))

def hostValuesToAtoms : List HostValue → List Atom
  | [] => []
  | value :: rest => value.toAtom :: hostValuesToAtoms rest

/-- Mapping entries arrive in Janus' canonical key order from the worker. -/
def hostMappingToAtoms : List (String × HostValue) → List Atom
  | [] => []
  | (key, value) :: rest =>
      value.toAtom :: Atom.sym key :: hostMappingToAtoms rest

end


mutual

/-- Convert a ground PLeaTTa value through Janus' default Prolog-to-Python
    conversion.  Unsupported compounds fail rather than being stringified. -/
def HostValue.ofAtomFuel : Nat → Atom → Except String HostValue
  | 0, _ => .error "Janus value nesting limit exhausted"
  | _ + 1, Atom.gnd (.int value) => .ok (.integer value)
  | _ + 1, Atom.gnd (.float value) => .ok (.floating value.toBits)
  | _ + 1, Atom.gnd (.str value) => .ok (.string value)
  | _ + 1, Atom.gnd (.bool true) => .ok (.string "true")
  | _ + 1, Atom.gnd (.bool false) => .ok (.string "false")
  | _ + 1, Atom.gnd (.external "python" payload) =>
      match payload.toNat? with
      | some id => .ok (.handle id)
      | Option.none => .error "invalid Python object handle"
  | _ + 1, Atom.gnd (.external kind payload) =>
      match payload.toNat? with
      | some id => .ok (.resource kind id)
      | Option.none => .error "invalid host resource handle"
  | _ + 1, Atom.gnd _ => .error "grounded value is not Janus-marshallable"
  | _ + 1, Atom.sym "True" => .ok (.string "true")
  | _ + 1, Atom.sym "False" => .ok (.string "false")
  | _ + 1, Atom.sym "true" => .ok (.string "true")
  | _ + 1, Atom.sym "false" => .ok (.string "false")
  | _ + 1, Atom.sym value => .ok (.string value)
  | _ + 1, Atom.var _ => .error "cannot pass an unbound variable to Python"
  | _ + 1, Atom.expr [Atom.sym "@", Atom.sym "true"] => .ok (.boolean true)
  | _ + 1, Atom.expr [Atom.sym "@", Atom.sym "false"] => .ok (.boolean false)
  | _ + 1, Atom.expr [Atom.sym "@", Atom.sym "none"] => .ok .none
  | fuel + 1, Atom.expr (Atom.sym "-" :: items) =>
      .tuple <$> hostValuesOfAtomsFuel fuel items
  | fuel + 1, Atom.expr (Atom.sym "dict" :: Atom.sym "py" :: fields) => do
      if fields.length % 2 != 0 then
        throw "malformed Janus dict atom"
      .mapping <$> hostMappingOfAtomsFuel fuel fields
  | fuel + 1, atom =>
      match chainListM atom with
      | some items => .list <$> hostValuesOfAtomsFuel fuel items
      | Option.none => .error "compound value is not Janus-marshallable"

private def hostValuesOfAtomsFuel : Nat → List Atom → Except String (List HostValue)
  | 0, [] => .ok []
  | 0, _ :: _ => .error "Janus value nesting limit exhausted"
  | _ + 1, [] => .ok []
  | fuel + 1, atom :: rest => do
      let value ← HostValue.ofAtomFuel fuel atom
      let values ← hostValuesOfAtomsFuel fuel rest
      .ok (value :: values)

private def hostMappingOfAtomsFuel (fuel : Nat) :
    List Atom → Except String (List (String × HostValue))
  | [] => .ok []
  | value :: Atom.sym key :: rest => do
      let decoded ← HostValue.ofAtomFuel fuel value
      let tail ← hostMappingOfAtomsFuel fuel rest
      .ok ((key, decoded) :: tail)
  | _ :: _ :: _ => .error "Janus dict key is not an atom"
  | [_] => .error "malformed Janus dict atom"

end

def HostValue.ofAtom (atom : Atom) : Except String HostValue :=
  HostValue.ofAtomFuel (atom.size + 1) atom

/-- Decode PeTTa's single `py-call` argument: a list whose head is the call
    specifier and whose tail contains positional arguments. -/
def HostRequest.ofPyCallArgs : List Atom → Except String HostRequest
  | [specification] => do
      let parts ← match chainListM specification with
        | some parts => .ok parts
        | Option.none => .error "py-call expects one call-list argument"
      match parts with
      | [] => .error "py-call call-list is empty"
      | Atom.sym spec :: args => .call spec <$> args.mapM HostValue.ofAtom
      | Atom.gnd (.str spec) :: args =>
          .call spec <$> args.mapM HostValue.ofAtom
      | _ => .error "py-call specifier must be a symbol or string"
  | _ => .error "py-call expects exactly one call-list argument"

/-- Runtime JSON envelope.  The request itself remains path-free; a live
    import may carry a path only in this ephemeral command. -/
structure HostCommand where
  id : Nat
  request : HostRequest
  modulePath? : Option String := none
  deriving Repr, ToJson, FromJson

structure HostReply where
  id : Nat
  response : HostResponse
  deriving Repr, ToJson, FromJson

theorem HostSession.resolve_replay_entry
    (transcript : List HostExchange) (cursor : Nat)
    (request : HostRequest) (response : HostResponse)
    (hentry : transcript[cursor]? = some { request, response }) :
    ({ mode := .replay, transcript, cursor } : HostSession).resolve request =
      .respond response
        { mode := .replay, transcript, cursor := cursor + 1 } := by
  simp [HostSession.resolve, hentry]

theorem HostSession.supply_then_resolve
    (session : HostSession) (request : HostRequest)
    (response : HostResponse)
    (hmode : session.mode = .live)
    (hpending : session.pending = some request)
    (hready : session.ready = none) :
    ∃ supplied,
      session.supply response = .ok supplied ∧
      supplied.resolve request =
        .respond response
          { supplied with
              cursor := supplied.cursor + 1
              pending := none
              ready := none } := by
  rcases session with ⟨mode, transcript, cursor, pending, ready⟩
  simp only at hmode hpending hready
  subst mode
  subst pending
  subst ready
  simp [HostSession.supply, HostSession.resolve]

theorem HostSession.resolve_deterministic
    (session : HostSession) (request : HostRequest)
    (left right : HostDecision)
    (hleft : session.resolve request = left)
    (hright : session.resolve request = right) : left = right := by
  rw [← hleft, ← hright]

end PLeaTTa
