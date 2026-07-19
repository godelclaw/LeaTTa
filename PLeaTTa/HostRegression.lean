import PLeaTTa.HostMachine
import PLeaTTa.Builtins

namespace PLeaTTa.HostRegression

open Metta (Atom Ground Subst)
open PLeaTTa.HostMachine
open PLeaTTa.SubstEngine

private def emptyProg : Prog := { clauses := [], facts := [], typeDecls := [] }

#guard match splitStringC
    [Atom.sym "left--right", Atom.gnd (.str "-"), Atom.gnd (.str "")] with
  | .ok [parts] => chainListM parts == some [Atom.gnd (.str "left"),
      Atom.gnd (.str ""), Atom.gnd (.str "right")]
  | _ => false

#guard match splitStringC
    [Atom.gnd (.int 1), Atom.gnd (.str "-"), Atom.gnd (.str "")] with
  | .incorrectArgument "split_string" => true
  | _ => false

#guard stringLengthC [Atom.sym "hello"] == .ok [Atom.gnd (.int 5)]
#guard stringConcatC [Atom.sym "hello", Atom.sym "world"] ==
  .ok [Atom.gnd (.str "helloworld")]
#guard subStringC [Atom.sym "hello", Atom.gnd (.int 1), Atom.var "length",
    Atom.gnd (.int 2)] == .ok [Atom.gnd (.str "el")]
#guard firstCharC [Atom.sym "hello"] == .ok [Atom.gnd (.str "h")]

#guard match firstCharC [Atom.gnd (.int 1)] with
  | .incorrectArgument "first_char" => true
  | _ => false

#guard notEqualOp [Atom.sym "left", Atom.sym "right"] ==
  .ok [Atom.sym "True"]
#guard notEqualOp [Atom.sym "same", Atom.sym "same"] ==
  .ok [Atom.sym "False"]

private def resultVar : Atom := Atom.var "hostResult"

private def lengthArgument : Atom :=
  chainOf [Atom.sym "len",
    chainOf [Atom.gnd (.int 1), Atom.gnd (.int 2)]]

private def lengthRequest : HostRequest :=
  .call "len" [.list [.integer 1, .integer 2]]

private def lengthExchange : HostExchange :=
  { request := lengthRequest, response := .returned (.integer 2) }

private def lengthConf : Conf := {
  cur := some ([Goal.bin "py-call" [lengthArgument] resultVar], [])
  alts := []
  world := {}
  counter := 0
  qterm := resultVar
}

private def replayLength : HostMachine.RunOutcome Subst :=
  HostMachine.runWith reference emptyProg pleattaTable 20
    { core := lengthConf, host := .replay [lengthExchange] } none

#guard match replayLength with
  | .done state =>
      state.core.answers == [Atom.gnd (.int 2)] && state.host.cursor == 1
  | _ => false

private def liveLength : HostMachine.RunOutcome Subst :=
  let initial : HostMachine.State Subst := {
    core := lengthConf
    host := .live }
  match HostMachine.stepWith reference emptyProg pleattaTable 20 initial with
  | .requested suspended request =>
      if request == lengthRequest then
        match suspended.host.supply (.returned (.integer 2)) with
        | .ok supplied =>
            HostMachine.runWith reference emptyProg pleattaTable 20
              { suspended with host := supplied } none
        | .error _ => .errored suspended (Atom.sym "supply-failed")
      else
        .errored suspended (Atom.sym "wrong-request")
  | _ => .errored initial (Atom.sym "did-not-suspend")

#guard match liveLength with
  | .done state =>
      state.core.answers == [Atom.gnd (.int 2)] &&
      state.host.transcript == [lengthExchange] &&
      state.host.cursor == 1
  | _ => false

#guard match HostMachine.runWith reference emptyProg pleattaTable 20
    { core := lengthConf, host := .live } none with
  | .requested _ request remaining =>
      request == lengthRequest && remaining == 20
  | _ => false

private def raisedExchange : HostExchange := {
  request := lengthRequest
  response := .raised { kind := "ValueError", message := "fixture" }
}

private def caughtConf : Conf := {
  cur := some ([Goal.catchg resultVar
    [Goal.bin "py-call" [lengthArgument] resultVar] resultVar], [])
  alts := []
  world := {}
  counter := 0
  qterm := resultVar
}

private def caughtReplay : HostMachine.RunOutcome Subst :=
  HostMachine.runWith reference emptyProg pleattaTable 30
    { core := caughtConf, host := .replay [raisedExchange] } none

#guard match caughtReplay with
  | .done state =>
      state.core.answers == [pythonErrorAtom {
        kind := "ValueError", message := "fixture" }]
  | _ => false

private def mismatchedReplay : HostMachine.RunOutcome Subst :=
  HostMachine.runWith reference emptyProg pleattaTable 20 {
    core := lengthConf
    host := .replay [{
      request := .call "sum" []
      response := .returned (.integer 0) }] } none

#guard match mismatchedReplay with
  | .errored _ _ => true
  | _ => false

private def nestedValue : HostValue :=
  .mapping [
    ("items", .list [.integer 1, .boolean true, .none]),
    ("pair", .tuple [.string "x", .handle 7])]

#guard match HostValue.ofAtom nestedValue.toAtom with
  | .ok decoded => decoded == nestedValue
  | .error _ => false

#guard (HostValue.mapping [
    ("alpha", .integer 1), ("beta", .string "x")]).toAtom ==
  Atom.expr [Atom.sym "dict", Atom.sym "py", Atom.gnd (.int 1),
    Atom.sym "alpha", Atom.sym "x", Atom.sym "beta"]

#guard match HostValue.ofAtom (Atom.gnd (.external "python" "not-a-number")) with
  | .error _ => true
  | .ok _ => false

#guard match HostValue.ofAtom (HostValue.resource "file" 3).toAtom with
  | .ok decoded => decoded == .resource "file" 3
  | .error _ => false

#guard HostRequest.ofPrologCall "sleep" [.int 0] [] ==
  .effect (.sleep (.integer 0))

#guard buildPrologCall
    (chainify (.expr [.sym "atom_codes", .var "NL",
      .expr [.gnd (.int 10)]])) ==
  some ("atom_codes", [.var "NL", .list [.int 10]], ["NL"])

#guard HostRequest.ofPrologCall "open"
    [.str "history.metta", .atom "append", .var "out"] ["out"] ==
  .effect (.fileOpen "history.metta" .append "out")

#guard HostRequest.ofPrologCall "open"
    [.str "history.metta", .atom "invalid", .var "out"] ["out"] ==
  .prologCall "open"
    [.str "history.metta", .atom "invalid", .var "out"] ["out"]

#guard (HostRequest.call "str" [.string "fixture"]).localResponse? ==
  some (.returned (.string "fixture"))

#guard (HostRequest.call "str" [.boolean true]).localResponse? ==
  some (.returned (.string "True"))

-- MeTTa booleans are Prolog atoms at the Janus boundary, while a bool that
-- originated in Python remains a Python bool through the explicit `(@ true)`
-- representation.  Python `str` therefore distinguishes `true` from `True`.
#guard match HostValue.ofAtom (Atom.sym "True") with
  | .ok (.string "true") => true
  | _ => false
#guard match HostValue.ofAtom (Atom.sym "False") with
  | .ok (.string "false") => true
  | _ => false
#guard match HostValue.ofAtom
    (Atom.expr [Atom.sym "@", Atom.sym "true"]) with
  | .ok (.boolean true) => true
  | _ => false
#guard (HostRequest.call "str" [.string "true"]).localResponse? ==
  some (.returned (.string "true"))

#guard (HostRequest.call "operator.add"
    [.string "left", .string "right"]).localResponse? ==
  some (.returned (.string "leftright"))

#guard (HostRequest.call "operator.add"
    [.integer 40, .integer 2]).localResponse? ==
  some (.returned (.integer 42))

-- Python float formatting and overloaded addition remain host operations;
-- the pure executor must not approximate them.
#guard (HostRequest.call "str" [.floating 0]).localResponse?.isNone

#guard (HostRequest.call "operator.add"
    [.string "left", .integer 1]).localResponse?.isNone

private def clockConf : Conf := {
  cur := some ([Goal.bin "get_time" [] resultVar], [])
  alts := []
  world := {}
  counter := 0
  qterm := resultVar
}

private def clockBits : UInt64 := 4745271043949575591

private def clockExchange : HostExchange := {
  request := .effect .clock
  response := .returned (.floating clockBits)
}

private def replayClock : HostMachine.RunOutcome Subst :=
  HostMachine.runWith reference emptyProg pleattaTable 20
    { core := clockConf, host := .replay [clockExchange] } none

#guard match replayClock with
  | .done state =>
      state.core.answers == [Atom.gnd (.float (Float.ofBits clockBits))] &&
      state.host.cursor == 1
  | _ => false

private def printValue : Atom := Atom.gnd (.str "fixture line")

private def printRequest : HostRequest :=
  .effect (.printLine "\"fixture line\"")

private def printExchange : HostExchange := {
  request := printRequest
  response := .returned .none
}

private def printConf : Conf := {
  cur := some ([Goal.bin "println!" [printValue] resultVar], [])
  alts := []
  world := {}
  counter := 0
  qterm := resultVar
}

private def replayPrint : HostMachine.RunOutcome Subst :=
  HostMachine.runWith reference emptyProg pleattaTable 20
    { core := printConf, host := .replay [printExchange] } none

#guard match replayPrint with
  | .done state =>
      state.core.answers == [Atom.sym "True"] && state.host.cursor == 1
  | _ => false

private def mismatchedPrintReplay : HostMachine.RunOutcome Subst :=
  HostMachine.runWith reference emptyProg pleattaTable 20 {
    core := printConf
    host := .replay [{
      request := .effect (.printLine "different line")
      response := .returned .none }] } none

#guard match mismatchedPrintReplay with
  | .errored _ _ => true
  | _ => false

end PLeaTTa.HostRegression
