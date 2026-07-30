import PLeaTTa.HostMachine
import PLeaTTa.Builtins

namespace PLeaTTa.HostRegression

open Metta (Atom Ground Subst)
open PLeaTTa.HostMachine
open PLeaTTa.SubstEngine

private def emptyProg : Prog := { clauses := [], facts := [], typeDecls := [] }

private def missingSourceSink : Atom :=
  chainOf [Atom.sym "Error",
    chainOf [Atom.sym "existence_error", Atom.sym "source_sink",
      Atom.gnd (.str "missing.txt")],
    Atom.var "_hostErrorContext"]

#guard pythonErrorAtom {
    kind := "existence_error:source_sink", message := "missing.txt" } ==
  missingSourceSink

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

private def parsedVar : Atom := Atom.var "Parsed"

-- Imported predicates already implemented by the PLeaTTa grounding table
-- remain inside the certified machine.  In particular, runtime `sread` uses
-- the proved Lean reader rather than silently escaping through SWI.
#guard localPrologGoals? {} pleattaTable "sread"
    [.atom "((rest))", .var "Parsed"] resultVar [] ==
  some [Goal.bin "sread" [Atom.sym "((rest))"] parsedVar,
    Goal.eq resultVar (Atom.sym "True")]

-- Wall-clock ownership is local too, but HostMachine gives this core goal its
-- explicit typed and replayable clock effect instead of approximating time.
#guard localPrologGoals? {} pleattaTable "get_time"
    [.var "Now"] resultVar [] ==
  some [Goal.bin "get_time" [] (Atom.var "Now"),
    Goal.eq resultVar (Atom.sym "True")]

-- A marker for a genuinely imported operation is not mistaken for a certified
-- implementation merely because it appears in the grounding table.
#guard (localPrologGoals? {} pleattaTable "read_line_to_string"
    [.atom "user_input", .var "Line"] resultVar []).isNone

private def localSpaceCatch : List PrologTerm :=
  [.compound "Predicate"
      [.compound "&self" [.atom "friend", .var "left", .var "right"]],
    .var "error", .atom "fail"]

#guard localPrologGoals? {} pleattaTable "catch" localSpaceCatch resultVar [] ==
  some [Goal.smatch (spacePat selfSpace
          (chainOf [Atom.sym "friend", Atom.var "left", Atom.var "right"])),
    Goal.eq resultVar (Atom.sym "True")]

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

-- Internal partial values cross the trusted SWI boundary as the real
-- `partial/2` compound used by pinned PeTTa, never as the internal tag.
#guard buildPrologCall
    (chainOf [.sym "probe", partialC "+" nilA]) ==
  some ("probe",
    [.compound "partial" [.atom "+", .list []]], [])

-- Prolog atoms and strings remain observably distinct, while nested lists and
-- compounds decode into the executable chain representation.
#guard (PrologTerm.atom "same").toAtom == Atom.sym "same"
#guard (PrologTerm.str "same").toAtom == Atom.gnd (.str "same")
#guard (PrologTerm.list [.int 1, .atom "a"]).toAtom ==
  chainOf [Atom.gnd (.int 1), Atom.sym "a"]
#guard (PrologTerm.compound "f" [.atom "a", .str "s"]).toAtom ==
  chainOf [Atom.sym "f", Atom.sym "a", Atom.gnd (.str "s")]

private def orderedPrologRequest : HostRequest :=
  .prologCall "between" [.int 1, .int 2, .var "X"] ["X"]

private def orderedPrologExchange : HostExchange := {
  request := orderedPrologRequest
  response := .prologReturned [
    [{ name := "X", value := .int 1 }],
    [{ name := "X", value := .int 2 }],
    [{ name := "X", value := .int 2 }]]
}

private def orderedPrologConf : Conf := {
  cur := some ([Goal.bin "translatePredicate"
    [chainify (.expr [.sym "between", .gnd (.int 1), .gnd (.int 2),
      .var "X"])] resultVar], [])
  alts := []
  world := {}
  counter := 0
  qterm := .var "X"
}

private def orderedPrologReplay : HostMachine.RunOutcome Subst :=
  HostMachine.runWith reference emptyProg pleattaTable 80
    { core := orderedPrologConf, host := .replay [orderedPrologExchange] } none

-- Returned clause order and duplicate multiplicity survive all the way to
-- ordered PeTTa answers.
#guard match orderedPrologReplay with
  | .done state => state.core.answerValues ==
      [Atom.gnd (.int 1), Atom.gnd (.int 2), Atom.gnd (.int 2)]
  | _ => false

private def wrongKindPrologReplay : HostMachine.RunOutcome Subst :=
  HostMachine.runWith reference emptyProg pleattaTable 20 {
    core := orderedPrologConf
    host := .replay [{
      request := orderedPrologRequest
      response := .returned (.mapping [("X", .integer 1)]) }] } none

-- An ordinary Python-shaped mapping is never silently accepted as a typed
-- Prolog substitution.
#guard match wrongKindPrologReplay with
  | .errored _ _ => true
  | _ => false

private def localIdentityClause : Clause := {
  params := [.var "Input"]
  result := .var "Input"
  body := [] }

private def localPredicateWorld : PWorld :=
  ({ progClauses := [("localIdentity", localIdentityClause)]
     knownHeads := ["localIdentity"]
     knownArities := [("localIdentity", 1)] } : PWorld).reindexClauses

private def localPredicateConf : Conf := {
  cur := some ([Goal.bin "translatePredicate"
    [chainify (.expr [.sym "Predicate",
      .expr [.sym "localIdentity", .gnd (.int 42), .var "Output"]])]
    resultVar], [])
  alts := []
  world := localPredicateWorld
  counter := 0
  qterm := .var "Output"
}

private def localPredicateReplay : HostMachine.RunOutcome Subst :=
  HostMachine.runWith reference emptyProg pleattaTable 80
    { core := localPredicateConf, host := .replay [] } none

-- A locally owned predicate remains inside the certified machine and consumes
-- no host exchange.
#guard match localPredicateReplay with
  | .done state =>
      state.core.answers == [Atom.gnd (.int 42)] && state.host.cursor == 0
  | _ => false

private def helloPredicate : Atom :=
  chainify (.expr [.sym "Predicate", .expr [.sym "hello", .sym "world"]])

private def assertedHelloConf : Conf := {
  cur := some ([
    Goal.wact "assertaPredicate" [helloPredicate] (.var "Asserted"),
    Goal.bin "translatePredicate"
      [chainify (.expr [.sym "Predicate",
        .expr [.sym "hello", .var "Output"]])]
      resultVar], [])
  alts := []
  world := ({} : PWorld).reindexClauses
  counter := 0
  qterm := .var "Output"
}

private def assertedHelloRun : HostMachine.RunOutcome Subst :=
  HostMachine.runWith reference emptyProg pleattaTable 120
    { core := assertedHelloConf, host := .replay [] } none

#guard match assertedHelloRun with
  | .done state =>
      state.core.answers == [Atom.sym "world"] &&
      state.core.world.clauseCandidates "hello" 0 ==
        [{ params := [], result := .sym "world", body := [] }] &&
      state.host.cursor == 0
  | _ => false

private def factPredicate (functor value : String) : Atom :=
  chainify (.expr [.sym "Predicate", .expr [.sym functor, .sym value]])

private def orderedDynamicPredicateConf : Conf := {
  cur := some ([
    Goal.wact "assertzPredicate" [factPredicate "ordered" "first"]
      (.var "A1"),
    Goal.wact "assertzPredicate" [factPredicate "ordered" "second"]
      (.var "A2"),
    Goal.wact "assertaPredicate" [factPredicate "ordered" "zero"]
      (.var "A0"),
    Goal.bin "translatePredicate"
      [chainify (.expr [.sym "Predicate",
        .expr [.sym "ordered", .var "Output"]])]
      resultVar], [])
  alts := []
  world := ({} : PWorld).reindexClauses
  counter := 0
  qterm := .var "Output"
}

-- `asserta` prepends, `assertz` appends, and resolution exposes exact clause
-- order.
#guard match HostMachine.runWith reference emptyProg pleattaTable 200
    { core := orderedDynamicPredicateConf, host := .replay [] } none with
  | .done state => state.core.answerValues ==
      [Atom.sym "zero", Atom.sym "first", Atom.sym "second"]
  | _ => false

private def retractFirstPredicateConf : Conf := {
  cur := some ([
    Goal.wact "assertzPredicate" [factPredicate "retractable" "same"]
      (.var "A1"),
    Goal.wact "assertzPredicate" [factPredicate "retractable" "middle"]
      (.var "A2"),
    Goal.wact "assertzPredicate" [factPredicate "retractable" "same"]
      (.var "A3"),
    Goal.wact "retractPredicate" [factPredicate "retractable" "same"]
      (.var "Removed"),
    Goal.bin "translatePredicate"
      [chainify (.expr [.sym "Predicate",
        .expr [.sym "retractable", .var "Output"]])]
      resultVar], [])
  alts := []
  world := ({} : PWorld).reindexClauses
  counter := 0
  qterm := .var "Output"
}

-- Retraction removes only the first matching clause; later duplicates remain.
#guard match HostMachine.runWith reference emptyProg pleattaTable 240
    { core := retractFirstPredicateConf, host := .replay [] } none with
  | .done state =>
      state.core.answerValues == [Atom.sym "middle", Atom.sym "same"]
  | _ => false

private def malformedPredicateConf : Conf := {
  cur := some ([Goal.wact "assertaPredicate"
    [chainify (.expr [.sym "Predicate", .sym "not-a-call"])] resultVar], [])
  alts := []
  world := ({} : PWorld).reindexClauses
  counter := 0
  qterm := resultVar
}

-- Malformed predicate syntax fails the branch and never mutates the world.
#guard match HostMachine.runWith reference emptyProg pleattaTable 40
    { core := malformedPredicateConf, host := .replay [] } none with
  | .done state =>
      state.core.answers.isEmpty && state.core.world.progClauses.isEmpty
  | _ => false

private def addTwoPredicate : Atom :=
  chainify (.expr [.sym "Predicate",
    .expr [.sym ":-",
      .expr [.sym "Predicate",
        .expr [.sym "addTwo", .var "Input", .var "Output"]],
      .expr [.sym "Predicate",
        .expr [.sym ",",
          .expr [.sym "Predicate",
            .expr [.sym "is", .var "Intermediate",
              .expr [.sym "Predicate",
                .expr [.sym "+", .var "Input", .gnd (.int 1)]]]],
          .expr [.sym "Predicate",
            .expr [.sym "+", .var "Intermediate", .gnd (.int 1),
              .var "Output"]]]]]])

private def assertedAddTwoConf : Conf := {
  cur := some ([
    Goal.wact "assertaPredicate" [addTwoPredicate] (.var "Asserted"),
    Goal.bin "translatePredicate"
      [chainify (.expr [.sym "Predicate",
        .expr [.sym "addTwo", .gnd (.int 40), .var "Output"]])]
      resultVar], [])
  alts := []
  world := ({} : PWorld).reindexClauses
  counter := 0
  qterm := .var "Output"
}

#guard match HostMachine.runWith reference emptyProg pleattaTable 200
    { core := assertedAddTwoConf, host := .replay [] } none with
  | .done state => state.core.answers == [Atom.gnd (.int 42)]
  | _ => false

private def dynamicSourceConf : Conf := {
  cur := some ([
    Goal.wact "process_metta_string"
      [.gnd (.str "(= (increment $x) (+ $x 1))")]
      (.var "Installed"),
    Goal.call "increment" [.gnd (.int 41)] (.var "Output")], [])
  alts := []
  world := ({} : PWorld).reindexClauses
  counter := 0
  qterm := .var "Output"
}

#guard match HostMachine.runWith reference emptyProg pleattaTable 200
    { core := dynamicSourceConf, host := .replay [] } none with
  | .done state => state.core.answers == [Atom.gnd (.int 42)]
  | _ => false

private def dynamicQuerySourceConf : Conf := {
  cur := some ([Goal.wact "process_metta_string"
    [.gnd (.str "!(+ 1 1)")] resultVar], [])
  alts := []
  world := ({} : PWorld).reindexClauses
  counter := 0
  qterm := resultVar
}

-- Runtime source queries are not silently executed as installation effects.
#guard match HostMachine.runWith reference emptyProg pleattaTable 40
    { core := dynamicQuerySourceConf, host := .replay [] } none with
  | .done state =>
      state.core.answers.isEmpty && state.core.world.progClauses.isEmpty
  | _ => false

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
