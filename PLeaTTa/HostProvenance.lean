-- SPDX-License-Identifier: Apache-2.0

import PLeaTTa.Builtins
import PLeaTTa.HostProtocol

/-!
# Typed host-boundary provenance

The replay transcript already records every request that escaped the pure
PLeaTTa machine.  This module derives provenance from that typed request; the
untrusted worker does not get to classify its own execution.  Classification
describes the implementation boundary crossed, not the semantic purity of an
arbitrary Python or SWI-Prolog operation.
-/

namespace PLeaTTa

/-- The implementation boundary crossed by one recorded host request.

`nativeShadowed` is a transcript-level routing regression signal: the request
names an operation in the static engine table that should normally have been
handled before a host exchange was recorded.  It also detects such entries in
imported or manually edited replay transcripts. -/
inductive HostBoundaryClass where
  | nativeShadowed
  | trustedEffect
  | trustedInput
  | trustedPython
  | trustedProlog
  deriving Repr, BEq, Inhabited

/-- A Prolog functor is engine-owned when PLeaTTa's static executable grounding
table has an implementation for it and the table does not deliberately mark it
as an imported host operation.  This is generated from the same routing data
used by the machine, not duplicated as a hand-maintained allowlist.  Runtime
table extensions are outside this standalone transcript classifier. -/
def engineOwnsPrologFunctor (functor : String) : Bool :=
  !importedPrologHostBacked functor &&
    (Metta.GroundingTable.lookup pleattaTable functor).isSome

/-- Classify solely from the typed request that live execution records and
replay consumes. -/
def HostRequest.boundaryClass : HostRequest → HostBoundaryClass
  | .call spec args =>
      if (HostRequest.localResponse? (.call spec args)).isSome then
        .nativeShadowed
      else .trustedPython
  | .importModule _ => .trustedPython
  | .readLine => .trustedInput
  | .prologCall functor _ _ =>
      if engineOwnsPrologFunctor functor then .nativeShadowed
      else .trustedProlog
  | .effect _ => .trustedEffect

/-- Additive accounting for a host transcript. -/
structure HostProvenanceSummary where
  nativeShadowed : Nat := 0
  trustedEffect : Nat := 0
  trustedInput : Nat := 0
  trustedPython : Nat := 0
  trustedProlog : Nat := 0
  deriving Repr, BEq, Inhabited

namespace HostProvenanceSummary

def add (left right : HostProvenanceSummary) : HostProvenanceSummary where
  nativeShadowed := left.nativeShadowed + right.nativeShadowed
  trustedEffect := left.trustedEffect + right.trustedEffect
  trustedInput := left.trustedInput + right.trustedInput
  trustedPython := left.trustedPython + right.trustedPython
  trustedProlog := left.trustedProlog + right.trustedProlog

def ofClass : HostBoundaryClass → HostProvenanceSummary
  | .nativeShadowed => { nativeShadowed := 1 }
  | .trustedEffect => { trustedEffect := 1 }
  | .trustedInput => { trustedInput := 1 }
  | .trustedPython => { trustedPython := 1 }
  | .trustedProlog => { trustedProlog := 1 }

def ofRequest (request : HostRequest) : HostProvenanceSummary :=
  ofClass request.boundaryClass

def ofTranscript : List HostExchange → HostProvenanceSummary
  | [] => {}
  | exchange :: rest => add (ofRequest exchange.request) (ofTranscript rest)

def total (summary : HostProvenanceSummary) : Nat :=
  summary.nativeShadowed + summary.trustedEffect + summary.trustedInput +
    summary.trustedPython + summary.trustedProlog

@[simp] theorem add_assoc (first second third : HostProvenanceSummary) :
    add (add first second) third = add first (add second third) := by
  cases first
  cases second
  cases third
  simp only [add, Nat.add_assoc]

@[simp] theorem total_ofRequest (request : HostRequest) :
    (ofRequest request).total = 1 := by
  cases request with
  | call spec args =>
      simp only [ofRequest, HostRequest.boundaryClass]
      split <;> rfl
  | importModule => rfl
  | readLine => rfl
  | prologCall functor args vars =>
      simp only [ofRequest, HostRequest.boundaryClass]
      split <;> rfl
  | effect => rfl

theorem ofTranscript_append (left right : List HostExchange) :
    ofTranscript (left ++ right) =
      add (ofTranscript left) (ofTranscript right) := by
  induction left with
  | nil =>
      simp only [List.nil_append, ofTranscript, add]
      cases ofTranscript right
      simp
  | cons exchange rest ih =>
      simp only [List.cons_append, ofTranscript, ih, add_assoc]

theorem total_add (left right : HostProvenanceSummary) :
    (add left right).total = left.total + right.total := by
  cases left
  cases right
  simp only [add, total]
  omega

theorem total_ofTranscript (transcript : List HostExchange) :
    (ofTranscript transcript).total = transcript.length := by
  induction transcript with
  | nil => rfl
  | cons exchange rest ih =>
      simp only [ofTranscript, total_add, total_ofRequest, ih, List.length_cons]
      omega

def render (summary : HostProvenanceSummary) : String :=
  "host requests: " ++ toString summary.total ++ "\n" ++
  "  native-shadowed: " ++ toString summary.nativeShadowed ++ "\n" ++
  "  trusted-effect:  " ++ toString summary.trustedEffect ++ "\n" ++
  "  trusted-input:   " ++ toString summary.trustedInput ++ "\n" ++
  "  trusted-python:  " ++ toString summary.trustedPython ++ "\n" ++
  "  trusted-prolog:  " ++ toString summary.trustedProlog

private def classLabel : HostBoundaryClass → String
  | .nativeShadowed => "native-shadowed"
  | .trustedEffect => "trusted-effect"
  | .trustedInput => "trusted-input"
  | .trustedPython => "trusted-python"
  | .trustedProlog => "trusted-prolog"

private def effectLabel : HostEffect → String
  | .printLine _ => "printLine"
  | .clock => "clock"
  | .sleep _ => "sleep"
  | .fileExists _ => "fileExists"
  | .fileRead _ _ => "fileRead"
  | .fileOpen _ _ _ => "fileOpen"
  | .fileWrite _ _ => "fileWrite"
  | .fileNewline _ => "fileNewline"
  | .fileClose _ => "fileClose"
  | .formatTime _ _ _ => "formatTime"

/-- A path- and argument-free operation label suitable for local summaries. -/
def requestLabel : HostRequest → String
  | request@(.call spec _) => classLabel request.boundaryClass ++ " " ++ spec
  | request@(.importModule name) =>
      classLabel request.boundaryClass ++ " import:" ++ name
  | request@(.readLine) => classLabel request.boundaryClass ++ " readLine"
  | request@(.prologCall functor args _) =>
      classLabel request.boundaryClass ++ " " ++ functor ++ "/" ++
        toString args.length
  | request@(.effect operation) =>
      classLabel request.boundaryClass ++ " " ++ effectLabel operation

private def bumpLabel : List (String × Nat) → String → List (String × Nat)
  | [], label => [(label, 1)]
  | (prior, count) :: rest, label =>
      if prior == label then (prior, count + 1) :: rest
      else (prior, count) :: bumpLabel rest label

def requestCounts (transcript : List HostExchange) : List (String × Nat) :=
  transcript.foldl
    (fun counts exchange => bumpLabel counts (requestLabel exchange.request)) []

def renderTranscript (transcript : List HostExchange) : String :=
  let summary := render (ofTranscript transcript)
  let rows := (requestCounts transcript).map fun (label, count) =>
    "  " ++ toString count ++ "  " ++ label
  if rows.isEmpty then summary
  else summary ++ "\nrequest kinds:\n" ++ String.intercalate "\n" rows

end HostProvenanceSummary
end PLeaTTa
