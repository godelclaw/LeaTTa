-- SPDX-License-Identifier: Apache-2.0

/-
Module: PLeaTTa.Proofs.PettaClawHistory
Purpose: Append-only guarantees for PettaClaw's recorded host trace and for
  history contents under explicit trusted-host and external-frame contracts.
Trusted boundary: the live host must implement successful history writes by
  append, and unrecorded external actors must leave the history file unchanged.
Main exports: HostSession.supply_transcript_exact,
  HostSession.supply_preserves_historyOpenTraceUsesAppend,
  HistoryRun.append_only,
  pettaClaw_append_open_request
-/
import PLeaTTa.HostProtocol

namespace PLeaTTa
namespace PettaClawHistory

/-- A later list retains the earlier list, in order and with multiplicity, as
an exact prefix. -/
def Extends {α : Type} (before after : List α) : Prop :=
  ∃ suffix, after = before ++ suffix

/-- A deliberately narrow fact about open requests: whenever the distinguished
history path is opened, the selected mode is append.  This is not a complete
capability-safety predicate: generic calls (including shell-like capabilities)
and writes through an already-open handle are accounted for only by the
`hostAppend` premise of `HistoryRun.append_only`. -/
def HistoryOpenUsesAppend (historyPath : String) : HostRequest → Prop
  | .effect (.fileOpen path mode _) => path = historyPath → mode = .append
  | _ => True

/-- Every recorded request that opens the distinguished history path selects
append mode.  Like `HistoryOpenUsesAppend`, this is an open-mode invariant,
not a complete history-integrity policy. -/
def HistoryOpenTraceUsesAppend (historyPath : String)
    (transcript : List HostExchange) : Prop :=
  ∀ exchange, exchange ∈ transcript →
    HistoryOpenUsesAppend historyPath exchange.request

/-- A successful live response extends the executable replay transcript by
exactly its pending request/response pair. -/
theorem HostSession.supply_transcript_exact
    {session next : HostSession} {response : HostResponse}
    (supplied : session.supply response = .ok next) :
    ∃ request,
      session.pending = some request ∧
      next.transcript =
        session.transcript ++ [{ request := request, response := response }] := by
  rcases session with ⟨mode, transcript, cursor, pending, ready⟩
  cases mode with
  | disabled => simp [HostSession.supply] at supplied
  | replay => simp [HostSession.supply] at supplied
  | live =>
      cases pending with
      | none => simp [HostSession.supply] at supplied
      | some request =>
          cases ready with
          | some priorResponse => simp [HostSession.supply] at supplied
          | none =>
              simp [HostSession.supply] at supplied
              subst next
              exact ⟨request, rfl, rfl⟩

/-- Supplying a response never removes or rewrites an existing recorded host
exchange. -/
theorem HostSession.supply_transcript_prefix
    {session next : HostSession} {response : HostResponse}
    (supplied : session.supply response = .ok next) :
    Extends session.transcript next.transcript := by
  rcases supply_transcript_exact supplied with
    ⟨request, _pending, transcript⟩
  exact ⟨[{ request := request, response := response }], transcript⟩

/-- If prior and pending open requests use append mode for the history path,
recording the pending response preserves that narrow open-mode invariant. -/
theorem HostSession.supply_preserves_historyOpenTraceUsesAppend
    {historyPath : String} {session next : HostSession}
    {response : HostResponse}
    (prior : HistoryOpenTraceUsesAppend historyPath session.transcript)
    (pending : ∀ request, session.pending = some request →
      HistoryOpenUsesAppend historyPath request)
    (supplied : session.supply response = .ok next) :
    HistoryOpenTraceUsesAppend historyPath next.transcript := by
  rcases supply_transcript_exact supplied with
    ⟨request, pendingRequest, transcript⟩
  rw [transcript]
  intro exchange member
  rcases List.mem_append.mp member with old | latest
  · exact prior exchange old
  · simp only [List.mem_singleton] at latest
    subst exchange
    exact pending request pendingRequest

abbrev HistoryBytes := List UInt8

/-- The trusted host's semantic promise for one history state change: old
bytes remain an exact prefix. -/
def HistoryContentExtends (before after : HistoryBytes) : Prop :=
  Extends before after

/-- A finite execution alternates recorded host exchanges with possible
unrecorded external steps.  The relation itself does not assume either kind of
step is safe; those premises are supplied to `HistoryRun.append_only`. -/
inductive HistoryRun
    (ApplyHost : HostExchange → HistoryBytes → HistoryBytes → Prop)
    (ExternalStep : HistoryBytes → HistoryBytes → Prop) :
    HistoryBytes → List HostExchange → HistoryBytes → Prop where
  | refl (initial : HistoryBytes) :
      HistoryRun ApplyHost ExternalStep initial [] initial
  | host {initial before after : HistoryBytes}
      {trace : List HostExchange} {exchange : HostExchange}
      (prior : HistoryRun ApplyHost ExternalStep initial trace before)
      (applied : ApplyHost exchange before after) :
      HistoryRun ApplyHost ExternalStep initial
        (trace ++ [exchange]) after
  | external {initial before after : HistoryBytes}
      {trace : List HostExchange}
      (prior : HistoryRun ApplyHost ExternalStep initial trace before)
      (framed : ExternalStep before after) :
      HistoryRun ApplyHost ExternalStep initial trace after

/-- Under an append contract for every recorded host transition and a frame
condition for every unrecorded external transition, every finite history run
is append-only. -/
theorem HistoryRun.append_only
    {ApplyHost : HostExchange → HistoryBytes → HistoryBytes → Prop}
    {ExternalStep : HistoryBytes → HistoryBytes → Prop}
    {initial final : HistoryBytes} {trace : List HostExchange}
    (hostAppend : ∀ exchange before after,
      ApplyHost exchange before after →
        HistoryContentExtends before after)
    (externalFrame : ∀ before after,
      ExternalStep before after → after = before)
    (run : HistoryRun ApplyHost ExternalStep initial trace final) :
    HistoryContentExtends initial final := by
  induction run with
  | refl => exact ⟨[], (List.append_nil _).symm⟩
  | host prior applied inductionHypothesis =>
      rcases inductionHypothesis with ⟨priorSuffix, priorResult⟩
      rcases hostAppend _ _ _ applied with ⟨nextSuffix, nextResult⟩
      refine ⟨priorSuffix ++ nextSuffix, ?_⟩
      rw [nextResult, priorResult, List.append_assoc]
  | external prior framed inductionHypothesis =>
      rw [externalFrame _ _ framed]
      exact inductionHypothesis

/-- PettaClaw's `append-file` primitive reaches the typed host boundary as an
append-mode open, rather than a write/truncate open.  This is an executable
marshalling equation, not yet source-level compiler adequacy for memory.metta.
-/
theorem pettaClaw_append_open_request (path resultVar : String) :
    HostRequest.ofPrologCall "open"
      [.str path, .atom "append", .var resultVar] [resultVar] =
    .effect (.fileOpen path .append resultVar) := by
  rfl

/-- The append-mode open admitted by the PettaClaw history path satisfies the
syntactic trace policy. -/
example (path resultVar : String) :
    HistoryOpenUsesAppend path
      (HostRequest.ofPrologCall "open"
        [.str path, .atom "append", .var resultVar] [resultVar]) := by
  rw [pettaClaw_append_open_request]
  simp [HistoryOpenUsesAppend]

/-- A truncate-mode open on the history path is deliberately rejected by the
policy; the general file capability therefore needs protection or a frame
assumption before the file-level theorem applies to an adversarial model. -/
example (path resultVar : String) :
    ¬ HistoryOpenUsesAppend path
      (.effect (.fileOpen path .write resultVar)) := by
  simp [HistoryOpenUsesAppend]

/-- Truncation is a concrete counterexample to append-only content evolution.
The final theorem cannot be obtained after such a step. -/
example :
    ¬ HistoryContentExtends ([1, 2] : HistoryBytes) [9] := by
  simp [HistoryContentExtends, Extends]

end PettaClawHistory
end PLeaTTa
