-- SPDX-License-Identifier: Apache-2.0

import PLeaTTa.HostProvenance
import PLeaTTa.Proofs.PettaClawHistory

/-!
# Host-provenance preservation

Live response injection appends exactly one classification unit to the
existing transcript summary.  A successful replay resolution advances its
cursor without changing the recorded transcript or its derived summary.
-/

namespace PLeaTTa
namespace HostSession

theorem supply_provenance_exact
    {session next : HostSession} {response : HostResponse}
    (supplied : session.supply response = .ok next) :
    ∃ request,
      session.pending = some request ∧
      HostProvenanceSummary.ofTranscript next.transcript =
        HostProvenanceSummary.add
          (HostProvenanceSummary.ofTranscript session.transcript)
          (HostProvenanceSummary.ofRequest request) := by
  rcases PettaClawHistory.HostSession.supply_transcript_exact supplied with
    ⟨request, pending, transcript⟩
  refine ⟨request, pending, ?_⟩
  rw [transcript, HostProvenanceSummary.ofTranscript_append]
  rfl

theorem resolve_replay_provenance
    {session next : HostSession} {request : HostRequest}
    {response : HostResponse}
    (replayMode : session.mode = .replay)
    (resolved : session.resolve request = .respond response next) :
    HostProvenanceSummary.ofTranscript next.transcript =
      HostProvenanceSummary.ofTranscript session.transcript := by
  rcases session with ⟨mode, transcript, cursor, pending, ready⟩
  simp only at replayMode
  subst mode
  cases hentry : transcript[cursor]? with
  | none =>
      simp [HostSession.resolve, hentry] at resolved
  | some exchange =>
      by_cases hmatch :
          ((Lean.toJson exchange.request).compress ==
            (Lean.toJson request).compress) = true
      · simp [HostSession.resolve, hentry, hmatch] at resolved
        rcases resolved with ⟨_, rfl⟩
        rfl
      · simp [HostSession.resolve, hentry, hmatch] at resolved

end HostSession
end PLeaTTa
