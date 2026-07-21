-- SPDX-License-Identifier: Apache-2.0

import PLeaTTa.HostProvenance

namespace PLeaTTa

#guard (HostRequest.prologCall "between"
  [.int 1, .int 2, .var "X"] ["X"]).boundaryClass ==
    .trustedProlog

#guard (HostRequest.prologCall "string_length"
  [.str "abc", .var "N"] ["N"]).boundaryClass ==
    .nativeShadowed

#guard (HostRequest.call "operator.mul"
  [.integer 6, .integer 7]).boundaryClass == .trustedPython

#guard (HostRequest.call "operator.add"
  [.integer 6, .integer 7]).boundaryClass == .nativeShadowed

#guard (HostRequest.effect (.fileExists "/fixture/path")).boundaryClass ==
  .trustedEffect

private def provenanceFixture : List HostExchange := [
  { request := .prologCall "between" [.int 1, .int 2, .var "X"] ["X"],
    response := .prologReturned [] },
  { request := .call "operator.mul" [.integer 6, .integer 7],
    response := .returned (.integer 42) },
  { request := .effect (.fileExists "/fixture/path"),
    response := .returned (.boolean true) }
]

#guard (HostProvenanceSummary.ofTranscript provenanceFixture).total == 3
#guard (HostProvenanceSummary.ofTranscript provenanceFixture).trustedProlog == 1
#guard (HostProvenanceSummary.ofTranscript provenanceFixture).trustedPython == 1
#guard (HostProvenanceSummary.ofTranscript provenanceFixture).trustedEffect == 1

end PLeaTTa
