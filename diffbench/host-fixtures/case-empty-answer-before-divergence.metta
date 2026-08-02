; SPDX-License-Identifier: Apache-2.0
; Pinned case-with-Empty is a caller-transparent disjunction between the
; positive case lane and a re-run guard under negation.  Once/1 can consume
; the first positive answer without demanding the later recursive answer.
(= (case-streaming-witness) first)
(= (case-streaming-witness) (case-streaming-witness))

!(once (case (case-streaming-witness)
  ((first selected) (Empty missing))))
