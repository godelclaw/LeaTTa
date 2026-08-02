; SPDX-License-Identifier: Apache-2.0
; A source `case` with an Empty fallback compiles through PeTTa's soft-cut
; lane.  The first scrutinee solution selects the first arm; its later
; recursive alternative must remain undemanded under the outer once/1.
(= (softcut-streaming-witness) first)
(= (softcut-streaming-witness) (softcut-streaming-witness))

!(once (case (softcut-streaming-witness)
  ((first selected) (Empty missing))))
