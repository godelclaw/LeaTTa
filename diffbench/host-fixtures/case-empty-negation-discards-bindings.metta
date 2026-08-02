; SPDX-License-Identifier: Apache-2.0
; The scrutinee binds $x before failing.  Both the failed positive disjunct and
; the re-run under negation must discard that binding before the Empty arm.
!(case (progn (let $x bound True) (empty))
  ((first selected) (Empty (let $x clean clean))))
