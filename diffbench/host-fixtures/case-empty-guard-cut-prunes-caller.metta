; SPDX-License-Identifier: Apache-2.0
; Pinned case-with-Empty runs its positive guard directly in the caller.  A
; cut there therefore prunes the caller's later disjunct; it is not hidden
; behind the internal barriers used by once/1 or genuine soft cut.
!(superpose
  ((case (progn (cut) first)
     ((first selected) (Empty fallback)))
   outer))
