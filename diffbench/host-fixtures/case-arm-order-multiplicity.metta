; SPDX-License-Identifier: Apache-2.0
; Pinned case-with-Empty leaves the positive lane nondeterministic.  Scrutinee
; order and duplicate multiplicity therefore remain observable through arms.
(= (case-many) first)
(= (case-many) first)
(= (case-many) second)

!(case (case-many)
  ((first first-selected) (second second-selected) (Empty fallback)))
