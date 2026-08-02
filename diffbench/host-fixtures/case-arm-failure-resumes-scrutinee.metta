; SPDX-License-Identifier: Apache-2.0
; Failure of the first selected arm resumes the positive scrutinee search.
; Once any scrutinee answer exists, later exhaustion cannot select Empty.
(= (case-resume) first)
(= (case-resume) second)

!(case (case-resume)
  ((first (empty)) (second second-selected) (Empty fallback)))
