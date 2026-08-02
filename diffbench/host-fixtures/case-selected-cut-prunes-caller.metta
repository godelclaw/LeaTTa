; SPDX-License-Identifier: Apache-2.0
; A selected case arm runs at caller cut scope.  Its cut prunes the retained
; scrutinee search and the caller's later alternative.
(= (case-cut-condition) first)
(= (case-cut-condition) second)

!(superpose
  ((case (case-cut-condition)
     ((first (progn (cut) selected))
      (second second-selected)
      (Empty fallback)))
   outer))
