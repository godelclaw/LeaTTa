; SPDX-License-Identifier: Apache-2.0

; Predicate/2 constructs the same partial/2 term that the translator uses
; for an incomplete call.  Dynamic application must therefore accept it.
(= (f $x) (applied $x))
!(let $partial (Predicate (partial f ()))
   ($partial value))
