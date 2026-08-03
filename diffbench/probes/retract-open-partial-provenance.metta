; SPDX-License-Identifier: Apache-2.0

; Predicate/2 may construct an open partial/2 term.  Pinned retract/1 later
; unifies it with a compiler-produced partial, binding both residual fields.
(= (f $x) $x)
!(assertzPredicate (Predicate (outer (f) stored)))
!(let $constructed (Predicate (partial $functor $arguments))
   (let $result
     (retractPredicate (Predicate (outer $constructed stored)))
     (retract-open-result $result $functor $arguments)))
