; SPDX-License-Identifier: Apache-2.0

; A compiler-produced partial application and Predicate/2's ordinary
; Prolog partial/2 compound have the same pinned Prolog term identity.
; Retraction therefore must match across the two runtime provenance paths.
(= (f $x) $x)
!(assertzPredicate (Predicate (outer (f) stored)))
!(let $constructed (Predicate (partial f ()))
   (let $result
     (retractPredicate (Predicate (outer $constructed stored)))
     (retract-result $result)))
!(callPredicate (Predicate (outer $remaining stored)))
