;; SPDX-License-Identifier: Apache-2.0

;; APP.hash_minus: both engines solve the simple unbound relational case
;; first. Pinned #-/3 then rejects a non-integer CLP(FD) domain, while the
;; current PLeaTTa shortcut continues with ordinary floating arithmetic.
!(let $difference (#- $x 2) (if (= $difference 3) $x empty))
!(catch (#- 1.5 0.5))
