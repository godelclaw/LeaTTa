;; SPDX-License-Identifier: Apache-2.0

;; APP.hash_plus: both engines solve the simple unbound relational case first.
;; Pinned #+/3 then rejects a non-integer CLP(FD) domain, while the current
;; PLeaTTa shortcut continues with ordinary floating arithmetic.
!(let $sum (#+ $x 2) (if (= $sum 5) $x empty))
!(catch (#+ 1.5 2))
