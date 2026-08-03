;; SPDX-License-Identifier: Apache-2.0
;; Pinned SWI rejects a new clause for its static car-atom/2 predicate.  The
;; executable currently accepts the source definition and dispatches to it.

(= (car-atom $x) custom)

!(car-atom (a b))
