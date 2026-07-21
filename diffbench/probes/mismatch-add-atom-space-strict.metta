;; SPDX-License-Identifier: Apache-2.0

;; APP.add_atom_other: pinned passes the space argument raw; PLeaTTa evaluates
;; it, so this state mutation is observable only in the current PLeaTTa path.
!(bind! strict-add-state (new-state initial))
!(add-atom (progn (change-state! strict-add-state changed) &self) (fact 1))
!(get-state strict-add-state)
