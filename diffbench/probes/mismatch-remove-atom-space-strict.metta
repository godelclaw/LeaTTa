;; SPDX-License-Identifier: Apache-2.0

;; APP.remove_atom_other: pinned passes the space argument raw; PLeaTTa
;; evaluates it before removing the ordinary atom.
!(add-atom &self (strict-remove-fact 1))
!(bind! strict-remove-state (new-state initial))
!(remove-atom (progn (change-state! strict-remove-state changed) &self)
   (strict-remove-fact 1))
!(get-state strict-remove-state)
