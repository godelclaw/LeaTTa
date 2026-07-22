;; SPDX-License-Identifier: Apache-2.0

;; APP.remove_atom_rule: the same strictness mismatch with a rule-shaped atom.
!(add-atom &self (= (strict-removed $x) $x))
!(bind! strict-remove-rule-state (new-state initial))
!(remove-atom (progn (change-state! strict-remove-rule-state changed) &self)
   (= (strict-removed $x) $x))
!(get-state strict-remove-rule-state)
