;; SPDX-License-Identifier: Apache-2.0

;; APP.add_atom_rule: the same strictness mismatch with a rule-shaped atom.
!(bind! strict-add-rule-state (new-state initial))
!(add-atom (progn (change-state! strict-add-rule-state changed) &self)
   (= (strict-added $x) $x))
!(get-state strict-add-rule-state)
