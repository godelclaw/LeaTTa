;; SPDX-License-Identifier: Apache-2.0

;; Characterize whether the pinned owned Predicate helper may be shadowed by a
;; source equality.  The executable must make the same dispatch choice.
(= (Predicate $value) shadowed)
!(Predicate (probe value))
