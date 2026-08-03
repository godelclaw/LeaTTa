;; SPDX-License-Identifier: Apache-2.0

;; Pinned Predicate/2 uses =../2 and may therefore construct an ordinary
;; Prolog partial/2 compound.  Its observation intentionally agrees with the
;; separately tagged executable partial-value encoding.
!(Predicate (partial f ()))
