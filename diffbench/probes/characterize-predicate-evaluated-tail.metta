;; SPDX-License-Identifier: Apache-2.0

;; Without an Expression declaration, ordinary nested arguments are reduced
;; before Predicate constructs the Prolog compound.
!(Predicate (probe (+ 1 2)))
