;; SPDX-License-Identifier: Apache-2.0

;; MISS.sealed: pinned PeTTa evaluates a fresh copy of the expression while
;; PLeaTTa currently has no dedicated sealed translation.
!(sealed () (+ 1 2))
