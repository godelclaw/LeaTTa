;; SPDX-License-Identifier: Apache-2.0

;; PAT.special_only: quote is a compiler special form but not a pinned fun/1.
;; Pinned keeps it structural in the rule pattern; PLeaTTa evaluates it.
(= (special-pattern (quote 3)) matched)
!(special-pattern (quote 3))
