; SPDX-License-Identifier: Apache-2.0
; Pinned case-with-Empty is `(G, Cases) ; (\+ G, Default)`: a failing
; scrutinee with a persistent prefix therefore executes that prefix twice.
!(case (progn (add-atom &self (guard-ran)) (empty))
  ((first selected) (Empty fallback)))
!(collapse (match &self (guard-ran) seen))
