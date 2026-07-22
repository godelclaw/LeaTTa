;; SPDX-License-Identifier: Apache-2.0

;; DESUGAR.expression_walk: a binder-looking form nested below two ordinary
;; data heads is data in pinned PeTTa. PLeaTTa recursively closure-converts it.
(walk-outer (walk-inner (|-> ($x) 7)))
!(match &self (walk-outer (walk-inner $value)) $value)
