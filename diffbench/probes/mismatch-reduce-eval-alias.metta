;; SPDX-License-Identifier: Apache-2.0

;; APP.reduce: pinned reduce translates nested arguments before runtime
;; dispatch. PLeaTTa currently aliases reduce to eval of the raw expression.
!(reduce (quote (+ 1 2)))
