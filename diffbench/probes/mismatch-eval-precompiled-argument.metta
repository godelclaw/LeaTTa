;; SPDX-License-Identifier: Apache-2.0

;; APP.eval: pinned passes the raw argument to runtime eval, so quote remains a
;; staging barrier. PLeaTTa currently precompiles the argument before eval.
!(eval (quote (+ 1 2)))
