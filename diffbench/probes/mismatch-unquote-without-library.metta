;; SPDX-License-Identifier: Apache-2.0

;; APP.unquote_quote: pinned gets unquote from lib_he.metta. Without that
;; library PLeaTTa must not hardcode evaluation of the quoted expression.
!(unquote (quote (+ 1 2)))
