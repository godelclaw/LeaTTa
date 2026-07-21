;; SPDX-License-Identifier: Apache-2.0

;; PROGRAM.static_predesugar: a binder-looking value in the static source
;; program is stored literally by pinned PeTTa but rewritten before PLeaTTa
;; partitions and compiles the source.
(static-lambda (|-> ($x) 7))
!(match &self (static-lambda $value) $value)
