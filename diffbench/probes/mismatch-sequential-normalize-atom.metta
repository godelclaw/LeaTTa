;; SPDX-License-Identifier: Apache-2.0

;; SEQ.normalize_atom: even data passed to a source-ordered add-atom event is
;; normalized recursively before PLeaTTa executes that event. Pinned stores
;; the atom as written.
!(add-atom &self (sequential-lambda (|-> ($x) 7)))
!(match &self (sequential-lambda $value) $value)
