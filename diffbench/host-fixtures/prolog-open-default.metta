;; SPDX-License-Identifier: Apache-2.0

;; `between/3` was not in the former allowlist. Default host execution must
;; preserve pinned PeTTa's open predicate dispatch and ordered answer bag.
!(progn (translatePredicate (between 1 3 $x)) $x)
