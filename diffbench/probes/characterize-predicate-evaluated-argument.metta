;; SPDX-License-Identifier: Apache-2.0

;; Without an Expression declaration, Predicate's ordinary registered-function
;; argument is translated before `=../2` sees it.
!(Predicate ((+ 1 2) value))
