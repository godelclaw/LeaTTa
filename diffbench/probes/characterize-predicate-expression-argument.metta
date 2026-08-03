;; SPDX-License-Identifier: Apache-2.0

;; An Expression declaration stages Predicate's argument as source data.
(: Predicate (-> Expression %Undefined%))
!(Predicate ((+ 1 2) value))
