;; SPDX-License-Identifier: Apache-2.0

;; An Expression declaration stages the entire payload as source data.
(: Predicate (-> Expression %Undefined%))
!(Predicate (probe (+ 1 2)))
