;; SPDX-License-Identifier: Apache-2.0

;; Two runtime conversions pin left-to-right staging and generated-result
;; allocation without relying on a single-occurrence coincidence.
!(let $left (Predicate (a b))
   (let $right (Predicate (c d))
     ($left $right)))
