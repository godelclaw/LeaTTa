;; SPDX-License-Identifier: Apache-2.0

;; Runtime eval distinguishes exact partial/2 compounds from every other
;; Predicate-built compound, and cannot confuse an ordinary source list with
;; the live partial representation.
(= (add-captured $x $y) (+ $x $y))

!(let $partial (add-captured 2)
   (let $roundtrip (eval $partial)
      ($roundtrip 3)))

!(let $compound (Predicate (probe value))
   (collapse (superpose ((eval $compound) rejected-compound))))

!(let $compound (Predicate (partial only-one-field))
   (collapse (superpose ((eval $compound) rejected-partial-one))))

!(let $compound (Predicate (partial one two three))
   (collapse (superpose ((eval $compound) rejected-partial-three))))

!(let $compound (Predicate (partial f malformed))
   (eval $compound))

!(let $source (quote (partial add-captured (2)))
   (let $roundtrip (eval $source)
      ($roundtrip 3)))

!(eval $unbound)
