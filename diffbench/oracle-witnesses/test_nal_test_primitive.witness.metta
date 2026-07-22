;; Corrected same-capability witness for test_nal_test_primitive (BROKEN-ORACLE).
;; The pinned test's numeric NAL primitives pass in both engines, but it asserts
;; facts with `!(Inherits ...)` (executes, not stores), so the final backward
;; deduction returns (). This witness stores the facts (bare) and runs a nested-
;; match backward deduction with an inline truth-value combiner, demonstrating
;; the stored-fact deduction capability portably (no machine-local NAL import;
;; the NAL formulas themselves are ordinary arithmetic both engines already
;; agree on). Both engines must AGREE.
(Inherits Cat Mammal (stv 0.95 0.99))
(Inherits Mammal Animal (stv 0.8 0.9))
(= (deduce $S $P)
  (match &self (Inherits $S $M (stv $f1 $c1))
    (match &self (Inherits $M $P (stv $f2 $c2))
      (Inherits $S $P (stv (* $f1 $f2) (* $c1 $c2))))))
!(deduce Cat Animal)
