;; Corrected same-capability witness for test_backward_v01 (BROKEN-ORACLE).
;; Pinned PeTTa itself crashes on the original: it stores facts with `!(...)`
;; (which executes, not stores) and defines fact? via an under-applied 2-arg
;; match, so pinned calls fact?/2 while only fact?/3 exists. This witness stores
;; the fact (bare) and defines fact? with the correct 3-arg match, exercising the
;; match / fact? DB-lookup capability the test intended. Both engines must AGREE.
(Inherits Cat Animal (stv 0.9 0.95))
!(match &self (Inherits Cat Animal $tv) (Inherits Cat Animal $tv))
(= (fact? $s $p) (match &self (Inherits $s $p $tv) (Inherits $s $p $tv)))
!(fact? Cat Animal)
