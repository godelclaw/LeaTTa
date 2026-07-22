;; Corrected same-capability witness for test_match_3arg (BROKEN-ORACLE).
;; The pinned test asserts facts with `!(Inherits ...)` (which executes, not
;; stores), so the 3-arg match returns () and the assertion fails in both
;; engines. This witness stores the facts (bare) and exercises the same 3-arg
;; match / collapse / let capability. Both engines must AGREE.
(Inherits Cat Animal (stv 0.9 0.95))
(Inherits Dog Animal (stv 0.85 0.9))
!(match &self (Inherits Cat Animal $tv) (Inherits Cat Animal $tv))
!(collapse (match &self (Inherits $S Animal $tv) (Inherits $S Animal $tv)))
!(let $x (match &self (Inherits Cat Animal $tv) $tv) $x)
