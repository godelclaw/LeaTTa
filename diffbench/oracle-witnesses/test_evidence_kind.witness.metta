;; Corrected same-capability witness for test_evidence_kind (BROKEN-ORACLE).
;; The pinned test imports a machine-local `.md` file; both engines faithfully
;; mangle the extension to `.md.metta`, so the import fails in both and the
;; assertions fail. This witness inlines the same evidence-kind definitions and
;; looks them up, demonstrating the evidence-kind capability portably. Both
;; engines must AGREE.
(= (evidence-kind empirical) 0)
(= (evidence-kind expertElicited) 1)
(= (evidence-kind modelDerived) 2)
(= (evidence-kind textInterpreted) 3)
(= (evidence-kind logicalDerivation) 4)
!(evidence-kind empirical)
!(evidence-kind expertElicited)
!(evidence-kind modelDerived)
!(evidence-kind textInterpreted)
!(evidence-kind logicalDerivation)
