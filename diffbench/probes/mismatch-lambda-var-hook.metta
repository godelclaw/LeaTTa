;; SPDX-License-Identifier: Apache-2.0

;; DESUGAR.lambda_var: the same priority mismatch for the single-variable
;; parameter spelling.
(= (|-> $params $body) (quote hooked-lambda))
!(add-translator-rule! |->)
!((|-> $x 7) 2)
