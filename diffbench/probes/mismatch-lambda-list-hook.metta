;; SPDX-License-Identifier: Apache-2.0

;; DESUGAR.lambda_list: pinned translator-hook priority sees the list-parameter
;; lambda; PLeaTTa closure-converts it before translator dispatch.
(= (|-> $params $body) (quote hooked-lambda))
!(add-translator-rule! |->)
!((|-> ($x) 7) 2)
