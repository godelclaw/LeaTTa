;; SPDX-License-Identifier: Apache-2.0

;; MISS.dynamic_lambda_eval: the lambda exists only inside a runtime string.
;; Pinned eval translates it after sread reveals the application.
!(import_prolog_function sread)
!(let $forms (sread "(((|-> ($x) (+ $x 1)) 2))")
   (once (eval (superpose $forms))))
