;; SPDX-License-Identifier: Apache-2.0
;; A runtime NaN supplied by Python must remain reflexively unifiable when the
;; same clause variable occurs twice.
(= (nan-head $x $x) matched)
!(nan-head (py-call (float "nan")) (py-call (float "nan")))
