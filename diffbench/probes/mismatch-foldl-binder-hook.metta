;; SPDX-License-Identifier: Apache-2.0

;; DESUGAR.foldl5: translator-hook priority versus binder pre-desugaring.
(= (foldl-atom $list $init $acc $x $body) (quote hooked-foldl))
!(add-translator-rule! foldl-atom)
!(foldl-atom (1 2) 0 $acc $x 7)
