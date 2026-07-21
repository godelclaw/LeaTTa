;; SPDX-License-Identifier: Apache-2.0

;; DESUGAR.filter5: translator-hook priority versus binder pre-desugaring.
(= (filter-atom $list $x $body) (quote hooked-filter))
!(add-translator-rule! filter-atom)
!(filter-atom (1 2) $x True)
