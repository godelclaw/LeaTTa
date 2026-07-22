;; SPDX-License-Identifier: Apache-2.0

;; DESUGAR.map5: pinned translator-hook priority sees the surface binder form;
;; PLeaTTa's program prepass lowers it before translator dispatch.
(= (map-atom $list $x $body) (quote hooked-map))
!(add-translator-rule! map-atom)
!(map-atom (1 2) $x 7)
