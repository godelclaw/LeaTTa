;; SPDX-License-Identifier: Apache-2.0

;; A caller-bound partial is live Prolog data. Pinned eval preserves the
;; compound identity, while the current executable erases it into a list.
(= (add-captured $x $y) (+ $x $y))
!(let $f (add-captured 2)
   (let $g (eval $f)
      ($g 3)))
