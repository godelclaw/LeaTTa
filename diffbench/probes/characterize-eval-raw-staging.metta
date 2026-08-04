;; SPDX-License-Identifier: Apache-2.0

;; Pinned eval receives raw code, recompiles it at run time, and preserves
;; ordered backtracking, caller-variable identity, and the live fresh counter.
(= (eval $left $right) (arity-two $left $right))

!(eval (quote (+ 1 2)))
!(eval (+ 1 2))
!(eval (superpose (1 2 2 3)))
!(let $ignored (eval (let $x 7 $x)) $x)
!(let $first (eval (let $x 1 (+ $x 1)))
   (let $second (eval (let $y 2 (+ $y 2)))
      (cons $first (cons $second ()))))
!(eval left right)
