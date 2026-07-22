(: typed-incomplete-shared-result (-> Expression B Atom))
(: typed-incomplete-shared-result (-> Number B Atom))
(= (typed-incomplete-shared-result $x $y) $x)

!(typed-incomplete-shared-result (+ 1 2))
