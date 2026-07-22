(: typed-incomplete-shared-result-conflict (-> Expression B Atom))
(: typed-incomplete-shared-result-conflict (-> Atom B Atom))
(= (typed-incomplete-shared-result-conflict $x $y) $x)

!(typed-incomplete-shared-result-conflict (quote (a b)))
