(: typed-parametric-overloads (-> $a $a))
(: typed-parametric-overloads (-> $b $b))
(= (typed-parametric-overloads $x) $x)

!(typed-parametric-overloads 5)
