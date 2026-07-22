(: typed-parametric-rejection (-> $a $a))
(= (typed-parametric-rejection $x) wrong-parametric-result)

!(typed-parametric-rejection 5)
