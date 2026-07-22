(: mid-parametric (-> $a $a))
(= (mid-parametric $x) (let (a b) $x $x))

(: at-parametric A)
(: at-parametric T)
(: t-parametric T)
(: testf-parametric (-> $a $a))
(= (testf-parametric at-parametric) t-parametric)

!(mid-parametric ($a b))
!(testf-parametric at-parametric)
