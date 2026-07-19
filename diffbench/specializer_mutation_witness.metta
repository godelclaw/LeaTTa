(= (g $x) old)

(= (child $hof $x)
   ($hof $x))

(= (parent $hof $x)
   (let $_ (add-atom &self (= (g $y) new))
      (child $hof $x)))

!(collapse (parent g input))
