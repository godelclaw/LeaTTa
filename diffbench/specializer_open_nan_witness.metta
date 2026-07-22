(= (apply1 $hof $x)
   ($hof $x))

!(let $n (sqrt-math -1.0)
   (apply1 (cons $n) ()))
