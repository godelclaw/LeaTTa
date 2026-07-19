(= (add2 $a $b) (+ $a $b))

(= (apply1 $hof $x)
   ($hof $x))

(= (caller $x)
   (apply1 (add2 $x) 1))

!(caller 41)
