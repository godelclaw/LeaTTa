(= (triple $a $b $c)
   (Triple $a $b $c))

(= (apply1 $hof $x)
   ($hof $x))

!(let $result (apply1 (triple $shared $shared) $shared)
   (let $bound (= $shared A)
      $result))
