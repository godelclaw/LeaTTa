(= (apply1 $hof $x)
   ($hof $x))

!(let $r (apply1 (cons $x) ())
   (let $ok (= $x 41)
      $r))
