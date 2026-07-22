(= (fixture-py-str-helper () $outp) $outp)
(= (fixture-py-str-helper $items $outp)
   (let* (($head (car-atom $items))
          ($tail (cdr-atom $items))
          ($next (py-call (operator.add $outp (py-call (str $head))))))
     (fixture-py-str-helper $tail $next)))
(= (fixture-py-str $items) (fixture-py-str-helper $items ""))

!(once (fixture-py-str ("left" "right")))
