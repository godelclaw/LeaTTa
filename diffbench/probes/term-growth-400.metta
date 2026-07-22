(= (bench-grow-term $n $acc)
   (if (== $n 0)
       (size-atom $acc)
       (bench-grow-term (- $n 1) (cons-atom item $acc))))

!(bench-grow-term 400 ())
