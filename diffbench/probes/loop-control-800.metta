(= (bench-loop-only $n)
   (if (== $n 0)
       done
       (bench-loop-only (- $n 1))))

!(bench-loop-only 800)
