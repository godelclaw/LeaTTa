(= (fixture-append $file $text)
  (progn
    (translatePredicate (exists_file $file))
    (translatePredicate (open $file append $out))
    (translatePredicate (write $out $text))
    (translatePredicate (nl $out))
    (translatePredicate (close $out))
    True))

!(fixture-append "host-effects-output.txt" "through-clause")
!(fixture-append (py-call (str "host-effects-output.txt"))
  (swrite ((timestamp) (newline) "message" (newline))))
