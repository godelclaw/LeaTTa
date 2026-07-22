(= (defined-before-import-error $x) (+ $x 1))
!(py-call (int "not-an-integer"))
(= (defined-after-import-error $x) (+ $x 2))
!(println! "CHILD_AFTER_ERROR")
