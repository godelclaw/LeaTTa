!(get_time)
!(progn (translatePredicate (sleep 0)) True)
!(progn (translatePredicate (exists_file "host-effects-input.txt")) True)
!(progn
    (translatePredicate
      (read_file_to_string "host-effects-input.txt" $content ()))
    $content)
!(progn
    (translatePredicate (open "host-effects-output.txt" write $out))
    (translatePredicate (write $out "first"))
    (translatePredicate (nl $out))
    (translatePredicate (close $out))
    True)
!(progn
    (translatePredicate (open "host-effects-output.txt" append $out))
    (translatePredicate (write $out "second"))
    (translatePredicate (nl $out))
    (translatePredicate (close $out))
    True)
!(progn
    (translatePredicate
      (format_time (Predicate (string $stamp)) "%Y-%m-%d %H:%M:%S"
        (get_time)))
    $stamp)
