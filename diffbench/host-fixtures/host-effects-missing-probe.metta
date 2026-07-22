(= (read-if-present $file)
  (progn
    (translatePredicate (exists_file $file))
    (translatePredicate (read_file_to_string $file $content ()))
    $content))

!(read-if-present "definitely-not-present-pleatta-host-witness.txt")
!(+ 20 22)
