(= (read-missing $file)
  (translatePredicate (read_file_to_string $file $content ())))

!(read-missing "definitely-not-present-pleatta-host-witness.txt")
!(+ 20 22)
