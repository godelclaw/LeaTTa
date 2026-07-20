(= (caught-read $file)
  (catch
    (translatePredicate (read_file_to_string $file $content ()))))

!(caught-read "definitely-not-present-pleatta-host-witness.txt")
!(+ 20 22)
