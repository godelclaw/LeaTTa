!(progn
    (translatePredicate
      (read_file_to_string "../outside-root.txt" $content ()))
    $content)
