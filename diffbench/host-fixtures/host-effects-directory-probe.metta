(= (file-present $path)
  (progn (translatePredicate (exists_file $path)) True))

!(file-present ".")
!(+ 20 22)
