!(import_prolog_function atomic_list_concat)
!(import_prolog_function split_string)

(= (fixture-string-replace $str $a $b)
   (atomic_list_concat (split_string $str $a "") $b))
(= (fixture-string-safe $str)
   (fixture-string-replace
     (fixture-string-replace
       (fixture-string-replace $str "\"\"" "_quote_")
       "\n" "_newline_")
     "'" "_apostrophe_"))

!(fixture-string-safe "line one\nline two's \"\"")
