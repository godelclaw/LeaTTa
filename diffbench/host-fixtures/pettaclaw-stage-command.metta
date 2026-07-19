!(import! &self (library pettaclaw-godel lib_mettaclaw))

!(once (initLoop))
!(once (sread "((rest))"))
!(once (superpose (sread "((rest))")))
!(once (eval (superpose (sread "((rest))"))))
!(once (let $sexpr (sread "((rest))") (superpose $sexpr)))
!(once (let $sexpr (sread "((rest))") (eval (superpose $sexpr))))
!(once
  (let $sexpr (sread "((rest))")
    (collapse
      (let $s (superpose $sexpr)
        (COMMAND_RETURN:
          ($s
            (HandleError
              SINGLE_COMMAND_FORMAT_ERROR_NOTHING_WAS_DONE_PLEASE_FIX_AND_RETRY
              $s
              (catch
                (let $result (eval $s)
                  (py-call (helper.normalize_string $result)))))))))))
!(once
  (collapse
    (let $s (superpose (sread "((rest))"))
      (COMMAND_RETURN:
        ($s
          (HandleError
            SINGLE_COMMAND_FORMAT_ERROR_NOTHING_WAS_DONE_PLEASE_FIX_AND_RETRY
            $s
            (catch
              (let $result (eval $s)
                (py-call (helper.normalize_string $result))))))))))
