!(import! &self (library pettaclaw-godel lib_mettaclaw))

!(let* (($raw
          (py-call
            (synthetic_llm.chat syn:large:text 128 low
              "Return exactly this S-expression and nothing else: ((remember \"live verified\"))")))
        ($balanced (py-call (helper.balance_parentheses $raw)))
        ($commands (catch (sread $balanced))))
   $commands)
