!(import! &self (library mettaclaw lib_llm_ext.py))
!(import! &self (library mettaclaw ./src/helper.py))
!(car-atom (sread (py-call (helper.balance_parentheses "pin verification bridge"))))
