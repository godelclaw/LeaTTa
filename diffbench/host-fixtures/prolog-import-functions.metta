!(import_prolog_functions_from_file "./prolog-import-tools.pl"
    (host_double host_echo host_fail host_raise))
!(host_double 21)
!(host_echo "left,=right")
!(collapse (superpose ((host_fail 1) 43)))
!(catch (host_raise 1))
