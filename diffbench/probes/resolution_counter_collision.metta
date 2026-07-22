(= (f $arg) (g $local))
(= (g 99) ok)

!(let $this_variable_name_is_deliberately_long_enough_to_force_compact_resolution_suffix#r1000000
   42
   ((f a)
    $this_variable_name_is_deliberately_long_enough_to_force_compact_resolution_suffix#r1000000))
