!(let $result
    (if False
        (progn (== True True) $shared)
        7)
    ($result $shared))

!(let $result
    (if True
        7
        (progn (== True True) $shared))
    ($result $shared))

!(let $result
    (if True
        (progn (== True True) $shared))
    (== $result $shared))

!(let $result
    (if (progn (== True True) False)
        (progn (== True True) $shared)
        7)
    (== $result $shared))

!(let $result
    (if False
        (progn (== True True) $left)
        (progn (== True True) $right))
    (== $left $right))
