; SPDX-License-Identifier: Apache-2.0

(= (pair $left $right) ($left $right))

!(pair 42)
!(let $f (pair 42)
   ((|-> ($value) ($f $value)) 43))

!((partial pair (42)) 43)
