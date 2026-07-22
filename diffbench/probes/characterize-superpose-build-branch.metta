;; SPDX-License-Identifier: Apache-2.0

;; Pinned build_branch/4 unifies a nonvariable branch value with the enclosing
;; output before it runs the branch conjunction.  The outer let fixes that
;; output to 2, so the value 1 fails before the state effect can run.
!(bind! superpose-order-state (new-state initial))
!(let 2
   (superpose ((progn
     (change-state! superpose-order-state touched)
     1)))
   matched)
!(get-state superpose-order-state)

;; A variable-valued nonempty branch is instead aliased to the enclosing
;; output while translating the whole branch list.  That alias is therefore
;; visible in the second alternative as well as the first.
!(bind! superpose-alias-state (new-state initial))
!(let 2
   (superpose (
     (progn (change-state! superpose-alias-state first) $shared)
     (progn (change-state! superpose-alias-state $shared) 2)))
   matched)
!(get-state superpose-alias-state)

;; The same alias is created while translating the complete enclosing
;; expression, not when the superpose branch later runs.  The outer let
;; schedules its pattern effect before the value goals; that effect must still
;; observe the value 2 through the already-shared variable.
!(bind! superpose-global-state (new-state initial))
!(bind! superpose-global-branch-state (new-state initial))
!(let
   (progn (change-state! superpose-global-state $global-shared) 2)
   (superpose ((progn
     (change-state! superpose-global-branch-state ran)
     $global-shared)))
   matched)
!(get-state superpose-global-state)
!(get-state superpose-global-branch-state)
