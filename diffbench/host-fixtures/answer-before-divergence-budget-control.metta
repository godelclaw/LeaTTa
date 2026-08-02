; SPDX-License-Identifier: Apache-2.0
; The same answer-then-recursion predicate returns immediately under once/1.
; This controls the exact semantic budget used by the case streaming witness.
(= (streaming-budget-control) first)
(= (streaming-budget-control) (streaming-budget-control))

!(once (streaming-budget-control))
