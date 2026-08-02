; SPDX-License-Identifier: Apache-2.0
; The same answer-then-recursion predicate returns immediately under once/1.
; This controls the semantic budget used by the soft-cut divergence witness.
(= (softcut-streaming-control) first)
(= (softcut-streaming-control) (softcut-streaming-control))

!(once (softcut-streaming-control))
