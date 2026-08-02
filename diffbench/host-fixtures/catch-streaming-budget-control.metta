; SPDX-License-Identifier: Apache-2.0
; The same answer-then-recursion predicate returns immediately under once/1.
; This controls for the semantic budget used by the catch/3 divergence witness.
(= (catch-streaming-control) first)
(= (catch-streaming-control) (catch-streaming-control))

!(once (catch-streaming-control))
