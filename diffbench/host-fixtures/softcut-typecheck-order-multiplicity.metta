; SPDX-License-Identifier: Apache-2.0
; Genuine translator.pl T356/T368 `*->` sites: duplicate direct type proofs
; must remain duplicate successful typed-call paths rather than committing to
; the first proof as ordinary `->` would.
(: typed-value DemoType)
(: typed-value DemoType)
(: typed-id (-> DemoType DemoType))
(= (typed-id $x) $x)
!(typed-id typed-value)
