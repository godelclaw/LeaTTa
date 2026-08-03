; SPDX-License-Identifier: Apache-2.0

; A value produced by Predicate/2 is a genuine positive-arity Prolog
; compound.  Assertion may retain that compound as a clause argument, and a
; later retract pattern must return it through an ordinary variable binding.
!(let $nested (Predicate (inner left right))
   (assertzPredicate (Predicate (outer $nested stored))))
!(progn
  (retractPredicate (Predicate (outer $removed stored)))
  (removed $removed))
