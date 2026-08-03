; SPDX-License-Identifier: Apache-2.0

; Exercise a rejected prefix whose source clauses reserve differently-sized
; private fresh intervals.  The selected clause and a later call must expose
; four distinct residual variables.  Failed-copy identities are not public,
; so this guard intentionally observes alpha separation after the prefix and
; does not claim numeric allocator equality or directly observe those copies.
!(assertzPredicate (Predicate (probe-retract-fresh no-one $same $same)))
!(assertzPredicate (Predicate (probe-retract-fresh no-two $left $right)))
!(assertzPredicate (Predicate (probe-retract-fresh target $selectedLeft $selectedRight)))
!(assertzPredicate (Predicate (probe-after-fresh target $laterLeft $laterRight)))
!(progn
  (retractPredicate
    (Predicate (probe-retract-fresh target $removedLeft $removedRight)))
  (callPredicate
    (Predicate (probe-after-fresh target $nextLeft $nextRight)))
  (removed-and-next $removedLeft $removedRight $nextLeft $nextRight))
