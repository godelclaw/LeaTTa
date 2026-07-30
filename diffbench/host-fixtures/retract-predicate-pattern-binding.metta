; SPDX-License-Identifier: Apache-2.0

!(assertzPredicate (Predicate (probe-retract first)))
!(assertzPredicate (Predicate (probe-retract second)))
!(progn
  (retractPredicate (Predicate (probe-retract $removed)))
  (removed $removed))
!(progn
  (callPredicate (Predicate (probe-retract $remaining)))
  (remaining $remaining))
