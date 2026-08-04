; SPDX-License-Identifier: Apache-2.0

(= (cycle-head (tag $x) (box blue) $x) accepted)

!(cycle-head (tag b) (box blue) b)
!(cycle-head $z (box $y) (pair $z b))
