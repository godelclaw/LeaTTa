; SPDX-License-Identifier: Apache-2.0

(= (f $x) $x)
(= (probe (partial f ())) collided)
!(probe (f))
