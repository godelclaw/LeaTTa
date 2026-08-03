;; SPDX-License-Identifier: Apache-2.0

;; A non-atom =../2 functor raises a structured type error that remains
;; catchable at the MeTTa observation boundary.
!(catch (Predicate ((bad head) value)))
