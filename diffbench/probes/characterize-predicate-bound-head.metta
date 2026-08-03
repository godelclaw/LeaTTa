;; SPDX-License-Identifier: Apache-2.0

;; Predicate remains non-strict in syntax but must observe ordinary runtime
;; substitution: a head variable bound by the surrounding computation becomes
;; a valid =../2 functor before the builtin inspects its argument.
!(let $f probe (Predicate ($f value)))
