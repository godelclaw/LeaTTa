; SPDX-License-Identifier: Apache-2.0
; A raw Prolog clause does not register its head.  Once add-atom registers the
; same name, however, raw and MeTTa clauses share one ordered predicate; after
; removing the MeTTa rule, the surviving raw clause keeps fun/1 registered.

!(assertzPredicate (Predicate (registry-mixed raw raw-result)))
!(add-atom &self (= (registry-mixed source) source-result))
!(registry-mixed source)
!(registry-mixed raw)
!(remove-atom &self (= (registry-mixed source) source-result))
!(registry-mixed raw)
