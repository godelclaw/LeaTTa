;; SPDX-License-Identifier: Apache-2.0

;; The local-space route removes SWI from the discriminator: only the wrapper
;; result differs after the same successful match.
(friend a b)
!(let $ok (translatePredicate (&self friend a b))
      (result-token $ok))
