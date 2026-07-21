;; SPDX-License-Identifier: Apache-2.0

;; APP.succeedsPredicate: pinned's translator rule accepts a general Prolog
;; predicate shape; PLeaTTa currently recognizes only space-predicate forms.
(: succeedsPredicate (-> Expression Bool))
(= (succeedsPredicate $pattern)
   (quote (case
     (translatePredicate (catch (Predicate $pattern) $_ fail))
     (($item True) (Empty False)))))
!(add-translator-rule! succeedsPredicate)
!(succeedsPredicate (true))
