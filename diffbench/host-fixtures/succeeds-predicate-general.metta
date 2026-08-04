;; SPDX-License-Identifier: Apache-2.0

(: succeedsPredicate (-> Expression Bool))
(= (succeedsPredicate $pattern)
   (quote (case
     (translatePredicate (catch (Predicate $pattern) $_ fail))
     (($item True) (Empty False)))))
!(add-translator-rule! succeedsPredicate)

!(succeedsPredicate (true))
!(succeedsPredicate (fail))
!(succeedsPredicate (True))
!(succeedsPredicate (False))
!(succeedsPredicate (atom_codes True (116 114 117 101)))
!(succeedsPredicate (atom_codes True (84 114 117 101)))
!(succeedsPredicate (atom_codes False (102 97 108 115 101)))
!(succeedsPredicate (atom_codes False (70 97 108 115 101)))
!(succeedsPredicate (between 2 3 $x))
!(if (succeedsPredicate (between 2 3 $x)) $x no-answer)
