#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0

"""Small same-family semantic witnesses for full-scale performance rows.

A completing, value-agreeing witness establishes that the target family's
functionality is present. It counts as *semantic witness coverage*, distinct
from *full-scale completion*. A non-agreeing witness means the target must not
be defended as "just performance".
"""
from __future__ import annotations
import os

import pathlib
import sys
import tempfile

sys.path.insert(0, str(pathlib.Path(__file__).parent))
import diff as D  # noqa: E402


EXAMPLES = pathlib.Path(os.environ.get("PETTA_DIR", str(pathlib.Path.home()/"repos/PeTTa"))) / "examples"


WITNESSES = [
    (
        "fib.metta",
        "fib-small",
        """(= (fib $N)
   (if (< $N 2)
       $N
       (+ (fib (- $N 1))
          (fib (- $N 2)))))

!(fib 10)
""",
        "same exponential recursive fib, smaller n",
    ),
    (
        "fibadd.metta",
        "fibadd-small",
        """!(add-atom &self (= (fib $N)
                    (if (< $N 2)
                        $N
                        (+ (fib (- $N 1))
                           (fib (- $N 2))))))

!(fib 10)
""",
        "dynamic add-atom of recursive rule, smaller n",
    ),
    (
        "he_minimalmetta.metta",
        "he-minimal-div-small",
        """!(import! &self ../lib/lib_he)

(= (div $x $y $accum)
   (chain (eval (- $x $y)) $r1
     (chain (eval (< $r1 0)) $r2
       (chain (unify $r2 True
         $accum
         (chain (eval (+ 1 $accum)) $inc
           (chain (eval (div $r1 $y $inc)) $r4 $r4)
         )) $r3 $r3
       )
     )
   )
)

!(chain (eval (div 100 5 0)) $rr $rr)
""",
        "lib_he chain/eval/unify recursion, smaller dividend",
    ),
    (
        "holbenchmark.metta",
        "holbenchmark-small",
        """(= (map-flat $f ()) ())
(= (map-flat $f (cons $x $xs)) (cons ($f $x) (map-flat $f $xs)))

(= (range $n)
   (if (== $n 0) ()
       (cons $n (range (- $n 1)))))

!(let $temp (map-flat (+ 1) (range 50)) (length $temp))

(= (fold-nested $f $init ()) $init)
(= (fold-nested $f $init (cons $x $xs))
      (if (is-expr $x)
        (fold-nested $f (fold-nested $f $init $x) $xs)
        (fold-nested $f ($f $init $x) $xs)))

(= (deep-nest $n)
   (if (== $n 0) ()
       (cons (range 5) (deep-nest (- $n 1)))))

!(fold-nested + 0 (deep-nest 4))

(= (apply-many $f $n $x)
   (if (== $n 0) $x
       (apply-many $f (- $n 1) ($f $x))))

!(apply-many (+ 1) 20 0)

(= (poly $f $n)
   (if (== $n 0) 0
       (+ ($f $n) (poly $f (- $n 1)))))

!(poly (+ 1) 50)
""",
        "HOF partial application, is-expr, nested folds, smaller ranges",
    ),
    (
        "hyperpose_primes.metta",
        "hyperpose-primes-small",
        """(= (find-divisor $n $test-divisor)
   (if (> (* $test-divisor $test-divisor) $n)
       $n
       (if (== 0 (% $n $test-divisor))
           $test-divisor
           (find-divisor $n (+ $test-divisor 1)))))

(= (prime? $n)
   (== $n (find-divisor $n 2)))

!(msort (collapse (let $xs (3 1 2) (hyperpose $xs))))
!(collapse (hyperpose ((prime? 101) (prime? 103) (prime? 107) (prime? 109))))
!(once (hyperpose ((prime? 1009) (prime? 1013) (prime? 101) (prime? 1019))))
""",
        "hyperpose plus primality recursion, smaller primes",
    ),
    (
        "superpose_primes.metta",
        "superpose-primes-small",
        """(= (find-divisor $n $test-divisor)
   (if (> (* $test-divisor $test-divisor) $n)
       $n
       (if (== 0 (% $n $test-divisor))
           $test-divisor
           (find-divisor $n (+ $test-divisor 1)))))

(= (prime? $n)
   (== $n (find-divisor $n 2)))

!(test ((prime? 1009) (prime? 1013) (prime? 1019) (prime? 1021))
       (True True True True))
""",
        "same four-branch trial-division workload with smaller primes",
    ),
    (
        "invertpeanoplus.metta",
        "invertpeanoplus-small",
        """(= (plus Z $y) $y)
(= (plus (S $x) $y)
   (S (plus $x $y)))

!(plus (S Z) (S Z))
!(let (plus $A (S Z)) (S (S Z)) $A)
!(let (plus (S Z) $B) (S (S Z)) $B)
!(collapse (let (plus $A $B) (S (S Z)) ($A $B)))
!(once (let (plus $A $B) (S (S Z)) ($A $B)))
""",
        "recursive Peano plus with forward and inverted calls, target 2",
    ),
    (
        "matespace.metta",
        "matespace-small",
        """(= (add-atom-no-duplicate $Space $Atom)
   (if (== () (collapse (once (match $Space $Atom $Atom))))
       (add-atom $Space $Atom)
       (empty)))

(= (expand)
   (case (match &self (num $t) $t)
         (($t ((add-atom-no-duplicate &self (num (M $t)))
               (add-atom-no-duplicate &self (num (W $t))))))))

(= (mate)
   (case (match &self (num (M $t)) $t)
         (($t (case (once (match &self (num (W $t)) $t))
                    (($t (add-atom-no-duplicate &self (num (C $t))))))))))

(= (expandK $n)
   (if (== $n 0)
       done
       (let $temp1 (expand)
            (expandK (- $n 1)))))

(= (mate-space-demo $K)
   (let* (($s (add-atom &self (num Z)))
          ($g (expandK $K))
          ($h (mate)))
          (match &self (num $1) (num $1))))

!(length (collapse (mate-space-demo 1)))
""",
        "add-atom-no-duplicate, case/match, collapse, smaller K",
    ),
    (
        "matespace2.metta",
        "matespace2-small",
        """(= (add-atom-no-duplicate $Space $Atom)
   (if (== () (collapse (once (match $Space $Atom $Atom))))
       (add-atom $Space $Atom)
       (empty)))

(= (expand)
   (case (superpose (collapse (match &self (num $t) $t)))
         (($t ((add-atom-no-duplicate &self (num (M $t)))
               (add-atom-no-duplicate &self (num (W $t))))))))

(= (mate)
   (case (superpose (collapse (match &self (num (M $t)) $t)))
         (($t (case (once (match &self (num (W $t)) $t))
                    (($t (add-atom-no-duplicate &self (num (C $t))))))))))

(= (rewriteK $n)
   (if (== $n 0)
       done
       (let* (($temp1 (expand))
              ($temp2 (mate)))
             (rewriteK (- $n 1)))))

(= (mate-space-demo $K)
   (let* (($s (add-atom &self (num Z)))
          ($g (rewriteK $K)))
          (match &self (num $1) (num $1))))

!(length (collapse (mate-space-demo 1)))
""",
        "matespace plus superpose/collapse rewrite loop, smaller K",
    ),
    (
        "matespacefast.metta",
        "matespacefast-small",
        """(= (rewriteK $t $n)
   (if (== $n 0)
       done
       (let* (($_1 (add-atom &self (num (M $t))))
              ($_2 (add-atom &self (num (W $t))))
              ($_3 (add-atom &self (num (C $t)))))
             ((rewriteK (M $t) (- $n 1))
              (rewriteK (W $t) (- $n 1))))))

(= (mate-space-demo $K)
   (let* (($s (add-atom &self (num Z)))
          ($g (rewriteK Z $K)))
          (match &self (num $1) (num $1))))

!(length (collapse (mate-space-demo 5)))
""",
        "binary add-atom expansion and final match, smaller depth",
    ),
    (
        "patrick_iterate_quad.metta",
        "patrick-iterate-quad-small",
        """!(import! &self (library lib_patrick))

(= (quad-step $dummy ($t $i $sum))
   (if (== $i $t)
       ( (+ $t 1) 1 (+ $sum (* $t $i)) )
       ( $t (+ $i 1) (+ $sum (* $t $i)) )))

(= (quad-sum $n)
   (last (iterate 0 (/ (* $n (+ $n 1)) 2) (1 1 0) quad-step)))

!(quad-sum 20)
""",
        "lib_patrick iterate with dynamic step function, smaller n",
    ),
    (
        "peano.metta",
        "peano-small",
        """(= (add-atom-no-duplicate $Space $Atom)
   (if (== () (collapse (once (match $Space $Atom $Atom))))
       (add-atom $Space $Atom)
       (empty)))

(= (expand-once)
   (case (match &self (num $t) $t)
         (($x (add-atom-no-duplicate &self (num (S $x)))))))

(= (expandK $n)
   (if (== $n 0)
       done
       (let $temp1 (expand-once)
            (expandK (- $n 1)))))

(= (demo-peano $K)
   (let* (($s (add-atom &self (num Z)))
          ($g (expandK $K)))
         (match &self (num $1) $1)))

!(length (collapse (demo-peano 12)))
""",
        "space-backed Peano expansion with duplicate guard, smaller K",
    ),
    (
        "peanofast.metta",
        "peanofast-small",
        """(= (expandK $expression $n)
   (if (== $n 0)
       done
       (let $temp1 (add-atom &self (num $expression))
            (expandK (S $expression) (- $n 1)))))

(= (demo-peano $K)
   (expandK Z $K))

!(demo-peano 25)
!(length (collapse (match &self (num $1) $1)))
""",
        "bulk add-atom plus match, smaller K",
    ),
    (
        "permutations.metta",
        "permutations-small",
        """(1 != 2) (1 != 3) (1 != 4)
(2 != 1) (2 != 3) (2 != 4)
(3 != 1) (3 != 2) (3 != 4)
(4 != 1) (4 != 2) (4 != 3)
(E $_1 $_2 $_3 $_4 1 (___ $_1 $_2 $_3 $_4))
(E $_1 $_2 $_3 $_4 2 ($_1 ___ $_2 $_3 $_4))
(E $_1 $_2 $_3 $_4 3 ($_1 $_2 ___ $_3 $_4))
(E $_1 $_2 $_3 $_4 4 ($_1 $_2 $_3 ___ $_4))
(E $_1 $_2 $_3 $_4 5 ($_1 $_2 $_3 $_4 ___))

!(length (collapse (match &self
  (, ($_1 != $_2) ($_2 != $_3) ($_3 != $_1)
     ($_3 != $_4) ($_4 != $_2) ($_4 != $_1)
     (E $_1 $_2 $_3 $_4 $x $state))
  (state1 $state))))
""",
        "comma structural match and factorial search, 4 variables",
    ),
    (
        "pln_roman.metta",
        "pln-roman-small",
        """!(import! &self ../lib/lib_pln)

(= (STV A) (stv 0.5 0.9))
(= (STV B) (stv 0.25 0.9))
(= (STV C) (stv 0.25 0.9))
(= (STV D) (stv 0.5 0.9))

(= (kb)
   ((Sentence ((Inheritance A B) (stv 0.25 0.9)) (1))
    (Sentence ((Inheritance A C) (stv 0.25 0.9)) (2))
    (Sentence ((Inheritance B D) (stv 0.5 0.9)) (3))
    (Sentence ((Inheritance C D) (stv 0.5 0.9)) (4))))

!(PLN.Query (kb) (Inheritance A D) 2 4 4)
""",
        "same PLN.Query path with explicit small step/queue bounds",
    ),
    (
        "scale.metta",
        "scale-small",
        """(= (addK $K)
   (if (== $K 0)
       done
       (let* (($K10 (% $K 10))
              ($t (add-atom &self (r $K $K10))))
              (addK (- $K 1)))))

(= (q-all)
   (collapse (match &self (r $x $y) (r $x $y))))

(= (q-first $a)
   (collapse (match &self (r $a $y) (r $a $y))))

(= (q-second $b)
   (collapse (match &self (r $x $b) (r $x $b))))

(= (q-both $a $b)
   (collapse (match &self (r $a $b) (r $a $b))))

(= (q-rel $r)
   (collapse (match &self ($r 43 3) ($r 43 3))))

(= (indexing-demo $K)
   (let* (($temp (addK $K))
          ($all (q-all))
          ($first (q-first 7))
          ($second (q-second 3))
          ($rel (q-rel r))
          ($both (q-both 42 2)))
         (all: (length $all) first: (length $first) second: (length $second) rel: (length $rel) both: (length $both))))

!(indexing-demo 100)
""",
        "bulk add-atom and index-shaped match queries, smaller K",
    ),
    (
        "tilepuzzle.metta",
        "tilepuzzle-mini-bfs",
        """!(import! &self ../lib/lib_datastructures)

(= (move (___ $_2 $_3
          $_4 $_5 $_6
          $_7 $_8 $_9) R)
   ($_2 ___ $_3
    $_4 $_5 $_6
    $_7 $_8 $_9))

(= (move (___ $_2 $_3
          $_4 $_5 $_6
          $_7 $_8 $_9) D)
   ($_4 $_2 $_3
    ___ $_5 $_6
    $_7 $_8 $_9))

(= (move ($_1 ___ $_3
          $_4 $_5 $_6
          $_7 $_8 $_9) L)
   (___ $_1 $_3
    $_4 $_5 $_6
    $_7 $_8 $_9))

(= (move ($_1 $_2 $_3
          ___ $_5 $_6
          $_7 $_8 $_9) U)
   (___ $_2 $_3
    $_1 $_5 $_6
    $_7 $_8 $_9))

(= (bfs_loop (empty-queue) $N0) $N0)
(= (bfs_loop $Q $N0)
   (let* (($Q1 (once (dequeue $S $Q)))
          ($Ln (collapse (let* (($Snew (move $S $_))
                                ($2 (add-unique-or-fail &dup $Snew)))
                               $Snew)))
          ($Q2 (foldl enqueue $Ln $Q1))
          ($N1 (+ $N0 1)))
         (bfs_loop $Q2 $N1)))

(= (bfs_all $Start)
   (let* (($Pt (add-unique-item-or-empty $Start))
          ($Q1 (enqueue $Start (empty-queue))))
        (bfs_loop $Q1 0)))

!(bfs_all (___ 1 2 3 4 5 6 7 8))
""",
        "tile move patterns plus duplicate-filtered queue BFS on a tiny graph",
    ),
]


def main() -> int:
    print("target\twitness\tfragment\tverdict\tpetta_n\tleatta_n\tcomponents")
    ok = True
    for target, witness, text, components in WITNESSES:
        with tempfile.NamedTemporaryFile(
            "w",
            suffix=".metta",
            prefix=f".perf-witness-{witness}-",
            dir=EXAMPLES,
            delete=False,
        ) as f:
            f.write(text)
            path = pathlib.Path(f.name)
        try:
            row = D.run_file(path)
        finally:
            path.unlink(missing_ok=True)
        _file, frag, _why, verdict, petta_n, leatta_n, _independent = row
        if verdict not in ("AGREE", "AGREE-ORD"):
            ok = False
        print(
            f"{target}\t{witness}\t{frag}\t{verdict}\t"
            f"{petta_n}\t{leatta_n}\t{components}",
            flush=True,
        )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
