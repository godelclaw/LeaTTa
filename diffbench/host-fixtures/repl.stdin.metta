;; Bounded one-turn stdin (readln!) witness for repl.metta (interactive-stdin).
;; The original repl.metta is an intentionally-unbounded REPL loop with a
;; symbolic `inf` bound, so it never terminates and errors before reaching
;; readln!. This witness exercises the same readln! host capability in one
;; bounded turn: read a line and echo it. Graded by running --host-live (record
;; the line) then --host-replay (deterministic reproduction).
!(let* (($inp (readln!)) ($echoed (println! $inp))) $inp)
