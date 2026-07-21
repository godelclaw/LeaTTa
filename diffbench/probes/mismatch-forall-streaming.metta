;; SPDX-License-Identifier: Apache-2.0

;; APP.forall: the first generated item fails the test. Pinned streams and
;; stops before the second branch; PLeaTTa materializes all generator answers.
(= (forall-stream-generator)
   (progn (change-state! forall-stream-state first) 1))
(= (forall-stream-generator)
   (progn (change-state! forall-stream-state second) 2))
!(bind! forall-stream-state (new-state initial))
!(forall (forall-stream-generator) (|-> ($value) False))
!(get-state forall-stream-state)
