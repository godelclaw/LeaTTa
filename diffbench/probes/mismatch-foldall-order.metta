;; SPDX-License-Identifier: Apache-2.0

;; APP.foldall: pinned executes aggregator setup before the generator, while
;; PLeaTTa materializes the generator before evaluating the aggregator value.
(= (fold-order-generator)
   (progn (change-state! fold-order-state generator)
          (superpose (1 2))))
!(bind! fold-order-state (new-state initial))
!(foldall
   (progn (change-state! fold-order-state aggregator)
          (|-> ($acc $value) (+ $acc $value)))
   (fold-order-generator)
   0)
!(get-state fold-order-state)
