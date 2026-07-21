;; SPDX-License-Identifier: Apache-2.0

;; APP.bind_new_state characterization: registering the existing static state
;; predicate as a translator rule is source-reachable and currently agrees.
;; Pinned PeTTa rejects attempts to replace that static predicate, so no
;; source-level divergence witness is claimed here.
!(add-translator-rule! change-state!)
!(bind! mismatch-state (new-state initial))
!(get-state mismatch-state)
