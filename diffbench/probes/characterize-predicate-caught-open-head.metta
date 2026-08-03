;; SPDX-License-Identifier: Apache-2.0

;; Predicate errors are PeTTa/Prolog exceptions and must remain observable by
;; the ordinary catch translation rather than escaping as an engine failure.
!(catch (Predicate ($f value)))
