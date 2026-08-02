; SPDX-License-Identifier: Apache-2.0
; The Empty fallback is selected exactly when the re-executed scrutinee has
; no answer under negation-as-failure.
!(case (empty) ((first selected) (Empty fallback)))
