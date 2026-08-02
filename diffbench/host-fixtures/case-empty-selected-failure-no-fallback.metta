; SPDX-License-Identifier: Apache-2.0
; A successful scrutinee suppresses the Empty fallback even when its selected
; arm subsequently fails: the negated guard re-runs and fails as well.
!(case first ((first (empty)) (Empty fallback)))
