; SPDX-License-Identifier: Apache-2.0

; [SPEC metta.pl:275] Predicate/2 constructs the ordinary partial/2 compound
; even when its second field is not a list.  Surface observation preserves
; that exact field rather than exposing the internal compound tag.
!(Predicate (partial f malformed))
