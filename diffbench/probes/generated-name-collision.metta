; SPDX-License-Identifier: Apache-2.0

; The pinned prelude consumes generated slots _q0 through _q24.  These first
; two queries deliberately collide with the next sequential compiler slots.
; Native PeTTa keeps source and compiler-generated Prolog identities distinct.
!(if True (let $_q25 1 2))

!(if True (let $_q26 1 2))

; Non-colliding large-spelling control.
!(if True (let $_q1000000 1 2))
