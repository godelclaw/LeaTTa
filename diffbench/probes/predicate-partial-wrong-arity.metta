; SPDX-License-Identifier: Apache-2.0

; Only the exact partial/2 shape is callable.  A same-named compound with
; arity three remains ordinary data under runtime dispatch.
!(let $value (Predicate (partial a b c))
   ($value argument))
