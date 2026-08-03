; SPDX-License-Identifier: Apache-2.0

; [SPEC translator.pl:59-61] Dynamic partial application appends the stored
; bound arguments.  A non-list second field makes append/3 fail; it must not
; be treated as an empty prefix that invents a call to f/1.
(= (f $x) (applied $x))
!(let $partial (Predicate (partial f malformed))
   ($partial value))
