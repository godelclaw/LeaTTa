; SPDX-License-Identifier: Apache-2.0
; Control: a guard-side cut in case without an Empty arm likewise runs at the
; caller scope and prunes its later alternative.
!(superpose
  ((case (progn (cut) first) ((first selected)))
   outer))
