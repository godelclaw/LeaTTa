; SPDX-License-Identifier: Apache-2.0
; A cut in catch/3's protected goal is local to the protected call.  It must
; retain the catch delimiter long enough to deliver the protected answer and
; must not prune the caller's later superpose alternative.

!(superpose ((catch (progn (cut) selected)) outer))
