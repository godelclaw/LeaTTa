; SPDX-License-Identifier: Apache-2.0
; A cut in a called predicate commits only that predicate activation.  The
; root query's later disjunct remains reachable.
(= (nested-cut) (progn (cut) nested-selected))
!(superpose ((nested-cut) outer))
