;; SPDX-License-Identifier: Apache-2.0

;; APP.size_constraint_nonint: pinned follows its generic equality behavior;
;; PLeaTTa currently raises a compiler error for a non-integer size literal.
!(== (size-atom (1 2)) not-an-integer)
