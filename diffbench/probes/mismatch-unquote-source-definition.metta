;; SPDX-License-Identifier: Apache-2.0

;; APP.unquote_other: pinned dispatches to a source-defined unquote function;
;; PLeaTTa's unconditional special handler currently bypasses that definition.
(= (unquote $value) custom-unquote)
!(unquote 42)
