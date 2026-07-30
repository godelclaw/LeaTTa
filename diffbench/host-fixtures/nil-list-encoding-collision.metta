; SPDX-License-Identifier: Apache-2.0

(= (probe-nil ()) empty-list)
(= (probe-nil #nil) source-atom)
!(probe-nil ())
!(probe-nil #nil)
