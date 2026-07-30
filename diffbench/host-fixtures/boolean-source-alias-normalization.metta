; SPDX-License-Identifier: Apache-2.0

(= (probe-boolean-alias true) lower-spelling)
(= (probe-boolean-alias True) upper-spelling)
!(probe-boolean-alias true)
!(probe-boolean-alias True)
