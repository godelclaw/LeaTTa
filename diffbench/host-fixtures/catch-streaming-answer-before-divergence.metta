; SPDX-License-Identifier: Apache-2.0
; A real Prolog catch/3 streams the first protected-goal answer to once/1.
; The second source clause then diverges if the consumer asks for more.
(= (catch-streaming-witness) first)
(= (catch-streaming-witness) (catch-streaming-witness))

!(once (catch (catch-streaming-witness)))
