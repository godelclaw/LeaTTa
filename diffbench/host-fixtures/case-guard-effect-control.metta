; SPDX-License-Identifier: Apache-2.0
; Control for observing duplicate persistent guard effects.
!(add-atom &self (guard-ran))
!(collapse (match &self (guard-ran) seen))
