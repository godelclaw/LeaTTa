#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 MesTTo
# SPDX-License-Identifier: Apache-2.0

#
# Static guard for the project invariant: the active development uses no proof placeholders or
# project axioms. The upstream totality gate additionally rejects partial and unsafe declarations;
# PLeaTTa joins the proof-placeholder gate, while its existing executable compiler and trace
# projector remain outside the totality gate until their recursion is made structural.
#
# This is a static check. It strips line comments and backtick-quoted mentions (our docstrings say
# things like "no `sorry`") so only real Lean uses are flagged. The CI also fails on every Lean/Lake
# build warning through scripts/ci/check-build-warnings.sh.
#
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

PROOF_TARGETS=(MettaHyperonFull MeTTaIL MeTTaILProofs MeTTaILTests
  MeTTaIL.lean MeTTaILProofs.lean MeTTaILTests.lean CordialMiners
  CordialMiners.lean PLeaTTa)
TOTAL_TARGETS=(MettaHyperonFull MeTTaIL MeTTaILProofs MeTTaILTests
  MeTTaIL.lean MeTTaILProofs.lean MeTTaILTests.lean CordialMiners
  CordialMiners.lean)

proof_hits=$(rg -n --glob '*.lean' \
  '\b(sorry|admit|native_decide)\b|^[[:space:]]*(axiom|theorem_wanted)\b|_wanted\b' \
  "${PROOF_TARGETS[@]}" 2>/dev/null \
  | rg -v '`[^`]*`' \
  | rg -v ':[0-9]+:[[:space:]]*(--|/-)' \
  | rg -v 'Zero sorry' \
  | rg -v 'no project axiom, no sorry' \
  || true)

totality_hits=$(rg -n --glob '*.lean' \
  '\b(partial|unsafe)[[:space:]]+(def|instance|abbrev|theorem|lemma|structure|inductive)\b' \
  "${TOTAL_TARGETS[@]}" 2>/dev/null \
  | rg -v '`[^`]*`' \
  | rg -v ':[0-9]+:[[:space:]]*(--|/-)' \
  || true)

if [ -n "$proof_hits" ] || [ -n "$totality_hits" ]; then
  echo "FORBIDDEN declarations found:"
  [ -z "$proof_hits" ] || printf '%s\n' "$proof_hits"
  [ -z "$totality_hits" ] || printf '%s\n' "$totality_hits"
  exit 1
fi
echo "OK: no proof placeholders or project axioms in the active Lean sources, including PLeaTTa/."
echo "OK: no partial or unsafe declarations in the upstream totality-gated sources."
