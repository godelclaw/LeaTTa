#!/bin/bash
# SPDX-License-Identifier: Apache-2.0

# Run a MeTTa program through PLeaTTa (verified core-PeTTa semantics); print its answers.
#   ./run.sh FILE.metta
# The engine is ulimit-guarded (Lean binaries reserve a large address space;
# running the bare binary unguarded has OOM'd machines — always go through this).
BIN="$(cd "$(dirname "$0")" && pwd)/.lake/build/bin/pleatta"
CPU="${PLEATTA_CPU_SECONDS:-3600}"
[ -x "$BIN" ] || { echo "not built yet — run:  lake build pleatta" >&2; exit 1; }
[ -n "$1" ] || { echo "usage: ./run.sh FILE.metta" >&2; exit 2; }
exec bash -c 'ulimit -v 16000000 -t "$1"; shift; exec "$@"' _ "$CPU" "$BIN" --file "$1"
