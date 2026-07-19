#!/bin/bash
# SPDX-License-Identifier: Apache-2.0

# Run FILE.metta and emit a machine-checked SLD certificate per answer, then
# verify each with the Lean `checktrace` certifier.  "swipl/pleatta finds, Lean checks."
#   ./run-certify.sh FILE.metta
D="$(cd "$(dirname "$0")" && pwd)"
BIN="$D/.lake/build/bin/pleatta"
CK="${CHECKTRACE:-$HOME/repos/MeTTapedia-algos-fix/lean/algos-lp/.lake/build/bin/checktrace}"
[ -x "$BIN" ] || { echo "not built — run: lake build pleatta" >&2; exit 1; }
[ -x "$CK" ]  || { echo "checker not built — set \$CHECKTRACE or build algos-lp-checker" >&2; exit 1; }
run(){ bash -c 'ulimit -v 16000000 -t "${PLEATTA_CPU_SECONDS:-3600}"; exec "$@"' _ "$@"; }
out="$(mktemp -d)"
trace_log="$(run "$BIN" --trace "$1" "$out" 2>&1)"; trace_status=$?
printf '%s\n' "$trace_log"
[ $trace_status -eq 0 ] || { rm -rf "$out"; exit $trace_status; }
traced="$(printf '%s\n' "$trace_log" | sed -n 's/^TRACED \([0-9][0-9]*\)\/\([0-9][0-9]*\)$/\1 \2/p' | tail -1)"
emitted_total="${traced%% *}"
answer_total="${traced##* }"
[ -n "$traced" ] || { emitted_total=0; answer_total=0; }
n=0; c=0
for t in "$out"/*.sexp; do [ -e "$t" ] || continue; n=$((n+1))
  run "$CK" "$t" >/dev/null 2>&1; r=$?
  { [ $r -eq 0 ] || [ $r -eq 3 ]; } && c=$((c+1)) || true
done
echo "certified $c/$answer_total answers  (emitted $n/$answer_total; checktrace exit 0=certified, 3=certified-except-trusted-collection)"
rm -rf "$out"
[ "$emitted_total" = "$answer_total" ] && [ "$n" = "$answer_total" ] && [ "$c" = "$answer_total" ]
