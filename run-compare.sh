#!/bin/bash
# SPDX-License-Identifier: Apache-2.0

# Side-by-side: PLeaTTa's answers vs native PeTTa's, for one MeTTa file.
# Uses the differential harness's own oracle extractor so both columns are the
# exact answer bags the benchmark compares.  Needs swipl + a PeTTa checkout.
#   ./run-compare.sh FILE.metta          ($PETTA_DIR to override PeTTa location)
D="$(cd "$(dirname "$0")" && pwd)"; BIN="$D/.lake/build/bin/pleatta"
export PETTA_RUNNER="${PETTA_DIR:-$HOME/repos/PeTTa}/test_runner.sh"
echo "--- PLeaTTa (verified engine):"
bash -c 'ulimit -v 16000000 -t "${PLEATTA_CPU_SECONDS:-3600}"; exec "$@"' _ "$BIN" --file "$1"
echo "--- native PeTTa (oracle):"
python3 - "$1" "$D/diffbench" <<'PY'
import sys, pathlib, importlib.util
f, dbench = pathlib.Path(sys.argv[1]).resolve(), sys.argv[2]
spec = importlib.util.spec_from_file_location("d", f"{dbench}/diff.py")
d = importlib.util.module_from_spec(spec); spec.loader.exec_module(d)
try:
    print("[" + ", ".join(d.petta_results(f, float(__import__("os").environ.get("PETTA_COMPARE_TIMEOUT", "600")))) + "]")
except Exception as e:
    print(f"(native run failed/timed out: {type(e).__name__})")
PY
echo "(note: native (test A B) returns 'true'; the benchmark rewrites test->collapse"
echo " so BOTH engines are scored on A's value — see diffbench/diff.py.)"
