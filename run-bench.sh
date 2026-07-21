#!/bin/bash
# SPDX-License-Identifier: Apache-2.0

# Differential-test PLeaTTa against native PeTTa over the WHOLE example corpus,
# then print the honest tiered summary.  Resumable; ~15 min; needs swipl + a
# PeTTa checkout ($PETTA_DIR to override).  One heavy job — don't run builds
# alongside it.
#   ./run-bench.sh [output.log]
D="$(cd "$(dirname "$0")" && pwd)"
LOG="${1:-$D/diffbench/run.log}"
case "$LOG" in
  /*) ;;
  *) LOG="$(pwd)/$LOG" ;;
esac
WRAP="$(mktemp)"; printf '#!/bin/bash\nulimit -v 16000000 -t "${PLEATTA_CPU_SECONDS:-3600}"\nexec "%s/.lake/build/bin/pleatta" "$@"\n' "$D" > "$WRAP"; chmod +x "$WRAP"
python3 "$D/diffbench/prolog_worker_policy.py" || exit 1
cd "$D/diffbench"
ADMIT_IMPORTS=1 ADMIT_SPACES=1 ADMIT_STATES=1 PLEATTA_WRAPPER="$WRAP" LEATTA_BIN="$WRAP" \
  python3 resume_run.py "$LOG"
echo "--- tiered summary (verified coverage; performance is not coverage) ---"
python3 - "$LOG" <<'PY'
import sys,collections
from pathlib import Path
all_rows={}
rows={}
for l in open(sys.argv[1]):
    if "\t" in l and not l.startswith("#"):
        fs=l.rstrip().split("\t")
        if len(fs)>=4:
            if fs[0].startswith("."): continue
            all_rows[fs[0]]=(fs[1],fs[3])
            if fs[1]=="IN": rows[fs[0]]=fs[3]
machine={f for f,v in rows.items() if v in ("AGREE","AGREE-ORD")}
root=Path(__file__).resolve().parent
deleg={}
for p in [root/"diffbench"/"delegated.tsv", Path("delegated.tsv")]:
    if p.exists():
        for l in p.read_text().splitlines():
            if l.startswith("#") or not l.strip(): continue
            fs=l.split("\t")
            if len(fs)>=2: deleg[fs[0]]=fs[1]
        break
deleg_checked={f for f,v in deleg.items()
               if v=="DELEGATED-CHECKED" and f in rows}-machine
perf=0
for pf in [root/"diffbench"/"performance-frontier.tsv",
           Path("performance-frontier.tsv")]:
    if pf.exists():
        perf=sum(1 for l in pf.read_text().splitlines()
                 if l.strip() and not l.startswith("#"))
        break
known_open_names=set()
for kf in [root/"diffbench"/"known-open.tsv", Path("known-open.tsv")]:
    if kf.exists():
        known_open_names={l.split("\t",1)[0] for l in kf.read_text().splitlines()
                          if l.strip() and not l.startswith("#")}
        break
covered=machine|deleg_checked
perf_in_run=perf
if rows:
    perf_names=set()
    for pf in [root/"diffbench"/"performance-frontier.tsv",
               Path("performance-frontier.tsv")]:
        if pf.exists():
            perf_names={l.split("\t",1)[0] for l in pf.read_text().splitlines()
                        if l.strip() and not l.startswith("#")}
            break
    perf_in_run=sum(1 for f in perf_names
                    if rows.get(f) in
                    ("LEATTA-TIMEOUT", "LEATTA-NOOUT", "LEATTA-EXHAUSTED"))
print(f"verified-engine: {len(machine)}")
print(f"verified-delegated-cert net-new: {len(deleg_checked)}")
if all_rows:
    print(f"VERIFIED coverage: {len(covered)}/{len(all_rows)} corpus; "
          f"{len(covered)}/{len(rows)} in-fragment")
else:
    print(f"VERIFIED coverage: {len(covered)}/{len(rows)} in-fragment")
print(f"performance-disqualified (reported, NOT coverage): {perf_in_run}")
print(f"known-open correctness/performance boundary: "
      f"{sum(1 for f in known_open_names if f in rows)}")
print("open verdicts:", dict(collections.Counter(
    v for f,v in rows.items() if f not in covered)))
PY
rm -f "$WRAP"
