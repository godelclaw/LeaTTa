#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0

"""Sweep covered PeTTa corpus files through pleatta --trace and checktrace.

The sweep is deliberately file-at-a-time and resumable.  Each pleatta
invocation goes through the required wrapper, and CHECKED counts only traces
accepted by checktrace with exit 0 or exit 3.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import subprocess
import sys
import tempfile
import time


ROOT = pathlib.Path(__file__).resolve().parents[1]
HOME = pathlib.Path.home()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--run-log", type=pathlib.Path,
                        default=ROOT / "diffbench" / "run-p19.log")
    parser.add_argument("--lane", type=pathlib.Path,
                        default=ROOT / "diffbench" / "lane-sweep-p19.tsv")
    parser.add_argument("--delegated", type=pathlib.Path,
                        default=ROOT / "diffbench" / "delegated.tsv")
    parser.add_argument("--examples", type=pathlib.Path,
                        default=HOME / "repos" / "PeTTa" / "examples")
    parser.add_argument("--wrapper", type=pathlib.Path,
                        default=pathlib.Path("/tmp/ptrace.sh"))
    parser.add_argument("--checktrace", type=pathlib.Path,
                        default=HOME / "repos" / "MeTTapedia-algos-fix"
                        / "lean" / "algos-lp" / ".lake" / "build"
                        / "bin" / "checktrace")
    parser.add_argument("--out", type=pathlib.Path,
                        default=ROOT / "diffbench" / "trace-sweep-p1.tsv")
    parser.add_argument("--timeout", type=int, default=90)
    parser.add_argument("--budget", type=int, default=3_000_000)
    parser.add_argument("--budget-override", action="append", default=[],
                        metavar="FILE=N",
                        help="Per-file trace budget override, e.g. types.metta=0")
    parser.add_argument("--only", action="append", default=[],
                        help="Run just this file; may be passed more than once")
    parser.add_argument("--limit", type=int, default=0,
                        help="Run at most N covered files after filtering")
    return parser.parse_args()


def read_covered(run_log: pathlib.Path, delegated: pathlib.Path) -> list[str]:
    covered: list[str] = []
    seen: set[str] = set()
    for line in run_log.read_text().splitlines():
        fields = line.split("\t")
        if len(fields) >= 4 and fields[1] == "IN" and "AGREE" in fields[3]:
            if fields[0] not in seen:
                covered.append(fields[0])
                seen.add(fields[0])
    if delegated.exists():
        for line in delegated.read_text().splitlines():
            if not line.strip() or line.startswith("#"):
                continue
            fields = line.split("\t")
            if len(fields) >= 2 and fields[1] in {"DELEGATED-CHECKED", "DELEGATED-TRUSTED"}:
                if fields[0] not in seen:
                    covered.append(fields[0])
                    seen.add(fields[0])
    return covered


def read_lane_certified(lane: pathlib.Path, delegated: pathlib.Path) -> set[str]:
    out: set[str] = set()
    for path in [lane, delegated]:
        if not path.exists():
            continue
        for line in path.read_text().splitlines():
            if not line.strip() or line.startswith("#"):
                continue
            fields = line.split("\t")
            if len(fields) >= 2 and fields[1] in {"DELEGATED-CHECKED", "DELEGATED-TRUSTED"}:
                out.add(fields[0])
    return out


def read_done(out: pathlib.Path) -> set[str]:
    done: set[str] = set()
    if not out.exists():
        return done
    for line in out.read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        done.add(line.split("\t", 1)[0])
    return done


def read_rows(out: pathlib.Path) -> dict[str, list[str]]:
    rows: dict[str, list[str]] = {}
    if not out.exists():
        return rows
    for line in out.read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        fields = line.split("\t")
        rows[fields[0]] = fields
    return rows


def parse_overrides(items: list[str]) -> dict[str, int]:
    out: dict[str, int] = {}
    for item in items:
        if "=" not in item:
            raise SystemExit(f"bad --budget-override {item!r}; expected FILE=N")
        name, raw = item.split("=", 1)
        out[name] = int(raw)
    return out


TRACED_RE = re.compile(r"TRACED\s+(\d+)/(\d+)")


def run_one(args: argparse.Namespace, name: str, budget: int) -> list[str]:
    src = args.examples / name
    start = time.monotonic()
    with tempfile.TemporaryDirectory(prefix="pleatta-trace-") as tmp_raw:
        tmp = pathlib.Path(tmp_raw)
        cmd = [
            "timeout", str(args.timeout), str(args.wrapper), "--trace",
            str(src), str(tmp), str(budget),
        ]
        proc = subprocess.run(cmd, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE)
        elapsed = f"{time.monotonic() - start:.3f}"
        sexps = sorted(tmp.glob("*.sexp"))
        checked = 0
        trusted = 0
        rejected = 0
        check_notes: list[str] = []
        for sexp in sexps:
            ck = subprocess.run([str(args.checktrace), str(sexp)], text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            if ck.returncode in {0, 3}:
                checked += 1
                if ck.returncode == 3:
                    trusted += 1
            else:
                rejected += 1
                note = (ck.stderr or ck.stdout).strip().splitlines()
                if note:
                    check_notes.append(f"{sexp.name}:{note[0]}")

    m = TRACED_RE.search(proc.stdout)
    traced = int(m.group(1)) if m else len(sexps)
    total = int(m.group(2)) if m else 0
    if proc.returncode == 124:
        status = "TRACE-TIMEOUT"
    elif proc.returncode != 0:
        status = "TRACE-FAIL"
    elif traced == total and checked == total:
        status = "PLEATTA-CERTIFIED"
    elif traced > 0:
        status = "PARTIAL"
    else:
        status = "NOTRACE"
    stderr1 = proc.stderr.strip().splitlines()
    stdout_bad = [line for line in proc.stdout.splitlines()
                  if line.startswith("INTERNAL PANIC")]
    notes = check_notes + stdout_bad + stderr1[:1]
    return [
        name,
        "TRACED",
        f"{traced}/{total}",
        "CHECKED",
        str(checked),
        status,
        f"trusted={trusted}",
        f"rejected={rejected}",
        f"exit={proc.returncode}",
        f"budget={budget}",
        f"seconds={elapsed}",
        " | ".join(notes),
    ]


def row_certified(fields: list[str]) -> bool:
    if len(fields) < 6 or fields[5] != "PLEATTA-CERTIFIED":
        return False
    try:
        traced, total = (int(x) for x in fields[2].split("/", 1))
        checked = int(fields[4])
    except Exception:
        return False
    return total > 0 and traced == total and checked == total


def main() -> int:
    args = parse_args()
    overrides = parse_overrides(args.budget_override)
    covered = read_covered(args.run_log, args.delegated)
    if args.only:
        requested = set(args.only)
        covered = [name for name in covered if name in requested]
    if args.limit > 0:
        covered = covered[:args.limit]
    lane_certified = read_lane_certified(args.lane, args.delegated)
    done = read_done(args.out)

    if not args.wrapper.exists():
        raise SystemExit(f"missing wrapper: {args.wrapper}")
    if not args.checktrace.exists():
        raise SystemExit(f"missing checktrace: {args.checktrace}")

    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("a", encoding="utf-8") as out:
        for name in covered:
            if name in done:
                continue
            budget = overrides.get(name, args.budget)
            row = run_one(args, name, budget)
            out.write("\t".join(row) + "\n")
            out.flush()
            print("\t".join(row), flush=True)

    rows = read_rows(args.out)
    pleatta_certified = {name for name, row in rows.items() if row_certified(row)}
    union = pleatta_certified | lane_certified
    print(
        f"SUMMARY covered={len(covered)} pleatta={len(pleatta_certified)} "
        f"lane={len(lane_certified)} union={len(union)}",
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
