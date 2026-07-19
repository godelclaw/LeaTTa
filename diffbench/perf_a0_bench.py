#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0

"""Reproducible Phase-A0 probes for PLeaTTa candidate-discovery costs.

Each generated program isolates one code path.  The harness records ordinary
wall-clock time and a separate ``--profile`` run, whose machine counters keep
source parsing/compilation costs distinct from execution costs.  Every row
contains the SHA-256 of the exact generated source.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import statistics
import subprocess
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_ENGINE = ROOT / ".lake" / "build" / "bin" / "pleatta"


@dataclass(frozen=True)
class Case:
    name: str
    purpose: str


CASES = (
    Case("loop-control", "recursive arithmetic/control path with constant world"),
    Case("add-only", "fixed-size non-rule add-atom; no match or output scan"),
    Case("exact-dedup", "growing exact-ground miss query followed by insertion"),
    Case("facts-control", "source/setup control for match and remove probes"),
    Case("data-loop-control", "fixed recursive work with growing preloaded data"),
    Case("match-bound-head", "repeated match with a fixed outer functor"),
    Case("match-unbound", "repeated fully open match"),
    Case("remove-miss", "repeated removal miss over a constant populated space"),
    Case("clauses-control", "fixed clause database with growing data space"),
    Case("clauses-growing", "repeated call with a growing live clause database"),
    Case("term-growth", "growing runtime term with constant space and clauses"),
)
CASE_NAMES = tuple(case.name for case in CASES)


PROFILE_RE = re.compile(
    r"^PROFILE q(?P<query>[0-9]+) "
    r"steps=(?P<steps>[0-9]+) "
    r"answers=(?P<answers>[0-9]+) "
    r"done=(?P<done>true|false) "
    r"stalled=(?P<stalled>\S+) "
    r"goals=(?P<goals>[0-9]+) "
    r"subst=(?P<subst>[0-9]+) "
    r"maxSubst=(?P<max_subst>[0-9]+) "
    r"alts=(?P<alts>[0-9]+) "
    r"maxAltSubst=(?P<max_alt_subst>[0-9]+) "
    r"selfAtoms=(?P<self_atoms>[0-9]+) "
    r"clauses=(?P<clauses>[0-9]+) "
    r"counter=(?P<counter>[0-9]+)$"
)

HEADER = (
    "case", "size", "source_sha256", "source_bytes", "plain_runs",
    "median_s", "min_s", "max_s", "profile_s", "steps", "answers",
    "done", "stalled", "goals", "subst", "max_subst", "alts", "max_alt_subst",
    "self_atoms", "clauses", "counter_delta", "verdict",
)


def facts(size: int) -> str:
    return "".join(f"(bench-item {i})\n" for i in range(size))


def dummy_clauses(size: int) -> str:
    return "".join(
        f"(= (bench-dummy-{i} $x) $x)\n" for i in range(size)
    )


def source(case: str, size: int, repeats: int) -> str:
    if case == "loop-control":
        return f"""(= (bench-loop-only $n)
   (if (== $n 0)
       done
       (bench-loop-only (- $n 1))))

!(bench-loop-only {size})
"""
    if case == "add-only":
        return f"""(= (bench-add-only $n)
   (if (== $n 0)
       done
       (let $ignored (add-atom &self (bench-fixed item))
            (bench-add-only (- $n 1)))))

!(bench-add-only {size})
"""
    if case == "exact-dedup":
        return f"""(= (bench-add-unique $n)
   (if (== $n 0)
       done
       (let* (($candidate (bench-item $n))
              ($seen (collapse (once
                       (match &self $candidate $candidate))))
              ($ignored (if (== $seen ())
                            (add-atom &self $candidate)
                            done)))
             (bench-add-unique (- $n 1)))))

!(bench-add-unique {size})
"""
    if case == "facts-control":
        return facts(size) + "\n!(== 0 0)\n"
    if case == "data-loop-control":
        return facts(size) + f"""
(= (bench-data-loop $n)
   (if (== $n 0)
       done
       (bench-data-loop (- $n 1))))

!(bench-data-loop {repeats})
"""
    if case == "match-bound-head":
        return facts(size) + f"""
(= (bench-match-bound $n)
   (if (== $n 0)
       done
       (let $ignored (once (match &self (bench-item 0) True))
            (bench-match-bound (- $n 1)))))

!(bench-match-bound {repeats})
"""
    if case == "match-unbound":
        return facts(size) + f"""
(= (bench-match-unbound $n)
   (if (== $n 0)
       done
       (let $ignored (once (match &self $anything True))
            (bench-match-unbound (- $n 1)))))

!(bench-match-unbound {repeats})
"""
    if case == "remove-miss":
        return facts(size) + f"""
(= (bench-remove-miss $n)
   (if (== $n 0)
       done
       (let $ignored (remove-atom &self (bench-never-present))
            (bench-remove-miss (- $n 1)))))

!(bench-remove-miss {repeats})
"""
    if case == "clauses-control":
        return facts(size) + f"""
(= (bench-target $x) $x)
(= (bench-call-target $n $acc)
   (if (== $n 0)
       $acc
       (bench-call-target (- $n 1) (bench-target $acc))))

!(bench-call-target {repeats} 0)
"""
    if case == "clauses-growing":
        return dummy_clauses(size) + f"""
(= (bench-target $x) $x)
(= (bench-call-target $n $acc)
   (if (== $n 0)
       $acc
       (bench-call-target (- $n 1) (bench-target $acc))))

!(bench-call-target {repeats} 0)
"""
    if case == "term-growth":
        return f"""(= (bench-grow-term $n $acc)
   (if (== $n 0)
       (size-atom $acc)
       (bench-grow-term (- $n 1) (cons-atom item $acc))))

!(bench-grow-term {size} ())
"""
    raise ValueError(f"unknown case: {case}")


def run_engine(
    engine: Path,
    mode: str,
    program: Path,
    fuel: int,
    timeout: float,
) -> tuple[float, subprocess.CompletedProcess[str]]:
    started = time.perf_counter()
    proc = subprocess.run(
        [str(engine), mode, str(program), str(fuel)],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
        check=False,
    )
    return time.perf_counter() - started, proc


def failure_detail(proc: subprocess.CompletedProcess[str]) -> str:
    text = (proc.stderr.strip() or proc.stdout.strip()).replace("\t", " ")
    return text.splitlines()[-1][:160] if text else f"exit-{proc.returncode}"


def profile_fields(stdout: str) -> dict[str, str] | None:
    for line in reversed(stdout.splitlines()):
        match = PROFILE_RE.match(line.strip())
        if match:
            return match.groupdict()
    return None


def timeout_row(case: str, size: int, digest: str, source_bytes: int,
                runs: int, verdict: str) -> tuple[str, ...]:
    return (
        case, str(size), digest, str(source_bytes), str(runs),
        "TIMEOUT", "-", "-", "-", "-", "-", "-", "-", "-", "-",
        "-", "-", "-", "-", "-", "-", verdict,
    )


def measure(
    engine: Path,
    case: str,
    size: int,
    query_repeats: int,
    runs: int,
    fuel: int,
    timeout: float,
    work: Path,
) -> tuple[str, ...]:
    program_source = source(case, size, query_repeats)
    encoded = program_source.encode("utf-8")
    digest = hashlib.sha256(encoded).hexdigest()
    program = work / f"{case}-{size}.metta"
    program.write_bytes(encoded)

    timings: list[float] = []
    try:
        for _ in range(runs):
            elapsed, proc = run_engine(
                engine, "--file", program, fuel, timeout
            )
            if proc.returncode != 0:
                return timeout_row(
                    case, size, digest, len(encoded), len(timings),
                    f"PLAIN-ERROR:{failure_detail(proc)}",
                )
            if not proc.stdout.strip():
                return timeout_row(
                    case, size, digest, len(encoded), len(timings),
                    "PLAIN-NO-OUTPUT",
                )
            timings.append(elapsed)
    except subprocess.TimeoutExpired:
        return timeout_row(
            case, size, digest, len(encoded), len(timings), "PLAIN-TIMEOUT"
        )

    try:
        profile_elapsed, profile = run_engine(
            engine, "--profile", program, fuel, timeout
        )
    except subprocess.TimeoutExpired:
        return timeout_row(
            case, size, digest, len(encoded), len(timings), "PROFILE-TIMEOUT"
        )
    if profile.returncode != 0:
        return timeout_row(
            case, size, digest, len(encoded), len(timings),
            f"PROFILE-ERROR:{failure_detail(profile)}",
        )
    fields = profile_fields(profile.stdout)
    if fields is None:
        return timeout_row(
            case, size, digest, len(encoded), len(timings),
            "PROFILE-MISSING-COUNTERS",
        )
    done = fields["done"]
    verdict = "OK" if done == "true" else "PROFILE-INCOMPLETE"
    counter_delta = int(fields["counter"]) - 1_000_000
    return (
        case,
        str(size),
        digest,
        str(len(encoded)),
        str(len(timings)),
        f"{statistics.median(timings):.6f}",
        f"{min(timings):.6f}",
        f"{max(timings):.6f}",
        f"{profile_elapsed:.6f}",
        fields["steps"],
        fields["answers"],
        done,
        fields["stalled"],
        fields["goals"],
        fields["subst"],
        fields["max_subst"],
        fields["alts"],
        fields["max_alt_subst"],
        fields["self_atoms"],
        fields["clauses"],
        str(counter_delta),
        verdict,
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--engine", type=Path, default=DEFAULT_ENGINE)
    parser.add_argument("--cases", nargs="+", choices=CASE_NAMES,
                        default=list(CASE_NAMES))
    parser.add_argument("--sizes", nargs="+", type=int,
                        default=[100, 200, 400])
    parser.add_argument("--query-repeats", type=int, default=16)
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--fuel", type=int, default=30_000_000)
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--emit-case", choices=CASE_NAMES)
    parser.add_argument("--emit-size", type=int, default=100)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.emit_case:
        print(source(args.emit_case, args.emit_size, args.query_repeats), end="")
        return 0
    if args.runs < 1 or args.query_repeats < 1:
        raise SystemExit("--runs and --query-repeats must be positive")
    if any(size < 1 for size in args.sizes):
        raise SystemExit("--sizes must be positive")
    engine = args.engine.resolve()
    if not engine.is_file():
        raise SystemExit(f"engine not found: {engine}")

    lines = ["\t".join(HEADER)]
    with tempfile.TemporaryDirectory(prefix="perf-a0-", dir=ROOT / "diffbench") as tmp:
        work = Path(tmp)
        for case in args.cases:
            for size in args.sizes:
                row = measure(
                    engine, case, size, args.query_repeats, args.runs,
                    args.fuel, args.timeout, work,
                )
                line = "\t".join(row)
                lines.append(line)
                print(line, flush=True)

    output = "\n".join(lines) + "\n"
    if args.output:
        args.output.write_text(output, encoding="utf-8")
    else:
        print("\n" + lines[0])
    return 0 if all(line.endswith("\tOK") for line in lines[1:]) else 1


if __name__ == "__main__":
    raise SystemExit(main())
