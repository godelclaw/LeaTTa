#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0

"""Reproducible microbenchmarks for PLeaTTa large-term handling.

The case families separate source construction from runtime construction and
ground atoms from variable-bearing atoms.  Results are tab-separated so that
before/after runs can be compared without parsing human-oriented output.
"""

from __future__ import annotations

import argparse
import statistics
import subprocess
import tempfile
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_ENGINE = ROOT / ".lake" / "build" / "bin" / "pleatta"
CASES = ("literal-ground", "literal-bare", "literal-var", "literal-deep", "runtime")


def sentence(i: int, variable: bool = False) -> str:
    subject = f"$v{i}" if variable else f"c{i}"
    return f"(Sentence ((--> {subject} ([] p{i})) (stv 0.{i % 9 + 1} 0.9)) ({i}))"


def source(case: str, size: int) -> str:
    if case in {"literal-ground", "literal-bare", "literal-var"}:
        variable = case == "literal-var"
        value = "(" + " ".join(sentence(i, variable) for i in range(size)) + ")"
        if case == "literal-bare":
            return f"!{value}\n"
        return f"!(car-atom {value})\n"
    if case == "literal-deep":
        value = "leaf"
        for i in range(size):
            value = f"(node{i} {value})"
        return f"!(car-atom ({value}))\n"
    if case == "runtime":
        return (
            "(= (mk $n)\n"
            "   (if (== $n 0)\n"
            "       ()\n"
            "       (cons-atom (S $n) (mk (- $n 1)))))\n"
            f"!(size-atom (mk {size}))\n"
        )
    raise ValueError(f"unknown case: {case}")


def run_once(engine: Path, program: Path, fuel: int, timeout: float) -> tuple[float, str]:
    started = time.perf_counter()
    proc = subprocess.run(
        [str(engine), "--file", str(program), str(fuel)],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
        check=False,
    )
    elapsed = time.perf_counter() - started
    if proc.returncode != 0:
        detail = proc.stderr.strip() or proc.stdout.strip()
        raise RuntimeError(f"exit {proc.returncode} for {program.name}: {detail}")
    return elapsed, proc.stdout.strip()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--engine", type=Path, default=DEFAULT_ENGINE)
    parser.add_argument("--cases", nargs="+", choices=CASES, default=list(CASES))
    parser.add_argument("--sizes", nargs="+", type=int, default=[25, 50, 100, 150])
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--fuel", type=int, default=300_000_000)
    parser.add_argument("--timeout", type=float, default=90.0)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    engine = args.engine.resolve()
    if not engine.is_file():
        raise SystemExit(f"engine not found: {engine}")
    if args.repeats < 1:
        raise SystemExit("--repeats must be positive")
    if any(size < 1 for size in args.sizes):
        raise SystemExit("--sizes must be positive")

    print("case\tsize\truns\tmedian_s\tmin_s\tmax_s\tresult")
    with tempfile.TemporaryDirectory(prefix="large-term-bench-", dir=ROOT / "diffbench") as tmp:
        work = Path(tmp)
        for case in args.cases:
            for size in args.sizes:
                program = work / f"{case}-{size}.metta"
                program.write_text(source(case, size), encoding="utf-8")
                timings: list[float] = []
                result = ""
                try:
                    for _ in range(args.repeats):
                        elapsed, result = run_once(engine, program, args.fuel, args.timeout)
                        timings.append(elapsed)
                except subprocess.TimeoutExpired:
                    print(f"{case}\t{size}\t{len(timings)}\tTIMEOUT\t-\t-\t-")
                    continue
                result_summary = result if len(result) <= 80 else f"{result[:77]}..."
                print(
                    f"{case}\t{size}\t{len(timings)}\t{statistics.median(timings):.6f}"
                    f"\t{min(timings):.6f}\t{max(timings):.6f}\t{result_summary}"
                )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
