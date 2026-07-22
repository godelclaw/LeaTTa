#!/usr/bin/env python3

"""Pinned compiler-rejection witnesses for source forms PLeaTTa must reject."""

from __future__ import annotations

import os
import pathlib
import subprocess
import sys
import tempfile

sys.path.insert(0, str(pathlib.Path(__file__).parent))
import diff as D  # noqa: E402


EXAMPLES = pathlib.Path(
    os.environ.get("PETTA_DIR", str(pathlib.Path.home() / "repos/PeTTa"))
) / "examples"

CASES = [
    ("let-star-empty", "!(let* () 42)\n"),
    ("let-star-malformed-entry", "!(let* (malformed) 42)\n"),
    ("let-star-malformed-tail", "!(let* (($x 1) malformed) $x)\n"),
]


def rejected(run, path: pathlib.Path) -> tuple[bool, int | None]:
    try:
        run(path, 15)
        return (False, None)
    except D.RunnerError as error:
        return (True, error.returncode)


def run_case(name: str, source: str) -> bool:
    with tempfile.NamedTemporaryFile(
        "w", suffix=".metta", prefix=".compiler-rejection-",
        dir=EXAMPLES, delete=False
    ) as handle:
        handle.write(source)
        path = pathlib.Path(handle.name)
    try:
        native_rejected, native_code = rejected(D.petta_results, path)
        pleatta_rejected, pleatta_code = rejected(D.leatta_results, path)
        ok = native_rejected and pleatta_rejected
        print(
            f"{name}\t{'PASS' if ok else 'FAIL'}\t"
            f"native={'rejected' if native_rejected else 'accepted'}:{native_code}\t"
            f"pleatta={'rejected' if pleatta_rejected else 'accepted'}:{pleatta_code}"
        )
        return ok
    except (D.FuelExhausted, subprocess.TimeoutExpired) as error:
        print(f"{name}\tFAIL\t{type(error).__name__}: {error}")
        return False
    finally:
        path.unlink(missing_ok=True)


def main() -> int:
    ok = True
    for case in CASES:
        ok &= run_case(*case)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
