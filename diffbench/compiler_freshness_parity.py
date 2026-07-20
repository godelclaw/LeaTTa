#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0

"""Pinned differential gate for compiler-generated variable freshness."""

from __future__ import annotations

import os
from pathlib import Path

import diff


ROOT = Path(__file__).resolve().parent.parent
PROBE = ROOT / "diffbench" / "probes" / "generated-name-collision.metta"


def main() -> None:
    os.environ["PLEATTA_PINNED_ALLOW_EXTERNAL"] = "1"
    native = diff.petta_results(PROBE, timeout=30)
    executable = diff.leatta_results(PROBE, timeout=30)
    if executable is None:
        raise SystemExit("compiler freshness parity: malformed PLeaTTa output")

    normalized_native = [diff.normalize(value) for value in native]
    normalized_executable = [diff.normalize(value) for value in executable]
    expected = ["2", "2", "2"]
    if normalized_native != expected:
        raise SystemExit(
            "compiler freshness parity: pinned PeTTa changed: "
            f"{normalized_native!r}"
        )
    if normalized_executable != normalized_native:
        raise SystemExit(
            "compiler freshness parity: divergence: "
            f"PeTTa={normalized_native!r} PLeaTTa={normalized_executable!r}"
        )
    print(
        "compiler freshness parity: PASS; legal source _qN variables remain "
        "distinct from compiler-generated logic variables"
    )


if __name__ == "__main__":
    main()
