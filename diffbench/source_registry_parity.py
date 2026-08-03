#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0

"""Pinned differential gate for source function registration and arity."""

from __future__ import annotations

import os
from pathlib import Path

import diff


ROOT = Path(__file__).resolve().parent.parent
PROBE = ROOT / "diffbench" / "probes" / "source-registry-multi-arity.metta"


def main() -> None:
    os.environ["PLEATTA_PINNED_ALLOW_EXTERNAL"] = "1"
    native = diff.petta_results(PROBE, timeout=30)
    executable = diff.leatta_results(PROBE, timeout=30)
    if executable is None:
        raise SystemExit("source registry parity: malformed PLeaTTa output")

    normalized_native = [diff.normalize(value) for value in native]
    normalized_executable = [diff.normalize(value) for value in executable]
    expected = [
        "7",
        "8",
        "(partial source-registry-probe ())",
        "true",
        "8",
        "true",
        "(source-registry-probe 7)",
    ]
    if normalized_native != expected:
        raise SystemExit(
            "source registry parity: pinned PeTTa changed: "
            f"{normalized_native!r}"
        )
    if normalized_executable != normalized_native:
        raise SystemExit(
            "source registry parity: divergence: "
            f"PeTTa={normalized_native!r} PLeaTTa={normalized_executable!r}"
        )
    print(
        "source registry parity: PASS; duplicate heads, two arities, "
        "incomplete partial construction, and last-clause unregistration "
        "agree"
    )


if __name__ == "__main__":
    main()
