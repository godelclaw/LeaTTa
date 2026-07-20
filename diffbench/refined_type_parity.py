#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0

"""Pinned differential gate for builtin and user-defined refined types."""

from __future__ import annotations

import os
from pathlib import Path

import diff


ROOT = Path(__file__).resolve().parent.parent
PROBE = ROOT / "diffbench" / "probes" / "refined-input-check.metta"


def main() -> None:
    os.environ["PLEATTA_PINNED_ALLOW_EXTERNAL"] = "1"
    native = diff.petta_results(PROBE, timeout=60)
    executable = diff.leatta_results(PROBE, timeout=60)
    if executable is None:
        raise SystemExit("refined type parity: malformed PLeaTTa output")

    normalized_native = [diff.normalize(value) for value in native]
    normalized_executable = [diff.normalize(value) for value in executable]
    expected = ["5", "6"]
    if normalized_native != expected:
        raise SystemExit(
            f"refined type parity: pinned PeTTa changed: {normalized_native!r}"
        )
    if normalized_executable != normalized_native:
        raise SystemExit(
            "refined type parity: divergence: "
            f"PeTTa={normalized_native!r} PLeaTTa={normalized_executable!r}"
        )
    print(
        "refined type parity: PASS; builtin/custom well-typed accepted, "
        "wrong types rejected"
    )


if __name__ == "__main__":
    main()
