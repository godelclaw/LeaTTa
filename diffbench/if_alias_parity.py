#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0

"""Pinned differential gate for `build_branch/4` variable aliasing."""

from __future__ import annotations

import os
from pathlib import Path

import diff


ROOT = Path(__file__).resolve().parent.parent
PROBE = ROOT / "diffbench" / "probes" / "if-cross-branch-alias.metta"


def main() -> None:
    os.environ["PLEATTA_PINNED_ALLOW_EXTERNAL"] = "1"
    native = diff.petta_results(PROBE, timeout=30)
    executable = diff.leatta_results(PROBE, timeout=30)
    if executable is None:
        raise SystemExit("if alias parity: malformed PLeaTTa output")

    normalized_native = [diff.normalize(value) for value in native]
    normalized_executable = [diff.normalize(value) for value in executable]
    expected = ["(7 7)", "(7 7)", "true", "true", "true"]
    if normalized_native != expected:
        raise SystemExit(
            f"if alias parity: pinned PeTTa changed: {normalized_native!r}"
        )
    if normalized_executable != normalized_native:
        raise SystemExit(
            "if alias parity: divergence: "
            f"PeTTa={normalized_native!r} PLeaTTa={normalized_executable!r}"
        )
    print(
        "if alias parity: PASS; two-/three-argument branches preserve "
        "cross-branch and surrounding variable aliases"
    )


if __name__ == "__main__":
    main()
