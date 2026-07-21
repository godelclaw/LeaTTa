#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0

"""Pinned differential gate for typed-dispatch order and multiplicity."""

from __future__ import annotations

import os
from pathlib import Path

import diff


ROOT = Path(__file__).resolve().parent.parent
DUPLICATE_SIGNATURE = (
    ROOT / "diffbench" / "probes" / "typed-duplicate-signature.metta"
)
EXPRESSION_RESULT = (
    ROOT / "diffbench" / "probes" / "typed-expression-result.metta"
)


def normalized(run, probe: Path) -> list[str]:
    values = run(probe, timeout=30)
    if values is None:
        raise SystemExit(f"typed dispatch parity: malformed output for {probe.name}")
    return [diff.normalize(value) for value in values]


def main() -> None:
    os.environ["PLEATTA_PINNED_ALLOW_EXTERNAL"] = "1"
    native = normalized(diff.petta_results, DUPLICATE_SIGNATURE)
    executable = normalized(diff.leatta_results, DUPLICATE_SIGNATURE)
    expected = ["5"]
    if native != expected:
        raise SystemExit(
            f"typed dispatch parity: pinned PeTTa changed: {native!r}"
        )
    if executable != native:
        raise SystemExit(
            "typed dispatch parity: duplicate signature changed answer "
            f"multiplicity: PeTTa={native!r} PLeaTTa={executable!r}"
        )

    native_expression = normalized(diff.petta_results, EXPRESSION_RESULT)
    executable_expression = normalized(diff.leatta_results, EXPRESSION_RESULT)
    if native_expression != []:
        raise SystemExit(
            "typed dispatch parity: pinned PeTTa Expression-result behavior "
            f"changed: {native_expression!r}"
        )
    if executable_expression != native_expression:
        raise SystemExit(
            "typed dispatch parity: Expression result was not checked: "
            f"PeTTa={native_expression!r} "
            f"PLeaTTa={executable_expression!r}"
        )
    print(
        "typed dispatch parity: PASS; duplicate signatures retain one "
        "first-occurrence branch and Expression results remain checked"
    )


if __name__ == "__main__":
    main()
