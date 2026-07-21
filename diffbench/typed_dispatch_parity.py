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
SURPLUS_PARAMETER_TYPE = (
    ROOT / "diffbench" / "probes" / "typed-surplus-parameter-type.metta"
)
MISSING_PARAMETER_TYPE = (
    ROOT / "diffbench" / "probes" / "typed-missing-parameter-type.metta"
)
VALID_PARAMETRIC_CHAIN = (
    ROOT / "diffbench" / "probes" / "typed-parametric-chain.metta"
)


def normalized(run, probe: Path) -> list[str]:
    values = run(probe, timeout=30)
    if values is None:
        raise SystemExit(f"typed dispatch parity: malformed output for {probe.name}")
    return [diff.normalize(value) for value in values]


def classified(run, probe: Path) -> tuple[str, list[str]]:
    try:
        return ("ok", normalized(run, probe))
    except diff.RunnerError:
        return ("error", [])


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

    native_surplus = normalized(diff.petta_results, SURPLUS_PARAMETER_TYPE)
    executable_surplus = normalized(
        diff.leatta_results, SURPLUS_PARAMETER_TYPE
    )
    if native_surplus != [] or executable_surplus != native_surplus:
        raise SystemExit(
            "typed dispatch parity: surplus parameter types do not retain "
            "the pinned cut-base behavior: "
            f"PeTTa={native_surplus!r} PLeaTTa={executable_surplus!r}"
        )

    native_missing = classified(diff.petta_results, MISSING_PARAMETER_TYPE)
    executable_missing = classified(
        diff.leatta_results, MISSING_PARAMETER_TYPE
    )
    if native_missing != ("error", []) or executable_missing != native_missing:
        raise SystemExit(
            "typed dispatch parity: a missing parameter type did not reject "
            "compilation on both engines: "
            f"PeTTa={native_missing!r} PLeaTTa={executable_missing!r}"
        )

    native_parametric = normalized(diff.petta_results, VALID_PARAMETRIC_CHAIN)
    executable_parametric = normalized(
        diff.leatta_results, VALID_PARAMETRIC_CHAIN
    )
    expected_parametric = ["(a b)", "t-parametric"]
    if native_parametric != expected_parametric:
        raise SystemExit(
            "typed dispatch parity: pinned parametric-chain behavior changed: "
            f"{native_parametric!r}"
        )
    if executable_parametric != native_parametric:
        raise SystemExit(
            "typed dispatch parity: sampled valid parametric chain changed "
            "behavior: "
            f"PeTTa={native_parametric!r} PLeaTTa={executable_parametric!r}"
        )
    print(
        "typed dispatch parity: PASS; duplicate signatures retain one "
        "first-occurrence branch, Expression results remain checked, and "
        "parameter-type exhaustion follows pinned asymmetry; the sampled "
        "valid parametric chain agrees, while rejection constraints remain "
        "a known compiler-ledger mismatch"
    )


if __name__ == "__main__":
    main()
