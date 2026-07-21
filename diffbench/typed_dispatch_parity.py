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
PARAMETRIC_REJECTION = (
    ROOT / "diffbench" / "probes" / "typed-parametric-rejection.metta"
)
PARAMETRIC_PARTIAL = (
    ROOT / "diffbench" / "probes" / "typed-parametric-partial.metta"
)
PARAMETRIC_OVERLOADS = (
    ROOT / "diffbench" / "probes" / "typed-parametric-overloads.metta"
)
IDENTICAL_PARAMETRIC_OVERLOADS = (
    ROOT
    / "diffbench"
    / "probes"
    / "typed-identical-parametric-signatures.metta"
)
INCOMPLETE_SHARED_RESULT = (
    ROOT / "diffbench" / "probes" / "typed-incomplete-shared-result.metta"
)
INCOMPATIBLE_SHARED_RESULTS = (
    ROOT
    / "diffbench"
    / "probes"
    / "typed-incomplete-shared-result-conflict.metta"
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

    native_rejection = normalized(diff.petta_results, PARAMETRIC_REJECTION)
    executable_rejection = normalized(
        diff.leatta_results, PARAMETRIC_REJECTION
    )
    if native_rejection != [] or executable_rejection != native_rejection:
        raise SystemExit(
            "typed dispatch parity: a shared parameter/result type variable "
            "did not reject an inconsistent result: "
            f"PeTTa={native_rejection!r} PLeaTTa={executable_rejection!r}"
        )

    native_partial = normalized(diff.petta_results, PARAMETRIC_PARTIAL)
    executable_partial = normalized(diff.leatta_results, PARAMETRIC_PARTIAL)
    expected_partial = ["(partial typed-parametric-partial (5))"]
    if native_partial != expected_partial or executable_partial != native_partial:
        raise SystemExit(
            "typed dispatch parity: parametric partial-call construction "
            "changed: "
            f"PeTTa={native_partial!r} PLeaTTa={executable_partial!r}"
        )

    native_overloads = normalized(diff.petta_results, PARAMETRIC_OVERLOADS)
    executable_overloads = normalized(
        diff.leatta_results, PARAMETRIC_OVERLOADS
    )
    expected_overloads = ["5", "5"]
    if (
        native_overloads != expected_overloads
        or executable_overloads != native_overloads
    ):
        raise SystemExit(
            "typed dispatch parity: branch-local parametric overload order "
            "or multiplicity changed: "
            f"PeTTa={native_overloads!r} PLeaTTa={executable_overloads!r}"
        )

    native_identical_parametric = normalized(
        diff.petta_results, IDENTICAL_PARAMETRIC_OVERLOADS
    )
    executable_identical_parametric = normalized(
        diff.leatta_results, IDENTICAL_PARAMETRIC_OVERLOADS
    )
    if (
        native_identical_parametric != expected_overloads
        or executable_identical_parametric != native_identical_parametric
    ):
        raise SystemExit(
            "typed dispatch parity: declaration-local variables were "
            "collapsed by source spelling: "
            f"PeTTa={native_identical_parametric!r} "
            f"PLeaTTa={executable_identical_parametric!r}"
        )

    native_shared_result = normalized(diff.petta_results, INCOMPLETE_SHARED_RESULT)
    executable_shared_result = normalized(
        diff.leatta_results, INCOMPLETE_SHARED_RESULT
    )
    expected_shared_result = [
        "(partial typed-incomplete-shared-result ((+ 1 2)))"
    ]
    if native_shared_result != expected_shared_result:
        raise SystemExit(
            "typed dispatch parity: pinned shared-result binding changed: "
            f"{native_shared_result!r}"
        )
    if executable_shared_result != native_shared_result:
        raise SystemExit(
            "typed dispatch parity: incomplete overload branches did not "
            "share one result binding: "
            f"PeTTa={native_shared_result!r} "
            f"PLeaTTa={executable_shared_result!r}"
        )

    native_conflict = classified(diff.petta_results, INCOMPATIBLE_SHARED_RESULTS)
    executable_conflict = classified(
        diff.leatta_results, INCOMPATIBLE_SHARED_RESULTS
    )
    if native_conflict != ("error", []) or executable_conflict != native_conflict:
        raise SystemExit(
            "typed dispatch parity: incompatible shared partial results did "
            "not reject translation on both engines: "
            f"PeTTa={native_conflict!r} PLeaTTa={executable_conflict!r}"
        )
    print(
        "typed dispatch parity: PASS; duplicate signatures retain one "
        "first-occurrence branch, Expression results remain checked, and "
        "parameter-type exhaustion follows pinned asymmetry; parametric "
        "input/result sharing, rejection, partial calls, declaration-local "
        "freshness, overload order/multiplicity, and incomplete-overload "
        "shared-result binding agree"
    )


if __name__ == "__main__":
    main()
