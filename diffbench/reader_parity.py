#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Differential regression gate for PeTTa's runtime ``sread`` contract.

The cases are synthetic and import-free. They deliberately cover both
accepted inputs and rejected inputs, including the byte patterns observed in
model-generated command batches. Native PeTTa is the pinned oracle; PLeaTTa
must return the same ordered values and the same caught syntax-error terms.
"""

from __future__ import annotations

import json
import os
import pathlib
import re
import tempfile

import diff as D


CASES = [
    ("simple", "((send ok))"),
    ("semicolon-unquoted", "((shell cat /a/b.metta 2>&1; echo END))"),
    ("semicolon-tight", "((shell a;b))"),
    ("semicolon-spaced", "((shell a ; b))"),
    ("multiple-forms", "((send ok)) ((rest))"),
    ("two-atoms", "foo bar"),
    ("trailing-material", "((send ok)) done."),
    ("bang-plus-form", "!(send ok)"),
    ("empty", ""),
    ("unexpected-close", ")"),
    ("leading-semicolon", ";comment"),
    ("ellipsis", "((cmd1 a) ... (cmd2 b))"),
    ("leading-dot", ".5"),
    ("trailing-dot", "1."),
    ("scientific", "1e2"),
    ("digit-separators", "1_2_3"),
    ("pipe", "((shell a | b))"),
]


def _fixture_source(source: str) -> str:
    return f"!(catch (sread {json.dumps(source, ensure_ascii=False)}))\n"


_VAR = re.compile(r"\$[A-Za-z0-9_#]+")


def _canonical(value: str) -> str:
    """Ignore layout and fresh variable names, but retain full error payloads."""
    seen: dict[str, str] = {}

    def rename(match: re.Match[str]) -> str:
        name = match.group(0)
        if name not in seen:
            seen[name] = f"$v{len(seen) + 1}"
        return seen[name]

    return _VAR.sub(rename, " ".join(value.split()))


def main() -> int:
    observations = []
    with tempfile.TemporaryDirectory(prefix="pleatta-reader-parity-") as td:
        fixture = pathlib.Path(td) / "reader-parity.metta"
        old_allow = os.environ.get("PLEATTA_PINNED_ALLOW_EXTERNAL")
        os.environ["PLEATTA_PINNED_ALLOW_EXTERNAL"] = "1"
        try:
            for name, source in CASES:
                fixture.write_text(_fixture_source(source), encoding="utf-8")
                native = D.petta_results(fixture, 60)
                pleatta = D.leatta_results(fixture, 60)
                observations.append((name, source, native, pleatta))
        finally:
            if old_allow is None:
                os.environ.pop("PLEATTA_PINNED_ALLOW_EXTERNAL", None)
            else:
                os.environ["PLEATTA_PINNED_ALLOW_EXTERNAL"] = old_allow

    failures = []
    for name, source, native, pleatta in observations:
        if pleatta is None or len(native) != 1 or len(pleatta) != 1:
            failures.append((name, source, repr(native), repr(pleatta)))
        elif _canonical(native[0]) != _canonical(pleatta[0]):
            failures.append((name, source, native[0], pleatta[0]))
    if failures:
        for name, source, expected, actual in failures:
            print(f"FAIL {name}: {source!r}")
            print(f"  PeTTa:   {expected}")
            print(f"  PLeaTTa: {actual}")
        return 1

    print(f"OK: {len(CASES)}/{len(CASES)} runtime-reader cases match pinned PeTTa")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
