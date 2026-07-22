#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Execute known semantics mismatches against the pinned PeTTa oracle.

This is evidence, not a proof ledger.  Green means that each exact documented
divergence remains observable.  Agreement, output drift, a stale ledger row,
or a fixture that escapes the repository all fail the gate so a repaired
semantic obligation cannot remain mislabeled as FAIL.
"""

from __future__ import annotations

import os
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "diffbench" / "prolog-semantics-obligations.tsv"
MANIFEST = ROOT / "diffbench" / "prolog-semantics-mismatch-witnesses.tsv"

sys.path.insert(0, str(ROOT / "diffbench"))
import compiler_mismatch_witnesses as witnesses  # noqa: E402


def main() -> int:
    os.environ["PLEATTA_PINNED_ALLOW_EXTERNAL"] = "1"

    ledger_rows = witnesses.rows(LEDGER)
    manifest_rows = witnesses.rows(MANIFEST)
    ledger_by_id = {row["id"]: row for row in ledger_rows}

    manifest_cases = [row["case"] for row in manifest_rows]
    duplicates = sorted({
        case for case in manifest_cases if manifest_cases.count(case) > 1
    })
    if duplicates:
        raise SystemExit(f"duplicate semantics-mismatch cases: {duplicates}")

    manifest_ids = [row["id"] for row in manifest_rows]
    unknown = sorted(set(manifest_ids) - set(ledger_by_id))
    wrong_status = sorted(
        row["id"] for row in manifest_rows
        if row["mode"] == "expected-divergence"
        and ledger_by_id.get(row["id"], {}).get("status") != "FAIL"
    )
    if unknown or wrong_status:
        raise SystemExit(
            "semantics mismatch manifest drift: "
            f"unknown={unknown} non_FAIL={wrong_status}")

    ledger_revision = witnesses.metadata(LEDGER).get("pinned_petta_revision")
    manifest_revision = witnesses.metadata(MANIFEST).get(
        "pinned_petta_revision")
    if not ledger_revision or manifest_revision != ledger_revision:
        raise SystemExit(
            "semantics mismatch manifest and ledger pin different PeTTa "
            "revisions")

    ok = True
    for row in manifest_rows:
        if row["mode"] not in {"expected-divergence", "characterization"}:
            raise SystemExit(
                f"unknown mode for {row['case']}: {row['mode']}")
        relative = row["fixture"]
        fixture = (ROOT / relative).resolve()
        try:
            fixture.relative_to(ROOT)
        except ValueError:
            raise SystemExit(f"fixture escapes repository: {relative}")
        if not fixture.is_file():
            raise SystemExit(f"missing semantics mismatch fixture: {relative}")
        if "SPDX-License-Identifier" not in "\n".join(
            fixture.read_text(encoding="utf-8").splitlines()[:3]
        ):
            raise SystemExit(f"fixture lacks SPDX header: {relative}")

        native = witnesses.run(witnesses.diff.petta_results, fixture)
        pleatta = witnesses.run(witnesses.diff.leatta_results, fixture)
        native_expected = witnesses.expected(
            row["native_kind"], row["native_expect"])
        pleatta_expected = witnesses.expected(
            row["pleatta_kind"], row["pleatta_expect"])
        case_ok = (
            native == native_expected
            and pleatta == pleatta_expected
        )
        if row["mode"] == "expected-divergence":
            case_ok &= native != pleatta
        else:
            case_ok &= native == pleatta
        ok &= case_ok
        print(
            f"{row['case']}\t{row['id']}\t"
            f"{'PASS' if case_ok else 'FAIL'}\t{row['mode']}\t"
            f"native={native.render()}\tpleatta={pleatta.render()}"
        )

    divergences = sum(
        row["mode"] == "expected-divergence" for row in manifest_rows)
    characterizations = len(manifest_rows) - divergences
    print(
        "prolog-semantics-mismatch-witnesses: "
        f"{'PASS' if ok else 'FAIL'}; {divergences} exact divergences, "
        f"{characterizations} characterization guards"
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
