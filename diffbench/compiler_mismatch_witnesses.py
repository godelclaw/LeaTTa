#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Execute every known compiler mismatch against pinned PeTTa.

This is an evidence gate, not a proof ledger.  A green expected-divergence row
means the documented difference is still observable exactly as recorded.  If
the engines start agreeing, the gate fails so the corresponding ledger row can
be reviewed and promoted rather than silently leaving a stale mismatch behind.

Values pass through the corpus agreement normalizer before comparison.  A
difference erased there therefore makes this gate fail closed (the engines
appear equal); it cannot manufacture a green expected divergence.  Error
classes avoid recording host-local payloads, but selected native classes are
recognized from diagnostic text, so diagnostic drift also turns the gate red.
"""

from __future__ import annotations

import csv
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "diffbench" / "compiler-obligations.tsv"
MANIFEST = ROOT / "diffbench" / "compiler-mismatch-witnesses.tsv"
COMPILER = ROOT / "PLeaTTa" / "Compile.lean"

sys.path.insert(0, str(ROOT / "diffbench"))
import diff  # noqa: E402


@dataclass(frozen=True)
class Outcome:
    kind: str
    payload: tuple[str, ...] | str

    def render(self) -> str:
        if self.kind == "ok":
            return json.dumps(list(self.payload), separators=(",", ":"))
        return f"error:{self.payload}"


def metadata(path: Path) -> dict[str, str]:
    values: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.startswith("#"):
            break
        body = line[1:].strip()
        if "=" in body:
            key, value = body.split("=", 1)
            values[key.strip()] = value.strip()
    return values


def rows(path: Path) -> list[dict[str, str]]:
    content = (
        line for line in path.read_text(encoding="utf-8").splitlines()
        if line and not line.startswith("#")
    )
    return list(csv.DictReader(content, delimiter="\t"))


def stable_value(value: str) -> str:
    normalized = diff.normalize(value)
    return re.sub(r"#lam[0-9]+", "#lamN", normalized)


def classify_runner_error(error: diff.RunnerError) -> str:
    diagnostic = (error.stdout or "") + "\n" + (error.stderr or "")
    if "superpose: empty" in diagnostic or (
        "failed to process form" in diagnostic and
        "[superpose,[]]" in diagnostic
    ):
        return "empty_superpose_rejected"
    if "clpfd_expression" in diagnostic:
        return "clpfd_expression"
    if "size-atom vs non-literal" in diagnostic:
        return "size_nonliteral"
    if "=../2: Type error" in diagnostic and "atom" in diagnostic:
        return "raw_space_type_error"
    return f"runner_error_{error.returncode}"


def run(runner, fixture: Path) -> Outcome:
    try:
        result = runner(fixture, timeout=30)
        if result is None:
            return Outcome("error", "malformed_output")
        return Outcome("ok", tuple(stable_value(value) for value in result))
    except diff.RunnerError as error:
        return Outcome("error", classify_runner_error(error))
    except diff.FuelExhausted:
        return Outcome("error", "fuel_exhausted")
    except subprocess.TimeoutExpired:
        return Outcome("error", "timeout")


def expected(kind: str, raw: str) -> Outcome:
    if kind == "ok":
        value = json.loads(raw)
        if not isinstance(value, list) or not all(
            isinstance(item, str) for item in value
        ):
            raise ValueError(f"ordered result must be a JSON string list: {raw}")
        return Outcome("ok", tuple(value))
    if kind == "error":
        return Outcome("error", raw)
    raise ValueError(f"unknown outcome kind: {kind}")


def main() -> int:
    os.environ["PLEATTA_PINNED_ALLOW_EXTERNAL"] = "1"

    ledger_rows = rows(LEDGER)
    manifest_rows = rows(MANIFEST)
    ledger_by_id = {row["id"]: row for row in ledger_rows}
    fail_ids = {
        row_id for row_id, row in ledger_by_id.items()
        if row.get("status") == "FAIL"
    }
    manifest_ids = [row["id"] for row in manifest_rows]
    duplicates = sorted({item for item in manifest_ids
                         if manifest_ids.count(item) > 1})
    if duplicates:
        raise SystemExit(f"duplicate mismatch IDs: {duplicates}")
    missing = sorted(fail_ids - set(manifest_ids))
    unknown = sorted(set(manifest_ids) - set(ledger_by_id))
    if missing or unknown:
        raise SystemExit(
            f"mismatch manifest drift: missing={missing} unknown={unknown}")

    ledger_revision = metadata(LEDGER).get("pinned_petta_revision")
    manifest_revision = metadata(MANIFEST).get("pinned_petta_revision")
    if not ledger_revision or manifest_revision != ledger_revision:
        raise SystemExit(
            "mismatch manifest and compiler ledger pin different PeTTa revisions")
    ledger_compiler_hash = metadata(LEDGER).get("compiler_sha256")
    compiler_hash = hashlib.sha256(COMPILER.read_bytes()).hexdigest()
    if not ledger_compiler_hash or ledger_compiler_hash != compiler_hash:
        raise SystemExit(
            "compiler mismatch witnesses refuse a stale obligation ledger")

    grouped: dict[str, list[dict[str, str]]] = {}
    for row in manifest_rows:
        if row["mode"] not in {"expected-divergence", "characterization"}:
            raise SystemExit(f"unknown mode for {row['id']}: {row['mode']}")
        ledger_status = ledger_by_id[row["id"]]["status"]
        if row["mode"] == "expected-divergence" and ledger_status != "FAIL":
            raise SystemExit(
                f"expected divergence {row['id']} requires ledger FAIL, "
                f"not {ledger_status}")
        grouped.setdefault(row["fixture"], []).append(row)

    observed: dict[str, tuple[Outcome, Outcome]] = {}
    ok = True
    for relative in sorted(grouped):
        fixture = (ROOT / relative).resolve()
        try:
            fixture.relative_to(ROOT)
        except ValueError:
            raise SystemExit(f"fixture escapes repository: {relative}")
        if not fixture.is_file():
            raise SystemExit(f"missing mismatch fixture: {relative}")
        if "SPDX-License-Identifier" not in "\n".join(
            fixture.read_text(encoding="utf-8").splitlines()[:3]
        ):
            raise SystemExit(f"fixture lacks SPDX header: {relative}")

        native = run(diff.petta_results, fixture)
        pleatta = run(diff.leatta_results, fixture)
        observed[relative] = (native, pleatta)
        case_ok = True
        modes = set()
        ids = []
        for row in grouped[relative]:
            ids.append(row["id"])
            modes.add(row["mode"])
            native_expected = expected(
                row["native_kind"], row["native_expect"])
            pleatta_expected = expected(
                row["pleatta_kind"], row["pleatta_expect"])
            case_ok &= native == native_expected
            case_ok &= pleatta == pleatta_expected
            if row["mode"] == "expected-divergence":
                case_ok &= native != pleatta
            else:
                case_ok &= native == pleatta
        if len(modes) != 1:
            case_ok = False
        ok &= case_ok
        mode = next(iter(modes)) if len(modes) == 1 else "mixed-invalid"
        print(
            f"{','.join(ids)}\t{'PASS' if case_ok else 'FAIL'}\t{mode}\t"
            f"native={native.render()}\tpleatta={pleatta.render()}"
        )

    divergence_rows = sum(
        row["mode"] == "expected-divergence" for row in manifest_rows)
    characterization_rows = len(manifest_rows) - divergence_rows
    characterization_label = (
        "characterization row" if characterization_rows == 1
        else "characterization rows"
    )
    print(
        "compiler-mismatch-witnesses: "
        f"{'PASS' if ok else 'FAIL'}; "
        f"{divergence_rows} expected-divergence rows, "
        f"{characterization_rows} {characterization_label}, "
        f"{len(observed)} unique fixtures"
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
