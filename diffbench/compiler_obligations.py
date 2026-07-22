#!/usr/bin/env python3
"""Fail closed when the audited compiler-obligation ledger becomes stale."""

from __future__ import annotations

import csv
import hashlib
import sys
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "diffbench" / "compiler-obligations.tsv"
COMPILER = ROOT / "PLeaTTa" / "Compile.lean"
PINNED_PETTA_REVISION = "6b7f52f064bdbc82fabd0a0998404121fb01d52e"
FIELDS = ["id", "native_source", "class", "reference", "proof", "status", "finding"]
CLASSES = {"X", "S", "L", "H", "P", "M"}
PROOFS = {"SC", "BC", "SH", "EQ", "N"}
STATUSES = {"PASS", "FAIL", "GAP", "BOUNDARY"}
REQUIRED_PREFIXES = {
    "EX.",
    "PAT.",
    "HOOK.",
    "CASE.",
    "ARGS.",
    "LIST.",
    "PATLIST.",
    "APP.",
    "FALLBACK.",
    "RULE.",
    "DESUGAR.",
    "PROGRAM.",
    "SEQ.",
    "MISS.",
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_ledger() -> tuple[dict[str, str], list[dict[str, str]]]:
    metadata: dict[str, str] = {}
    table: list[str] = []
    for raw in LEDGER.read_text(encoding="utf-8").splitlines():
        if raw.startswith("#"):
            body = raw[1:].strip()
            if "=" in body:
                key, value = body.split("=", 1)
                metadata[key.strip()] = value.strip()
        elif raw.strip():
            table.append(raw)
    if not table:
        raise ValueError("ledger has no table")
    reader = csv.DictReader(table, delimiter="\t")
    if reader.fieldnames != FIELDS:
        raise ValueError(f"unexpected columns: {reader.fieldnames!r}")
    return metadata, list(reader)


def check() -> list[str]:
    errors: list[str] = []
    try:
        metadata, rows = load_ledger()
    except (OSError, ValueError) as exc:
        return [str(exc)]

    expected_metadata = {
        "pinned_petta_revision": PINNED_PETTA_REVISION,
        "compiler_sha256": digest(COMPILER),
    }
    for key, expected in expected_metadata.items():
        actual = metadata.get(key)
        if actual != expected:
            errors.append(f"{key}: ledger={actual!r}, expected={expected!r}")

    if len(rows) < 140:
        errors.append(f"ledger unexpectedly small: {len(rows)} rows")

    seen: set[str] = set()
    for line, row in enumerate(rows, start=2):
        row_id = row["id"]
        if not row_id:
            errors.append(f"row {line}: empty id")
        elif row_id in seen:
            errors.append(f"row {line}: duplicate id {row_id}")
        seen.add(row_id)

        if row["class"] not in CLASSES:
            errors.append(f"{row_id}: invalid class {row['class']!r}")
        if row["proof"] not in PROOFS:
            errors.append(f"{row_id}: invalid proof {row['proof']!r}")
        if row["status"] not in STATUSES:
            errors.append(f"{row_id}: invalid status {row['status']!r}")
        if not row["finding"]:
            errors.append(f"{row_id}: empty finding")

        if row["status"] == "PASS":
            if row["proof"] not in {"SC", "BC"}:
                errors.append(f"{row_id}: PASS requires SC or BC, not {row['proof']}")
            if row["native_source"] == "-" or row["reference"] == "-":
                errors.append(f"{row_id}: PASS requires source and independent reference")

    present_prefixes = {prefix for prefix in REQUIRED_PREFIXES if any(i.startswith(prefix) for i in seen)}
    missing_prefixes = sorted(REQUIRED_PREFIXES - present_prefixes)
    if missing_prefixes:
        errors.append("missing branch families: " + ", ".join(missing_prefixes))
    return errors


def main() -> int:
    errors = check()
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1

    _, rows = load_ledger()
    counts = Counter(row["status"] for row in rows)
    summary = " ".join(f"{status}={counts[status]}" for status in sorted(STATUSES))
    print(f"compiler obligations: {len(rows)} rows; {summary}; compiler hash current")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
