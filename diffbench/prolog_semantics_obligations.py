#!/usr/bin/env python3
"""Fail closed when the audited Prolog-semantics ledger becomes stale."""

from __future__ import annotations

import csv
import hashlib
import sys
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "diffbench" / "prolog-semantics-obligations.tsv"
TRACE_SEMANTICS = ROOT / "PLeaTTa" / "PeTTaSpec" / "PrologTraceSemantics.lean"
TERM_ALGEBRA = ROOT / "PLeaTTa" / "PeTTaSpec" / "PrologTermAlgebra.lean"
PROLOG_FLOAT = ROOT / "PLeaTTa" / "PrologFloat.lean"
UNIFICATION_CORE = ROOT / "MettaHyperonFull" / "Core" / "Unification.lean"
ORDERED_MGU = ROOT / "PLeaTTa" / "PeTTaSpec" / "PrologMgu.lean"
LOCAL_RESOLVER = ROOT / "PLeaTTa" / "PeTTaSpec" / "PrologResolver.lean"
PROLOG_COPY = ROOT / "PLeaTTa" / "PeTTaSpec" / "PrologCopy.lean"
GOAL_SEMANTICS = ROOT / "PLeaTTa" / "PeTTaSpec" / "PrologGoalSemantics.lean"
DEMAND_DRIVEN_STEP = ROOT / "PLeaTTa" / "Proofs" / "DemandDrivenStep.lean"
DEMAND_DRIVEN_CALL_STEP = (
    ROOT / "PLeaTTa" / "Proofs" / "DemandDrivenCallStep.lean"
)
PROLOG_STATE_BRIDGE = ROOT / "PLeaTTa" / "Proofs" / "PrologStateBridge.lean"
PROLOG_CALL_ENTRY_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologCallEntryBridge.lean"
)
PROLOG_CALL_STEP_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologCallStepBridge.lean"
)
PROLOG_GOAL_ALPHA = ROOT / "PLeaTTa" / "Proofs" / "PrologGoalAlpha.lean"
PROLOG_ACTIVATION_MACRO = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologActivationMacro.lean"
)
PROLOG_ACTIVATION_BRIDGE = (
    ROOT / "PLeaTTa" / "Proofs" / "PrologActivationBridge.lean"
)
PINNED_PETTA_REVISION = "6b7f52f064bdbc82fabd0a0998404121fb01d52e"
FIELDS = ["id", "native_source", "layer", "reference", "proof", "status", "finding"]
LAYERS = {"trace", "control", "collection", "exception", "world", "boundary",
          "resolver", "projection", "composition", "instantiation"}
PROOFS = {"SC", "W", "SH", "N"}
STATUSES = {"PASS", "FAIL", "GAP", "BOUNDARY"}
REQUIRED_PREFIXES = {
    "TRACE.", "CONTROL.", "CUT.", "COLLECT.", "EXCEPTION.", "WORLD.",
    "CALL.", "RESOLVER.", "EXTERNAL.", "PROJECTION.", "BISIM.",
    "COMPOSE.", "PETTACLAW.",
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
        "trace_semantics_sha256": digest(TRACE_SEMANTICS),
        "term_algebra_sha256": digest(TERM_ALGEBRA),
        "prolog_float_sha256": digest(PROLOG_FLOAT),
        "unification_core_sha256": digest(UNIFICATION_CORE),
        "ordered_mgu_sha256": digest(ORDERED_MGU),
        "local_resolver_sha256": digest(LOCAL_RESOLVER),
        "prolog_copy_sha256": digest(PROLOG_COPY),
        "goal_semantics_sha256": digest(GOAL_SEMANTICS),
        "demand_driven_step_sha256": digest(DEMAND_DRIVEN_STEP),
        "demand_driven_call_step_sha256": digest(DEMAND_DRIVEN_CALL_STEP),
        "prolog_state_bridge_sha256": digest(PROLOG_STATE_BRIDGE),
        "prolog_call_entry_bridge_sha256": digest(PROLOG_CALL_ENTRY_BRIDGE),
        "prolog_call_step_bridge_sha256": digest(PROLOG_CALL_STEP_BRIDGE),
        "prolog_goal_alpha_sha256": digest(PROLOG_GOAL_ALPHA),
        "prolog_activation_macro_sha256": digest(PROLOG_ACTIVATION_MACRO),
        "prolog_activation_bridge_sha256": digest(PROLOG_ACTIVATION_BRIDGE),
    }
    for key, expected in expected_metadata.items():
        actual = metadata.get(key)
        if actual != expected:
            errors.append(f"{key}: ledger={actual!r}, expected={expected!r}")

    if len(rows) < 30:
        errors.append(f"ledger unexpectedly small: {len(rows)} rows")

    seen: set[str] = set()
    for line, row in enumerate(rows, start=2):
        row_id = row["id"]
        if not row_id:
            errors.append(f"row {line}: empty id")
        elif row_id in seen:
            errors.append(f"row {line}: duplicate id {row_id}")
        seen.add(row_id)

        if row["layer"] not in LAYERS:
            errors.append(f"{row_id}: invalid layer {row['layer']!r}")
        if row["proof"] not in PROOFS:
            errors.append(f"{row_id}: invalid proof {row['proof']!r}")
        if row["status"] not in STATUSES:
            errors.append(f"{row_id}: invalid status {row['status']!r}")
        if not row["finding"]:
            errors.append(f"{row_id}: empty finding")

        if row["status"] == "PASS":
            if row["proof"] == "N":
                errors.append(f"{row_id}: PASS requires a checked proof or witness")
            if row["reference"] == "-":
                errors.append(f"{row_id}: PASS requires an independent reference")

    missing = sorted(
        prefix for prefix in REQUIRED_PREFIXES
        if not any(row_id.startswith(prefix) for row_id in seen)
    )
    if missing:
        errors.append("missing obligation families: " + ", ".join(missing))

    required_rows = {
        "EXTERNAL.imported_swi": "BOUNDARY",
        "EXTERNAL.current_worker": "FAIL",
        "BISIM.machine_step": "GAP",
        "COMPOSE.source_observation": "GAP",
    }
    by_id = {row["id"]: row for row in rows}
    for row_id, expected in required_rows.items():
        actual = by_id.get(row_id, {}).get("status")
        if actual != expected:
            errors.append(f"{row_id}: status={actual!r}, expected={expected}")
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
    print(f"Prolog semantics: {len(rows)} rows; {summary}; trace hash current")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
