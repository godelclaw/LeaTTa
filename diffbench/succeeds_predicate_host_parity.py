#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Trusted-host parity for the library-defined succeedsPredicate hook.

The compiler and local-space cases remain inside the certified engine.  A
general Prolog predicate crosses the typed host boundary, so this gate compares
that execution with pinned PeTTa and then requires deterministic replay.  It is
evidence for the explicit host boundary, not certified-core coverage.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import signal
import subprocess
import tempfile

import diff
from host_grade import _parse_answers


ROOT = Path(__file__).resolve().parents[1]
PLEATTA = ROOT / ".lake" / "build" / "bin" / "pleatta"
FIXTURE = ROOT / "diffbench" / "host-fixtures" / \
    "succeeds-predicate-general.metta"
WORKER = ROOT / "scripts" / "pleatta-python-worker.py"
EXPECTED = [
    "true", "true", "false", "true", "false", "true", "false",
    "true", "false", "true", "true", "2", "3",
]


def run(command: list[Path | str], *, env: dict[str, str], timeout: int = 60):
    process = subprocess.Popen(
        [str(part) for part in command],
        cwd=ROOT,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True,
    )
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(os.getpgid(process.pid), signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.communicate()
        raise
    return subprocess.CompletedProcess(
        command, process.returncode, stdout, stderr)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> int:
    require(PLEATTA.is_file(), "build pleatta before running host parity")
    env = os.environ.copy()
    env["PLEATTA_PY_WORKER"] = str(WORKER)
    old_external = os.environ.get("PLEATTA_PINNED_ALLOW_EXTERNAL")
    os.environ["PLEATTA_PINNED_ALLOW_EXTERNAL"] = "1"
    try:
        native = diff.petta_results(FIXTURE, 60)
    finally:
        if old_external is None:
            os.environ.pop("PLEATTA_PINNED_ALLOW_EXTERNAL", None)
        else:
            os.environ["PLEATTA_PINNED_ALLOW_EXTERNAL"] = old_external
    native_normalized = [diff.normalize(answer) for answer in native]
    require(native_normalized == EXPECTED,
            f"pinned characterization drifted: {native_normalized!r}")

    with tempfile.TemporaryDirectory(
        prefix="pleatta-succeeds-predicate-"
    ) as raw:
        transcript = Path(raw) / "transcript.json"
        live = run([
            PLEATTA, "--host-live", FIXTURE, transcript, "4000000"
        ], env=env)
        require(live.returncode == 0, live.stderr.strip())
        answers = _parse_answers(live.stdout)
        normalized = ([diff.normalize(answer) for answer in answers]
                      if answers is not None else None)
        require(normalized == native_normalized,
                f"host-live mismatch: native={native!r} pleatta={answers!r}")

        exchanges = json.loads(transcript.read_text(encoding="utf-8"))
        prolog_calls = [
            exchange for exchange in exchanges
            if "prologCall" in exchange.get("request", {})
        ]
        require(prolog_calls, "general predicate never crossed the host boundary")

        replay = run([
            PLEATTA, "--host-replay", FIXTURE, transcript, "4000000"
        ], env=env)
        require(replay.returncode == 0, replay.stderr.strip())
        require(replay.stdout == live.stdout,
                "replay changed the ordered host-live observation")

    print(
        "succeeds-predicate-host-parity\tPASS\t"
        f"answers={len(native)}\tprolog-calls={len(prolog_calls)}\t"
        "replay=identical\ttier=trusted-host"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
