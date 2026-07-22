#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Regression gate for PLeaTTa's opt-in SWI-Prolog policies."""

from __future__ import annotations

import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
WORKER_PATH = ROOT / "scripts" / "pleatta-prolog-worker.py"


def load_worker():
    # The policy probes use SWI builtins and do not need PeTTa's library.
    os.environ["PLEATTA_PROLOG_LIB"] = "__pleatta_no_library__"
    spec = importlib.util.spec_from_file_location(
        "pleatta_prolog_worker_policy_test", WORKER_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load Prolog worker")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def between_request():
    return {
        "goal": "between",
        "args": [{"int": 1}, {"int": 3}, {"var": "X"}],
        "vars": ["X"],
    }


def runtime_roundtrip() -> None:
    binary = ROOT / ".lake" / "build" / "bin" / "pleatta"
    fixture = ROOT / "diffbench" / "host-fixtures" / \
        "prolog-open-default.metta"
    if not binary.is_file():
        raise RuntimeError("build pleatta before running the policy gate")
    env = os.environ.copy()
    env.update({
        "PLEATTA_PYTHON": sys.executable,
        "PLEATTA_PY_WORKER": str(
            ROOT / "scripts" / "pleatta-python-worker.py"),
        "PLEATTA_PROLOG_LIB": "__pleatta_no_library__",
    })
    for name in (
        "PLEATTA_PROLOG_DENY",
        "PLEATTA_PROLOG_INFERENCE_LIMIT",
        "PLEATTA_PROLOG_TIMEOUT_SECONDS",
    ):
        env.pop(name, None)
    with tempfile.TemporaryDirectory(prefix="pleatta-prolog-policy-") as raw:
        transcript = Path(raw) / "transcript.json"
        live = subprocess.run(
            [str(binary), "--host-live", str(fixture), str(transcript),
             "4000000"],
            capture_output=True, text=True, env=env, timeout=15)
        assert live.returncode == 0, live.stderr
        assert live.stdout.strip() == "[1, 2, 3]", live.stdout

        replay = subprocess.run(
            [str(binary), "--host-replay", str(fixture), str(transcript),
             "4000000"],
            capture_output=True, text=True, env=env, timeout=15)
        assert replay.returncode == 0, replay.stderr
        assert replay.stdout == live.stdout, (live.stdout, replay.stdout)

        provenance = subprocess.run(
            [str(binary), "--host-provenance", str(transcript)],
            capture_output=True, text=True, timeout=15)
        assert provenance.returncode == 0, provenance.stderr
        assert "host requests: 1" in provenance.stdout, provenance.stdout
        assert "native-shadowed: 0" in provenance.stdout, provenance.stdout
        assert "1  trusted-prolog between/3" in provenance.stdout, \
            provenance.stdout

        rows = json.loads(transcript.read_text(encoding="utf-8"))
        answers = rows[0]["response"]["prologReturned"]["answers"]
        assert [answer[0]["value"]["int"]["value"]
                for answer in answers] == [1, 2, 3], answers


def main() -> int:
    worker = load_worker()
    saved = {
        name: os.environ.get(name)
        for name in (
            "PLEATTA_PROLOG_ALLOWLIST",
            "PLEATTA_PROLOG_DENY",
            "PLEATTA_PROLOG_INFERENCE_LIMIT",
            "PLEATTA_PROLOG_TIMEOUT_SECONDS",
        )
    }
    try:
        for name in saved:
            os.environ.pop(name, None)

        expected = [
            {"X": {"int": 1}},
            {"X": {"int": 2}},
            {"X": {"int": 3}},
        ]
        opened = worker.solve(between_request())
        assert opened == {"answers": expected}, opened

        # A legacy restrictive allowlist must have no effect: it is not a
        # verification boundary and no longer governs execution.
        os.environ["PLEATTA_PROLOG_ALLOWLIST"] = "atom_codes"
        still_open = worker.solve(between_request())
        assert still_open == {"answers": expected}, still_open

        os.environ["PLEATTA_PROLOG_DENY"] = "between/3"
        denied_exact = worker.solve(between_request())
        assert denied_exact == {"error": "predicate-denied:between/3"}, \
            denied_exact

        os.environ["PLEATTA_PROLOG_DENY"] = "between"
        denied_all_arities = worker.solve(between_request())
        assert denied_all_arities == {
            "error": "predicate-denied:between/3"
        }, denied_all_arities

        os.environ.pop("PLEATTA_PROLOG_DENY", None)
        limited = worker.solve({"goal": "repeat", "args": [], "limit": 1000})
        assert limited == {"error": "prolog-exception"}, limited

        os.environ["PLEATTA_PROLOG_DENY"] = "between"
        nested = worker.solve({
            "goal": "findall",
            "args": [
                {"var": "X"},
                {"compound": ["between", {"int": 1}, {"int": 2},
                              {"var": "X"}]},
                {"var": "Items"},
            ],
            "vars": ["Items"],
        })
        assert nested == {"answers": [{"Items": {
            "list": [{"int": 1}, {"int": 2}]
        }}]}, nested

        os.environ.pop("PLEATTA_PROLOG_DENY", None)
        observed_timeouts = []
        real_run = worker.subprocess.run

        class FakeProcess:
            returncode = 0
            stdout = "ANS:[]\n"

        def observe_timeout(*args, **kwargs):
            observed_timeouts.append(kwargs.get("timeout"))
            return FakeProcess()

        worker.subprocess.run = observe_timeout
        try:
            assert worker.solve({"goal": "true", "args": []}) == {
                "answers": [{}]
            }
        finally:
            worker.subprocess.run = real_run
        assert observed_timeouts == [None], observed_timeouts

        os.environ["PLEATTA_PROLOG_TIMEOUT_SECONDS"] = "0.2"
        timed = worker.solve({"goal": "repeat", "args": []})
        assert timed == {"error": "timeout"}, timed
        os.environ.pop("PLEATTA_PROLOG_TIMEOUT_SECONDS", None)

        assert worker._optional_positive_int(None, "limit") is None
        assert worker._optional_positive_float("", "timeout") is None
    finally:
        for name, value in saved.items():
            if value is None:
                os.environ.pop(name, None)
            else:
                os.environ[name] = value

    runtime_roundtrip()
    print("prolog-worker-policy: default-open, legacy-allowlist-ignored, "
          "direct-deny-opt-in, nested-not-sandboxed, limits-opt-in, "
          "live-replay-provenance")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
