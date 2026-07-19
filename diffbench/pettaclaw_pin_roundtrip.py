#!/usr/bin/env python3

"""Exercise PettaClaw's generic pin path across two unchanged loop turns."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import sys
import time

from pettaclaw_live_run import (
    require_checkpoint,
    run_checked,
    run_live_until_sleep,
)
from pettaclaw_one_turn import (
    require_new_directory,
    sandbox_command,
    snapshot,
    stage,
)


PIN_TOKEN = "pin-roundtrip-fixture"
SLEEP_COUNT = 2
FUEL = 1_000_000


def strings_in(value):
    if isinstance(value, str):
        yield value
    elif isinstance(value, list):
        for item in value:
            yield from strings_in(item)
    elif isinstance(value, dict):
        for item in value.values():
            yield from strings_in(item)


def request_calls(transcript: list[dict], name: str) -> list[dict]:
    return [
        request["call"]
        for exchange in transcript
        for request in [exchange.get("request", {})]
        if request.get("call", {}).get("spec") == name
    ]


def validate_pin_path(transcript: list[dict], history: str) -> dict:
    chats = request_calls(transcript, "synthetic_llm.chat")
    if len(chats) != 2:
        raise SystemExit(f"expected two synthetic turns, got {len(chats)}")
    second_prompt = next(
        (value for value in strings_in(chats[1].get("args", []))
         if "LAST_SKILL_USE_RESULTS:" in value),
        None,
    )
    if second_prompt is None:
        raise SystemExit("second turn did not carry a PettaClaw context")
    history_marker = " HISTORY: "
    results_marker = " LAST_SKILL_USE_RESULTS: "
    time_marker = " TIME: "
    if history_marker not in second_prompt or results_marker not in second_prompt:
        raise SystemExit("second context omitted history or last-results markers")
    dynamic = second_prompt.split(history_marker, 1)[1]
    history_part, last_part = dynamic.split(results_marker, 1)
    last_results = last_part.rsplit(time_marker, 1)[0]
    normalizations = request_calls(transcript, "helper.normalize_string")
    pin_reached_normalizer = any(
        PIN_TOKEN in value
        for call in normalizations
        for value in strings_in(call.get("args", []))
    )
    pin_in_history = PIN_TOKEN in history_part and PIN_TOKEN in history
    pin_in_last_results = (
        PIN_TOKEN in last_results and "COMMAND_RETURN" in last_results
    )
    if not pin_reached_normalizer:
        raise SystemExit("unmatched pin did not reach generic result normalization")
    if not pin_in_history:
        raise SystemExit("pin response did not reach history and next-turn context")
    if not pin_in_last_results:
        raise SystemExit("pin echo did not reach next-turn last results")
    return {
        "pin_reached_generic_normalizer": True,
        "pin_in_history": True,
        "pin_in_next_turn_last_results": True,
    }


def main() -> int:
    os.umask(0o077)
    parser = argparse.ArgumentParser()
    parser.add_argument("--pettaclaw-root", type=Path, required=True)
    parser.add_argument("--petta-root", type=Path, required=True)
    parser.add_argument("--work-root", type=Path, required=True)
    parser.add_argument("--pause-sentinel", type=Path, required=True)
    parser.add_argument("--python", type=Path,
                        default=Path(sys.executable).resolve())
    args = parser.parse_args()

    repo = Path(__file__).resolve().parent.parent
    pettaclaw = args.pettaclaw_root.resolve()
    petta = args.petta_root.resolve()
    work = args.work_root.resolve()
    python = args.python.resolve()
    calls_fixture = (repo / "diffbench" / "host-fixtures" /
                     "pettaclaw-pin-two-turn.calls.json")
    if not args.pause_sentinel.is_file():
        raise SystemExit("the production-agent pause sentinel is absent")
    for required in [
        repo / ".lake" / "build" / "bin" / "pleatta",
        repo / "diffbench" / "pettaclaw_godel_one_turn.metta",
        pettaclaw / "lib_mettaclaw.metta",
        petta / "lib",
        calls_fixture,
        python,
    ]:
        if not required.exists():
            raise SystemExit(f"required input is absent: {required}")

    require_new_directory(work)
    artifacts = work / "artifacts"
    artifacts.mkdir()
    live_root = work / "live"
    replay_root = work / "replay"
    profile_root = work / "profile"
    data_fixture = repo / "diffbench" / "host-fixtures" / "pettaclaw"
    for root in [live_root, replay_root, profile_root]:
        stage(data_fixture, root)

    environment = os.environ.copy()
    transcript = live_root / "transcript.json"
    live_stdout = live_root / "stdout.txt"
    live_stderr = live_root / "stderr.txt"
    prefix, live_status, live_seconds = run_live_until_sleep(
        command=sandbox_command(
            repo=repo, pettaclaw=pettaclaw, petta=petta, python=python,
            root=live_root, mode="--host-live", transcript=transcript,
            exchanges=None, fuel=FUEL, calls_fixture=calls_fixture),
        environment=environment,
        transcript=transcript,
        sleep_count=SLEEP_COUNT,
        timeout=120,
        stdout_path=live_stdout,
        stderr_path=live_stderr,
    )
    prefix_path = work / "verified-prefix.json"
    prefix_path.write_text(
        json.dumps(prefix, ensure_ascii=False, indent=2), encoding="utf-8")
    history = (live_root / "history.metta").read_text(encoding="utf-8")
    pin_checks = validate_pin_path(prefix, history)
    raw_prefix = prefix_path.read_text(encoding="utf-8")
    for root in [repo, pettaclaw, petta, work]:
        if str(root) in raw_prefix:
            raise SystemExit("transcript contains a machine-local path")

    replay_before = snapshot(replay_root)
    replay = run_checked(
        command=sandbox_command(
            repo=repo, pettaclaw=pettaclaw, petta=petta, python=python,
            root=replay_root, mode="--host-replay-prefix",
            transcript=prefix_path, exchanges=len(prefix), fuel=FUEL),
        environment=environment,
        timeout=120,
        stdout_path=artifacts / "replay-stdout.txt",
        stderr_path=artifacts / "replay-stderr.txt",
    )
    require_checkpoint("pin replay", replay, len(prefix))
    replay_after = snapshot(replay_root)
    if replay_before != replay_after:
        raise SystemExit("offline replay mutated its fixture data")

    profile_started = time.monotonic()
    profile = run_checked(
        command=sandbox_command(
            repo=repo, pettaclaw=pettaclaw, petta=petta, python=python,
            root=profile_root, mode="--host-profile-prefix",
            transcript=prefix_path, exchanges=len(prefix), fuel=FUEL),
        environment=environment,
        timeout=120,
        stdout_path=artifacts / "profile-stdout.txt",
        stderr_path=artifacts / "profile-stderr.txt",
    )
    require_checkpoint("pin profile", profile, len(prefix))
    profile_seconds = time.monotonic() - profile_started
    match = re.search(
        r"PROFILE total_steps=(\d+) answers=(\d+) exhausted=(\w+)",
        profile.stdout,
    )
    if match is None or match.group(3) != "false":
        raise SystemExit("pin profile did not finish cleanly")

    result = {
        "status": "PASS",
        "turns": 2,
        "host_exchanges": len(prefix),
        "semantic_steps": int(match.group(1)),
        "answers": int(match.group(2)),
        "live_process_status_after_boundary": live_status,
        "live_wall_seconds": round(live_seconds, 3),
        "profile_wall_seconds": round(profile_seconds, 3),
        "network": "isolated",
        "replay_prefix_consumed": True,
        "replay_filesystem_unchanged": True,
        **pin_checks,
    }
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
