#!/usr/bin/env python3

"""Run one unchanged PettaClaw turn live, replay it, and profile the prefix."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time


FUEL = 500_000
REQUIRED_MODULES = {
    "lib_llm",
    "helper",
    "synthetic_llm",
    "mcp_bridge",
    "qwen_embed",
    "irc",
    "mattermost",
    "telegram",
    "websearch",
    "lib_chromadb",
}


def require_new_directory(path: Path) -> None:
    if path.exists():
        raise SystemExit(f"work directory already exists: {path}")
    path.mkdir(parents=True)


def stage(fixture: Path, destination: Path) -> None:
    destination.mkdir(parents=True)
    shutil.copytree(fixture, destination, dirs_exist_ok=True)
    (destination / "chroma_db").mkdir()
    (destination / ".cache").mkdir()


def snapshot(root: Path) -> dict[str, str]:
    result = {}
    for path in sorted(root.rglob("*")):
        if path.is_file():
            result[str(path.relative_to(root))] = hashlib.sha256(
                path.read_bytes()).hexdigest()
    return result


def sandbox_command(
    *,
    repo: Path,
    pettaclaw: Path,
    petta: Path,
    python: Path,
    root: Path,
    mode: str,
    transcript: Path,
    exchanges: int | None = None,
    fuel: int = FUEL,
    calls_fixture: Path | None = None,
) -> list[str]:
    swipl = shutil.which("swipl")
    bwrap = shutil.which("bwrap")
    if swipl is None or bwrap is None:
        raise SystemExit("both bwrap and swipl must be available")
    path_entries = [
        str(python.parent),
        str(Path(swipl).parent),
        "/usr/local/bin",
        "/usr/bin",
        "/bin",
    ]
    path_value = ":".join(dict.fromkeys(path_entries))
    environment = {
        "HOME": str(root),
        "XDG_CACHE_HOME": str(root / ".cache"),
        "PATH": path_value,
        "LANG": "C.UTF-8",
        "PYTHONDONTWRITEBYTECODE": "1",
        "PLEATTA_LIBRARY_PATH": os.pathsep.join([
            str(pettaclaw), str(pettaclaw / "repos" / "petta_lib_chromadb")
        ]),
        "PETTA_LIB_ROOT": str(petta / "lib"),
        "PLEATTA_PROLOG_LIB": str(petta / "src" / "metta.pl"),
        # Fixture state is writable; source and pinned-library roots are
        # declared read-only inputs to imported Python/Prolog modules.
        "PLEATTA_HOST_ROOTS": os.pathsep.join([
            str(root), str(pettaclaw), str(petta)
        ]),
        "PLEATTA_MAX_SLEEP_SECONDS": "1",
        "METTACLAW_PROMPT_PATH": "prompt.txt",
        "METTACLAW_HISTORY_PATH": "history.metta",
        "METTACLAW_PERSISTENT_PATH": "persistent.metta",
        "METTACLAW_MODEL_STATE_PATH": "persistent.metta",
        "METTACLAW_RECYCLE_REQUEST_PATH": "recycle.requested",
        "METTACLAW_REPOS_DIR": "repos",
        "METTACLAW_CHROMA_DIR": "chroma_db",
        "METTACLAW_CHROMA_COLLECTION": "pleatta-fixture",
        "SYNTHETIC_MODEL": "fixture-model",
    }
    prolog_allowlist = os.environ.get("PLEATTA_PROLOG_ALLOWLIST", "")
    if prolog_allowlist:
        environment["PLEATTA_PROLOG_ALLOWLIST"] = prolog_allowlist
    if mode in {"--host-live", "--host-live-prefix"}:
        environment.update({
            "PLEATTA_PYTHON": str(python),
            "PLEATTA_PY_WORKER": str(repo / "scripts" /
                                      "pleatta-python-worker.py"),
            "PLEATTA_CALL_FIXTURE": str(calls_fixture or
                (repo / "diffbench" / "host-fixtures" /
                 "pettaclaw-one-turn.calls.json")),
        })
    command = [
        bwrap,
        "--die-with-parent",
        "--unshare-net",
        "--ro-bind", "/", "/",
        "--bind", str(root), str(root),
        "--dev", "/dev",
        "--proc", "/proc",
        "--tmpfs", "/tmp",
        "--chdir", str(root),
        "--clearenv",
    ]
    for name, value in environment.items():
        command.extend(["--setenv", name, value])
    command.extend([
        str(repo / ".lake" / "build" / "bin" / "pleatta"),
        mode,
        str(repo / "diffbench" / "pettaclaw_godel_one_turn.metta"),
        str(transcript),
    ])
    if exchanges is not None:
        command.append(str(exchanges))
    command.extend([str(fuel), "--", "default"])
    return command


def run(command: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        stdin=subprocess.DEVNULL,
        capture_output=True,
        text=True,
        timeout=120,
        check=False,
    )


def require_live_success(
    name: str, result: subprocess.CompletedProcess[str]
) -> None:
    if result.returncode != 0:
        raise SystemExit(
            f"{name} failed ({result.returncode})\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}")
    if result.stderr:
        raise SystemExit(f"{name} wrote stderr:\n{result.stderr}")


def request_names(transcript: list[dict]) -> tuple[set[str], list[str]]:
    modules = set()
    calls = []
    for exchange in transcript:
        request = exchange["request"]
        if "importModule" in request:
            modules.add(request["importModule"]["name"])
        if "call" in request:
            calls.append(request["call"]["spec"])
    return modules, calls


def validate_transcript(transcript_path: Path, roots: list[Path]) -> list[dict]:
    raw = transcript_path.read_text(encoding="utf-8")
    transcript = json.loads(raw)
    if not transcript:
        raise SystemExit("the completed turn recorded no host exchanges")
    modules, calls = request_names(transcript)
    missing = REQUIRED_MODULES - modules
    if missing:
        raise SystemExit(f"missing transitive Python imports: {sorted(missing)}")
    expected_call_counts = {
        "openai.OpenAI": 1,
        "telegram.start_telegram": 1,
        "telegram.getLastMessage": 1,
        "telegram.lastMessageIsHuman": 1,
        "synthetic_llm.chat": 1,
        "helper.recycle_requested": 1,
    }
    for name, expected in expected_call_counts.items():
        actual = calls.count(name)
        if actual != expected:
            raise SystemExit(f"{name}: expected {expected}, got {actual}")
    recycle_responses = [exchange["response"]
                         for exchange in transcript
                         if exchange["request"].get("call", {}).get("spec") ==
                         "helper.recycle_requested"]
    expected_recycle_response = {
        "returned": {"value": {"integer": {"value": 1}}}
    }
    if recycle_responses != [expected_recycle_response]:
        raise SystemExit("the staged recycle request did not return integer 1")
    requests = [exchange["request"] for exchange in transcript]
    certified_prolog_functors = {
        "atomic_list_concat", "first_char", "gc", "get_time", "sread",
        "split_string", "string_concat", "string_length", "sub_string",
        "swrite",
    }
    escaped_certified = sorted({
        request["prologCall"]["functor"]
        for request in requests
        if request.get("prologCall", {}).get("functor")
        in certified_prolog_functors
    })
    if escaped_certified:
        raise SystemExit(
            "certified Prolog predicates escaped to SWI: "
            f"{escaped_certified}")
    if not any(request.get("prologCall", {}).get("functor") == "atom_codes"
               for request in requests):
        raise SystemExit("the real newline/atom_codes path was not exercised")
    effects = [request["effect"].get("operation", request["effect"])
               for request in requests if "effect" in request]
    effect_tags = ["clock" if effect == "clock" else next(iter(effect))
                   for effect in effects]
    required_effects = {
        "clock", "fileExists", "fileRead", "fileOpen", "fileWrite",
        "fileNewline", "fileClose", "formatTime", "printLine",
    }
    missing_effects = required_effects - set(effect_tags)
    if missing_effects:
        raise SystemExit(
            f"first turn missed typed host effects: {sorted(missing_effects)}")
    if "sleep" in effect_tags:
        raise SystemExit("the staged recycle request did not stop before sleep")
    printed = [effect["printLine"]["text"] for effect in effects
               if isinstance(effect, dict) and "printLine" in effect]
    if "(RECYCLE_AT_TURN_BOUNDARY iteration 1)" not in printed:
        raise SystemExit("the cooperative recycle boundary was not observed")
    append_opens = [effect["fileOpen"] for effect in effects
                    if isinstance(effect, dict) and "fileOpen" in effect and
                    effect["fileOpen"].get("mode") == "append"]
    if len(append_opens) != 1 or append_opens[0].get("path") != "history.metta":
        raise SystemExit("history was not opened exactly once in append mode")
    normalized_results = [request["call"]["args"]
                          for request in requests
                          if request.get("call", {}).get("spec") ==
                          "helper.normalize_string"]
    expected_rest = [{"list": {"items": [
        {"string": {"value": "RESTING"}},
        {"string": {"value": "loops-left"}},
        {"integer": {"value": 0}},
        {"string": {"value": "sleep-interval-seconds"}},
        {"integer": {"value": 1}},
    ]}}]
    if normalized_results != [expected_rest]:
        raise SystemExit("the harmless rest skill did not execute exactly once")
    for root in roots:
        if str(root) in raw:
            raise SystemExit("transcript contains a machine-local path")
    return transcript


def main() -> int:
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
    if not args.pause_sentinel.is_file():
        raise SystemExit("the production-agent pause sentinel is absent")
    for required in [
        repo / ".lake" / "build" / "bin" / "pleatta",
        repo / "diffbench" / "pettaclaw_godel_one_turn.metta",
        pettaclaw / "lib_mettaclaw.metta",
        petta / "lib",
        python,
    ]:
        if not required.exists():
            raise SystemExit(f"required input is absent: {required}")
    require_new_directory(work)
    live_root = work / "live"
    replay_root = work / "replay"
    profile_root = work / "profile"
    fixture = repo / "diffbench" / "host-fixtures" / "pettaclaw"
    for root in [live_root, replay_root, profile_root]:
        stage(fixture, root)

    transcript_path = live_root / "transcript.json"
    live = run(sandbox_command(
        repo=repo, pettaclaw=pettaclaw, petta=petta, python=python,
        root=live_root, mode="--host-live", transcript=transcript_path,
        exchanges=None))
    (live_root / "stdout.txt").write_text(live.stdout, encoding="utf-8")
    (live_root / "stderr.txt").write_text(live.stderr, encoding="utf-8")
    require_live_success("live turn", live)
    transcript = validate_transcript(
        transcript_path, [repo, pettaclaw, petta, work])
    exchanges = len(transcript)
    history = (live_root / "history.metta").read_text(encoding="utf-8")
    if not history.startswith("(FIXTURE_HISTORY initial)\n"):
        raise SystemExit("history append did not preserve the fixture prefix")
    if (history.count("fixture human message") != 1 or
            history.count("((rest))") != 1):
        raise SystemExit("the completed command/history evidence is absent")

    before = snapshot(replay_root)
    replay = run(sandbox_command(
        repo=repo, pettaclaw=pettaclaw, petta=petta, python=python,
        root=replay_root, mode="--host-replay",
        transcript=transcript_path, exchanges=None))
    after = snapshot(replay_root)
    (replay_root / "stdout.txt").write_text(
        replay.stdout, encoding="utf-8")
    (replay_root / "stderr.txt").write_text(
        replay.stderr, encoding="utf-8")
    require_live_success("offline replay", replay)
    if live.stdout != replay.stdout:
        raise SystemExit("live and replay observable output differs")
    if before != after:
        raise SystemExit("offline replay mutated its data directory")

    profile_started = time.monotonic()
    profile = run(sandbox_command(
        repo=repo, pettaclaw=pettaclaw, petta=petta, python=python,
        root=profile_root, mode="--host-profile",
        transcript=transcript_path, exchanges=None))
    profile_wall_seconds = time.monotonic() - profile_started
    require_live_success("offline profile", profile)
    (profile_root / "stdout.txt").write_text(profile.stdout, encoding="utf-8")
    (profile_root / "stderr.txt").write_text(profile.stderr, encoding="utf-8")
    match = re.search(
        r"PROFILE total_steps=(\d+) answers=(\d+) exhausted=(\w+)",
        profile.stdout)
    if match is None or match.group(3) != "false":
        raise SystemExit("profile did not finish at the checkpoint")
    host_profiles = re.findall(
        r"HOST_PROFILE q\d+ steps=\d+ maxActive=(\d+) maxDepth=(\d+)",
        profile.stdout)
    if not host_profiles:
        raise SystemExit("profile did not report host-machine activity")
    peak_active = max(int(active) for active, _depth in host_profiles)
    peak_depth = max(int(depth) for _active, depth in host_profiles)

    print(json.dumps({
        "status": "PASS",
        "host_exchanges": exchanges,
        "semantic_steps": int(match.group(1)),
        "peak_active_substitution": peak_active,
        "peak_host_depth": peak_depth,
        "profile_wall_seconds": round(profile_wall_seconds, 3),
        "answers": int(match.group(2)),
        "live_replay_equal": True,
        "replay_filesystem_unchanged": True,
        "network": "isolated",
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
