#!/usr/bin/env python3

"""Run an unchanged PettaClaw graph against live hosts, then replay it."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time


DEFAULT_FUEL = 2_000_000
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
SECRET_NAMES = {
    "SYNTHETIC_API_KEY",
    "ANTHROPIC_API_KEY",
    "TAVILY_API_KEY",
    "METTACLAW_TELEGRAM_BOT_TOKEN",
    "TELEGRAM_BOT_TOKEN",
    "MOLTBOOK_API_KEY",
}


def require_new_directory(path: Path) -> None:
    if path.exists():
        raise SystemExit(f"work directory already exists: {path}")
    path.mkdir(parents=True, mode=0o700)


def stage_checkout(source: Path, destination: Path) -> None:
    """Copy the normal checkout while excluding credentials and bulky logs."""

    def ignored(directory: str, names: list[str]) -> set[str]:
        relative = Path(directory).resolve().relative_to(source)
        result = {
            name for name in names
            if name in {
                "__pycache__", ".pytest_cache", "pettaclaw-godel.log",
                "recycle.requested",
            }
        }
        if relative == Path("."):
            result.update(name for name in names if name.startswith(".env"))
            result.add("archive")
        if relative == Path("config"):
            result.add("secrets.env")
        return result

    shutil.copytree(source, destination, symlinks=True, ignore=ignored)
    for directory in [
        destination / "chat",
        destination / "episodes",
        destination / "attachments",
        destination / ".cache",
        destination / ".local" / "state",
    ]:
        directory.mkdir(parents=True, exist_ok=True)
def file_digest(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while block := handle.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def snapshot(root: Path) -> dict[str, str]:
    result: dict[str, str] = {}
    for path in sorted(root.rglob("*")):
        if path.is_file() and not path.is_symlink():
            result[str(path.relative_to(root))] = file_digest(path)
    return result


def changed_paths(before: dict[str, str], after: dict[str, str]) -> list[str]:
    return sorted(
        path for path in set(before) | set(after)
        if before.get(path) != after.get(path)
    )


def child_setup() -> None:
    os.setsid()


def runtime_environment(
    *, repo: Path, root: Path, petta: Path, python: Path
) -> dict[str, str]:
    prefixes = (
        "METTACLAW_",
        "SYNTHETIC_",
        "ANTHROPIC_",
        "TAVILY_",
        "MOLTBOOK_",
        "PLEATTA_",
        "SESSION_MEMORY_",
    )
    names = {
        "HTTP_PROXY", "HTTPS_PROXY", "ALL_PROXY", "NO_PROXY",
        "http_proxy", "https_proxy", "all_proxy", "no_proxy",
        "SSL_CERT_FILE", "SSL_CERT_DIR", "REQUESTS_CA_BUNDLE",
        "CURL_CA_BUNDLE", "TZ",
    }
    environment = {
        key: value for key, value in os.environ.items()
        if key.startswith(prefixes) or key in names
    }
    python_home = python.parent.parent
    path_entries = [
        str(python.parent),
        str(Path(shutil.which("swipl") or "/usr/bin/swipl").parent),
        "/usr/local/bin",
        "/usr/bin",
        "/bin",
    ]
    environment.update({
        "HOME": str(root),
        "XDG_CACHE_HOME": str(root / ".cache"),
        "XDG_STATE_HOME": str(root / ".local" / "state"),
        "PATH": ":".join(dict.fromkeys(path_entries)),
        "LANG": "C.UTF-8",
        "PYTHONHOME": str(python_home),
        "PYTHONNOUSERSITE": "1",
        "PYTHONDONTWRITEBYTECODE": "1",
        "PYTHONPATH": os.pathsep.join([
            str(root / "src"), str(root / "channels")
        ]),
        "LD_LIBRARY_PATH": os.pathsep.join(filter(None, [
            str(python_home / "lib"), os.environ.get("LD_LIBRARY_PATH", "")
        ])),
        "PLEATTA_LIBRARY_PATH": os.pathsep.join([
            str(root), str(root / "repos" / "petta_lib_chromadb")
        ]),
        "PETTA_LIB_ROOT": str(petta / "lib"),
        "PLEATTA_HOST_ROOT": str(root),
        "PLEATTA_PYTHON": str(python),
        "PLEATTA_PY_WORKER": str(repo / "scripts" /
                                  "pleatta-python-worker.py"),
        "PLEATTA_MAX_SLEEP_SECONDS": os.environ.get(
            "PLEATTA_MAX_SLEEP_SECONDS", "120"),
        "METTACLAW_PROMPT_PATH": "memory/prompt.txt",
        "METTACLAW_HISTORY_PATH": "memory/history.metta",
        "METTACLAW_PERSISTENT_PATH": "memory/persistent.metta",
        "METTACLAW_MODEL_STATE_PATH": "memory/persistent.metta",
        "METTACLAW_RECYCLE_REQUEST_PATH":
            ".local/state/recycle.requested",
        "METTACLAW_REPOS_DIR": "repos",
        "METTACLAW_CHROMA_DIR": "chroma_db",
        "METTACLAW_MEMORY_LOG_DIR": "memory/remembered",
        "METTACLAW_TELEGRAM_OFFSET_PATH": "telegram_offset.txt",
        "METTACLAW_TELEGRAM_LOG_PATH": "telegram_updates.jsonl",
        "METTACLAW_TELEGRAM_ATTACHMENTS_DIR": "attachments",
        "METTACLAW_MCP_CONFIG": ".mcp.json",
    })
    environment.pop("PLEATTA_CALL_FIXTURE", None)
    return environment


def sandbox_command(
    *, repo: Path, root: Path, mode: str, transcript: Path,
    exchanges: int | None, fuel: int,
) -> list[str]:
    bwrap = shutil.which("bwrap")
    if bwrap is None:
        raise SystemExit("bubblewrap is required")
    command = [
        bwrap,
        "--die-with-parent",
        "--ro-bind", "/", "/",
        "--bind", str(root), str(root),
        "--bind", str(transcript.parent), str(transcript.parent),
        "--dev", "/dev",
        "--proc", "/proc",
        "--tmpfs", "/tmp",
        "--chdir", str(repo),
        str(repo / ".lake" / "build" / "bin" / "pleatta"),
        mode,
        str(root / "run.metta"),
        str(transcript),
    ]
    if exchanges is not None:
        command.append(str(exchanges))
    command.extend([str(fuel), "--", "default"])
    return command


def load_transcript(path: Path) -> list[dict] | None:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError, UnicodeDecodeError):
        return None
    return value if isinstance(value, list) else None


def effect_tag(request: dict) -> str | None:
    effect = request.get("effect")
    if not isinstance(effect, dict):
        return None
    operation = effect.get("operation", effect)
    if operation == "clock":
        return "clock"
    if isinstance(operation, dict) and len(operation) == 1:
        return next(iter(operation))
    return None


def prefix_through_sleep(
    transcript: list[dict], sleep_count: int
) -> list[dict] | None:
    seen = 0
    for index, exchange in enumerate(transcript):
        request = exchange.get("request", {})
        if effect_tag(request) == "sleep":
            seen += 1
            if seen == sleep_count:
                return transcript[:index + 1]
    return None


def terminate_group(process: subprocess.Popen, grace: float = 10.0) -> None:
    if process.poll() is not None:
        return
    try:
        os.killpg(process.pid, signal.SIGTERM)
        process.wait(timeout=grace)
    except (ProcessLookupError, subprocess.TimeoutExpired):
        if process.poll() is None:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait(timeout=grace)


def run_live_until_sleep(
    *, command: list[str], environment: dict[str, str], transcript: Path,
    sleep_count: int, timeout: float, stdout_path: Path, stderr_path: Path,
) -> tuple[list[dict], int, float]:
    started = time.monotonic()
    with stdout_path.open("w", encoding="utf-8") as stdout, \
            stderr_path.open("w", encoding="utf-8") as stderr:
        process = subprocess.Popen(
            command,
            stdin=subprocess.DEVNULL,
            stdout=stdout,
            stderr=stderr,
            env=environment,
            preexec_fn=child_setup,
            text=True,
        )
        prefix = None
        try:
            deadline = started + timeout
            while time.monotonic() < deadline:
                current = load_transcript(transcript)
                if current is not None:
                    prefix = prefix_through_sleep(current, sleep_count)
                    if prefix is not None:
                        time.sleep(0.5)
                        break
                if process.poll() is not None:
                    break
                time.sleep(0.2)
        finally:
            terminate_group(process)
    if prefix is None:
        if process.returncode is None:
            reason = "live run timed out before the requested sleep boundary"
        else:
            reason = ("live run exited before the requested sleep boundary "
                      f"(status {process.returncode})")
        raise SystemExit(reason)
    return prefix, process.returncode or 0, time.monotonic() - started


def run_checked(
    *, command: list[str], environment: dict[str, str], timeout: float,
    stdout_path: Path, stderr_path: Path,
) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        command,
        stdin=subprocess.DEVNULL,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        env=environment,
        timeout=timeout,
        check=False,
        preexec_fn=child_setup,
    )
    stdout_path.write_text(result.stdout, encoding="utf-8")
    stderr_path.write_text(result.stderr, encoding="utf-8")
    os.chmod(stdout_path, 0o600)
    os.chmod(stderr_path, 0o600)
    return result


def transcript_summary(transcript: list[dict]) -> dict:
    modules: set[str] = set()
    calls: list[str] = []
    effects: list[str] = []
    prolog: list[str] = []
    for exchange in transcript:
        request = exchange.get("request", {})
        if "importModule" in request:
            modules.add(request["importModule"]["name"])
        if "call" in request:
            calls.append(request["call"]["spec"])
        if "prologCall" in request:
            prolog.append(request["prologCall"]["functor"])
        tag = effect_tag(request)
        if tag is not None:
            effects.append(tag)
    return {
        "modules": sorted(modules),
        "calls": calls,
        "effects": effects,
        "prolog": prolog,
    }


def assert_no_secret_leak(paths: list[Path], environment: dict[str, str]) -> None:
    secrets = [
        environment.get(name, "") for name in SECRET_NAMES
        if len(environment.get(name, "")) >= 8
    ]
    for path in paths:
        source = path.read_text(encoding="utf-8", errors="replace")
        if any(secret in source for secret in secrets):
            raise SystemExit(f"credential material reached recorded artifact {path.name}")


def require_checkpoint(
    name: str, result: subprocess.CompletedProcess[str], exchanges: int
) -> None:
    marker = f"HOST_CHECKPOINT exchanges={exchanges}\n"
    if result.returncode != 0:
        raise SystemExit(f"{name} failed with status {result.returncode}")
    if marker not in result.stdout:
        raise SystemExit(f"{name} missed the host checkpoint marker")


def main() -> int:
    os.umask(0o077)
    parser = argparse.ArgumentParser()
    parser.add_argument("--pettaclaw-root", type=Path, required=True)
    parser.add_argument("--petta-root", type=Path, required=True)
    parser.add_argument("--work-root", type=Path, required=True)
    parser.add_argument("--pause-sentinel", type=Path, required=True)
    parser.add_argument("--python", type=Path, required=True)
    parser.add_argument("--sleep-count", type=int, default=1)
    parser.add_argument("--fuel", type=int, default=DEFAULT_FUEL)
    parser.add_argument("--live-timeout", type=float, default=300.0)
    parser.add_argument("--replay-timeout", type=float, default=180.0)
    args = parser.parse_args()

    if args.sleep_count < 1:
        raise SystemExit("sleep-count must be positive")
    repo = Path(__file__).resolve().parent.parent
    pettaclaw = args.pettaclaw_root.resolve()
    petta = args.petta_root.resolve()
    work = args.work_root.resolve()
    python = args.python.resolve()
    if not args.pause_sentinel.is_file():
        raise SystemExit("the production-agent pause sentinel is absent")
    if not os.environ.get("SYNTHETIC_API_KEY"):
        raise SystemExit("SYNTHETIC_API_KEY is absent")
    if not os.environ.get("METTACLAW_TELEGRAM_BOT_TOKEN"):
        raise SystemExit("the Telegram bot token is absent")
    for required in [
        repo / ".lake" / "build" / "bin" / "pleatta",
        repo / "scripts" / "pleatta-python-worker.py",
        pettaclaw / "run.metta",
        pettaclaw / "lib_mettaclaw.metta",
        petta / "lib",
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
    for root in [live_root, replay_root, profile_root]:
        stage_checkout(pettaclaw, root)

    live_before = snapshot(live_root)
    transcript = artifacts / "live-transcript.json"
    live_stdout = artifacts / "live-stdout.txt"
    live_stderr = artifacts / "live-stderr.txt"
    live_env = runtime_environment(
        repo=repo, root=live_root, petta=petta, python=python)
    live_command = sandbox_command(
        repo=repo, root=live_root, mode="--host-live",
        transcript=transcript, exchanges=None, fuel=args.fuel)
    prefix, live_status, live_seconds = run_live_until_sleep(
        command=live_command,
        environment=live_env,
        transcript=transcript,
        sleep_count=args.sleep_count,
        timeout=args.live_timeout,
        stdout_path=live_stdout,
        stderr_path=live_stderr,
    )
    live_after = snapshot(live_root)

    prefix_path = artifacts / "verified-prefix.json"
    prefix_path.write_text(
        json.dumps(prefix, ensure_ascii=False, indent=2), encoding="utf-8")
    exchanges = len(prefix)
    summary = transcript_summary(prefix)
    missing_modules = REQUIRED_MODULES - set(summary["modules"])
    if missing_modules:
        raise SystemExit(f"live graph missed modules: {sorted(missing_modules)}")
    if summary["calls"].count("synthetic_llm.chat") < 1:
        raise SystemExit("the live prefix never called synthetic.new")
    for call in ["telegram.start_telegram", "telegram.getLastMessage"]:
        if call not in summary["calls"]:
            raise SystemExit(f"the live prefix missed {call}")

    replay_before = snapshot(replay_root)
    replay_env = runtime_environment(
        repo=repo, root=replay_root, petta=petta, python=python)
    replay = run_checked(
        command=sandbox_command(
            repo=repo, root=replay_root, mode="--host-replay-prefix",
            transcript=prefix_path, exchanges=exchanges, fuel=args.fuel),
        environment=replay_env,
        timeout=args.replay_timeout,
        stdout_path=artifacts / "replay-stdout.txt",
        stderr_path=artifacts / "replay-stderr.txt",
    )
    require_checkpoint("offline replay", replay, exchanges)
    replay_after = snapshot(replay_root)
    if replay_before != replay_after:
        raise SystemExit("offline replay mutated its staged checkout")

    profile_started = time.monotonic()
    profile_env = runtime_environment(
        repo=repo, root=profile_root, petta=petta, python=python)
    profile = run_checked(
        command=sandbox_command(
            repo=repo, root=profile_root, mode="--host-profile-prefix",
            transcript=prefix_path, exchanges=exchanges, fuel=args.fuel),
        environment=profile_env,
        timeout=args.replay_timeout,
        stdout_path=artifacts / "profile-stdout.txt",
        stderr_path=artifacts / "profile-stderr.txt",
    )
    require_checkpoint("offline profile", profile, exchanges)
    profile_seconds = time.monotonic() - profile_started
    profile_match = re.search(
        r"PROFILE total_steps=(\d+) answers=(\d+) exhausted=(\w+)",
        profile.stdout,
    )
    if profile_match is None or profile_match.group(3) != "false":
        raise SystemExit("offline profile did not finish cleanly")
    host_profiles = re.findall(
        r"HOST_PROFILE q\d+ steps=\d+ maxActive=(\d+) maxDepth=(\d+)",
        profile.stdout,
    )
    if not host_profiles:
        raise SystemExit("offline profile did not report host-machine activity")

    recorded = [
        transcript,
        prefix_path,
        live_stdout,
        live_stderr,
        artifacts / "replay-stdout.txt",
        artifacts / "replay-stderr.txt",
        artifacts / "profile-stdout.txt",
        artifacts / "profile-stderr.txt",
    ]
    assert_no_secret_leak(recorded, live_env)
    os.chmod(transcript, 0o600)
    os.chmod(prefix_path, 0o600)

    peak_active = max(int(active) for active, _ in host_profiles)
    peak_depth = max(int(depth) for _, depth in host_profiles)
    calls = summary["calls"]
    result = {
        "status": "PASS",
        "synthetic_model": live_env.get("SYNTHETIC_MODEL", ""),
        "completed_sleep_boundaries": args.sleep_count,
        "host_exchanges": exchanges,
        "synthetic_chat_calls": calls.count("synthetic_llm.chat"),
        "telegram_get_calls": calls.count("telegram.getLastMessage"),
        "telegram_send_calls": sum(
            1 for name in calls if name in {
                "telegram.send", "telegram.send_message",
                "telegram.send_message_to_chat",
            }),
        "host_effects": sorted(set(summary["effects"])),
        "prolog_functors": sorted(set(summary["prolog"])),
        "live_state_changes": changed_paths(live_before, live_after),
        "live_process_status_after_boundary": live_status,
        "live_wall_seconds": round(live_seconds, 3),
        "replay_prefix_consumed": True,
        "replay_filesystem_unchanged": True,
        "semantic_steps": int(profile_match.group(1)),
        "answers": int(profile_match.group(2)),
        "peak_active_substitution": peak_active,
        "peak_host_depth": peak_depth,
        "profile_wall_seconds": round(profile_seconds, 3),
        "credential_leak_scan": "clean",
    }
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
