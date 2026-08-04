#!/usr/bin/env python3

"""Compare the exact first-turn LLM prompt under PeTTa and PLeaTTa."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys


FUEL = 500_000
FIXED_TIME = "2030-01-02 03:04:05"


TELEGRAM_STUB = '''\
def start_telegram(token="", chat_id=""):
    return None


def getLastMessage():
    return "fixture human message"


def lastMessageIsHuman():
    return 1


def lastMessageArmLoops():
    return 50


def recent_activity(*args):
    return "fixture recent activity"
'''


SYNTHETIC_STUB = '''\
import os


def current_model():
    return os.environ.get("SYNTHETIC_MODEL", "fixture-model")


def chat(model, max_tokens, effort, prompt):
    path = os.environ["PETTACLAW_PARITY_PROMPT_PATH"]
    with open(path, "xb") as handle:
        handle.write(str(prompt).encode("utf-8"))
    return "((rest))"
'''


OPENAI_STUB = '''\
class OpenAI:
    def __new__(cls, *args, **kwargs):
        return None
'''


ENTRY = '''\
!(import! &self (library lib_import))
!(import! &self ./lib_mettaclaw)
!(mettaclaw)
'''


def require_new_directory(path: Path) -> None:
    if path.exists():
        raise SystemExit(f"work directory already exists: {path}")
    path.mkdir(parents=True, mode=0o700)


def stage_checkout(source: Path, destination: Path, fixture: Path) -> None:
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
    for name in ["prompt.txt", "history.metta", "persistent.metta",
                 "recycle.requested"]:
        shutil.copy2(fixture / name, destination / name)
    for directory in [destination / ".cache", destination / "chroma_db"]:
        directory.mkdir(parents=True, exist_ok=True)

    (destination / "channels" / "telegram.py").write_text(
        TELEGRAM_STUB, encoding="utf-8")
    (destination / "src" / "synthetic_llm.py").write_text(
        SYNTHETIC_STUB, encoding="utf-8")
    (destination / "src" / "openai.py").write_text(
        OPENAI_STUB, encoding="utf-8")
    (destination / "prompt-parity.metta").write_text(
        ENTRY, encoding="utf-8")

    utils = destination / "src" / "utils.metta"
    source_text = utils.read_text(encoding="utf-8")
    old = '''\
(= (get_time_as_string)
   (progn (translatePredicate (format_time (Predicate (string $String)) "%Y-%m-%d %H:%M:%S" (get_time)))
          $String))'''
    new = f'''\
(= (get_time_as_string)
   "{FIXED_TIME}")'''
    if source_text.count(old) != 1:
        raise SystemExit("could not install the fixed-clock test oracle")
    utils.write_text(source_text.replace(old, new), encoding="utf-8")


def runtime_environment(
    *, repo: Path, root: Path, petta: Path, python: Path
) -> dict[str, str]:
    python_home = python.parent.parent
    swipl = shutil.which("swipl")
    if swipl is None:
        raise SystemExit("swipl is unavailable")
    path_entries = [
        str(python.parent), str(Path(swipl).parent),
        "/usr/local/bin", "/usr/bin", "/bin",
    ]
    return {
        "HOME": str(root),
        "XDG_CACHE_HOME": str(root / ".cache"),
        "PATH": ":".join(dict.fromkeys(path_entries)),
        "LANG": "C.UTF-8",
        "PYTHONHOME": str(python_home),
        "PYTHONNOUSERSITE": "1",
        "PYTHONDONTWRITEBYTECODE": "1",
        "PYTHONPATH": os.pathsep.join([
            str(root / "src"), str(root / "channels")
        ]),
        "LD_LIBRARY_PATH": str(python_home / "lib"),
        "PLEATTA_LIBRARY_PATH": os.pathsep.join([
            str(root), str(root / "repos" / "petta_lib_chromadb")
        ]),
        "PETTA_LIB_ROOT": str(petta / "lib"),
        "PLEATTA_HOST_ROOT": str(root),
        "PLEATTA_PYTHON": str(python),
        "PLEATTA_PY_WORKER": str(repo / "scripts" /
                                  "pleatta-python-worker.py"),
        "PLEATTA_MAX_SLEEP_SECONDS": "1",
        "METTACLAW_PROMPT_PATH": "prompt.txt",
        "METTACLAW_HISTORY_PATH": "history.metta",
        "METTACLAW_PERSISTENT_PATH": "persistent.metta",
        "METTACLAW_MODEL_STATE_PATH": "persistent.metta",
        "METTACLAW_RECYCLE_REQUEST_PATH": "recycle.requested",
        "METTACLAW_REPOS_DIR": "repos",
        "METTACLAW_CHROMA_DIR": "chroma_db",
        "METTACLAW_CHROMA_COLLECTION": "pleatta-parity",
        "PETTACLAW_PARITY_PROMPT_PATH": str(root / "captured-prompt.txt"),
        "SYNTHETIC_MODEL": "fixture-model",
    }


def sandbox_prefix(root: Path, environment: dict[str, str]) -> list[str]:
    bwrap = shutil.which("bwrap")
    if bwrap is None:
        raise SystemExit("bubblewrap is unavailable")
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
    return command


def run(name: str, command: list[str], root: Path) -> None:
    result = subprocess.run(
        command,
        stdin=subprocess.DEVNULL,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=120,
        check=False,
    )
    (root / "stdout.txt").write_text(result.stdout, encoding="utf-8")
    (root / "stderr.txt").write_text(result.stderr, encoding="utf-8")
    if result.returncode != 0:
        raise SystemExit(
            f"{name} failed ({result.returncode})\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}")
    if not (root / "captured-prompt.txt").is_file():
        raise SystemExit(f"{name} did not call the LLM exactly once")


def transcript_prompt(path: Path) -> bytes:
    transcript = json.loads(path.read_text(encoding="utf-8"))
    calls = [
        exchange["request"]["call"]
        for exchange in transcript
        if exchange["request"].get("call", {}).get("spec") ==
        "synthetic_llm.chat"
    ]
    if len(calls) != 1:
        raise SystemExit(
            f"expected one recorded LLM call, found {len(calls)}")
    args = calls[0].get("args", [])
    try:
        prompt = args[3]["string"]["value"]
    except (IndexError, KeyError, TypeError) as exc:
        raise SystemExit("recorded LLM prompt has an unexpected shape") from exc
    return prompt.encode("utf-8")


def sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def main() -> int:
    os.umask(0o077)
    parser = argparse.ArgumentParser()
    parser.add_argument("--pettaclaw-root", type=Path, required=True)
    parser.add_argument("--petta-root", type=Path, required=True)
    parser.add_argument("--work-root", type=Path, required=True)
    parser.add_argument("--pause-sentinel", type=Path, required=True)
    parser.add_argument("--python", type=Path, required=True)
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
        repo / "scripts" / "pleatta-python-worker.py",
        pettaclaw / "lib_mettaclaw.metta",
        petta / "run.sh",
        python,
    ]:
        if not required.exists():
            raise SystemExit(f"required input is absent: {required}")

    require_new_directory(work)
    fixture = repo / "diffbench" / "host-fixtures" / "pettaclaw"
    native_root = work / "petta"
    pleatta_root = work / "pleatta"
    stage_checkout(pettaclaw, native_root, fixture)
    stage_checkout(pettaclaw, pleatta_root, fixture)

    native_env = runtime_environment(
        repo=repo, root=native_root, petta=petta, python=python)
    native_command = sandbox_prefix(native_root, native_env) + [
        str(petta / "run.sh"), str(native_root / "prompt-parity.metta"),
        "default",
    ]
    run("PeTTa", native_command, native_root)

    transcript = pleatta_root / "transcript.json"
    pleatta_env = runtime_environment(
        repo=repo, root=pleatta_root, petta=petta, python=python)
    pleatta_command = sandbox_prefix(pleatta_root, pleatta_env) + [
        str(repo / ".lake" / "build" / "bin" / "pleatta"),
        "--host-live", str(pleatta_root / "prompt-parity.metta"),
        str(transcript), str(FUEL), "--", "default",
    ]
    run("PLeaTTa", pleatta_command, pleatta_root)

    native_prompt = (native_root / "captured-prompt.txt").read_bytes()
    pleatta_prompt = (pleatta_root / "captured-prompt.txt").read_bytes()
    recorded_prompt = transcript_prompt(transcript)
    if pleatta_prompt != recorded_prompt:
        raise SystemExit("PLeaTTa's recorded and delivered prompts differ")
    if native_prompt != pleatta_prompt:
        mismatch = next(
            (index for index, pair in enumerate(
                zip(native_prompt, pleatta_prompt)) if pair[0] != pair[1]),
            min(len(native_prompt), len(pleatta_prompt)),
        )
        raise SystemExit(
            "prompt bytes differ: "
            f"PeTTa={len(native_prompt)} PLeaTTa={len(pleatta_prompt)} "
            f"first_mismatch={mismatch}")

    native_history = (native_root / "history.metta").read_bytes()
    pleatta_history = (pleatta_root / "history.metta").read_bytes()
    if native_history != pleatta_history:
        raise SystemExit("post-turn history bytes differ")
    transcript_raw = transcript.read_text(encoding="utf-8")
    for root in [repo, pettaclaw, petta, work]:
        if str(root) in transcript_raw:
            raise SystemExit("the transcript contains a machine-local path")

    result = {
        "fixed_clock": FIXED_TIME,
        "history_bytes_equal": True,
        "network": "isolated",
        "prompt_bytes": len(native_prompt),
        "prompt_sha256": sha256(native_prompt),
        "recorded_prompt_equal": True,
        "status": "PASS",
    }
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
