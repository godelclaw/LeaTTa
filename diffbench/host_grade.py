#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Trusted-host grading.

Runs PLeaTTa through the CERTIFIED host bridge (`pleatta --host-live` + the real
Python worker) and compares its answer bag against pinned PeTTa + Janus on the
same file. The result is reported in the trusted-host tier only -- never merged
into certified-core equivalence. The emitted transcript is kept for a
deterministic `--host-replay` re-grade; transcripts may contain host paths, so
only synthetic transcripts are ever published (leak-checked at finalize).
"""
import os
import signal
import subprocess
import pathlib
import tempfile

import diff as D

# Use the pinned PeTTa Python environment for PLeaTTa's worker too, so both
# engines call the identical Python (matching Janus behaviour); fall back to
# system python3 if the env is absent.
PETTA_PY = os.environ.get(
    "PLEATTA_PYTHON",
    str(pathlib.Path.home() / "miniforge3" / "envs" / "petta" / "bin" / "python"),
)
if not pathlib.Path(PETTA_PY).exists():
    PETTA_PY = "python3"

TRANSCRIPT_DIR = pathlib.Path(__file__).resolve().parent / "host-transcripts"
# Absolute worker path so grading is CWD-independent (the same worker dispatches
# py-call/importModule to Janus and translatePredicate to the SWI-Prolog bridge).
REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent
HOST_WORKER = REPO_ROOT / "scripts" / "pleatta-python-worker.py"


def _host_env():
    env = os.environ.copy()
    env["PLEATTA_PYTHON"] = PETTA_PY
    env["PLEATTA_PY_WORKER"] = str(HOST_WORKER)
    return env


def _parse_answers(txt):
    """Parse pleatta's bracketed `[a, b, c]` answer line into items (string- and
    paren-aware). Mirrors diff.leatta_results' inner parser."""
    txt = txt.strip()
    if not (txt.startswith("[") and txt.endswith("]")):
        return None
    inner = txt[1:-1].strip()
    if not inner:
        return []
    items, depth, cur, in_str, esc = [], 0, "", False, False
    for ch in inner:
        if in_str:
            cur += ch
            if esc:
                esc = False
            elif ch == "\\":
                esc = True
            elif ch == '"':
                in_str = False
            continue
        if ch == '"':
            in_str = True
            cur += ch
            continue
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == "," and depth == 0:
            items.append(cur.strip())
            cur = ""
        else:
            cur += ch
    items.append(cur.strip())
    return items


def grade_python_live(path, timeout):
    """Grade a py-call corpus file. Returns (verdict, petta_n, pleatta_n,
    transcript_path). verdict AGREE/AGREE-ORD => trusted-host covered."""
    path = pathlib.Path(path)
    TRANSCRIPT_DIR.mkdir(parents=True, exist_ok=True)
    transcript = TRANSCRIPT_DIR / f"{path.stem}.live.json"
    # transformed temp beside the source keeps relative imports meaningful
    with D.transformed_temp(path) as t:
        t.write(D.transform(path.read_text(errors="replace")))
        tpath = pathlib.Path(t.name)
    try:
        try:
            pr = D.petta_results(
                tpath, timeout * D.DEFAULT_PETTA_TIMEOUT_MULTIPLIER)
        except D.RunnerError as err:
            print(f"{path.name}: pinned host oracle error: {err.stderr.strip()}",
                  file=__import__("sys").stderr)
            return ("PETTA-ERROR", "", "", str(transcript))
        except subprocess.TimeoutExpired:
            return ("PETTA-TIMEOUT", "", "", str(transcript))
        env = _host_env()
        cmd = [D.LEATTA_BIN, "--host-live", str(tpath), str(transcript), "4000000"]
        p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             text=True, env=env, start_new_session=True)
        try:
            out, err = p.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(os.getpgid(p.pid), signal.SIGKILL)
            except ProcessLookupError:
                pass
            p.communicate()
            return ("LEATTA-TIMEOUT", len(pr), "", str(transcript))
        if p.returncode != 0:
            print(f"{path.name}: pleatta --host-live error: {err.strip()}",
                  file=__import__("sys").stderr)
            return ("LEATTA-ERROR", len(pr), "", str(transcript))
        lr = _parse_answers(D.ANSI.sub("", out))
        if lr is None:
            return ("LEATTA-NOOUT", len(pr), "", str(transcript))
        if D.compare(pr, lr):
            verdict = "AGREE"
        elif D.compare_ord(pr, lr):
            verdict = "AGREE-ORD"
        elif len(pr) == len(lr):
            verdict = "DIFF-VAL"
        else:
            verdict = "DIFF-COUNT"
        return (verdict, len(pr), len(lr), str(transcript))
    finally:
        tpath.unlink(missing_ok=True)


def grade_stdin_replay(fixture, timeout, input_line="pleatta stdin witness"):
    """Bounded one-turn trusted-host WITNESS for readln! programs.  Runs a
    fixture through the certified bridge with one recorded stdin line
    (`--host-live`), then replays the recorded transcript (`--host-replay`).
    Passes iff the recorded line is consumed and replay reproduces the live
    output deterministically. Returns (verdict, petta_n, pleatta_n)."""
    import json
    fixture = pathlib.Path(fixture)
    if not fixture.exists():
        return ("NO-FIXTURE", "", "")
    TRANSCRIPT_DIR.mkdir(parents=True, exist_ok=True)
    transcript = TRANSCRIPT_DIR / f"{fixture.stem}.stdin.json"
    fuel = "4000000"
    env = _host_env()
    try:
        live = subprocess.run(
            [D.LEATTA_BIN, "--host-live", str(fixture), str(transcript), fuel],
            input=input_line + "\n", capture_output=True, text=True,
            env=env, timeout=timeout)
    except subprocess.TimeoutExpired:
        return ("LEATTA-TIMEOUT", "", "")
    if live.returncode != 0 or not transcript.exists():
        return ("LEATTA-ERROR", "", "")
    try:
        tx = json.loads(transcript.read_text())
    except json.JSONDecodeError:
        return ("BAD-TRANSCRIPT", "", "")
    consumed = (any(e.get("request") == "readLine" for e in tx)
                and input_line in live.stdout)
    try:
        replay = subprocess.run(
            [D.LEATTA_BIN, "--host-replay", str(fixture), str(transcript), fuel],
            capture_output=True, text=True, env=env, timeout=timeout)
    except subprocess.TimeoutExpired:
        return ("LEATTA-TIMEOUT", "", "")
    deterministic = (replay.returncode == 0 and live.stdout == replay.stdout)
    if consumed and deterministic:
        return ("WITNESS-AGREE", 1, 1)
    return ("WITNESS-FAIL", "", "")


if __name__ == "__main__":
    import sys
    for name in sys.argv[1:]:
        p = pathlib.Path.home() / "repos/PeTTa/examples" / name
        print(name, grade_python_live(p, 60))
