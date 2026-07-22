#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Pinned host-effect failure/error and optional-confinement witnesses.

These checks deliberately remain in the trusted-host tier.  They compare
observable control flow with pinned PeTTa, verify that ordinary Prolog failure
is recorded and replayed as ``HostResponse.failed``, and separately exercise
the operator's optional filesystem-confinement policy.
"""

import importlib.util
import json
import os
import pathlib
import signal
import subprocess
import tempfile

import diff as D
from host_grade import _parse_answers


ROOT = pathlib.Path(__file__).resolve().parent.parent
PLEATTA = ROOT / ".lake" / "build" / "bin" / "pleatta"
WORKER = ROOT / "scripts" / "pleatta-python-worker.py"
FIXTURES = ROOT / "diffbench" / "host-fixtures"
PYTHON = pathlib.Path.home() / "miniforge3" / "envs" / "petta" / "bin" / "python"


def run_grouped(command, *, env=None, cwd=ROOT, timeout=60):
    process = subprocess.Popen(
        [str(part) for part in command], cwd=cwd, env=env,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        start_new_session=True)
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


def host_env(*, root=None, roots=None):
    env = os.environ.copy()
    env.pop("PLEATTA_HOST_ROOT", None)
    env.pop("PLEATTA_HOST_ROOTS", None)
    env["PLEATTA_PYTHON"] = str(PYTHON) if PYTHON.exists() else "python3"
    env["PLEATTA_PY_WORKER"] = str(WORKER)
    if root is not None:
        env["PLEATTA_HOST_ROOT"] = str(root)
    if roots is not None:
        env["PLEATTA_HOST_ROOTS"] = os.pathsep.join(str(path) for path in roots)
    return env


def live(program, transcript, *, root=None, roots=None):
    return run_grouped(
        [PLEATTA, "--host-live", program, transcript, "4000000"],
        env=host_env(root=root, roots=roots))


def replay(program, transcript):
    return run_grouped(
        [PLEATTA, "--host-replay", program, transcript, "4000000"],
        env=host_env())


def pinned_answers(program):
    previous = os.environ.get("PLEATTA_PINNED_ALLOW_EXTERNAL")
    os.environ["PLEATTA_PINNED_ALLOW_EXTERNAL"] = "1"
    try:
        return D.petta_results(program, 60)
    finally:
        if previous is None:
            os.environ.pop("PLEATTA_PINNED_ALLOW_EXTERNAL", None)
        else:
            os.environ["PLEATTA_PINNED_ALLOW_EXTERNAL"] = previous


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def check_missing_probe(tempdir):
    program = FIXTURES / "host-effects-missing-probe.metta"
    transcript = tempdir / "missing-probe.json"
    native = pinned_answers(program)
    result = live(program, transcript, root=FIXTURES)
    answers = _parse_answers(result.stdout)
    require(result.returncode == 0, result.stderr.strip())
    require(answers is not None and D.compare(native, answers),
            f"missing probe diverged: native={native!r} pleatta={answers!r}")
    exchanges = json.loads(transcript.read_text())
    require(any(exchange.get("response") == "failed" for exchange in exchanges),
            "missing exists_file/1 did not record HostResponse.failed")
    replayed = replay(program, transcript)
    require(replayed.returncode == 0, replayed.stderr.strip())
    require(replayed.stdout == result.stdout,
            "failed-probe replay changed the ordered observation")
    print("missing-exists-is-failure\tPASS\tnative=42\tpleatta=42\treplay=identical")


def check_missing_read_is_exception(tempdir):
    program = FIXTURES / "host-effects-missing-read.metta"
    try:
        pinned_answers(program)
    except D.RunnerError as error:
        native_returncode = error.returncode
        native_output = error.stdout + error.stderr
    else:
        raise AssertionError("pinned read_file_to_string/3 unexpectedly succeeded")
    result = live(program, tempdir / "missing-read.json")
    require(native_returncode != 0 and result.returncode != 0,
            "missing read_file_to_string/3 must remain an exception")
    require("42" not in native_output and "42" not in result.stdout,
            "execution continued past an uncaught missing-file exception")
    require("existence_error source_sink" in result.stderr,
            "PLeaTTa lost the typed missing-read exception kind")
    print("missing-read-is-exception\tPASS\tboth-abort-before-42\ttyped")


def check_caught_missing_read_shape(tempdir):
    program = FIXTURES / "host-effects-missing-read-caught.metta"
    native = pinned_answers(program)
    result = live(program, tempdir / "missing-read-caught.json")
    answers = _parse_answers(result.stdout)
    require(result.returncode == 0, result.stderr.strip())
    require(answers is not None and D.compare(native, answers),
            f"caught missing-read diverged: native={native!r} pleatta={answers!r}")
    require(any("existence_error source_sink" in answer for answer in answers),
            "caught PLeaTTa error lost the typed source_sink classification")
    print("caught-missing-read-shape\tPASS\texistence_error:source_sink")


def check_directory_is_not_file(tempdir):
    program = FIXTURES / "host-effects-directory-probe.metta"
    native = pinned_answers(program)
    result = live(program, tempdir / "directory-probe.json", root=FIXTURES)
    answers = _parse_answers(result.stdout)
    require(result.returncode == 0, result.stderr.strip())
    require(answers is not None and D.compare(native, answers),
            f"exists_file/1 directory case diverged: {native!r} vs {answers!r}")
    print("directory-is-not-file\tPASS\tnative=42\tpleatta=42")


def check_open_does_not_create_parent(tempdir):
    missing_parent = tempdir / "not-created"
    output = missing_parent / "output.txt"
    program = tempdir / "missing-parent-open.metta"
    literal = json.dumps(str(output))
    program.write_text(
        "(= (create-caught $file)\n"
        "  (catch (progn\n"
        "    (translatePredicate (open $file write $out))\n"
        "    (translatePredicate (close $out))\n"
        "    True)))\n"
        f"!(create-caught {literal})\n"
        "!(+ 20 22)\n",
        encoding="utf-8")
    native = pinned_answers(program)
    result = live(program, tempdir / "missing-parent-open.json")
    answers = _parse_answers(result.stdout)
    require(result.returncode == 0, result.stderr.strip())
    require(answers is not None and D.compare(native, answers),
            f"missing-parent open diverged: native={native!r} pleatta={answers!r}")
    require(not missing_parent.exists(),
            "PLeaTTa created a parent directory that pinned open/3 rejects")
    print("open-missing-parent\tPASS\tboth-caught\tparent-not-created")


def check_optional_confinement(tempdir):
    allowed = tempdir / "allowed"
    outside = tempdir / "outside"
    allowed.mkdir()
    outside.mkdir()
    input_path = outside / "input.txt"
    input_path.write_text("optional-root-witness", encoding="utf-8")
    program = tempdir / "absolute-read.metta"
    literal = json.dumps(str(input_path))
    program.write_text(
        "(= (read-now $file)\n"
        "  (progn (translatePredicate "
        "(read_file_to_string $file $content ())) $content))\n"
        f"!(read-now {literal})\n",
        encoding="utf-8")

    native = pinned_answers(program)
    unrestricted = live(program, tempdir / "unrestricted.json")
    unrestricted_answers = _parse_answers(unrestricted.stdout)
    require(unrestricted.returncode == 0, unrestricted.stderr.strip())
    require(unrestricted_answers is not None and
            D.compare(native, unrestricted_answers),
            "unset root policy did not preserve native absolute-path access")

    confined = live(
        program, tempdir / "confined.json", root=allowed)
    require(confined.returncode != 0 and
            "escapes the configured roots" in confined.stderr,
            "configured single root did not confine an outside path")

    multiroot = live(
        program, tempdir / "multiroot.json", roots=[allowed, outside])
    multiroot_answers = _parse_answers(multiroot.stdout)
    require(multiroot.returncode == 0, multiroot.stderr.strip())
    require(multiroot_answers is not None and
            D.compare(native, multiroot_answers),
            "configured second root did not authorize its path")
    print("filesystem-confinement\tPASS\tunset=native\tsingle=denied\tmultiple=allowed")


def check_optional_sleep_bound():
    spec = importlib.util.spec_from_file_location(
        "pleatta_python_worker_sleep_witness", WORKER)
    require(spec is not None and spec.loader is not None,
            "could not load the PLeaTTa Python worker")
    worker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(worker)

    observed = []
    original_sleep = worker.time.sleep
    previous = os.environ.get("PLEATTA_MAX_SLEEP_SECONDS")
    operation = {
        "sleep": {"duration": {"integer": {"value": 86400}}}
    }
    try:
        worker.time.sleep = observed.append

        os.environ.pop("PLEATTA_MAX_SLEEP_SECONDS", None)
        response = worker.host_effect(operation)
        require(observed == [86400.0],
                f"unset sleep policy changed native duration: {observed!r}")
        require(response == worker._mapping(),
                "unbounded sleep did not return the empty substitution")

        observed.clear()
        os.environ["PLEATTA_MAX_SLEEP_SECONDS"] = "120"
        response = worker.host_effect(operation)
        require(observed == [120.0],
                f"explicit sleep policy did not clamp: {observed!r}")
        require(response == worker._mapping(),
                "clamped sleep did not return the empty substitution")

        observed.clear()
        os.environ["PLEATTA_MAX_SLEEP_SECONDS"] = ""
        worker.host_effect(operation)
        require(observed == [86400.0],
                "blank sleep policy did not preserve native parity")

        for invalid in ("-1", "nan"):
            observed.clear()
            os.environ["PLEATTA_MAX_SLEEP_SECONDS"] = invalid
            try:
                worker.host_effect(operation)
            except ValueError:
                pass
            else:
                raise AssertionError(
                    f"invalid sleep policy {invalid!r} was accepted")
            require(not observed,
                    "invalid sleep policy reached the host sleeper")
    finally:
        worker.time.sleep = original_sleep
        if previous is None:
            os.environ.pop("PLEATTA_MAX_SLEEP_SECONDS", None)
        else:
            os.environ["PLEATTA_MAX_SLEEP_SECONDS"] = previous
    print("sleep-policy\tPASS\tunset=86400\texplicit-120=clamped"
          "\tblank=86400\tinvalid=rejected")


def main():
    require(PLEATTA.exists(), "build the pleatta executable first")
    require(WORKER.exists(), "PLeaTTa Python worker is missing")
    with tempfile.TemporaryDirectory(prefix="pleatta-host-semantics-") as raw:
        tempdir = pathlib.Path(raw)
        check_missing_probe(tempdir)
        check_missing_read_is_exception(tempdir)
        check_caught_missing_read_shape(tempdir)
        check_directory_is_not_file(tempdir)
        check_open_does_not_create_parent(tempdir)
        check_optional_confinement(tempdir)
        check_optional_sleep_bound()
    print("host-effect-semantics\tPASS")


if __name__ == "__main__":
    main()
