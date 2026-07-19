#!/usr/bin/env python3

"""Canonical manifest-denominator PLeaTTa corpus measurement.

Every file named by the selected manifest receives exactly one row. Direct
value/multiplicity agreement and same-family semantic witness agreement are
separate columns; external host dependencies and oracle failures remain in the
denominator. Extra files in a working PeTTa checkout are ignored, never folded
silently into the denominator. The command never extrapolates from a prefix.
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import os
import pathlib
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
DEFAULT_CORPUS_MANIFEST = HERE / "corpus-official-149.txt"
DEFAULT_CORPUS_HASHES = HERE / "corpus-official-149.sha256"

import diff as D  # noqa: E402
import host_grade as HG  # noqa: E402
import nars_witnesses as NW  # noqa: E402
import perf_witnesses as PW  # noqa: E402


AGREE = {"AGREE", "AGREE-ORD"}
PERFORMANCE_RESULTS = {
    "LEATTA-TIMEOUT", "LEATTA-EXHAUSTED", "PETTA-TIMEOUT"
}
HEADER = (
    "file", "dependency", "direct_verdict", "petta_n", "pleatta_n",
    "witness", "witness_verdict", "semantic_status", "pleatta_independent",
)
DEFAULT_ORACLE_LEDGER = HERE / "broken-oracle-ledger.tsv"


def read_ledger(path: pathlib.Path) -> set[str]:
    """Files adjudicated BROKEN-ORACLE: pinned PeTTa itself errors/asserts-out
    on a malformed test, and PLeaTTa's independent result (recorded in every
    row) shows PLeaTTa is not the defect. Membership is evidence-backed in the
    ledger file; it is never inferred from a bare PETTA-ERROR."""
    if not path.exists():
        return set()
    names: set[str] = set()
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        names.add(line.split("\t", 1)[0])
    return names


DEFAULT_HOST_REGISTRY = HERE / "host-cases.tsv"
HOST_FIXTURE_DIR = HERE / "host-fixtures"


def read_host_registry(path: pathlib.Path) -> dict[str, dict]:
    """Explicit host-case grading registry: file -> {driver, timeout, tier}.
    Files absent here are never auto-run (they stay deferred
    external-unavailable), so interactive/network programs cannot hang a run."""
    reg: dict[str, dict] = {}
    if not path.exists():
        return reg
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) < 4:
            continue
        reg[parts[0]] = {
            "driver": parts[1], "timeout": float(parts[2]), "tier": parts[3],
        }
    return reg


def generic_witnesses() -> dict[str, tuple[str, str]]:
    return {target: (name, source) for target, name, source, _ in PW.WITNESSES}


def run_generic_witness(name: str, source: str, timeout: float) -> str:
    with tempfile.NamedTemporaryFile(
        "w", suffix=".metta", prefix=f".coverage-{name}-",
        dir=PW.EXAMPLES, delete=False,
    ) as handle:
        handle.write(source)
        path = pathlib.Path(handle.name)
    try:
        row = D.run_file(
            path, timeout=timeout, petta_timeout=timeout,
            leatta_timeout_multiplier=1,
        )
        return row[3]
    finally:
        path.unlink(missing_ok=True)


DEFAULT_ORACLE_WITNESS_DIR = HERE / "oracle-witnesses"


def run_oracle_witness(name: str, timeout: float) -> str:
    """Run the corrected same-capability witness for a broken-oracle file and
    return its direct verdict. AGREE/AGREE-ORD means PLeaTTa demonstrates the
    capability the (malformed) pinned test intended, on both engines. The
    witness source is copied into PETTA_DIR/examples first, since the pinned
    oracle runner requires programs to live inside the checkout."""
    witness = DEFAULT_ORACLE_WITNESS_DIR / f"{pathlib.Path(name).stem}.witness.metta"
    if not witness.exists():
        return ""
    with tempfile.NamedTemporaryFile(
        "w", suffix=".metta", prefix=f".coverage-oracle-{pathlib.Path(name).stem}-",
        dir=PW.EXAMPLES, delete=False,
    ) as handle:
        handle.write(witness.read_text())
        path = pathlib.Path(handle.name)
    try:
        row = D.run_file(
            path, timeout=timeout, petta_timeout=timeout,
            leatta_timeout_multiplier=1,
        )
        return row[3]
    finally:
        path.unlink(missing_ok=True)


def normalized(items: list[str] | None) -> collections.Counter[str] | None:
    if items is None:
        return None
    return collections.Counter(D.normalize(item) for item in items)


def run_exact_witnesses(target: str, timeout: float) -> tuple[str, str]:
    if target == "nars_tuffy.metta":
        cases = (
            ("lookup", NW.LOOKUP, [NW.IMPORT_RESULT, NW.LOOKUP_RESULT]),
            ("ground", NW.GROUND_DEDUCTION,
             [NW.IMPORT_RESULT, NW.DEDUCTION_RESULT]),
            ("variable", NW.VARIABLE_DEDUCTION,
             [NW.IMPORT_RESULT, NW.DEDUCTION_RESULT]),
        )
        name = "nars-lookup+ground+variable"
    elif target == "pln_tuffy.metta":
        cases = (("variable", NW.PLN_VARIABLE_DEDUCTION,
                  [NW.IMPORT_RESULT, NW.PLN_DEDUCTION_RESULT]),)
        name = "pln-variable-deduction"
    else:
        return "", ""
    for _case_name, source, expected in cases:
        try:
            native, pleatta, status = NW.run_source(source, timeout)
        except (D.RunnerError, D.FuelExhausted, subprocess.TimeoutExpired):
            return name, "ERROR"
        want = normalized(expected)
        if status != "VALUE" or normalized(native) != want or normalized(pleatta) != want:
            return name, "DIFF-VALUE"
    return name, "AGREE-VALUE"


def read_existing(path: pathlib.Path) -> dict[str, tuple[str, ...]]:
    if not path.exists():
        return {}
    rows: dict[str, tuple[str, ...]] = {}
    for index, line in enumerate(path.read_text().splitlines()):
        fields = tuple(line.split("\t"))
        if index == 0 and fields == HEADER:
            continue
        if len(fields) == len(HEADER):
            rows[fields[0]] = fields
    return rows


def classify_semantics(direct: str, witness: str, name: str,
                       dependency: str, ledger: set[str]) -> str:
    # A host-effect file (non-empty dependency) that value-agrees was graded
    # through the certified host bridge -> trusted-host tier, never conflated
    # with certified-core equivalence.
    if direct == "WITNESS-AGREE":
        # bounded one-turn host witness (stdin/readln!) -> trusted-host tier
        return "TRUSTED-HOST-WITNESS-COVERED"
    if direct in AGREE:
        return "TRUSTED-HOST-COVERED" if dependency else "DIRECT-COVERED"
    if witness in AGREE or witness == "AGREE-VALUE":
        # A ledgered broken-oracle file whose corrected same-capability witness
        # agrees is oracle-witness-covered (capability demonstrated on both
        # engines); the original malformed pinned test stays adjudicated-broken.
        if direct == "PETTA-ERROR" and name in ledger:
            return "ORACLE-WITNESS-COVERED"
        return "WITNESS-COVERED"
    if direct in {"DIFF-VAL", "DIFF-COUNT"}:
        return "DIVERGENCE"
    if direct == "EXTERNAL-UNAVAILABLE":
        return "EXTERNAL-UNAVAILABLE"
    # Pinned oracle errored AND this file is in the evidence-backed ledger:
    # the pinned test is malformed and PLeaTTa is correct (adjudicated, not
    # claimed as coverage). A PETTA-ERROR without a ledger entry stays
    # oracle-unavailable so a real PLeaTTa problem cannot hide.
    if direct == "PETTA-ERROR" and name in ledger:
        return "BROKEN-ORACLE"
    if direct.startswith("PETTA-"):
        return "ORACLE-UNAVAILABLE"
    if direct in PERFORMANCE_RESULTS:
        return "PERFORMANCE-UNWITNESSED"
    return "ENGINE-GAP"


def measure(path: pathlib.Path, timeout: float,
            witnesses: dict[str, tuple[str, str]],
            ledger: set[str],
            host_registry: dict[str, dict]) -> tuple[str, ...]:
    text = path.read_text(errors="replace")
    surface, dependency = D.classify(text)
    independent = ""
    if surface == "OUT":
        entry = host_registry.get(path.name)
        if entry and entry["driver"] == "python-live":
            # Grade through the certified host bridge (real Python worker) vs
            # pinned PeTTa+Janus -> trusted-host tier.
            direct, pn, ln, _tx = HG.grade_python_live(path, entry["timeout"])
        elif entry and entry["driver"] == "stdin-replay":
            # Bounded one-turn readln! witness through the certified bridge
            # (live record then deterministic replay) -> trusted-host-witness.
            fixture = HOST_FIXTURE_DIR / f"{pathlib.Path(path.name).stem}.stdin.metta"
            direct, pn, ln = HG.grade_stdin_replay(fixture, entry["timeout"])
        elif entry and entry["driver"] == "swi-worker":
            # Prolog host effects (translatePredicate) through the certified
            # bridge + SWI-Prolog worker vs pinned PeTTa -> trusted-host tier.
            # The unified worker dispatches prologCall to swipl; PLeaTTa threads
            # the answer substitutions back through the certified reductions.
            direct, pn, ln, _tx = HG.grade_python_live(path, entry["timeout"])
        else:
            # Not registered: deferred external-unavailable.
            direct, pn, ln = "EXTERNAL-UNAVAILABLE", "", ""
    else:
        _name, _surface, _why, direct, pn, ln, independent = D.run_file(
            path, timeout=timeout, petta_timeout=timeout,
            leatta_timeout_multiplier=1,
        )

    witness_name = ""
    witness_verdict = ""
    if direct in PERFORMANCE_RESULTS:
        if path.name in witnesses:
            witness_name, source = witnesses[path.name]
            witness_verdict = run_generic_witness(witness_name, source, timeout)
        else:
            witness_name, witness_verdict = run_exact_witnesses(path.name, timeout)
    elif direct == "PETTA-ERROR" and path.name in ledger:
        witness_name = f"{pathlib.Path(path.name).stem}.witness"
        witness_verdict = run_oracle_witness(path.name, timeout)
    semantic = classify_semantics(
        direct, witness_verdict, path.name, dependency, ledger)
    return (
        path.name, dependency, direct, str(pn), str(ln), witness_name,
        witness_verdict, semantic, independent,
    )


def print_summary(rows: list[tuple[str, ...]], expected: int) -> int:
    total = len(rows)
    statuses = collections.Counter(row[7] for row in rows)
    core = [r for r in rows if not r[1]]          # certified-core (no host dep)
    host = [r for r in rows if r[1]]              # trusted-host tier
    core_direct = sum(1 for r in core if r[7] == "DIRECT-COVERED")
    core_witness = sum(1 for r in core if r[7] == "WITNESS-COVERED")
    core_owc = sum(1 for r in core if r[7] == "ORACLE-WITNESS-COVERED")
    core_broken = sum(1 for r in core if r[7] == "BROKEN-ORACLE")
    core_covered = core_direct + core_witness + core_owc
    host_covered = sum(1 for r in host if r[7] in
                       ("TRUSTED-HOST-COVERED", "TRUSTED-HOST-WITNESS-COVERED"))
    host_deferred = sum(1 for r in host if r[7] == "EXTERNAL-UNAVAILABLE")
    # "Adjudicated" = correctly disposed: certified-core covered + trusted-host
    # covered + broken-oracle (PLeaTTa correct, pinned test malformed). Broken-
    # oracle is reported separately and is NOT claimed as coverage.
    adjudicated = core_covered + host_covered + core_broken
    full_scale_incomplete = sum(
        1 for row in rows if row[2] in PERFORMANCE_RESULTS
    )
    print(f"\n# denominator: {total}/{expected} files assigned")
    print(f"# certified-core: {core_covered}/{len(core)} "
          f"({core_direct} direct + {core_witness} perf-witness + "
          f"{core_owc} oracle-witness); broken-oracle(unwitnessed)={core_broken}")
    print(f"# trusted-host: {host_covered}/{len(host)} bridge-graded; "
          f"deferred-external={host_deferred}")
    print(f"# operational (adjudicated): {adjudicated}/{total}")
    print(f"# full-scale performance outcomes: {full_scale_incomplete}")
    for status in (
        "DIVERGENCE", "ENGINE-GAP", "PERFORMANCE-UNWITNESSED",
        "ORACLE-WITNESS-COVERED", "BROKEN-ORACLE", "ORACLE-UNAVAILABLE",
        "TRUSTED-HOST-COVERED", "TRUSTED-HOST-WITNESS-COVERED",
        "EXTERNAL-UNAVAILABLE",
    ):
        print(f"# {status.lower()}: {statuses[status]}")
        for row in rows:
            if row[7] == status:
                detail = row[2]
                if row[8]:
                    detail += f", pleatta_independent={row[8]}"
                if row[6]:
                    detail += f", witness={row[6]}"
                if row[1]:
                    detail += f", dependency={row[1]}"
                print(f"#   {row[0]}: {detail}")
    if total != expected:
        print("# ERROR: corpus denominator mismatch", file=sys.stderr)
        return 2
    if statuses["DIVERGENCE"] or statuses["ENGINE-GAP"]:
        return 1
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--corpus", type=pathlib.Path,
        default=pathlib.Path(os.environ.get(
            "PETTA_DIR", str(pathlib.Path.home() / "repos/PeTTa"))) / "examples",
    )
    parser.add_argument("--timeout", type=float, default=30.0)
    parser.add_argument(
        "--manifest", type=pathlib.Path, default=DEFAULT_CORPUS_MANIFEST,
        help="ordered file-name manifest defining the denominator",
    )
    parser.add_argument(
        "--hashes", type=pathlib.Path, default=DEFAULT_CORPUS_HASHES,
        help="name<TAB>sha256 manifest ('-' permits external-file drift)",
    )
    parser.add_argument(
        "--expect-count", type=int, default=None,
        help="optional assertion on the selected manifest's denominator",
    )
    parser.add_argument(
        "--output", type=pathlib.Path,
        default=HERE / "coverage-official-current.tsv",
    )
    parser.add_argument(
        "--ledger", type=pathlib.Path, default=DEFAULT_ORACLE_LEDGER,
        help="evidence-backed broken-oracle ledger (file<TAB>reason...)",
    )
    parser.add_argument(
        "--host-registry", type=pathlib.Path, default=DEFAULT_HOST_REGISTRY,
        help="explicit host-case grading registry (file<TAB>driver<TAB>timeout<TAB>tier)",
    )
    parser.add_argument(
        "--resume", action="store_true",
        help="reuse complete rows already present in --output",
    )
    args = parser.parse_args()

    expected_names = [
        line.strip() for line in args.manifest.read_text().splitlines()
        if line.strip() and not line.startswith("#")
    ]
    if len(expected_names) != len(set(expected_names)):
        print("refusing manifest with duplicate names", file=sys.stderr)
        return 2
    if args.expect_count is not None and len(expected_names) != args.expect_count:
        print(
            f"refusing denominator {len(expected_names)}; "
            f"expected {args.expect_count}", file=sys.stderr,
        )
        return 2
    available = {
        path.name: path for path in args.corpus.glob("*.metta")
        if not path.name.startswith(".")
    }
    missing = [name for name in expected_names if name not in available]
    if missing:
        print(f"refusing partial corpus; missing={missing}", file=sys.stderr)
        return 2
    corpus = [available[name] for name in expected_names]
    expected_hashes = dict(
        line.split("\t", 1)
        for line in args.hashes.read_text().splitlines()
        if line.strip() and not line.startswith("#")
    )
    if set(expected_hashes) != set(expected_names):
        print("refusing hash manifest with a different name set", file=sys.stderr)
        return 2
    changed = [
        path.name for path in corpus
        if expected_hashes[path.name] != "-" and
        hashlib.sha256(path.read_bytes()).hexdigest()
        != expected_hashes.get(path.name)
    ]
    if changed:
        print(
            f"refusing changed corpus contents: {changed}",
            file=sys.stderr,
        )
        return 2

    prior = read_existing(args.output) if args.resume else {}
    rows: list[tuple[str, ...]] = []
    witnesses = generic_witnesses()
    ledger = read_ledger(args.ledger)
    host_registry = read_host_registry(args.host_registry)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w") as output:
        output.write("\t".join(HEADER) + "\n")
        output.flush()
        for index, path in enumerate(corpus, 1):
            row = prior.get(path.name)
            if row is None:
                row = measure(path, args.timeout, witnesses, ledger, host_registry)
            rows.append(row)
            line = "\t".join(row)
            output.write(line + "\n")
            output.flush()
            print(f"[{index}/{len(corpus)}]\t{line}", flush=True)
    return print_summary(rows, len(expected_names))


if __name__ == "__main__":
    raise SystemExit(main())
