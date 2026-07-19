#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0

"""Value-sensitive NARS/PLN witnesses against the pinned PeTTa oracle.

Agreement alone is insufficient here: both engines can leave `NARS.Query`
unreduced. These probes require the concrete truth value and evidence stamp.
"""

from __future__ import annotations

import collections
import os
import pathlib
import subprocess
import sys
import tempfile

sys.path.insert(0, str(pathlib.Path(__file__).parent))
import diff as D  # noqa: E402


EXAMPLES = pathlib.Path(
    os.environ.get("PETTA_DIR", str(pathlib.Path.home() / "repos/PeTTa"))
) / "examples"

IMPORT_RESULT = "true"
DEDUCTION_RESULT = "((stv 0.6 0.486) (2 10))"
LOOKUP_RESULT = "((stv 1 0.9) (10))"
PLN_DEDUCTION_RESULT = "((stv 0.6 0.81) (2 10))"


LOOKUP = """!(import! &self ../lib/lib_nars)

(= (kb)
   ((Sentence ((--> Edward ([] smokes)) (stv 1.0 0.9)) (10))))

!(NARS.Query (kb) (--> Edward ([] smokes)) 0 4 4)
"""


GROUND_DEDUCTION = """!(import! &self ../lib/lib_nars)

(= (kb)
   ((Sentence ((--> Edward ([] smokes)) (stv 1.0 0.9)) (10))
    (Sentence ((--> ([] smokes) ([] cancerous)) (stv 0.6 0.9)) (2))))

!(NARS.Query (kb) (--> Edward ([] cancerous)) 1 4 4)
"""


VARIABLE_DEDUCTION = """!(import! &self ../lib/lib_nars)

(= (kb)
   ((Sentence ((--> Edward ([] smokes)) (stv 1.0 0.9)) (10))
    (Sentence ((==> (--> $1 ([] smokes))
                    (--> $1 ([] cancerous)))
               (stv 0.6 0.9)) (2))))

!(NARS.Query (kb) (--> Edward ([] cancerous)) 1 4 4)
"""


PLN_VARIABLE_DEDUCTION = """!(import! &self ../lib/lib_pln)

(= (kb)
   ((Sentence ((Inheritance Edward Smokes) (stv 1.0 0.9)) (10))
    (Sentence ((Implication (Inheritance $1 Smokes)
                            (Inheritance $1 Cancerous))
               (stv 0.6 0.9)) (2))))

!(PLN.Query (kb) (Inheritance Edward Cancerous) 1 4 4)
"""


def normalized(items: list[str] | None) -> collections.Counter[str] | None:
    if items is None:
        return None
    return collections.Counter(D.normalize(item) for item in items)


def run_source(source: str, timeout: float) -> tuple[list[str], list[str] | None, str]:
    with tempfile.NamedTemporaryFile(
        "w", suffix=".metta", prefix=".nars-witness-", dir=EXAMPLES, delete=False
    ) as handle:
        handle.write(D.transform(source))
        path = pathlib.Path(handle.name)
    try:
        native = D.petta_results(path, timeout)
        try:
            pleatta = D.leatta_results(path, timeout)
            status = "VALUE" if pleatta is not None else "NOOUT"
        except subprocess.TimeoutExpired:
            pleatta = None
            status = "TIMEOUT"
        except D.FuelExhausted:
            pleatta = None
            status = "EXHAUSTED"
        except D.RunnerError as error:
            pleatta = None
            status = f"ERROR-{error.returncode}"
        return native, pleatta, status
    finally:
        path.unlink(missing_ok=True)


def check_closed(name: str, source: str, expected: list[str]) -> bool:
    native, pleatta, status = run_source(source, 15)
    want = normalized(expected)
    native_ok = normalized(native) == want
    pleatta_ok = normalized(pleatta) == want
    verdict = "PASS" if native_ok and pleatta_ok else "FAIL"
    print(f"{name}\t{verdict}\tnative={native}\tpleatta={pleatta}\tstatus={status}")
    return native_ok and pleatta_ok


def main() -> int:
    ok = check_closed(
        "nars-lookup", LOOKUP, [IMPORT_RESULT, LOOKUP_RESULT]
    )
    ok &= check_closed(
        "nars-ground-deduction", GROUND_DEDUCTION,
        [IMPORT_RESULT, DEDUCTION_RESULT],
    )
    ok &= check_closed(
        "nars-variable-deduction", VARIABLE_DEDUCTION,
        [IMPORT_RESULT, DEDUCTION_RESULT],
    )
    ok &= check_closed(
        "pln-variable-deduction", PLN_VARIABLE_DEDUCTION,
        [IMPORT_RESULT, PLN_DEDUCTION_RESULT],
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
