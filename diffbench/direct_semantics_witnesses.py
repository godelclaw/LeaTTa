#!/usr/bin/env python3

"""Unrewritten PeTTa helper-form witnesses against the pinned oracle.

The main corpus lane rewrites diagnostic helpers to expose the values they
test. These probes complement it by sending the original source to both
engines and discarding only explicitly expected host-output lines.
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

CASES = [
    (
        "test-singleton",
        "(= (twice $x) (+ $x $x))\n!(test (twice 21) 42)\n",
        [],
        ["true"],
    ),
    (
        "test-collected",
        "!(test (superpose (1 2)) (1 2))\n",
        [],
        ["true"],
    ),
    (
        "trace-value",
        "!(trace! pleatta-trace-marker (+ 1 2))\n",
        ["pleatta-trace-marker"],
        ["3"],
    ),
    (
        "println-value",
        "!(println! pleatta-println-marker)\n",
        ["pleatta-println-marker"],
        ["true"],
    ),
    (
        "identity-equality-open-terms",
        """!(== (p $x) (p $x))
!(== (p $x) (p $y))
!(== (p $x) (q $x))
""",
        [],
        ["true", "false", "false"],
    ),
    (
        "if2-open-condition-is-identity",
        "!(collapse (if $condition 42))\n",
        [],
        ["()"],
    ),
    (
        "let-star-valid-source-order",
        "!(let* (($x 1) ($y (+ $x 2))) (+ $x $y))\n",
        [],
        ["4"],
    ),
    (
        "current-list-fallbacks",
        """!(car-atom ())
!(cdr-atom ())
!(car-atom not-a-list)
!(cdr-atom not-a-list)
""",
        [],
        ["()", "()", "()", "()"],
    ),
    (
        "short-circuit-booleans",
        """!(and-then False (empty))
!(or-else True (empty))
!(and-then True 42)
!(or-else False 43)
""",
        [],
        ["false", "true", "42", "43"],
    ),
    (
        "short-circuit-branch-effect-order",
        """!(bind! and-order-state initial)
!(let expected
    (and-then True
      (progn (change-state! and-order-state changed) actual))
    unreachable)
!(get-state and-order-state)
!(bind! or-order-state initial)
!(let expected
    (or-else False
      (progn (change-state! or-order-state changed) actual))
    unreachable)
!(get-state or-order-state)
""",
        [],
        ["changed", "changed"],
    ),
    (
        "chain-source-effect-order",
        """!(bind! chain-order-state (new-state initial))
!(chain
    (progn (change-state! chain-order-state first) Same)
    (progn (change-state! chain-order-state second) $x)
    (get-state chain-order-state))
""",
        [],
        ["true", "second"],
    ),
    (
        "quoted-binders-remain-data",
        """!(quote (|-> () 42))
!(quote (nested (|-> () 42)))
""",
        [],
        ["(|-> () 42)", "(nested (|-> () 42))"],
    ),
    (
        "translator-add-remove",
        """(= (compile42 $arg) (quote (cons 42 $arg)))
!(add-translator-rule! compile42)
!(compile42 (43))
!(remove-translator-rule! compile42)
!(compile42 (43))
""",
        [],
        ["true", "(42 43)", "true", "(cons 42 (43))"],
    ),
    (
        "transaction-commit-rollback",
        """!(add-atom &tx (value 1))
!(transaction (progn (remove-atom &tx (value 1))
                      (add-atom &tx (value 2))))
!(collapse (get-atoms &tx))
!(transaction (progn (remove-atom &tx (value 2)) (empty)))
!(collapse (get-atoms &tx))
""",
        [],
        ["true", "true", "((value 2))", "((value 2))"],
    ),
]


def normalized(items: list[str]) -> collections.Counter[str]:
    return collections.Counter(D.normalize(item) for item in items)


def run_case(
    name: str, source: str, native_noise: list[str], expected: list[str]
) -> bool:
    with tempfile.NamedTemporaryFile(
        "w", suffix=".metta", prefix=".direct-semantics-",
        dir=EXAMPLES, delete=False
    ) as handle:
        handle.write(source)
        path = pathlib.Path(handle.name)
    try:
        native = D.petta_results(path, 15)
        noise = normalized(native_noise)
        for item, count in noise.items():
            for _ in range(count):
                try:
                    native.remove(next(x for x in native if D.normalize(x) == item))
                except (StopIteration, ValueError):
                    break
        pleatta = D.leatta_results(path, 15)
        want = normalized(expected)
        ok = pleatta is not None and normalized(native) == want and normalized(pleatta) == want
        print(
            f"{name}\t{'PASS' if ok else 'FAIL'}\t"
            f"native={native}\tpleatta={pleatta}"
        )
        return ok
    except (D.RunnerError, D.FuelExhausted, subprocess.TimeoutExpired) as error:
        print(f"{name}\tFAIL\t{type(error).__name__}: {error}")
        return False
    finally:
        path.unlink(missing_ok=True)


def main() -> int:
    ok = True
    for case in CASES:
        ok &= run_case(*case)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
