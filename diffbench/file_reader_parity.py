#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Differential gate for pinned PeTTa's source-file reader.

Unlike runtime ``sread``, the file loader first runs ``strip/3`` and then
``top_forms//2``.  These cases lock acceptance/rejection and ordered runnable
answers across that distinct path, including its escaped-quote quirks.
"""

from __future__ import annotations

import os
import pathlib
import tempfile

import diff as D


CASES = [
    ("empty", ""),
    ("only-blanks", " \t\r\n"),
    ("top-atom-rejected", "foo\n"),
    ("top-number-rejected", "42\n"),
    ("top-string-rejected", '"hello"\n'),
    ("stored-form", "(foo)\n"),
    ("runnable", "!(foo)\n"),
    ("bang-space-rejected", "! (foo)\n"),
    ("tight-forms", "(a)(b)\n"),
    ("nested", "(a (b c))\n"),
    ("comment-line", "; comment\n(a)\n"),
    ("comment-tail", "(a) ; tail\n!(b)\n"),
    ("comment-at-eof", "(a) ; tail"),
    ("comment-newline-is-removed", "!; comment\n(foo)\n"),
    ("semicolon-in-string", '(show "a;b")\n'),
    ("parenthesis-in-string", '(show "(a)")\n'),
    ("escaped-quote-semicolon", '(show "a\\\";b")\n'),
    ("escaped-quote-parenthesis", '(show "a\\\")b" x)\n'),
    ("escaped-backslash-before-close", '(show "a\\\\" x)\n'),
    ("escaped-backslash-semicolon-tail", '(show "a\\\\"; tail\n(b)\n'),
    ("trailing-junk-rejected", "(a) junk\n"),
    ("missing-close-rejected", "(a\n"),
    ("extra-close-rejected", "(a))\n"),
]


def _outcome(runner, path: pathlib.Path):
    try:
        values = runner(path, 60)
        if values is None:
            return ("bad-output", ())
        return ("ok", tuple(D.normalize(value) for value in values))
    except D.RunnerError:
        return ("rejected", ())


def main() -> int:
    failures = []
    old_allow = os.environ.get("PLEATTA_PINNED_ALLOW_EXTERNAL")
    os.environ["PLEATTA_PINNED_ALLOW_EXTERNAL"] = "1"
    try:
        with tempfile.TemporaryDirectory(prefix="pleatta-file-reader-parity-") as td:
            fixture = pathlib.Path(td) / "reader-case.metta"
            for name, source in CASES:
                fixture.write_text(source, encoding="utf-8")
                native = _outcome(D.petta_results, fixture)
                pleatta = _outcome(D.leatta_results, fixture)
                if native != pleatta:
                    failures.append((name, source, native, pleatta))
    finally:
        if old_allow is None:
            os.environ.pop("PLEATTA_PINNED_ALLOW_EXTERNAL", None)
        else:
            os.environ["PLEATTA_PINNED_ALLOW_EXTERNAL"] = old_allow

    if failures:
        for name, source, native, pleatta in failures:
            print(f"FAIL {name}: {source!r}")
            print(f"  PeTTa:   {native}")
            print(f"  PLeaTTa: {pleatta}")
        return 1

    print(f"OK: {len(CASES)}/{len(CASES)} source-reader cases match pinned PeTTa")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
