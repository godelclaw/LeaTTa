#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Unit checks for the compiler mismatch witness gate itself."""

from __future__ import annotations

import contextlib
import hashlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import compiler_mismatch_witnesses as witnesses


class CompilerMismatchWitnessGateTest(unittest.TestCase):
    def test_outcome_preserves_order_and_multiplicity(self) -> None:
        ordered = witnesses.Outcome("ok", ("first", "second", "second"))
        reversed_order = witnesses.Outcome(
            "ok", ("second", "second", "first"))
        deduplicated = witnesses.Outcome("ok", ("first", "second"))
        self.assertNotEqual(ordered, reversed_order)
        self.assertNotEqual(ordered, deduplicated)

    def test_stable_value_normalizes_generated_lambda_counter(self) -> None:
        self.assertEqual(witnesses.stable_value("(#lam381 7)"), "(#lamN 7)")

    def test_expected_requires_an_ordered_string_list(self) -> None:
        with self.assertRaises(ValueError):
            witnesses.expected("ok", '"not-a-list"')
        with self.assertRaises(ValueError):
            witnesses.expected("ok", '[1, 2]')

    def _run_synthetic_gate(
        self,
        *,
        manifest_rows: list[str],
        native: witnesses.Outcome,
        pleatta: witnesses.Outcome,
        ledger_compiler_hash: str | None = None,
    ) -> int:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fixture = root / "fixture.metta"
            fixture.write_text(
                ";; SPDX-License-Identifier: Apache-2.0\n!(unit)\n",
                encoding="utf-8",
            )
            compiler = root / "PLeaTTa" / "Compile.lean"
            compiler.parent.mkdir(parents=True)
            compiler.write_text("-- synthetic compiler\n", encoding="utf-8")
            compiler_hash = hashlib.sha256(compiler.read_bytes()).hexdigest()
            recorded_compiler_hash = ledger_compiler_hash or compiler_hash
            ledger = root / "compiler-obligations.tsv"
            ledger.write_text(
                "# pinned_petta_revision=test-pin\n"
                f"# compiler_sha256={recorded_compiler_hash}\n"
                "id\tstatus\n"
                "UNIT.fail\tFAIL\n",
                encoding="utf-8",
            )
            manifest = root / "compiler-mismatch-witnesses.tsv"
            manifest.write_text(
                "# pinned_petta_revision=test-pin\n"
                "id\tfixture\tmode\tnative_kind\tnative_expect\t"
                "pleatta_kind\tpleatta_expect\tnote\n"
                + "\n".join(manifest_rows)
                + "\n",
                encoding="utf-8",
            )

            def fake_run(runner, _fixture):
                if runner is witnesses.diff.petta_results:
                    return native
                return pleatta

            with (
                mock.patch.object(witnesses, "ROOT", root),
                mock.patch.object(witnesses, "LEDGER", ledger),
                mock.patch.object(witnesses, "MANIFEST", manifest),
                mock.patch.object(witnesses, "COMPILER", compiler),
                mock.patch.object(witnesses, "run", side_effect=fake_run),
                contextlib.redirect_stdout(io.StringIO()),
            ):
                return witnesses.main()

    def test_exact_divergence_is_green(self) -> None:
        row = (
            'UNIT.fail\tfixture.metta\texpected-divergence\tok\t["left"]'
            '\tok\t["right"]\tsynthetic'
        )
        self.assertEqual(
            self._run_synthetic_gate(
                manifest_rows=[row],
                native=witnesses.Outcome("ok", ("left",)),
                pleatta=witnesses.Outcome("ok", ("right",)),
            ),
            0,
        )

    def test_stale_expected_outcome_is_red(self) -> None:
        row = (
            'UNIT.fail\tfixture.metta\texpected-divergence\tok\t["old"]'
            '\tok\t["right"]\tsynthetic'
        )
        self.assertEqual(
            self._run_synthetic_gate(
                manifest_rows=[row],
                native=witnesses.Outcome("ok", ("new",)),
                pleatta=witnesses.Outcome("ok", ("right",)),
            ),
            1,
        )

    def test_equal_expected_divergence_is_red(self) -> None:
        row = (
            'UNIT.fail\tfixture.metta\texpected-divergence\tok\t["same"]'
            '\tok\t["same"]\tsynthetic'
        )
        self.assertEqual(
            self._run_synthetic_gate(
                manifest_rows=[row],
                native=witnesses.Outcome("ok", ("same",)),
                pleatta=witnesses.Outcome("ok", ("same",)),
            ),
            1,
        )

    def test_missing_fail_row_is_rejected(self) -> None:
        with self.assertRaisesRegex(SystemExit, "manifest drift"):
            self._run_synthetic_gate(
                manifest_rows=[],
                native=witnesses.Outcome("ok", ()),
                pleatta=witnesses.Outcome("ok", ()),
            )

    def test_stale_compiler_ledger_is_rejected(self) -> None:
        row = (
            'UNIT.fail\tfixture.metta\texpected-divergence\tok\t["left"]'
            '\tok\t["right"]\tsynthetic'
        )
        with self.assertRaisesRegex(SystemExit, "stale obligation ledger"):
            self._run_synthetic_gate(
                manifest_rows=[row],
                native=witnesses.Outcome("ok", ("left",)),
                pleatta=witnesses.Outcome("ok", ("right",)),
                ledger_compiler_hash="stale",
            )


if __name__ == "__main__":
    unittest.main()
