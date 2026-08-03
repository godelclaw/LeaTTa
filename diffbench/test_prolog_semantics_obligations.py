#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Regression tests for fail-closed Prolog-semantics source guards."""

from __future__ import annotations

from pathlib import Path
import tempfile
import unittest
from unittest import mock

import prolog_semantics_obligations as obligations


class PacketFreeScheduledConsumerGuardTests(unittest.TestCase):
    @staticmethod
    def compatibility_source() -> str:
        legacy_carrier_occurrences = ["ScheduledPayloadState"] * 32
        adapter_occurrences = [
            "PersistentFreeScheduledPayloadState.ofLegacy"
        ] * 2
        return "\n".join(
            legacy_carrier_occurrences + adapter_occurrences)

    def check_tree(
        self,
        *,
        compatibility_suffix: str = "",
        other_sources: dict[str, str] | None = None,
    ) -> list[str]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            compatibility = (
                root / "PLeaTTa" / "Proofs" /
                "PrologHeterogeneousPrefixBridge.lean"
            )
            compatibility.parent.mkdir(parents=True)
            compatibility.write_text(
                self.compatibility_source() + compatibility_suffix,
                encoding="utf-8",
            )
            for relative, source in (other_sources or {}).items():
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source, encoding="utf-8")
            with (
                mock.patch.object(obligations, "ROOT", root),
                mock.patch.object(
                    obligations,
                    "PROLOG_HETEROGENEOUS_PREFIX_BRIDGE",
                    compatibility,
                ),
            ):
                return obligations.packet_free_scheduled_consumer_errors()

    def test_exact_compatibility_surface_passes(self) -> None:
        errors = self.check_tree(other_sources={
            "PLeaTTa/Proofs/AxiomAudit.lean":
                "#print axioms X.RepresentativeScheduledPayloadState\n"
                "#print axioms X.PersistentFreeScheduledPayloadState.ofLegacy\n",
            "PLeaTTa/Other.lean":
                "def native := RepresentativePersistentFreeScheduledPayloadState\n",
        })
        self.assertEqual(errors, [])

    def test_alias_laundering_inside_compatibility_module_fails(self) -> None:
        errors = self.check_tree(
            compatibility_suffix=
                "\nabbrev LegacySched := RepresentativeScheduledPayloadState\n")
        self.assertTrue(errors)
        self.assertIn("legacy scheduled carrier=33", errors[0])

    def test_consumer_inside_compatibility_module_fails(self) -> None:
        errors = self.check_tree(
            compatibility_suffix=
                "\ntheorem leaked (state : ScheduledPayloadState) : True := "
                "by trivial\n")
        self.assertTrue(errors)
        self.assertIn("legacy scheduled carrier=33", errors[0])

    def test_consumer_outside_prolog_proof_glob_fails(self) -> None:
        errors = self.check_tree(other_sources={
            "PLeaTTa/Runtime/HiddenConsumer.lean":
                "abbrev LegacySched := RepresentativeScheduledPayloadState\n",
        })
        self.assertTrue(errors)
        self.assertIn("PLeaTTa/Runtime/HiddenConsumer.lean", errors[0])


if __name__ == "__main__":
    unittest.main()
