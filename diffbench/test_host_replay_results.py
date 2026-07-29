#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0

"""Regression checks for deterministic host-replay differential results."""

from pathlib import Path
import sys
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import diff


class HostReplayResultsTests(unittest.TestCase):
    def test_replay_uses_typed_host_mode_and_shared_result_parser(self) -> None:
        fixture = Path("fixture.metta")
        transcript = Path("fixture.replay.json")
        with mock.patch.object(
            diff, "run_grouped", return_value=("[matched, matched]", "", 0)
        ) as run:
            self.assertEqual(
                diff.leatta_replay_results(fixture, transcript, timeout=17),
                ["matched", "matched"],
            )
        run.assert_called_once_with(
            diff.LEATTA_BASE + [
                "--host-replay",
                str(fixture),
                str(transcript),
                "4000000",
            ],
            17,
        )

    def test_replay_preserves_empty_answer_bag(self) -> None:
        with mock.patch.object(
            diff, "run_grouped", return_value=("[]", "", 0)
        ):
            self.assertEqual(
                diff.leatta_replay_results(
                    Path("fixture.metta"),
                    Path("fixture.replay.json"),
                    timeout=17,
                ),
                [],
            )


if __name__ == "__main__":
    unittest.main()
