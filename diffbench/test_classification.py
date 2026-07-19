#!/usr/bin/env python3

"""Regression checks for the coverage classifier's trust boundary."""

import unittest
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import diff


class ClassificationTests(unittest.TestCase):
    def assert_core(self, source: str) -> None:
        self.assertEqual(diff.classify(source), ("IN", ""))

    def assert_external(self, source: str, capability: str) -> None:
        self.assertEqual(diff.classify(source), ("OUT", capability))

    def test_state_and_spaces_are_core(self) -> None:
        self.assert_core("!(add-atom &self (a b))")
        self.assert_core("!(remove-atom &self (a b))")
        self.assert_core("!(bind! s (new-state x)) !(change-state! s y)")
        self.assert_core("!(match &self $x $x)")

    def test_local_import_repr_and_helpers_are_core(self) -> None:
        self.assert_core("!(import! &self ../lib/lib_he) !(repr x)")
        self.assert_core("!(assertEqual (+ 1 1) 2) !(trace! x true)")

    def test_external_hosts_are_narrowly_identified(self) -> None:
        self.assert_external("!(py-call (torch.tensor (1)))", "python-host")
        self.assert_external("!(git-import! \"https://example.invalid/x\")",
                             "git-network-plugin")
        self.assert_external("!(import_prolog_function hello)",
                             "prolog-host-ffi")
        self.assert_external("!(useGPT \"hello\")", "llm-python-host")
        self.assert_external("!(readln!)", "interactive-stdin")


if __name__ == "__main__":
    unittest.main()
