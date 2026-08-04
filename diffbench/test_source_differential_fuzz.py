#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0

"""Unit checks for deterministic source differential generation."""

from __future__ import annotations

from collections import Counter
import unittest
from unittest import mock

import source_differential_fuzz as fuzz


class StableRngTest(unittest.TestCase):
    def test_same_seed_has_same_stream(self) -> None:
        left = fuzz.StableRng(123)
        right = fuzz.StableRng(123)
        self.assertEqual(
            [left.next_u64() for _ in range(20)],
            [right.next_u64() for _ in range(20)],
        )

    def test_case_seed_separates_indices(self) -> None:
        self.assertNotEqual(fuzz.case_seed(7, 2), fuzz.case_seed(7, 3))


class GeneratorTest(unittest.TestCase):
    def test_generation_is_reproducible_by_case_index(self) -> None:
        first = fuzz.generate_case(42, 17)
        second = fuzz.generate_case(42, 17)
        self.assertEqual(first, second)
        self.assertEqual(first.render(), second.render())

    def test_generated_fragment_has_a_well_shaped_ground_anchor(self) -> None:
        for index in range(256):
            case = fuzz.generate_case(0, index)
            self.assertTrue(case.well_shaped())
            self.assertTrue(case.clauses)
            self.assertTrue(case.queries)
            self.assertTrue(all(term.is_ground() for term in case.queries[0]))

    def test_every_case_has_a_real_matching_query(self) -> None:
        for index in range(128):
            case = fuzz.generate_case(99, index)
            first_query = case.queries[0]
            first_head = case.clauses[0].head
            self.assertTrue(fuzz.pattern_matches(first_head, first_query))

    def test_repeated_pattern_variable_requires_one_ground_value(self) -> None:
        pattern = (fuzz.Term.variable("$x"), fuzz.Term.variable("$x"))
        self.assertTrue(fuzz.pattern_matches(
            pattern, (fuzz.Term.atom("a"), fuzz.Term.atom("a"))))
        self.assertFalse(fuzz.pattern_matches(
            pattern, (fuzz.Term.atom("a"), fuzz.Term.atom("b"))))

    def test_linearization_gives_each_query_occurrence_a_fresh_name(self) -> None:
        query = (
            fuzz.Term.variable("$x"),
            fuzz.Term.compound("tag", (fuzz.Term.variable("$x"),)),
            fuzz.Term.variable("$y"),
        )
        linear = fuzz.linearize_query_variables(query)
        self.assertTrue(fuzz.query_is_linear(linear))
        self.assertEqual(
            tuple(name for term in linear for name in term.variable_occurrences()),
            ("$q0", "$q1", "$q2"),
        )

    def test_generated_open_queries_are_linear(self) -> None:
        for index in range(256):
            case = fuzz.generate_case(2, index)
            self.assertTrue(all(
                fuzz.query_is_linear(query) for query in case.queries[1:]))

    def test_supported_fragment_rejects_aliased_open_query(self) -> None:
        variable = fuzz.Term.variable("$z")
        case = fuzz.ProgramCase(
            clauses=(fuzz.Clause(
                (
                    fuzz.Term.compound("tag", (fuzz.Term.variable("$x"),)),
                    fuzz.Term.variable("$x"),
                ),
                fuzz.DataBody((fuzz.Term.atom("accepted"),)),
            ),),
            queries=(
                (fuzz.Term.compound("tag", (fuzz.Term.atom("b"),)),
                 fuzz.Term.atom("b")),
                (variable, fuzz.Term.compound("tag", (variable,))),
            ),
            chain_depth=0,
        )
        self.assertFalse(fuzz.query_is_linear(case.queries[1]))
        self.assertFalse(case.well_shaped())

    def test_render_has_license_rules_and_queries(self) -> None:
        source = fuzz.generate_case(1, 0).render()
        self.assertTrue(source.startswith("; SPDX-License-Identifier: Apache-2.0"))
        self.assertIn("(= (fz0", source)
        self.assertIn("!(fz", source)

    def test_compound_data_body_is_quoted_directly(self) -> None:
        body = fuzz.DataBody((fuzz.Term.compound(
            "callee", (fuzz.Term.variable("$x"),)),))
        self.assertEqual(body.render(), "(quote (callee $x))")

    def test_well_shaped_rejects_a_non_data_body_type(self) -> None:
        class CallBody:
            pass

        case = fuzz.ProgramCase(
            clauses=(fuzz.Clause(
                (fuzz.Term.variable("$x"),),
                CallBody(),  # type: ignore[arg-type]
            ),),
            queries=((fuzz.Term.atom("a"),),),
            chain_depth=0,
        )
        self.assertFalse(case.well_shaped())

    def test_well_shaped_rejects_a_foreign_open_query_namespace(self) -> None:
        case = fuzz.ProgramCase(
            clauses=(fuzz.Clause(
                (fuzz.Term.variable("$x"),),
                fuzz.DataBody((fuzz.Term.atom("accepted"),)),
            ),),
            queries=(
                (fuzz.Term.atom("a"),),
                (fuzz.Term.variable("$foreign"),),
            ),
            chain_depth=0,
        )
        self.assertTrue(fuzz.query_is_linear(case.queries[1]))
        self.assertFalse(case.well_shaped())

    def test_simplifications_are_strict_smaller_and_unique(self) -> None:
        case = fuzz.generate_case(5, 11)
        candidates = case.simplifications()
        self.assertTrue(candidates)
        self.assertEqual(len(candidates), len({item.render() for item in candidates}))
        self.assertTrue(all(item.size() < case.size() for item in candidates))
        self.assertTrue(all(item.well_shaped() for item in candidates))

    def test_fixed_gate_covers_every_required_shape(self) -> None:
        observed: Counter[str] = Counter()
        for index in range(128):
            observed.update(fuzz.case_features(fuzz.generate_case(0, index)))
        self.assertFalse({
            name: (observed[name], minimum)
            for name, minimum in fuzz.REQUIRED_FEATURE_MINIMUMS.items()
            if observed[name] < minimum
        })


class ComparisonTest(unittest.TestCase):
    def test_exact_agreement(self) -> None:
        observed = fuzz.Comparison(
            fuzz.Outcome("ok", ("first", "second", "second")),
            fuzz.Outcome("ok", ("first", "second", "second")),
        )
        self.assertIsNone(observed.mismatch_class())

    def test_order_is_observable(self) -> None:
        observed = fuzz.Comparison(
            fuzz.Outcome("ok", ("first", "second", "second")),
            fuzz.Outcome("ok", ("second", "second", "first")),
        )
        self.assertEqual(observed.mismatch_class(), "answer-order")

    def test_multiplicity_is_observable(self) -> None:
        observed = fuzz.Comparison(
            fuzz.Outcome("ok", ("first", "second", "second")),
            fuzz.Outcome("ok", ("first", "second")),
        )
        self.assertEqual(observed.mismatch_class(), "answer-multiplicity")

    def test_same_length_different_values_are_observable(self) -> None:
        observed = fuzz.Comparison(
            fuzz.Outcome("ok", ("first", "second")),
            fuzz.Outcome("ok", ("first", "third")),
        )
        self.assertEqual(observed.mismatch_class(), "answer-value")

    def test_matching_errors_are_not_accepted(self) -> None:
        observed = fuzz.Comparison(
            fuzz.Outcome("runner-error", "same"),
            fuzz.Outcome("runner-error", "same"),
        )
        self.assertEqual(
            observed.mismatch_class(),
            "status:runner-error:'same':runner-error:'same'",
        )

    def test_error_payload_is_part_of_shrink_signature(self) -> None:
        left = fuzz.Comparison(
            fuzz.Outcome("runner-error", "first"),
            fuzz.Outcome("ok", ()),
        )
        right = fuzz.Comparison(
            fuzz.Outcome("runner-error", "second"),
            fuzz.Outcome("ok", ()),
        )
        self.assertNotEqual(left.mismatch_class(), right.mismatch_class())

    def test_shrinker_makes_strict_progress_without_changing_class(self) -> None:
        case = fuzz.ProgramCase(
            clauses=(
                fuzz.Clause(
                    (fuzz.Term.variable("$x"),),
                    fuzz.DataBody((fuzz.Term.variable("$x"),)),
                ),
                fuzz.Clause(
                    (fuzz.Term.variable("$x"),),
                    fuzz.DataBody((fuzz.Term.atom("extra"),)),
                ),
            ),
            queries=((fuzz.Term.atom("a"),),),
            chain_depth=1,
        )
        mismatch = fuzz.Comparison(
            fuzz.Outcome("ok", ("left", "right")),
            fuzz.Outcome("ok", ("right", "left")),
        )
        with mock.patch.object(fuzz, "evaluate", return_value=mismatch):
            minimized, observed, attempts = fuzz.minimize(
                case, mismatch, timeout=1, max_attempts=50)
        self.assertLess(minimized.size(), case.size())
        self.assertEqual(observed.mismatch_class(), "answer-order")
        self.assertGreater(attempts, 0)


if __name__ == "__main__":
    unittest.main()
