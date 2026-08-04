#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0

"""Deterministic source-shaped differential generation against pinned PeTTa.

The generated fragment is deliberately small and terminating: ordered local
clauses, finite first-order patterns, quoted result data, finite `superpose`,
and acyclic identity-only forwarding calls.  Every case contains a ground
query constructed from a real clause head; additional queries may be open but
are linear (each query variable occurs once).  Together with data-only clause
bodies, these constraints structurally exclude rational-tree-only head
matches, which have their own exact expected-divergence fixture, while an
all-dead random corpus still cannot pass as useful coverage.

Successful runs compare the exact normalized answer sequence.  Order and
multiplicity are therefore observable; this does not use the corpus harness's
order-insensitive fallback.  A runner error, timeout, fuel exhaustion, or
malformed result is a failing generated case even when both engines fail.

Generation is stable by `(seed, case-index)`.  On failure a bounded structural
shrinker preserves the mismatch class and prints a standalone reproducer.
Generated programs are ephemeral unless `--write-failure` is requested.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass, replace
from pathlib import Path
import os
import subprocess
import sys
import tempfile
from typing import Callable, Iterable, Sequence


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "diffbench"))
import compiler_mismatch_witnesses as mismatch  # noqa: E402
import diff  # noqa: E402


MASK64 = (1 << 64) - 1
GOLDEN_GAMMA = 0x9E3779B97F4A7C15


class StableRng:
    """Small SplitMix64 generator whose output is independent of Python RNG."""

    def __init__(self, seed: int):
        self.state = seed & MASK64

    def next_u64(self) -> int:
        self.state = (self.state + GOLDEN_GAMMA) & MASK64
        value = self.state
        value = ((value ^ (value >> 30)) * 0xBF58476D1CE4E5B9) & MASK64
        value = ((value ^ (value >> 27)) * 0x94D049BB133111EB) & MASK64
        return (value ^ (value >> 31)) & MASK64

    def below(self, bound: int) -> int:
        if bound <= 0:
            raise ValueError("bound must be positive")
        return self.next_u64() % bound

    def choice(self, values: Sequence):
        if not values:
            raise ValueError("cannot choose from an empty sequence")
        return values[self.below(len(values))]

    def chance(self, numerator: int, denominator: int) -> bool:
        if not 0 <= numerator <= denominator or denominator <= 0:
            raise ValueError("invalid probability")
        return self.below(denominator) < numerator


@dataclass(frozen=True)
class Term:
    kind: str
    name: str
    children: tuple["Term", ...] = ()

    @staticmethod
    def atom(name: str) -> "Term":
        return Term("atom", name)

    @staticmethod
    def integer(value: int) -> "Term":
        return Term("integer", str(value))

    @staticmethod
    def variable(name: str) -> "Term":
        return Term("variable", name)

    @staticmethod
    def compound(name: str, children: Iterable["Term"]) -> "Term":
        return Term("compound", name, tuple(children))

    def render(self) -> str:
        if self.kind == "compound":
            return f"({self.name} {' '.join(child.render() for child in self.children)})"
        return self.name

    def variables(self) -> tuple[str, ...]:
        if self.kind == "variable":
            return (self.name,)
        result: list[str] = []
        for child in self.children:
            for name in child.variables():
                if name not in result:
                    result.append(name)
        return tuple(result)

    def variable_occurrences(self) -> tuple[str, ...]:
        if self.kind == "variable":
            return (self.name,)
        return tuple(
            name
            for child in self.children
            for name in child.variable_occurrences()
        )

    def is_ground(self) -> bool:
        return self.kind != "variable" and all(
            child.is_ground() for child in self.children)

    def size(self) -> int:
        return 1 + sum(child.size() for child in self.children)

    def simplifications(self, *, ground: bool) -> tuple["Term", ...]:
        candidates: list[Term] = []
        if self.kind == "compound":
            candidates.append(Term.atom("a"))
            for index, child in enumerate(self.children):
                for simpler in child.simplifications(ground=ground):
                    changed = list(self.children)
                    changed[index] = simpler
                    candidates.append(Term.compound(self.name, changed))
        elif self.kind == "integer" and self.name != "0":
            candidates.append(Term.integer(0))
        elif self.kind == "atom" and self.name != "a":
            candidates.append(Term.atom("a"))
        elif self.kind == "variable" and not ground and self.name != "$x":
            candidates.append(Term.variable("$x"))
        return unique_terms(candidates)


def unique_terms(items: Iterable[Term]) -> tuple[Term, ...]:
    seen: set[Term] = set()
    result: list[Term] = []
    for item in items:
        if item not in seen:
            seen.add(item)
            result.append(item)
    return tuple(result)


@dataclass(frozen=True)
class DataBody:
    """An inert result body; this type has no local-call constructor."""

    values: tuple[Term, ...]
    nondeterministic: bool = False

    def render_value(self, value: Term) -> str:
        if value.kind == "compound":
            return f"(quote {value.render()})"
        return value.render()

    def render(self) -> str:
        rendered = tuple(self.render_value(value) for value in self.values)
        if self.nondeterministic:
            return f"(superpose ({' '.join(rendered)}))"
        return rendered[0]

    def size(self) -> int:
        return 1 + sum(value.size() for value in self.values)

    def simplifications(self) -> tuple["DataBody", ...]:
        candidates: list[DataBody] = []
        if self.nondeterministic:
            for index in range(len(self.values)):
                reduced = self.values[:index] + self.values[index + 1:]
                if reduced:
                    candidates.append(DataBody(reduced, len(reduced) > 1))
            candidates.append(DataBody((self.values[0],), False))
        for index, value in enumerate(self.values):
            for simpler in value.simplifications(ground=False):
                changed = list(self.values)
                changed[index] = simpler
                candidates.append(DataBody(tuple(changed), self.nondeterministic))
        if self != DataBody((Term.atom("out"),), False):
            candidates.append(DataBody((Term.atom("out"),), False))
        return unique_bodies(candidates)


def unique_bodies(items: Iterable[DataBody]) -> tuple[DataBody, ...]:
    seen: set[DataBody] = set()
    result: list[DataBody] = []
    for item in items:
        if item not in seen:
            seen.add(item)
            result.append(item)
    return tuple(result)


@dataclass(frozen=True)
class Clause:
    head: tuple[Term, ...]
    body: DataBody

    def render(self, predicate: str) -> str:
        arguments = "" if not self.head else " " + " ".join(
            term.render() for term in self.head)
        return f"(= ({predicate}{arguments}) {self.body.render()})"

    def size(self) -> int:
        return 1 + sum(term.size() for term in self.head) + self.body.size()

    def simplifications(self) -> tuple["Clause", ...]:
        candidates: list[Clause] = []
        for index, term in enumerate(self.head):
            for simpler in term.simplifications(ground=False):
                changed = list(self.head)
                changed[index] = simpler
                candidates.append(replace(self, head=tuple(changed)))
        candidates.extend(replace(self, body=body) for body in self.body.simplifications())
        return tuple(dict.fromkeys(candidates))


@dataclass(frozen=True)
class ProgramCase:
    clauses: tuple[Clause, ...]
    queries: tuple[tuple[Term, ...], ...]
    chain_depth: int

    def render(self) -> str:
        lines = ["; SPDX-License-Identifier: Apache-2.0", ""]
        lines.extend(clause.render("fz0") for clause in self.clauses)
        relay_variables = tuple(
            Term.variable(f"$r{index}") for index in range(self.arity))
        relay_args = "" if not relay_variables else " " + " ".join(
            variable.render() for variable in relay_variables)
        for depth in range(1, self.chain_depth + 1):
            lines.append(
                f"(= (fz{depth}{relay_args}) (fz{depth - 1}{relay_args}))")
        lines.append("")
        target = f"fz{self.chain_depth}"
        for query in self.queries:
            arguments = "" if not query else " " + " ".join(
                term.render() for term in query)
            lines.append(f"!({target}{arguments})")
        return "\n".join(lines) + "\n"

    @property
    def arity(self) -> int:
        return len(self.clauses[0].head)

    def size(self) -> int:
        return (
            self.chain_depth + len(self.clauses) + len(self.queries)
            + sum(clause.size() for clause in self.clauses)
            + sum(term.size() for query in self.queries for term in query)
        )

    def well_shaped(self) -> bool:
        return (
            bool(self.clauses)
            and bool(self.queries)
            and all(len(clause.head) == self.arity for clause in self.clauses)
            and all(len(query) == self.arity for query in self.queries)
            and all(type(clause.body) is DataBody for clause in self.clauses)
            and all(
                all(term.is_ground() for term in query)
                if index == 0 else (
                    query_is_linear(query)
                    and query_uses_query_namespace(query)
                )
                for index, query in enumerate(self.queries)
            )
            and pattern_matches(self.clauses[0].head, self.queries[0])
        )

    def simplifications(self) -> tuple["ProgramCase", ...]:
        candidates: list[ProgramCase] = []
        if len(self.clauses) > 1:
            for index in range(len(self.clauses)):
                candidates.append(replace(
                    self, clauses=self.clauses[:index] + self.clauses[index + 1:]))
        if len(self.queries) > 1:
            for index in range(len(self.queries)):
                candidates.append(replace(
                    self, queries=self.queries[:index] + self.queries[index + 1:]))
        if self.chain_depth:
            candidates.append(replace(self, chain_depth=self.chain_depth - 1))
        for index, clause in enumerate(self.clauses):
            for simpler in clause.simplifications():
                changed = list(self.clauses)
                changed[index] = simpler
                candidates.append(replace(self, clauses=tuple(changed)))
        for query_index, query in enumerate(self.queries):
            for term_index, term in enumerate(query):
                for simpler in term.simplifications(ground=query_index == 0):
                    changed_query = list(query)
                    changed_query[term_index] = simpler
                    changed_queries = list(self.queries)
                    changed_queries[query_index] = tuple(changed_query)
                    candidates.append(replace(self, queries=tuple(changed_queries)))
        unique: dict[str, ProgramCase] = {}
        for candidate in candidates:
            if candidate.well_shaped() and candidate.size() < self.size():
                unique.setdefault(candidate.render(), candidate)
        return tuple(sorted(unique.values(), key=lambda item: (item.size(), item.render())))


def pattern_matches(pattern: tuple[Term, ...], ground: tuple[Term, ...]) -> bool:
    """Check that `ground` is an instance of the finite first-order pattern."""
    if len(pattern) != len(ground) or not all(term.is_ground() for term in ground):
        return False
    bindings: dict[str, Term] = {}

    def match(left: Term, right: Term) -> bool:
        if left.kind == "variable":
            previous = bindings.setdefault(left.name, right)
            return previous == right
        if left.kind != right.kind or left.name != right.name:
            return False
        return len(left.children) == len(right.children) and all(
            match(lchild, rchild)
            for lchild, rchild in zip(left.children, right.children)
        )

    return all(match(left, right) for left, right in zip(pattern, ground))


def query_is_linear(query: tuple[Term, ...]) -> bool:
    """True when no source query variable occurs more than once.

    Clause variables are standardized apart from query variables.  Orienting
    query/head equations with this linear query on the left therefore gives a
    left-linear system with an empty dependency relation, the sufficient
    occur-check-freedom criterion of Apt--Pellegrini's NSTO Lemma 2.9.
    """
    occurrences = [
        name for term in query for name in term.variable_occurrences()
    ]
    return len(occurrences) == len(set(occurrences))


def query_uses_query_namespace(query: tuple[Term, ...]) -> bool:
    """Keep query identities syntactically apart from clause and relay names."""
    names = {
        name
        for term in query
        for name in term.variable_occurrences()
    }
    return (
        all(name.startswith("$q") for name in names)
        and CLAUSE_VARIABLE_NAMES.isdisjoint(names)
    )


def linearize_query_variables(query: tuple[Term, ...]) -> tuple[Term, ...]:
    """Give every variable occurrence a distinct, deterministic source name."""
    next_index = 0

    def linearize(term: Term) -> Term:
        nonlocal next_index
        if term.kind == "variable":
            result = Term.variable(f"$q{next_index}")
            next_index += 1
            return result
        if term.kind == "compound":
            return Term.compound(
                term.name, (linearize(child) for child in term.children))
        return term

    return tuple(linearize(term) for term in query)


PATTERN_ATOMS = tuple(Term.atom(name) for name in ("a", "b", "c", "red", "blue"))
GROUND_ATOMS = PATTERN_ATOMS + tuple(Term.integer(value) for value in range(3))
VARIABLES = tuple(Term.variable(name) for name in ("$x", "$y", "$z"))
CLAUSE_VARIABLE_NAMES = frozenset(
    variable.name for variable in VARIABLES) | {"$u"}
CONSTRUCTORS = (("tag", 1), ("box", 1), ("pair", 2), ("node", 2))


def generated_term(
    rng: StableRng, *, depth: int, allow_variables: bool,
) -> Term:
    leaves = GROUND_ATOMS + (VARIABLES if allow_variables else ())
    if depth <= 0 or rng.chance(3, 5):
        return rng.choice(leaves)
    name, arity = rng.choice(CONSTRUCTORS)
    return Term.compound(
        name,
        (generated_term(
            rng, depth=depth - 1, allow_variables=allow_variables)
         for _ in range(arity)),
    )


def result_term(rng: StableRng, variables: tuple[str, ...]) -> Term:
    variable_terms = tuple(Term.variable(name) for name in variables)
    if variable_terms and rng.chance(2, 5):
        return rng.choice(variable_terms)
    if rng.chance(1, 10):
        return Term.variable("$u")
    if rng.chance(1, 2):
        return rng.choice(GROUND_ATOMS)
    children: list[Term] = []
    for _ in range(1 + rng.below(2)):
        pool = GROUND_ATOMS + variable_terms + (Term.variable("$u"),)
        children.append(rng.choice(pool))
    return Term.compound(rng.choice(("result", "pair", "seen")), children)


def generated_clause(rng: StableRng, arity: int) -> Clause:
    head = list(generated_term(
        rng, depth=2, allow_variables=True) for _ in range(arity))
    if head and rng.chance(1, 6):
        repeated = rng.choice(VARIABLES)
        first = rng.below(arity)
        if arity == 1:
            head[first] = Term.compound("pair", (repeated, repeated))
        else:
            second = (first + 1 + rng.below(arity - 1)) % arity
            head[first] = repeated
            head[second] = repeated
    fixed_head = tuple(head)
    variables: list[str] = []
    for term in fixed_head:
        for name in term.variables():
            if name not in variables:
                variables.append(name)
    count = 2 + rng.below(2) if rng.chance(1, 4) else 1
    values = tuple(result_term(rng, tuple(variables)) for _ in range(count))
    if len(values) > 1 and rng.chance(1, 4):
        values = values[:-1] + (values[0],)
    return Clause(fixed_head, DataBody(values, len(values) > 1))


def ground_instance(
    terms: tuple[Term, ...], rng: StableRng,
) -> tuple[Term, ...]:
    assignment: dict[str, Term] = {}

    def ground(term: Term) -> Term:
        if term.kind == "variable":
            assignment.setdefault(term.name, rng.choice(GROUND_ATOMS))
            return assignment[term.name]
        if term.kind == "compound":
            return Term.compound(term.name, (ground(child) for child in term.children))
        return term

    return tuple(ground(term) for term in terms)


def case_seed(seed: int, index: int) -> int:
    return (seed + (index + 1) * GOLDEN_GAMMA) & MASK64


def generate_case(seed: int, index: int) -> ProgramCase:
    rng = StableRng(case_seed(seed, index))
    arity = rng.below(4)
    clauses: list[Clause] = []
    for _ in range(1 + rng.below(5)):
        if clauses and rng.chance(1, 5):
            clauses.append(rng.choice(tuple(clauses)))
        else:
            clauses.append(generated_clause(rng, arity))
    queries = [ground_instance(clauses[0].head, rng)]
    for _ in range(rng.below(3)):
        allow_variables = rng.chance(1, 3)
        query = tuple(generated_term(
            rng, depth=2, allow_variables=allow_variables) for _ in range(arity))
        queries.append(linearize_query_variables(query))
    case = ProgramCase(tuple(clauses), tuple(queries), rng.below(3))
    if not case.well_shaped():
        raise AssertionError("generator produced a malformed case")
    return case


REQUIRED_FEATURE_MINIMUMS = {
    "compound-pattern": 8,
    "duplicate-branch": 8,
    "duplicate-clause": 8,
    "multi-clause": 8,
    "multi-query": 8,
    "nested-call": 8,
    "nondeterministic-body": 8,
    "nullary-call": 8,
    "open-query": 15,
    "repeated-head-variable": 15,
    "unbound-result-variable": 8,
}


def case_features(case: ProgramCase) -> set[str]:
    features: set[str] = {"matched-ground-query"}
    if case.arity == 0:
        features.add("nullary-call")
    if len(case.clauses) > 1:
        features.add("multi-clause")
    if len(set(case.clauses)) < len(case.clauses):
        features.add("duplicate-clause")
    if len(case.queries) > 1:
        features.add("multi-query")
    if any(
        not term.is_ground()
        for query in case.queries[1:]
        for term in query
    ):
        features.add("open-query")
    if case.chain_depth:
        features.add("nested-call")
    for clause in case.clauses:
        if any(term.kind == "compound" for term in clause.head):
            features.add("compound-pattern")
        head_variables = [
            name for term in clause.head for name in term.variables()
        ]
        if len(head_variables) != len(set(head_variables)):
            features.add("repeated-head-variable")
        if clause.body.nondeterministic:
            features.add("nondeterministic-body")
        if len(set(clause.body.values)) < len(clause.body.values):
            features.add("duplicate-branch")
        body_variables = {
            name for value in clause.body.values for name in value.variables()
        }
        if body_variables - set(head_variables):
            features.add("unbound-result-variable")
    return features


@dataclass(frozen=True)
class Outcome:
    kind: str
    payload: tuple[str, ...] | str

    def render(self) -> str:
        return f"{self.kind}:{self.payload!r}"


@dataclass(frozen=True)
class Comparison:
    native: Outcome
    pleatta: Outcome

    def mismatch_class(self) -> str | None:
        if self.native.kind != "ok" or self.pleatta.kind != "ok":
            return (
                f"status:{self.native.kind}:{self.native.payload!r}:"
                f"{self.pleatta.kind}:{self.pleatta.payload!r}"
            )
        native = tuple(self.native.payload)
        pleatta = tuple(self.pleatta.payload)
        if native == pleatta:
            return None
        if Counter(native) == Counter(pleatta):
            return "answer-order"
        if len(native) == len(pleatta):
            return "answer-value"
        return "answer-multiplicity"


def execute(runner: Callable, path: Path, timeout: float) -> Outcome:
    try:
        values = runner(path, timeout=timeout)
        if values is None:
            return Outcome("malformed-output", "")
        return Outcome("ok", tuple(mismatch.stable_value(value) for value in values))
    except diff.FuelExhausted:
        return Outcome("fuel-exhausted", "")
    except subprocess.TimeoutExpired:
        return Outcome("timeout", "")
    except diff.RunnerError as error:
        return Outcome("runner-error", mismatch.classify_runner_error(error))


def evaluate(case: ProgramCase, timeout: float) -> Comparison:
    with tempfile.TemporaryDirectory(prefix="pleatta-source-fuzz-") as raw:
        path = Path(raw) / "case.metta"
        path.write_text(case.render(), encoding="utf-8")
        native = execute(diff.petta_results, path, timeout)
        pleatta = execute(diff.leatta_results, path, timeout)
    return Comparison(native, pleatta)


def minimize(
    case: ProgramCase,
    comparison: Comparison,
    timeout: float,
    max_attempts: int,
) -> tuple[ProgramCase, Comparison, int]:
    mismatch_class = comparison.mismatch_class()
    if mismatch_class is None:
        return case, comparison, 0
    current = case
    current_comparison = comparison
    attempts = 0
    while attempts < max_attempts:
        improved = False
        for candidate in current.simplifications():
            if attempts >= max_attempts:
                break
            attempts += 1
            observed = evaluate(candidate, timeout)
            if observed.mismatch_class() == mismatch_class:
                current = candidate
                current_comparison = observed
                improved = True
                break
        if not improved:
            break
    return current, current_comparison, attempts


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--count", type=int, default=128)
    parser.add_argument("--start-index", type=int, default=0)
    parser.add_argument("--case-index", type=int)
    parser.add_argument("--timeout", type=float, default=10.0)
    parser.add_argument("--max-shrinks", type=int, default=200)
    parser.add_argument("--keep-going", action="store_true")
    parser.add_argument("--write-failure", type=Path)
    parser.add_argument("--require-feature-coverage", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.count <= 0:
        raise SystemExit("--count must be positive")
    if args.timeout <= 0:
        raise SystemExit("--timeout must be positive")
    if args.max_shrinks < 0:
        raise SystemExit("--max-shrinks must be nonnegative")
    if args.start_index < 0 or (
        args.case_index is not None and args.case_index < 0
    ):
        raise SystemExit("case indices must be nonnegative")
    os.environ["PLEATTA_PINNED_ALLOW_EXTERNAL"] = "1"

    indices = (
        [args.case_index]
        if args.case_index is not None
        else range(args.start_index, args.start_index + args.count)
    )
    failures = 0
    completed = 0
    feature_counts: Counter[str] = Counter()
    for index in indices:
        case = generate_case(args.seed, index)
        feature_counts.update(case_features(case))
        observed = evaluate(case, args.timeout)
        mismatch_class = observed.mismatch_class()
        completed += 1
        if mismatch_class is None:
            if completed % 32 == 0:
                print(f"source-differential-fuzz: {completed} cases agree", flush=True)
            continue

        failures += 1
        minimized, final, attempts = minimize(
            case, observed, args.timeout, args.max_shrinks)
        print(
            f"SOURCE DIFFERENTIAL MISMATCH seed={args.seed} index={index} "
            f"class={mismatch_class} original_size={case.size()} "
            f"minimized_size={minimized.size()} shrink_attempts={attempts}",
            file=sys.stderr,
        )
        print(f"native={final.native.render()}", file=sys.stderr)
        print(f"pleatta={final.pleatta.render()}", file=sys.stderr)
        print("--- minimized source ---", file=sys.stderr)
        print(minimized.render(), file=sys.stderr, end="")
        if args.write_failure is not None:
            target = args.write_failure
            if failures > 1 or args.keep_going:
                target = target.with_name(
                    f"{target.stem}-{args.seed}-{index}{target.suffix or '.metta'}")
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(minimized.render(), encoding="utf-8")
            print(f"wrote minimized failure: {target}", file=sys.stderr)
        if not args.keep_going:
            break

    if failures:
        print(
            f"source-differential-fuzz: FAIL; {failures} mismatch(es) in "
            f"{completed} generated cases",
            file=sys.stderr,
        )
        return 1
    undercovered = {
        name: (feature_counts[name], minimum)
        for name, minimum in REQUIRED_FEATURE_MINIMUMS.items()
        if feature_counts[name] < minimum
    }
    if args.require_feature_coverage and undercovered:
        print(
            "source-differential-fuzz: FAIL; generated corpus under-covered "
            f"required features {undercovered}",
            file=sys.stderr,
        )
        return 1
    feature_summary = ",".join(
        f"{name}={feature_counts[name]}" for name in sorted(feature_counts)
    )
    print(
        f"source-differential-fuzz: PASS; {completed} exact ordered cases "
        f"agree (seed={args.seed}); features: {feature_summary}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
