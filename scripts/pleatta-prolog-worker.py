#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Provenance-visible SWI-Prolog worker for PLeaTTa's trusted-host tier.

Reads JSON-stdio requests, evaluates a single (translatePredicate-lowered)
Prolog goal against PeTTa's predicate library, and returns the ordered answer
substitutions.  This backs `translatePredicate`; the surrounding PeTTa
reductions remain certified, only the Prolog result is trusted.

Boundary:
  * consult is restricted to one configured PeTTa source file;
  * predicates are callable by default, matching pinned PeTTa;
  * an operator may install an explicit direct-call deny filter, inference
    limit, or wall-clock timeout without confusing them with certification or
    a complete Prolog sandbox;
  * this worker is only ever launched in LIVE grading -- replay reads the
    recorded transcript and never launches swipl.

Request  (one JSON object per line):
  {"goal": "<functor>", "args": [<term>...], "vars": ["X", ...]}
  An optional positive "limit" applies an inference limit to this request.
Response (one JSON object per line):
  {"id": .., "answers": [ {"X": <term>, ...}, ... ]}   # ordered substitution bag
  {"id": .., "error": "<kind>"}
A <term> is one of: {"int": n} | {"float": bits} | {"atom": s} | {"str": s}
                  | {"var": "X"} | {"list": [term...]} |
                    {"compound": [functor, arg...]}
"""
import ast
import json
import os
import re
import struct
import subprocess
import sys

SWIPL = os.environ.get("PLEATTA_SWIPL", "swipl")
PROLOG_LIB = os.environ.get(
    "PLEATTA_PROLOG_LIB",
    os.path.join(
        os.environ.get("PLEATTA_CACHE_DIR",
                       os.path.join(os.path.expanduser("~"), ".cache", "pleatta")),
        "petta-6b7f52f064bdbc82fabd0a0998404121fb01d52e", "src", "metta.pl"))


def _csv_policy(name):
    """Read an explicit comma-separated policy set; blank means no policy."""
    return {
        item.strip()
        for item in os.environ.get(name, "").split(",")
        if item.strip()
    }


def _goal_denied(functor, arity):
    """An opt-in direct-call filter, deliberately separate from proof scope.

    Entries may name every arity of a functor (``shell``) or one exact
    predicate indicator (``shell/1``).  The default set is empty.  This checks
    only the requested outer functor: Prolog meta-calls and dynamically built
    goals require process isolation if they are an actual security boundary.
    """
    denied = _csv_policy("PLEATTA_PROLOG_DENY")
    return functor in denied or f"{functor}/{arity}" in denied


def _optional_positive_int(value, label):
    if value is None or str(value).strip() == "":
        return None
    parsed = int(value)
    if parsed <= 0:
        raise ValueError(f"{label} must be a positive integer")
    return parsed


def _optional_positive_float(value, label):
    if value is None or str(value).strip() == "":
        return None
    parsed = float(value)
    if parsed <= 0:
        raise ValueError(f"{label} must be positive")
    return parsed


def term_to_prolog(term, varmap):
    """Render a JSON term as SWI source text, allocating fresh Prolog vars."""
    if "int" in term:
        return str(term["int"])
    if "float" in term:
        return repr(struct.unpack("<d", struct.pack("<Q", term["float"]))[0])
    if "atom" in term:
        return "'" + str(term["atom"]).replace("\\", "\\\\").replace("'", "\\'") + "'"
    if "str" in term:
        return '"' + str(term["str"]).replace("\\", "\\\\").replace('"', '\\"') + '"'
    if "var" in term:
        name = term["var"]
        # PLeaTTa variables may contain characters (for example the freshening
        # suffix in `NL#r42`) that are not legal in a Prolog variable token.
        # Keep the source name only as protocol metadata and allocate a private,
        # capture-free Prolog identifier for the generated query.
        varmap.setdefault(name, f"V{len(varmap)}")
        return varmap[name]
    if "list" in term:
        return "[" + ",".join(
            term_to_prolog(x, varmap) for x in term["list"]) + "]"
    if "compound" in term:
        f, *a = term["compound"]
        return term_to_prolog({"atom": f}, varmap) + "(" + \
            ",".join(term_to_prolog(x, varmap) for x in a) + ")"
    raise ValueError("bad term")


def _compound_open(text):
    """Return the first top-level compound `(`, excluding quoted text."""
    quote = None
    escaped = False
    for index, char in enumerate(text):
        if quote is not None:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == quote:
                quote = None
            continue
        if char in {"'", '"'}:
            quote = char
        elif char == "(":
            return index
    return None


def _parse_value(text):
    """Parse a canonical Prolog value into the typed protocol term tree."""
    text = text.strip()
    if not text:
        raise ValueError("empty Prolog value")
    if text.startswith("[") and text.endswith("]"):
        body = text[1:-1].strip()
        if not body:
            return {"list": []}
        if len(_split_top_level(body, "|")) != 1:
            raise ValueError("improper Prolog lists are unsupported")
        return {"list": [
            _parse_value(item) for item in _split_top_level(body, ",")
        ]}
    compound_open = _compound_open(text)
    if compound_open is not None and text.endswith(")"):
        functor_term = _parse_value(text[:compound_open])
        if "atom" not in functor_term:
            raise ValueError("compound functor is not an atom")
        body = text[compound_open + 1:-1].strip()
        args = [] if not body else [
            _parse_value(item) for item in _split_top_level(body, ",")
        ]
        return {"compound": [functor_term["atom"], *args]}
    try:
        return {"int": int(text)}
    except ValueError:
        pass
    try:
        return {"float": struct.unpack("<Q", struct.pack("<d", float(text)))[0]}
    except ValueError:
        pass
    if len(text) >= 2 and text[0] == text[-1] and text[0] in {"'", '"'}:
        try:
            kind = "str" if text[0] == '"' else "atom"
            return {kind: ast.literal_eval(text)}
        except (SyntaxError, ValueError):
            pass
    if re.fullmatch(r"[_A-Z][A-Za-z0-9_]*", text):
        return {"var": text}
    return {"atom": text.strip("'")}


def _split_top_level(text, separator):
    """Split a canonical Prolog term outside quotes and nested structures."""
    result = []
    start = 0
    depth = 0
    quote = None
    escaped = False
    for index, char in enumerate(text):
        if quote is not None:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == quote:
                quote = None
            continue
        if char in {"'", '"'}:
            quote = char
        elif char in "([{" :
            depth += 1
        elif char in ")]}":
            depth -= 1
        elif char == separator and depth == 0:
            result.append(text[start:index])
            start = index + 1
    result.append(text[start:])
    return result


def solve(req):
    """Run one goal and return its ordered answer substitution bag.

    Pinned PeTTa imposes no predicate allowlist, inference cap, or timeout.
    PLeaTTa therefore defaults to the same behaviour.  Operators may opt into
    each resource/safety policy explicitly; those policies do not alter the
    certification boundary and are reported separately as runtime policy.
    """
    import tempfile
    varmap = {}
    functor = str(req["goal"])
    libraries = [os.path.realpath(path) for path in req.get("libraries", [])]
    arguments = req.get("args", [])
    arity = len(arguments)
    if _goal_denied(functor, arity):
        return {"error": f"predicate-denied:{functor}/{arity}"}
    if any(not os.path.isfile(path) for path in libraries):
        return {"error": "consult-file-missing"}
    args = ",".join(term_to_prolog(a, varmap) for a in arguments)
    goal = f"'{functor}'({args})" if args else f"'{functor}'"
    wanted = req.get("vars", list(varmap.keys()))
    for v in wanted:
        varmap.setdefault(v, f"V{len(varmap)}")
    limit = _optional_positive_int(
        req.get("limit", os.environ.get("PLEATTA_PROLOG_INFERENCE_LIMIT")),
        "Prolog inference limit")
    timeout = _optional_positive_float(
        os.environ.get("PLEATTA_PROLOG_TIMEOUT_SECONDS"),
        "Prolog timeout")
    binds = ",".join(
        f"{term_to_prolog({'atom': v}, varmap)}={varmap[v]}" for v in wanted
    ) if wanted else ""
    # findall preserves answer order+multiplicity; each answer is one binding
    # list rendered with term_to_atom and parsed back on this side.
    consults = ",\n    ".join(
        f"consult({term_to_prolog({'atom': path}, {})})"
        for path in libraries)
    if consults:
        consults = consults + ",\n    "
    invoked_goal = f"({goal})"
    if limit is not None:
        invoked_goal = (
            f"(call_with_inference_limit(({goal}), {limit}, LimitResult), "
            "(LimitResult == inference_limit_exceeded -> "
            "throw(inference_limit_exceeded) ; true))")
    script = f""":- initialization(main).
main :-
    ( exists_file('{PROLOG_LIB}') -> catch(consult('{PROLOG_LIB}'), _, true) ; true ),
    {consults}
    catch(
      ( findall(A,
          ( {invoked_goal},
            term_to_atom([{binds}], A) ), As),
        forall(member(A, As), (write('ANS:'), write(A), nl)) ),
      E, (write('ERR:'), write_canonical(E), nl)),
    halt(0).
"""
    fh = tempfile.NamedTemporaryFile("w", suffix=".pl", delete=False,
                                     prefix=".pleatta-prolog-")
    fh.write(script)
    fh.close()
    try:
        p = subprocess.run([SWIPL, "-q", fh.name],
                           capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return {"error": "timeout"}
    finally:
        os.unlink(fh.name)
    if p.returncode != 0:
        return {"error": "prolog-failed"}
    answers = []
    for line in p.stdout.splitlines():
        if line.startswith("ERR:"):
            return {"error": "prolog-exception"}
        if not line.startswith("ANS:"):
            continue
        inner = line[4:].strip()
        binding = {}
        if inner.startswith("[") and inner.endswith("]"):
            body = inner[1:-1].strip()
            if body:
                for part in _split_top_level(body, ","):
                    if "=" in part:
                        k, v = _split_top_level(part, "=")[:2]
                        binding[k.strip().strip("'")] = \
                            _parse_value(v)
        answers.append(binding)
    return {"answers": answers}


def main():
    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        try:
            req = json.loads(line)
            out = solve(req)
            out["id"] = req.get("id")
        except Exception as exc:  # noqa: BLE001 -- report, never crash the loop
            out = {"error": f"worker:{type(exc).__name__}"}
        sys.stdout.write(json.dumps(out) + "\n")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
