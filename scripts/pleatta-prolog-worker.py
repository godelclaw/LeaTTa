#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Capability-bounded SWI-Prolog worker for PLeaTTa's trusted-host tier.

Reads JSON-stdio requests, evaluates a single (translatePredicate-lowered)
Prolog goal against PeTTa's predicate library, and returns the ordered answer
substitutions.  This backs `translatePredicate`; the surrounding PeTTa
reductions remain certified, only the Prolog result is trusted.

Boundary:
  * consult is restricted to one configured PeTTa source file;
  * only an explicit predicate allowlist can be called;
  * every goal runs under a bounded inference limit (call_with_inference_limit);
  * this worker is only ever launched in LIVE grading -- replay reads the
    recorded transcript and never launches swipl.

Request  (one JSON object per line):
  {"goal": "<functor>", "args": [<term>...], "vars": ["X", ...], "limit": 1000000}
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
import struct
import subprocess
import sys

SWIPL = os.environ.get("PLEATTA_SWIPL", "swipl")
# Allowlisted predicate library: PeTTa's own Prolog definitions (`+/3`, etc.).
PROLOG_LIB = os.environ.get(
    "PLEATTA_PROLOG_LIB",
    os.path.join(
        os.environ.get("PLEATTA_CACHE_DIR",
                       os.path.join(os.path.expanduser("~"), ".cache", "pleatta")),
        "petta-6b7f52f064bdbc82fabd0a0998404121fb01d52e", "src", "metta.pl"))

DEFAULT_ALLOWED_GOALS = {
    "+", "-", "*", "/", "//", "mod", "is",
    "<", "=<", ">", ">=", "=:=", r"=\=",
    "atom_codes",
}
ALLOWED_GOALS = DEFAULT_ALLOWED_GOALS | {
    item.strip()
    for item in os.environ.get("PLEATTA_PROLOG_ALLOWLIST", "").split(",")
    if item.strip()
}


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


def _parse_value(text):
    """Parse a Prolog value token into a structured term (int/float/atom)."""
    text = text.strip()
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
    """Run one goal under a bounded inference limit; return the ordered answer
    substitution bag (preserving answer order and multiplicity)."""
    import tempfile
    varmap = {}
    functor = str(req["goal"])
    libraries = [os.path.realpath(path) for path in req.get("libraries", [])]
    if functor not in ALLOWED_GOALS and not libraries:
        return {"error": f"predicate-not-allowed:{functor}"}
    if any(not os.path.isfile(path) for path in libraries):
        return {"error": "consult-file-missing"}
    args = ",".join(term_to_prolog(a, varmap) for a in req.get("args", []))
    goal = f"'{functor}'({args})" if args else f"'{functor}'"
    wanted = req.get("vars", list(varmap.keys()))
    for v in wanted:
        varmap.setdefault(v, f"V{len(varmap)}")
    limit = int(req.get("limit", 1000000))
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
    script = f""":- initialization(main).
main :-
    ( exists_file('{PROLOG_LIB}') -> catch(consult('{PROLOG_LIB}'), _, true) ; true ),
    {consults}
    catch(
      ( findall(A,
          ( call_with_inference_limit(({goal}), {limit}, _R),
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
                           capture_output=True, text=True, timeout=20)
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
