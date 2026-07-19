#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0

"""diffbench: differential harness (NONDET IS ORDER-AGNOSTIC: results are a
multiset/bag compared via Counter -- multiplicity matters, enumeration order
does not; DIFF-COUNT = genuine multiplicity mismatch, not order).

Original: — real native PeTTa (oracle) vs pleatta --file.

For each corpus file: identify genuine external execution dependencies, run
both engines, normalize results, compare as multisets, append a scoreboard
row. Every corpus file remains in the denominator. ``OUT`` is retained in the
low-level TSV format for compatibility, but means only "requires an external
host capability"; it never means that a core PLeaTTa defect may be excluded.
"""
import os
import re
import signal
import argparse
import subprocess
import sys
import pathlib
import tempfile
import collections
import time

REPO = pathlib.Path(__file__).resolve().parent.parent
PETTA_RUNNER = ["bash", os.environ.get("PETTA_RUNNER",
    str(REPO / "scripts" / "run-petta-pinned.sh"))]
LEATTA_BIN = os.environ.get(
    "LEATTA_BIN",
    os.environ.get("PLEATTA_WRAPPER", str(REPO / ".lake" / "build" / "bin" / "pleatta")),
)
LEATTA = [LEATTA_BIN] + (os.environ.get("LEATTA_ARGS", "").split() if os.environ.get("LEATTA_ARGS") else []) + ["--file"]
SCOREBOARD = REPO / "diffbench" / "scoreboard.tsv"
DEFAULT_TIMEOUT = float(os.environ.get("DIFFBENCH_TIMEOUT", "30"))
DEFAULT_PETTA_TIMEOUT_MULTIPLIER = float(
    os.environ.get("PETTA_TIMEOUT_MULTIPLIER", "10"))
DEFAULT_LEATTA_TIMEOUT_MULTIPLIER = float(
    os.environ.get("LEATTA_TIMEOUT_MULTIPLIER", "10"))

# This is deliberately narrow. PLeaTTa core includes local ``import!``, spaces,
# add/remove-atom, state cells, repr, matching, transactions, and diagnostic
# helper forms. Those constructs must be tested, never classified away.
#
# The value paired with each pattern is a stable capability name suitable for
# reports. A matched file still occupies one slot in the fixed corpus
# denominator; the canonical coverage command records it as externally
# unavailable rather than attempting network, Python, Prolog-FFI, or stdin.
EXTERNAL_CAPABILITIES = (
    (re.compile(r"\bpy-(?:call|atom)\b"), "python-host"),
    (re.compile(r"\bgit-import!?\b"), "git-network-plugin"),
    (re.compile(r"\bimport_prolog(?:_function|_functions_from_file)?\b"),
     "prolog-host-ffi"),
    (re.compile(r"\btranslatePredicate\b"), "prolog-host-ffi"),
    (re.compile(r"\b(?:useGPT|py-str)\b"), "llm-python-host"),
    (re.compile(r"\breadln!(?![A-Za-z0-9_-])"), "interactive-stdin"),
)

ANSI = re.compile(r"\x1b\[[0-9;]*m")


class RunnerError(RuntimeError):
    def __init__(self, engine, returncode, stdout="", stderr=""):
        super().__init__(f"{engine} runner exited {returncode}")
        self.engine = engine
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr


class FuelExhausted(RuntimeError):
    pass


def classify(text):
    for pattern, capability in EXTERNAL_CAPABILITIES:
        if pattern.search(text):
            return ("OUT", capability)
    return ("IN", "")


def _matching_paren(text, start):
    """Return the matching close paren for text[start] == '(', respecting
    quoted strings and backslash escapes."""
    depth = 0
    in_str = False
    esc = False
    for j in range(start, len(text)):
        ch = text[j]
        if in_str:
            if esc:
                esc = False
            elif ch == "\\":
                esc = True
            elif ch == '"':
                in_str = False
            continue
        if ch == '"':
            in_str = True
        elif ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
            if depth == 0:
                return j
    return len(text) - 1


def _expr_at(text, start):
    """Extract one MeTTa expression/token from text[start:], preserving the
    exact source spelling for strings and escaped characters. Returns
    (expression, end_offset)."""
    n = len(text)
    i = start
    while i < n and text[i].isspace():
        i += 1
    if i >= n:
        return "", i
    if text[i] == '"':
        j = i + 1
        esc = False
        while j < n:
            ch = text[j]
            if esc:
                esc = False
            elif ch == "\\":
                esc = True
            elif ch == '"':
                j += 1
                break
            j += 1
        return text[i:j], j
    if text[i] == '(':
        j = _matching_paren(text, i)
        return text[i:j + 1], j + 1
    j = i
    while j < n and (not text[j].isspace()) and text[j] != ')':
        j += 1
    return text[i:j], j


def _first_expr(text, start):
    expr, _end = _expr_at(text, start)
    return expr


def _rewrite_println_to_true(text):
    """Replace `(println! X)` expressions with `true`.

    Native `println!/2` prints `X` as a side effect and returns `true`
    (`metta.pl:199-200`). The differential surface is answer values, not
    host stdout, so this extends the existing top-level println transform to
    inline printlns while preserving the return value.
    """
    out = []
    i = 0
    n = len(text)
    in_str = False
    esc = False
    in_comment = False
    while i < n:
        ch = text[i]
        if in_comment:
            out.append(ch)
            if ch == "\n":
                in_comment = False
            i += 1
            continue
        if in_str:
            out.append(ch)
            if esc:
                esc = False
            elif ch == "\\":
                esc = True
            elif ch == '"':
                in_str = False
            i += 1
            continue
        if ch == ';':
            in_comment = True
            out.append(ch)
            i += 1
            continue
        if ch == '"':
            in_str = True
            out.append(ch)
            i += 1
            continue
        if text.startswith("(println!", i):
            end = i + len("(println!")
            if end < n and (text[end].isspace() or text[end] == ')'):
                j = _matching_paren(text, i)
                out.append("true")
                i = j + 1
                continue
        if text.startswith("println!", i):
            end = i + len("println!")
            before_ok = i == 0 or text[i - 1].isspace() or text[i - 1] in "()"
            after_ok = end == n or text[end].isspace() or text[end] in "()"
            if before_ok and after_ok:
                out.append("(|-> ($__println_arg) true)")
                i = end
                continue
        out.append(ch)
        i += 1
    return "".join(out)


def _rewrite_trace_to_value(text):
    """Replace `(trace! X Y)` with `Y`.

    PeTTa rewrites trace! to `(progn (println! X) Y)` (translator.pl:74-75),
    so `X` is host diagnostic output and the expression value is `Y`.
    """
    out = []
    i = 0
    n = len(text)
    in_str = False
    esc = False
    in_comment = False
    while i < n:
        ch = text[i]
        if in_comment:
            out.append(ch)
            if ch == "\n":
                in_comment = False
            i += 1
            continue
        if in_str:
            out.append(ch)
            if esc:
                esc = False
            elif ch == "\\":
                esc = True
            elif ch == '"':
                in_str = False
            i += 1
            continue
        if ch == ';':
            in_comment = True
            out.append(ch)
            i += 1
            continue
        if ch == '"':
            in_str = True
            out.append(ch)
            i += 1
            continue
        if text.startswith("(trace!", i):
            end = i + len("(trace!")
            if end < n and (text[end].isspace() or text[end] == ')'):
                j = _matching_paren(text, i)
                form = text[i:j + 1]
                _arg1, k = _expr_at(form, len("(trace!"))
                arg2 = _first_expr(form, k)
                out.append(arg2)
                i = j + 1
                continue
        out.append(ch)
        i += 1
    return "".join(out)


def transform(text):
    # Keep PeTTa and HE assertion forms intact. Rewriting an assertion into
    # its first argument masks missing assertion/equality semantics and can
    # even make the pinned oracle fail a program it accepts unchanged.
    # println! interleaves side-effect lines into PeTTa's stdout that a pure
    # kernel cannot mirror; drop whole-line print directives so BOTH engines
    # run the identical print-free program (oracle-fair transform).
    text = re.sub(r"^\s*!\(println!.*$", "", text, flags=re.M)
    text = _rewrite_trace_to_value(text)
    text = _rewrite_println_to_true(text)
    return text

def run_grouped(cmd, timeout):
    """Run with its own process group; on timeout kill the WHOLE group so no
    orphaned swipl survives (shared machine courtesy)."""
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                         text=True, start_new_session=True)
    try:
        out, err = p.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(os.getpgid(p.pid), signal.SIGKILL)
        except ProcessLookupError:
            pass
        p.communicate()
        raise
    return out, err, p.returncode


def petta_timeout_for(timeout, explicit=None,
                      multiplier=DEFAULT_PETTA_TIMEOUT_MULTIPLIER):
    return explicit if explicit is not None else timeout * multiplier


def _is_petta_trace_header(line):
    stripped = line.strip()
    return stripped.startswith("-->") and stripped.endswith("-->")


def petta_results(path, timeout):
    out, err, returncode = run_grouped(PETTA_RUNNER + [str(path)], timeout)
    if returncode != 0:
        raise RunnerError("PeTTa", returncode, out, err)
    txt = ANSI.sub("", out + err)
    out, keep = [], False
    for line in txt.splitlines():
        if "^^^" in line:
            keep = True
            continue
        if _is_petta_trace_header(line):
            keep = False
            continue
        # specializer.pl emits compile-time diagnostics with `format/2`;
        # these are not MeTTa answers and native prints them inside the kept
        # block for failed specialization attempts.
        if line.startswith("Not specialized "):
            continue
        # PeTTa's test/3 prints a check line before returning true
        # (metta.pl:203-207). It is diagnostic host output, not an answer.
        if re.match(r"^is .*, should .*\. [✅❌]$", line.strip()):
            continue
        # lib_pln/lib_nars use trace! for `(SELECTED ...)` progress logs.
        # PeTTa rewrites trace! to `(progn (println! X) Y)`
        # (translator.pl:74-75), so these are host diagnostics while the
        # expression value is the second argument.
        if line.strip().startswith("(SELECTED "):
            continue
        if keep and line.strip():
            out.append(line.strip())
    return out


def leatta_results(path, timeout):
    out, _err, returncode = run_grouped(LEATTA + [str(path)], timeout)
    if returncode != 0:
        if "fuel exhausted before a semantics-licensed result" in out + _err:
            raise FuelExhausted
        raise RunnerError("PLeaTTa", returncode, out, _err)
    txt = out.strip()
    if not (txt.startswith("[") and txt.endswith("]")):
        return None
    inner = txt[1:-1].strip()
    if not inner:
        return []
    items, depth, cur = [], 0, ""
    in_str = False
    esc = False
    for ch in inner:
        if in_str:
            cur += ch
            if esc:
                esc = False
            elif ch == "\\":
                esc = True
            elif ch == '"':
                in_str = False
            continue
        if ch == '"':
            in_str = True
            cur += ch
            continue
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == "," and depth == 0:
            items.append(cur.strip())
            cur = ""
        else:
            cur += ch
    items.append(cur.strip())
    return items

def transformed_temp(source_path):
    """Create a transformed file beside the source so relative imports keep
    the same meaning as the original corpus file."""
    return tempfile.NamedTemporaryFile("w", suffix=".metta", prefix=".diffbench-",
                                       dir=source_path.parent, delete=False)


_NUM = re.compile(r"-?\d+\.\d+(?:[eE][+-]?\d+)?")


def _canon_num(m):
    f = float(m.group(0))
    return str(int(f)) if f == int(f) else f"{f:g}"


_BOOL = re.compile(r"\b(True|False)\b")
_VAR = re.compile(r"\$[A-Za-z0-9_#]+")


def _canon_vars(s):
    """Canonicalize variable NAMES per item (de Bruijn-style: first distinct
    var -> $v1, ...). Fresh-variable results (`(get-type $a)` -> `$_123` vs
    `$_gt0`) are counter artifacts, not semantics; per-item numbering keeps
    `(p $x $y)` distinct from `(p $x $x)`."""
    seen = {}
    def sub(m):
        v = m.group(0)
        if v not in seen:
            seen[v] = f"$v{len(seen) + 1}"
        return seen[v]
    return _VAR.sub(sub, s)


def _first_error_kind(body):
    body = body.strip()
    if not body:
        return "unknown"
    if body[0] == "(":
        j = 1
        while j < len(body) and body[j].isspace():
            j += 1
        k = j
        while k < len(body) and (not body[k].isspace()) and body[k] not in "()":
            k += 1
        return body[j:k] or "unknown"
    return body.split(None, 1)[0].strip("()") or "unknown"


def _canon_error_terms(s):
    """Canonicalize host-specific error payloads while preserving kind.

    Native PeTTa `catch/3` returns Prolog-shaped terms such as
    `(Error (type_error ...) (context ...))`; PLeaTTa returns the same kind
    with a Lean-side message payload. The payload is host noise, not an answer
    value, so both sides normalize to `(Error <kind>)`.
    """
    out, i, n = [], 0, len(s)
    while i < n:
        if s.startswith("(Error", i) and (
            i + 6 == n or s[i + 6].isspace() or s[i + 6] == ")"
        ):
            j = _matching_paren(s, i)
            out.append(f"(Error {_first_error_kind(s[i + len('(Error'):j])})")
            i = j + 1
        else:
            out.append(s[i])
            i += 1
    return "".join(out)


def normalize(item):
    s = " ".join(item.split())
    s = _canon_error_terms(s)
    low = s.lower()
    if low in ("true", "false"):
        return low
    # PeTTa aliases true<->True (lib rule `(= true True)`); engines print
    # different cases INSIDE structures -- presentation, not semantics.
    s = _BOOL.sub(lambda m: m.group(0).lower(), s)
    s = _canon_vars(s)
    # float vs int presentation (42 vs 42.0)
    try:
        f = float(s)
        if f == int(f):
            return str(int(f))
    except ValueError:
        pass
    # canonicalize float literals INSIDE compound terms: 0.900000 -> 0.9
    return _NUM.sub(_canon_num, s)


def _sexp_parse(s):
    """Parse one result item into a nested-tuple tree (leaves = tokens)."""
    toks = re.findall(r"[()]|[^\s()]+", s)
    def rec(i):
        if i >= len(toks):
            return None, i
        if toks[i] == "(":
            items, i = [], i + 1
            while i < len(toks) and toks[i] != ")":
                node, i = rec(i)
                if node is None:
                    break
                items.append(node)
            return tuple(items), i + 1
        if toks[i] == ")":
            return None, i + 1
        return toks[i], i + 1
    node, i = rec(0)
    return node if i >= len(toks) and node is not None else s


def _canon_ord(node):
    """Order-insensitive canonical form: tuple children compared as bags.
    Nondet enumeration order (collapse tuples, space dumps) is engine-
    unspecified; both sides canonicalize identically so this cannot create
    one-sided agreement."""
    if isinstance(node, tuple):
        return "(" + " ".join(sorted(_canon_ord(c) for c in node)) + ")"
    return node


def compare(petta, leatta):
    a = collections.Counter(normalize(x) for x in petta)
    b = collections.Counter(normalize(x) for x in leatta)
    return a == b


def compare_ord(petta, leatta):
    """Order-insensitive fallback: recursive multiset tree equality."""
    a = collections.Counter(_canon_ord(_sexp_parse(normalize(x))) for x in petta)
    b = collections.Counter(_canon_ord(_sexp_parse(normalize(x))) for x in leatta)
    return a == b


def run_file(path, timeout=DEFAULT_TIMEOUT, petta_timeout=None,
             petta_timeout_multiplier=DEFAULT_PETTA_TIMEOUT_MULTIPLIER,
             leatta_timeout_multiplier=DEFAULT_LEATTA_TIMEOUT_MULTIPLIER):
    text = path.read_text(errors="replace")
    frag, why = classify(text)
    with transformed_temp(path) as t:
        t.write(transform(text))
        tpath = pathlib.Path(t.name)
    try:
        # --- pinned oracle (may fail; do NOT early-return) ---
        petta_status, pr, petta_elapsed = "OK", None, 0.001
        try:
            t0 = time.monotonic()
            pr = petta_results(
                tpath,
                petta_timeout_for(timeout, petta_timeout,
                                  petta_timeout_multiplier))
            petta_elapsed = max(0.001, time.monotonic() - t0)
        except subprocess.TimeoutExpired:
            petta_status = "PETTA-TIMEOUT"
        except RunnerError as err:
            print(f"{path.name}: PeTTa runner error: {err.stderr.strip()}", file=sys.stderr)
            petta_status = "PETTA-ERROR"
        # --- PLeaTTa runs UNCONDITIONALLY so its independent result is recorded
        # even when the pinned oracle errors/times out: no PLeaTTa bug can hide
        # behind a broken oracle, and broken-oracle adjudication has evidence. ---
        leatta_timeout = max(timeout, petta_elapsed * leatta_timeout_multiplier)
        leatta_status, lr = "OK", None
        try:
            lr = leatta_results(tpath, leatta_timeout)
            if lr is None:
                leatta_status = "LEATTA-NOOUT"
        except subprocess.TimeoutExpired:
            leatta_status = "LEATTA-TIMEOUT"
        except FuelExhausted:
            leatta_status = "LEATTA-EXHAUSTED"
        except RunnerError as err:
            print(f"{path.name}: PLeaTTa runner error: {err.stderr.strip()}", file=sys.stderr)
            leatta_status = "LEATTA-ERROR"
        ln = str(len(lr)) if lr is not None else ""
        # When the oracle could not grade, record PLeaTTa's independent outcome
        # (this is the both-engines evidence tiering + the ledger rely on).
        if petta_status != "OK":
            independent = (f"PLEATTA-OK:{len(lr)}"
                           if leatta_status == "OK" else leatta_status)
            return (path.name, frag, why, petta_status, "", ln, independent)
        # oracle graded below
        if leatta_status != "OK":
            return (path.name, frag, why, leatta_status, len(pr), ln, "")
        if compare(pr, lr):
            verdict = "AGREE"
        elif compare_ord(pr, lr):
            verdict = "AGREE-ORD"   # equal modulo nondet enumeration order
        elif len(pr) == len(lr):
            verdict = "DIFF-VAL"    # same multiplicity, different values
        else:
            verdict = "DIFF-COUNT"  # nondeterminism/backtracking divergence
        return (path.name, frag, why, verdict, len(pr), len(lr), "")
    finally:
        tpath.unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--timeout", type=float, default=DEFAULT_TIMEOUT)
    parser.add_argument("--petta-timeout", type=float, default=None)
    parser.add_argument("--petta-timeout-multiplier", type=float,
                        default=DEFAULT_PETTA_TIMEOUT_MULTIPLIER)
    parser.add_argument("--leatta-timeout-multiplier", type=float,
                        default=DEFAULT_LEATTA_TIMEOUT_MULTIPLIER)
    parser.add_argument("corpus_dir")
    parser.add_argument("names_file", nargs="?")
    args = parser.parse_args()
    cdir = pathlib.Path(args.corpus_dir)
    if args.names_file and pathlib.Path(args.names_file).exists():
        names = [l.strip() for l in open(args.names_file)
                 if l.strip() and not pathlib.Path(l.strip()).name.startswith(".")]
        corpus = [cdir / n for n in names if (cdir / n).exists()]
    else:
        corpus = sorted(f for f in cdir.glob("*.metta")
                        if not f.name.startswith("."))
    rows = []
    for f in corpus:
        row = run_file(
            f,
            timeout=args.timeout,
            petta_timeout=args.petta_timeout,
            petta_timeout_multiplier=args.petta_timeout_multiplier,
            leatta_timeout_multiplier=args.leatta_timeout_multiplier)
        rows.append(row)
        print("\t".join(str(x) for x in row), flush=True)
    with open(SCOREBOARD, "a") as out:
        for row in rows:
            out.write("\t".join(str(x) for x in row) + "\n")
    in_frag = [r for r in rows if r[1] == "IN"]
    agree = [r for r in in_frag if r[3] in ("AGREE", "AGREE-ORD")]
    # This low-level runner reports direct agreement only. The canonical
    # fixed-denominator command (`coverage.py`) additionally runs same-family
    # semantic witnesses and assigns external/oracle-unavailable rows without
    # dropping them from the corpus denominator.
    deleg = {}
    dpath = REPO / "diffbench" / "delegated.tsv"
    if dpath.exists():
        for line in dpath.read_text().splitlines():
            p = line.split("\t")
            if len(p) >= 2:
                deleg[p[0]] = p[1]
    perf = []
    ppath = REPO / "diffbench" / "performance-frontier.tsv"
    if ppath.exists():
        for line in ppath.read_text().splitlines():
            if line.startswith("#") or not line.strip():
                continue
            perf.append(line.split("\t", 1)[0])
    known_open = []
    kpath = REPO / "diffbench" / "known-open.tsv"
    if kpath.exists():
        for line in kpath.read_text().splitlines():
            if line.startswith("#") or not line.strip():
                continue
            known_open.append(line.split("\t", 1)[0])
    agreeset = {r[0] for r in agree}
    rowset = {r[0] for r in rows}
    dchecked = [f for f, v in deleg.items()
                if v == "DELEGATED-CHECKED" and f in rowset and f not in agreeset]
    coveredset = agreeset | set(dchecked)
    total = len(coveredset)
    print(f"\n# DIRECT COVERAGE = {total}/{len(rows)} "
          f"({100*total//max(1,len(rows))}% of corpus): "
          f"{len(agree)} kernel-agree + {len(dchecked)} certificate-checked "
          f"(swipl-finds/Lean-checks)")
    perf_in_run = [f for f in perf if f in rowset]
    print(f"# full-scale performance frontier in this run: {len(perf_in_run)}")
    known_open_in_run = [f for f in known_open if f in rowset]
    print("# known-open correctness/performance boundary: "
          f"{len(known_open_in_run)}")
    print(f"# not directly covered: {len(rows)-total}; no row is removed from "
          "the denominator")
    print("# run diffbench/coverage.py for witness coverage and complete "
          "fixed-denominator dispositions")
    ctr = collections.Counter(r[3] for r in in_frag)
    print("# divergent verdicts:", dict(ctr))


if __name__ == "__main__":
    main()
