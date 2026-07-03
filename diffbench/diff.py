#!/usr/bin/env python3
"""diffbench: differential harness (NONDET IS ORDER-AGNOSTIC: results are a
multiset/bag compared via Counter -- multiplicity matters, enumeration order
does not; DIFF-COUNT = genuine multiplicity mismatch, not order).

Original: — real native PeTTa (oracle) vs LeaTTa --file.

For each corpus file: classify in/out-of-fragment (core PeTTa), run both
engines, normalize results, compare as multisets, append a scoreboard row.
Out-of-fragment and parse-gap files are counted, never silently dropped.
"""
import os
import re
import signal
import subprocess
import sys
import pathlib
import tempfile
import collections

REPO = pathlib.Path(__file__).resolve().parent.parent
PETTA_RUNNER = ["bash", os.environ.get("PETTA_RUNNER",
    str(pathlib.Path.home() / "repos/PeTTa/test_runner.sh"))]
LEATTA = [str(REPO / ".lake/build/bin/LeaTTa")] + (os.environ.get("LEATTA_ARGS", "").split() if os.environ.get("LEATTA_ARGS") else []) + ["--file"]
SCOREBOARD = REPO / "diffbench" / "scoreboard.tsv"

# Tokens that put a file outside the declared "core PeTTa" fragment
# (effects, Prolog/Python interop, spaces/state, modules). See plan.
# ADMIT_IMPORTS=1 admits import!-using files (T1.2 gate); repr became a
# supported petta builtin at the same arm.
_IMPORT_TOKENS = r"" if os.environ.get("ADMIT_IMPORTS") else r"import!|repr|"
_SPACE_TOKENS = r"" if os.environ.get("ADMIT_SPACES") else r"new-space|add-atom|remove-atom|add-reduct|match\s+&|bind!|"
OUT_OF_FRAGMENT = re.compile(
    r"py-call|py-atom|" + _IMPORT_TOKENS + _SPACE_TOKENS +
    r"git-import|import_prolog|translatePredicate"
    r"" if os.environ.get("ADMIT_STATES") else r"|change-state!|new-state|get-state"
    r"|shell|call-cleanup|time-limit|sread"
    r"|assertEqual|regex|random|get_time|flush|trace|halt"
)

ANSI = re.compile(r"\x1b\[[0-9;]*m")


def classify(text):
    hit = OUT_OF_FRAGMENT.search(text)
    return ("OUT", hit.group(0)) if hit else ("IN", "")


def transform(text):
    # PeTTa's test helper prints checkmark lines LeaTTa lacks; (test A B) and
    # (== A B) evaluate both args the same way, so rewrite for comparability.
    text = re.sub(r"\((test|assertEqual)\s", "(== ", text)
    # println! interleaves side-effect lines into PeTTa's stdout that a pure
    # kernel cannot mirror; drop whole-line print directives so BOTH engines
    # run the identical print-free program (oracle-fair transform).
    text = re.sub(r"^\s*!\(println!.*$", "", text, flags=re.M)
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
    return out, err


def petta_results(path, timeout):
    out, err = run_grouped(PETTA_RUNNER + [str(path)], timeout)
    txt = ANSI.sub("", out + err)
    out, keep = [], False
    for line in txt.splitlines():
        if "^^^" in line:
            keep = True
            continue
        if "-->" in line:
            keep = False
            continue
        if keep and line.strip():
            out.append(line.strip())
    return out


def leatta_results(path, timeout):
    out, _err = run_grouped(LEATTA + [str(path)], timeout)
    txt = out.strip()
    if not (txt.startswith("[") and txt.endswith("]")):
        return None
    inner = txt[1:-1].strip()
    if not inner:
        return []
    items, depth, cur = [], 0, ""
    for ch in inner:
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


_NUM = re.compile(r"-?\d+\.\d+(?:[eE][+-]?\d+)?")


def _canon_num(m):
    f = float(m.group(0))
    return str(int(f)) if f == int(f) else f"{f:g}"


def normalize(item):
    s = " ".join(item.split())
    low = s.lower()
    if low in ("true", "false"):
        return low
    # float vs int presentation (42 vs 42.0)
    try:
        f = float(s)
        if f == int(f):
            return str(int(f))
    except ValueError:
        pass
    # canonicalize float literals INSIDE compound terms: 0.900000 -> 0.9
    return _NUM.sub(_canon_num, s)


def compare(petta, leatta):
    a = collections.Counter(normalize(x) for x in petta)
    b = collections.Counter(normalize(x) for x in leatta)
    return a == b


def run_file(path, timeout=45):
    text = path.read_text(errors="replace")
    frag, why = classify(text)
    with tempfile.NamedTemporaryFile("w", suffix=".metta", delete=False) as t:
        t.write(transform(text))
        tpath = pathlib.Path(t.name)
    try:
        try:
            pr = petta_results(tpath, timeout)
        except subprocess.TimeoutExpired:
            return (path.name, frag, why, "PETTA-TIMEOUT", "", "")
        try:
            lr = leatta_results(tpath, timeout)
        except subprocess.TimeoutExpired:
            return (path.name, frag, why, "LEATTA-TIMEOUT", len(pr), "")
        if lr is None:
            return (path.name, frag, why, "LEATTA-NOOUT", len(pr), "")
        if compare(pr, lr):
            verdict = "AGREE"
        elif len(pr) == len(lr):
            verdict = "DIFF-VAL"    # same multiplicity, different values
        else:
            verdict = "DIFF-COUNT"  # nondeterminism/backtracking divergence
        return (path.name, frag, why, verdict, len(pr), len(lr))
    finally:
        tpath.unlink(missing_ok=True)


def main():
    cdir = pathlib.Path(sys.argv[1])
    if len(sys.argv) > 2 and pathlib.Path(sys.argv[2]).exists():
        names = [l.strip() for l in open(sys.argv[2]) if l.strip()]
        corpus = [cdir / n for n in names if (cdir / n).exists()]
    else:
        corpus = sorted(cdir.glob("*.metta"))
    rows = []
    for f in corpus:
        row = run_file(f)
        rows.append(row)
        print("\t".join(str(x) for x in row), flush=True)
    with open(SCOREBOARD, "a") as out:
        for row in rows:
            out.write("\t".join(str(x) for x in row) + "\n")
    in_frag = [r for r in rows if r[1] == "IN"]
    agree = [r for r in in_frag if r[3] == "AGREE"]
    print(f"\n# corpus={len(rows)} in-fragment={len(in_frag)} "
          f"({100*len(in_frag)//max(1,len(rows))}%) "
          f"agree={len(agree)}/{len(in_frag)} "
          f"({100*len(agree)//max(1,len(in_frag))}% of in-fragment)")
    ctr = collections.Counter(r[3] for r in in_frag)
    print("# in-fragment verdicts:", dict(ctr))


if __name__ == "__main__":
    main()
