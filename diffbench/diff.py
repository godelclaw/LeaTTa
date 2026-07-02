#!/usr/bin/env python3
"""diffbench: differential harness — real native PeTTa (oracle) vs LeaTTa --file.

For each corpus file: classify in/out-of-fragment (core PeTTa), run both
engines, normalize results, compare as multisets, append a scoreboard row.
Out-of-fragment and parse-gap files are counted, never silently dropped.
"""
import re
import subprocess
import sys
import pathlib
import tempfile
import collections

REPO = pathlib.Path(__file__).resolve().parent.parent
PETTA_RUNNER = ["bash", "/home/oruzi/repos/PeTTa/test_runner.sh"]
LEATTA = [str(REPO / ".lake/build/bin/LeaTTa"), "--file"]
SCOREBOARD = REPO / "diffbench" / "scoreboard.tsv"

# Tokens that put a file outside the declared "core PeTTa" fragment
# (effects, Prolog/Python interop, spaces/state, modules). See plan.
OUT_OF_FRAGMENT = re.compile(
    r"py-call|py-atom|import!|git-import|import_prolog|translatePredicate"
    r"|change-state!|new-state|get-state|bind!|new-space|add-atom|remove-atom"
    r"|add-reduct|match\s+&|shell|call-cleanup|time-limit|sread|repr"
    r"|assertEqual|regex|random|get_time|flush|trace|halt"
)

ANSI = re.compile(r"\x1b\[[0-9;]*m")


def classify(text):
    hit = OUT_OF_FRAGMENT.search(text)
    return ("OUT", hit.group(0)) if hit else ("IN", "")


def transform(text):
    # PeTTa's test helper prints checkmark lines LeaTTa lacks; (test A B) and
    # (== A B) evaluate both args the same way, so rewrite for comparability.
    return re.sub(r"\((test|assertEqual)\s", "(== ", text)


def petta_results(path, timeout):
    p = subprocess.run(PETTA_RUNNER + [str(path)], capture_output=True,
                       text=True, timeout=timeout)
    txt = ANSI.sub("", p.stdout + p.stderr)
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
    p = subprocess.run(LEATTA + [str(path)], capture_output=True,
                       text=True, timeout=timeout)
    txt = p.stdout.strip()
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
    return s


def compare(petta, leatta):
    a = collections.Counter(normalize(x) for x in petta)
    b = collections.Counter(normalize(x) for x in leatta)
    return a == b


def run_file(path, timeout=90):
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
        verdict = "AGREE" if compare(pr, lr) else "DIFF"
        return (path.name, frag, why, verdict, len(pr), len(lr))
    finally:
        tpath.unlink(missing_ok=True)


def main():
    corpus = sorted(pathlib.Path(sys.argv[1]).glob("*.metta"))
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
