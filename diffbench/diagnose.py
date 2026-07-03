#!/usr/bin/env python3
"""diagnose: per-file CRUX analysis of divergences.

For each divergent file, run both engines (same transform/normalize as
diff.py), compute the symmetric multiset difference, and auto-bucket the crux:

  INERT-FORM   leatta-only items contain unreduced forms `(op ...)` whose
               head never heads a petta-only item -> missing/wrong op `op`
  EMPTY-SIDE   one engine yields results, the other none
  MULTIPLICITY same values, different counts (backtracking multiplicity)
  VALUE        same shape, different values (semantic divergence at a value)
  MIXED        several of the above

Output: TSV rows + aggregated crux buckets + the concrete missing-op list.
"""
import collections
import pathlib
import re
import subprocess
import sys

sys.path.insert(0, str(pathlib.Path(__file__).parent))
import diff as D

HEAD = re.compile(r"^\(\s*([^\s()]+)")


def heads(items):
    hs = set()
    for x in items:
        m = HEAD.match(x)
        if m:
            hs.add(m.group(1))
    return hs


def diagnose(path, timeout=15):
    text = path.read_text(errors="replace")
    import tempfile
    with tempfile.NamedTemporaryFile("w", suffix=".metta", delete=False) as t:
        t.write(D.transform(text))
        tpath = pathlib.Path(t.name)
    try:
        try:
            pr = D.petta_results(tpath, timeout)
        except subprocess.TimeoutExpired:
            return ("PETTA-TIMEOUT", [], [], "")
        try:
            lr = D.leatta_results(tpath, timeout)
        except subprocess.TimeoutExpired:
            return ("LEATTA-TIMEOUT", pr, [], "")
        if lr is None:
            return ("LEATTA-NOOUT", pr, [], "")
        a = collections.Counter(D.normalize(x) for x in pr)
        b = collections.Counter(D.normalize(x) for x in lr)
        ponly = list((a - b).elements())
        lonly = list((b - a).elements())
        if not ponly and not lonly:
            return ("AGREE", [], [], "")
        # bucket
        crux = []
        inert_ops = sorted(heads(lonly) - heads(ponly))
        if not pr and lr:
            crux.append("EMPTY-PETTA")
        elif pr and not lr:
            crux.append("EMPTY-LEATTA")
        if inert_ops and lonly:
            crux.append("INERT-FORM:" + ",".join(inert_ops[:6]))
        vals_a = collections.Counter(ponly)
        vals_b = collections.Counter(lonly)
        if set(vals_a) == set(vals_b) and vals_a != vals_b:
            crux.append("MULTIPLICITY")
        if not crux:
            crux.append("VALUE")
        return ("|".join(crux), ponly, lonly, inert_ops)
    finally:
        tpath.unlink(missing_ok=True)


def main():
    cdir = pathlib.Path(sys.argv[1])
    names = [l.strip() for l in open(sys.argv[2]) if l.strip()]
    op_counter = collections.Counter()
    bucket_counter = collections.Counter()
    for n in names:
        p = cdir / n
        if not p.exists():
            continue
        crux, ponly, lonly, inert_ops = diagnose(p)
        bucket_counter[crux.split(":")[0].split("|")[0]] += 1
        for op in (inert_ops or []):
            op_counter[op] += 1
        ps = " ;; ".join(ponly[:3])[:160]
        ls = " ;; ".join(lonly[:3])[:160]
        print(f"{n}\t{crux}\tP-only[{len(ponly)}]: {ps}\tL-only[{len(lonly)}]: {ls}",
              flush=True)
    print("\n# CRUX buckets:", dict(bucket_counter.most_common()))
    print("# INERT-FORM head symbols (the missing/wrong-op worklist):")
    for op, c in op_counter.most_common(40):
        print(f"#   {op}\t{c}")


if __name__ == "__main__":
    main()
