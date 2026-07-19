#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0

"""Resumable corpus run: one file at a time, appending; skips files already
in the log, so external kills lose at most the in-flight file."""
import os
import pathlib, sys, subprocess, os
sys.path.insert(0, str(pathlib.Path(__file__).parent))
import diff as D
log = pathlib.Path(sys.argv[1])
corpus = sorted(f for f in (pathlib.Path(os.environ.get("PETTA_DIR", str(pathlib.Path.home()/"repos/PeTTa"))) / "examples").glob("*.metta")
                if not f.name.startswith("."))
done = set()
if log.exists():
    for l in log.read_text().splitlines():
        if "\t" in l and not l.startswith("#"):
            done.add(l.split("\t")[0])
with open(log, "a") as out:
    for f in corpus:
        if f.name in done: continue
        try:
            row = D.run_file(f)
        except Exception as e:
            row = (f.name, "IN", "", "HARNESS-ERR", "", "")
        out.write("\t".join(str(x) for x in row) + "\n"); out.flush()
print("DONE")
