"""compare.py <base.jsonl> <cand.jsonl> <outdir>: transition matrix and the changed runs."""
import json
import os
import random
import sys
from collections import Counter

from classify import load

base, cand, outdir = load(sys.argv[1]), load(sys.argv[2]), sys.argv[3]
assert set(base) == set(cand), "the runs differ"
matrix = Counter()
changed = []
for id_ in sorted(base):
    b, c = base[id_], cand[id_]
    matrix[(b["class"], c["class"])] += 1
    if (b["class"], b["exit"], b["transcript"], b["stderr"]) != (c["class"], c["exit"], c["transcript"], c["stderr"]):
        changed.append(id_)
for (bc, cc), n in sorted(matrix.items()):
    print(f"{bc:>14} -> {cc:<14} {n}")
print("changed runs:", len(changed))
needs = [i for i in changed if cand[i]["class"] != "match"]
print("changed and the candidate is not a match:", len(needs), Counter(cand[i]["class"] for i in needs))
decline_to_match = [i for i in changed if base[i]["class"] == "decline" and cand[i]["class"] == "match"]
random.seed(20261112)
sample = sorted(random.sample(decline_to_match, min(300, len(decline_to_match))))
os.makedirs(outdir, exist_ok=True)
with open(f"{outdir}/changed.tsv", "w") as f:
    f.write("id\tbaseline_class\tcandidate_class\tbaseline_verdict\tcandidate_verdict\tbaseline_reason\tcandidate_reason\n")
    for i in changed:
        b, c = base[i], cand[i]
        f.write("\t".join([i, b["class"], c["class"], b["verdict"], c["verdict"], b["reason"], c["reason"]]) + "\n")
with open(f"{outdir}/needs-tlc.txt", "w") as f:
    f.write("".join(i + "\n" for i in needs))
with open(f"{outdir}/decline-to-match-sample.txt", "w") as f:
    f.write("".join(i + "\n" for i in sample))
regressions = [i for i in sorted(base) if base[i]["class"] == "match" and cand[i]["class"] != "match"]
print("baseline matches no longer matching:", len(regressions))
for i in regressions:
    print("  REGRESSION", i, cand[i]["class"], cand[i]["verdict"], cand[i]["reason"])
