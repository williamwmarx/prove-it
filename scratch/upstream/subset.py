"""subset.py <base.jsonl> <new.jsonl> <tlc.jsonl>...: new vs base on the runs new holds, adjudicated by the pinned jar.

Writes the ids that changed, aren't a match or decline on new, and have no jar run, to need-tlc.txt.
"""
import json
import sys
from collections import Counter

from classify import load

base, new = load(sys.argv[1]), load(sys.argv[2])
tlc = {}
for path in sys.argv[3:]:
    for line in open(path):
        row = json.loads(line)
        tlc[row["id"]] = row
adj = "/home/user/work/adj"


def same(a, t):
    return a["exit"] == t["exit"] and a["transcript"] == t["transcript"]


def verdict(r):
    if r["class"] in ("match", "decline", "noncompletion", "unrecorded"):
        return r["class"]
    if r["id"] not in tlc:
        return "UNADJUDICATED"
    return "matches-pinned-tlc" if same(r, tlc[r["id"]]) else "WRONG"


ids = lambda f: [l for l in open(f"{adj}/{f}").read().split("\n") if l]
need = sorted(i for i in new if verdict(new[i]) == "UNADJUDICATED")
open(f"{adj}/need-tlc.txt", "w").write("".join(i + "\n" for i in need))
print("runs:", len(new), "unadjudicated:", len(need))
print("new classes:", dict(Counter(verdict(new[i]) for i in new)))
print("transitions base->new:", dict(Counter(f"{base[i]['class']}->{verdict(new[i])}" for i in new)))
regs = [l.split("\t")[0] for l in open(f"{adj}/regressions.tsv").read().split("\n")[1:] if l]
print("the 112:", dict(Counter(verdict(new[i]) for i in regs)))
print("the 6,795:", dict(Counter(verdict(new[i]) for i in ids("overreach.txt") if i in new)))
print("the 575:", dict(Counter(verdict(new[i]) for i in ids("swc.txt") if i in new)))
lost = sorted(i for i in new if base[i]["class"] == "match" and new[i]["class"] != "match")
print("baseline matches lost:", len(lost))
for i in lost:
    print("  LOST", i, new[i]["class"], new[i]["reason"])
wrong = sorted(i for i in new if verdict(new[i]) == "WRONG")
print("WRONG:", len(wrong))
for i in wrong:
    print("  WRONG", i, "baseline", verdict(base[i]) if base[i]["class"] != "wrong" else "wrong")
