"""adjudicate.py <base.jsonl> <cand.jsonl> <tlc.jsonl> <adjdir>: compare against the pinned jar."""
import json
import sys
from collections import Counter

from classify import load

base, cand, adj = load(sys.argv[1]), load(sys.argv[2]), sys.argv[4]
tlc = {}
for line in open(sys.argv[3]):
    row = json.loads(line)
    tlc[row["id"]] = row


def same(a, t):
    return a["exit"] == t["exit"] and a["transcript"] == t["transcript"]


def verdict(r):
    if r["class"] == "match":
        return "match"
    if r["class"] in ("decline", "noncompletion", "unrecorded"):
        return r["class"]
    return "matches-pinned-tlc" if same(r, tlc[r["id"]]) else "WRONG"


ids = lambda f: [l for l in open(f"{adj}/{f}").read().split("\n") if l]
report = {}

needs = ids("needs-tlc.txt")
c = Counter((base[i]["class"], verdict(cand[i])) for i in needs)
report["changed, candidate not a match (baseline class, candidate adjudicated)"] = {f"{k[0]} -> {k[1]}": n for k, n in sorted(c.items())}
new_wrong = [i for i in needs if verdict(cand[i]) == "WRONG"]
report["new wrong outputs"] = new_wrong

sample = ids("decline-to-match-sample.txt")
report["decline->match sample of 300: candidate also equals the pinned jar"] = sum(same(cand[i], tlc[i]) for i in sample)
report["decline->match sample of 300: pinned jar differs from the recording"] = [i for i in sample if not same(cand[i], tlc[i])]

for name, f in (("guard-overreach (6,795)", "overreach.txt"), ("startup-wrong-cases (575)", "swc.txt")):
    report[name] = {
        "candidate": dict(Counter(verdict(cand[i]) for i in ids(f))),
        "baseline": dict(Counter(verdict(base[i]) if base[i]["id"] in tlc or base[i]["class"] != "wrong" else "wrong-unadjudicated" for i in ids(f))),
        "wrong": [i for i in ids(f) if verdict(cand[i]) == "WRONG"],
    }

regressions = [i for i in sorted(base) if base[i]["class"] == "match" and cand[i]["class"] != "match"]
report["regressions (baseline match, candidate not)"] = {
    "count": len(regressions),
    "baseline output equals pinned jar": sum(same(base[i], tlc[i]) for i in regressions),
    "candidate classes": dict(Counter(cand[i]["class"] for i in regressions)),
    "reasons": dict(Counter(cand[i]["reason"] for i in regressions)),
}
wrong_all = [i for i in sorted(cand) if cand[i]["class"] == "wrong"]
report["all candidate wrong-vs-recording runs"] = {
    "count": len(wrong_all),
    "adjudicated": dict(Counter(verdict(cand[i]) for i in wrong_all)),
    "WRONG": [i for i in wrong_all if verdict(cand[i]) == "WRONG"],
}
wrong_base = [i for i in sorted(base) if base[i]["class"] == "wrong"]
report["all baseline wrong-vs-recording runs"] = {
    "count": len(wrong_base),
    "adjudicated (pinned jar run where available)": dict(Counter(verdict(base[i]) if i in tlc else "not-run" for i in wrong_base)),
}
json.dump(report, sys.stdout, indent=1)
print()
with open(f"{adj}/regressions.tsv", "w") as f:
    f.write("id\tcandidate_class\tcandidate_verdict\tbaseline_equals_pinned_tlc\tdecline_reason\n")
    for i in regressions:
        f.write(f"{i}\t{cand[i]['class']}\t{cand[i]['verdict']}\t{same(base[i], tlc[i])}\t{cand[i]['reason']}\n")
