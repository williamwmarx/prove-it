"""Compact per-run results: classify.py <run.jsonl> <out.tsv>.

class: match (verdict pass), decline (stderr or stdout carries the decline marker),
noncompletion (time-limit, memory-limit, crash), unrecorded, wrong (anything else).
"""
import hashlib
import json
import sys

MARKER = "prove-it: not native yet:"


def classify(row):
    text = row["stderr"] + "\n" + row["transcript"]
    if row["verdict"] == "pass":
        return "match", ""
    if MARKER in text:
        reason = text[text.index(MARKER) + len(MARKER):].split("\n", 1)[0].strip()
        return "decline", reason
    if row["verdict"] in ("time-limit", "memory-limit", "crash"):
        return "noncompletion", ""
    if row["verdict"] == "unrecorded":
        return "unrecorded", ""
    return "wrong", ""


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


def load(path):
    rows = {}
    with open(path) as f:
        for line in f:
            row = json.loads(line)
            row["class"], row["reason"] = classify(row)
            rows[row["id"]] = row
    return rows


if __name__ == "__main__":
    rows = load(sys.argv[1])
    with open(sys.argv[2], "w") as out:
        out.write("id\tclass\tverdict\texit\ttranscript_sha256\tstderr_sha256\tmillis\tdecline_reason\n")
        for id_ in sorted(rows):
            r = rows[id_]
            out.write("\t".join([id_, r["class"], r["verdict"], str(r["exit"]), sha(r["transcript"]), sha(r["stderr"]), str(r["millis"]), r["reason"].replace("\t", " ")]) + "\n")
