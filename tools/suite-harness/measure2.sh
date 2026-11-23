#!/bin/bash
# measure2.sh <tree> <backend-run-dir> <tag>: builds the tree's release binary and the backend runner, runs the upstream tlapm suite, counts.
S=/tmp/claude-0/-home-user-prove-it/41c9ddda-3031-5ac6-9e2b-4d93d5416735/scratchpad
tree=$1; br=$2; tag=$3
N=$tree/packages/prove-it/native
cd $N && cargo build --release --locked -p prove-it-cli 2>&1 | tail -1
cd $br && cargo build --release 2>&1 | tail -1
cd $S/harness && SUITES=tlapm BACKEND_CMD=$br/target/release/backend-run bun harness.ts $S/up/tla-ts/packages/conformance/test $S/results/tlapm-$tag.jsonl 120 2 $N/target/release/prove-it | tail -1
python3 - "$S/results/tlapm-$tag.jsonl" <<'PY'
import json, sys, collections
sys.path.insert(0, "/tmp/claude-0/-home-user-prove-it/41c9ddda-3031-5ac6-9e2b-4d93d5416735/scratchpad/harness")
import classify
rows = classify.load(sys.argv[1])
by = collections.Counter()
for r in rows.values():
    by[(r.get("kind"), r["class"])] += 1
print(sorted(by.items()))
PY
echo MEASURE-DONE
