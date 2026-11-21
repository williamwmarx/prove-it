#!/bin/bash
# pr.sh <binary> <dir-of-probes>: each probe dir holds M.tla (module text) and M.cfg; runs binary and jar via the harness and prints the comparison.
B=$1; D=$2; S=${WORK:?set WORK}/psuite-$(basename $D); rm -rf $S; mkdir -p $S/tlc
for p in $D/*/; do n=$(basename $p); mkdir -p $S/tlc/$n; m=$(ls $p/*.tla | head -1); args=$(cat $p/args 2>/dev/null); python3 - "$p" "$m" "$S/tlc/$n/$(basename $m)" "$args" <<'PY'
import json,sys
p,m,o,args=sys.argv[1:5]
h={"description":"probe","outcome":"any","config":open(p+'/M.cfg').read()}
if args.strip(): h["args"]=args.split()
open(o,'w').write("(*---\n"+json.dumps(h)+"\n---*)\n"+open(m).read())
PY
done
J=${WORK:?set WORK}/tlaplus/tlatools/org.lamport.tlatools/dist/tla2tools.jar
cd ${WORK:?set WORK}/h; export -n JAVA_TOOL_OPTIONS _JAVA_OPTIONS; unset JAVA_TOOL_OPTIONS _JAVA_OPTIONS
rm -f $S.pi.jsonl; bun harness.ts $S $S.pi.jsonl 120 4 $B >/dev/null 2>&1
[ -f $S.jar.jsonl ] && [ "$REJAR" != 1 ] || { rm -f $S.jar.jsonl; bun harness.ts $S $S.jar.jsonl 600 4 java -XX:+UseSerialGC -XX:TieredStopAtLevel=1 -XX:-UsePerfData -Xmx1g -Xss2m -cp $J tlc2.TLC >/dev/null 2>&1; }
python3 vs_jar.py $S.pi.jsonl $S.jar.jsonl
python3 vs_jar.py $S.pi.jsonl $S.jar.jsonl | python3 diff1.py $S.pi.jsonl $S.jar.jsonl
