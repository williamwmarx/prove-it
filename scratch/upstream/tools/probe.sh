#!/bin/bash
# probe.sh <binary> <out.jsonl> <filter>... : run the binary on unit-suite cases matching the filters
B=$1; O=$2; shift 2
rm -f $O; cd ${WORK:?set WORK}/h && env -u JAVA_TOOL_OPTIONS -u _JAVA_OPTIONS bun harness.ts ${WORK:?set WORK}/unit-suite $O 120 4 $B -- "$@" >/dev/null 2>&1
python3 $(dirname "$0")/../unit/vs_jar.py $O ${WORK:?set WORK}/unit-jar.jsonl
