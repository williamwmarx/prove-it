#!/bin/bash
# tryfix.sh <binary> <fixture>...: MATCH, DIFF or DECLINE as startup_checks.rs compares, at 1 and 4 workers.
B=$1; shift
for src in "$@"; do for w in 1 4; do d=$(mktemp -d); cp $src/*.tla $src/*.cfg $d/; spec=$(basename $(ls $src/*.cfg) .cfg)
out=$(cd $d && env -u JAVA_TOOL_OPTIONS -u _JAVA_OPTIONS $B -workers $w -fp 0 -noGenerateSpecTE $(cat $src/args 2>/dev/null) $spec 2>&1); code=$?
got=$( { echo "exit $code"; printf '%s\n' "$out" | grep -v -E '^(TLC2 Version|Running breadth-first search|Parsing file|Starting\.\.\.|Finished computing initial states|Finished in|calculated \(optimistic\)|Progress\(|Checking temporal properties|Finished checking temporal properties)' | sed "s#$d#{directory}#g"; } )
if grep -q "not native yet" <<<"$got"; then echo "DECLINE $src w$w"; elif [ "$got" == "$(cat $src/tlc.out)" ]; then echo "MATCH $src w$w"; else echo "DIFF $src w$w"; diff <(echo "$got") $src/tlc.out | head -8; fi; rm -rf $d; done; done
