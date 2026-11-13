#!/bin/bash
# try-fixture.sh <binary> <fixture-dir>...: MATCH, DECLINE <reason> or DIFF per fixture, as startup_checks.rs compares.
bin=$1; shift
for src in "$@"; do src=$(realpath "$src")
  dir=$(mktemp -d /tmp/tryfix-XXXX); cp "$src"/*.tla "$src"/*.cfg "$dir"/; spec=$(basename "$(ls "$src"/*.cfg)" .cfg)
  for w in 1 4; do
    out=$(cd "$dir" && "$bin" -workers $w -fp 0 -noGenerateSpecTE $(cat "$src/args" 2>/dev/null) "$spec" 2>"$dir/err"); code=$?
    actual=$({ echo "exit $code"; printf '%s\n' "$out" | grep -v -E '^(TLC2 Version|Running breadth-first search|Parsing file|Starting\.\.\.|Finished computing initial states|Finished in|calculated \(optimistic\)|Progress\(|Checking temporal properties|Finished checking temporal properties)' | sed "s#$dir#{directory}#g"; })
    if grep -q "not native yet" "$dir/err"; then echo "DECLINE w$w $(basename $src): $(sed 's/.*not native yet: //' $dir/err | head -1)";
    elif [ "$actual" == "$(cat $src/tlc.out)" ]; then echo "MATCH   w$w $(basename $src)";
    else echo "DIFF    w$w $(basename $src)"; diff <(echo "$actual") $src/tlc.out | head -8; fi
  done
  rm -rf "$dir"
done
