#!/bin/bash
# jar-fixture.sh <fixture-dir>: writes tlc.out from the pinned jar, as startup_checks.rs compares it.
set -euo pipefail
src=$(realpath "$1")
dir=$(mktemp -d ${TMPDIR:-/tmp}/jarfix-XXXX)
cp "$src"/*.tla "$src"/*.cfg "$dir"/
spec=$(basename "$(ls "$src"/*.cfg)" .cfg)
cd "$dir"
set +e
out=$("${JAVA:-java}" -XX:+UseParallelGC -Xss2m -cp "${TLA2TOOLS:?set TLA2TOOLS to the pinned tla2tools.jar}" tlc2.TLC -workers 1 -fp 0 -noGenerateSpecTE $(cat "$src/args" 2>/dev/null) "$spec")
code=$?
set -e
{ echo "exit $code"; printf '%s\n' "$out" | grep -v -E '^(TLC2 Version|Running breadth-first search|Parsing file|Starting\.\.\.|Finished computing initial states|Finished in|calculated \(optimistic\)|Progress\(|Checking temporal properties|Finished checking temporal properties)' | sed "s#$dir#{directory}#g"; } > "$src/tlc.out"
rm -rf "$dir"
