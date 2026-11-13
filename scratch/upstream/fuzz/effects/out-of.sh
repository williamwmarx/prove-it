#!/bin/bash
# out-of.sh <binary> <tag> <fixture>...: writes <fixture>/out-<tag>: the normalized output, as try-fixture.sh compares it, or DECLINE <reason>.
bin=$1; tag=$2; shift 2
for src in "$@"; do src=$(realpath "$src")
  dir=$(mktemp -d /home/user/work/tmpfix/f-XXXX); cp "$src"/*.tla "$src"/*.cfg "$dir"/; spec=$(basename "$(ls "$src"/*.cfg)" .cfg)
  out=$(cd "$dir" && "$bin" -workers 1 -fp 0 -noGenerateSpecTE $(cat "$src/args" 2>/dev/null) "$spec" 2>"$dir/err"); code=$?
  if grep -q "not native yet" "$dir/err"; then echo "DECLINE $(sed 's/.*not native yet: //' $dir/err | head -1)" > "$src/out-$tag"
  else { echo "exit $code"; printf '%s\n' "$out" | grep -v -E '^(TLC2 Version|Running breadth-first search|Parsing file|Starting\.\.\.|Finished computing initial states|Finished in|calculated \(optimistic\)|Progress\(|Checking temporal properties|Finished checking temporal properties)' | sed "s#$dir#{directory}#g"; } > "$src/out-$tag"; fi
  rm -rf "$dir"
done
