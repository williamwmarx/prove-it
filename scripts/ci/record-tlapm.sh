#!/usr/bin/env bash
# Runs tlapm on each spec a list names, in a copy of the spec's directory, and keeps what it
# prints: record-tlapm.sh <tlapm> <list> <out> [filter]. Each line of the list is a spec's path
# from the repository root, then |, then tlapm's options; a line starting with # is a comment. Each
# run gets a numbered directory under <out> holding its command line, stdout, stderr, exit code and
# the fingerprints file tlapm wrote, and <out>/version holds tlapm's version.
set -euo pipefail
tlapm=$1
list=$2
out=$3
filter=${4-}
mkdir -p "$out"
"$tlapm" --version > "$out/version" 2>&1 || true
echo "tlapm $(cat "$out/version")"
index=0
while IFS= read -r line || [ -n "$line" ]; do
  case "$line" in '' | '#'*) continue ;; esac
  spec=$(echo "${line%%|*}" | xargs)
  args=$(echo "${line#*|}" | xargs)
  if [ -n "$filter" ] && [[ "$spec" != *"$filter"* ]]; then
    continue
  fi
  if [ ! -f "$spec" ]; then
    echo "skipped, no such spec: $spec"
    continue
  fi
  index=$((index + 1))
  name=$(basename "$spec" .tla)
  run="$out/$(printf '%03d' "$index")-$name"
  mkdir -p "$run"
  work=$(mktemp -d)
  cp "$(dirname "$spec")"/*.tla "$work/"
  echo "tlapm $args $name.tla" > "$run/command"
  set +e
  # shellcheck disable=SC2086
  (cd "$work" && "$tlapm" $args "$name.tla" < /dev/null > "$run/stdout" 2> "$run/stderr")
  echo $? > "$run/exit"
  set -e
  if [ -f "$work/.tlacache/$name.tlaps/fingerprints" ]; then
    cp "$work/.tlacache/$name.tlaps/fingerprints" "$run/fingerprints"
  fi
  rm -rf "$work"
  echo "$(basename "$run"): tlapm $args $name.tla, exit $(cat "$run/exit")"
done < "$list"
echo "$index runs recorded"
