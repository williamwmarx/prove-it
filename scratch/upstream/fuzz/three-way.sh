#!/bin/bash
# three-way.sh <main-binary> <branch-binary> <fixture-dir>...: per fixture and worker count, main's and the branch's class against the jar.
for f in "${@:3}"; do
  m=$(bash /home/user/work/scripts/try-fixture.sh "$1" "$f" | grep -E '^(MATCH|DECLINE|DIFF)' | awk '{print $1}' | tr '\n' ',')
  b=$(bash /home/user/work/scripts/try-fixture.sh "$2" "$f" | grep -E '^(MATCH|DECLINE|DIFF)' | awk '{print $1}' | tr '\n' ',')
  echo "$(basename $f) main=$m branch=$b"
done
