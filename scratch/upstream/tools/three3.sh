#!/bin/bash
# three3.sh <main> <base> <new> <fixture>...: one line per fixture, each binary's class (the new one at -workers 1 and 4).
for f in "${@:4}"; do
  m=$(bash "$(dirname "$0")/try-fixture.sh" "$1" "$f" 2>&1 | grep -E '^(MATCH|DIFF|DECLINE)' | head -1 | awk '{print $1}')
  b=$(bash "$(dirname "$0")/try-fixture.sh" "$2" "$f" 2>&1 | grep -E '^(MATCH|DIFF|DECLINE)' | head -1 | awk '{print $1}')
  r=$(bash "$(dirname "$0")/try-fixture.sh" "$3" "$f" 2>&1 | grep -E '^(MATCH|DIFF|DECLINE)' | awk '{print $1}' | sort -u | tr '\n' ,)
  echo "$(basename $f) main=$m base=$b new=$r"
done
