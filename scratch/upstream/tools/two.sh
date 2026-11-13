#!/bin/bash
# two.sh <base> <new> <fixture>...: base and new class per fixture, with the new one's decline reason.
for f in "${@:3}"; do
  m=$(bash "$(dirname "$0")/try-fixture.sh" "$1" "$f" 2>&1 | grep -E '^(MATCH|DIFF|DECLINE)' | awk '{print $1}' | sort -u | tr '\n' ,)
  r=$(bash "$(dirname "$0")/try-fixture.sh" "$2" "$f" 2>&1 | grep -E '^(MATCH|DIFF|DECLINE)')
  c=$(echo "$r" | awk '{print $1}' | sort -u | tr '\n' ,); why=$(echo "$r" | grep -m1 DECLINE | sed 's/^[^:]*: //')
  echo "$(basename $f) base=$m new=$c | $why"
done
