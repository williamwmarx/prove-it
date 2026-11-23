#!/bin/sh
# Runs Z3 4.8.9 as tlapm does on a suite .smt file, with its front matter stripped.
S=/tmp/claude-0/-home-user-prove-it/41c9ddda-3031-5ac6-9e2b-4d93d5416735/scratchpad
python3 -I -c '
import re,sys
text=open(sys.argv[1]).read()
sys.stdout.write(re.sub(r"\(\*---.*?---\*\)\n?","",text,flags=re.S))' "$1" > "$S/z3in.smt2"
"$S/z3-venv/bin/z3" -smt2 -v:0 AUTO_CONFIG=false smt.MBQI=true "$S/z3in.smt2"
echo "exit=$?"
