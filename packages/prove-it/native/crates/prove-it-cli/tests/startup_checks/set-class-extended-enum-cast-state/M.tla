---- MODULE M ----
EXTENDS Integers, TLC, TLCExt, FiniteSets, Sequences

VARIABLE x
S == {1,2}
Init == x = S
Next == UNCHANGED x
Inv == (x+1)
====
