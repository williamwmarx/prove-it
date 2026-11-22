---- MODULE TraceLong ----
EXTENDS TLCExt, Naturals, Sequences
VARIABLE x
Init == x = 0
Next == x < 100000 /\ x' = x + 1
Inv == x >= 0 \/ Len(Trace) > 0
====
