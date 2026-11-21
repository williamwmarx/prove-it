---- MODULE M ----
EXTENDS TLC
VARIABLE x
Init == x = 0
Next == x' = x
Inv == x = 0 => (TLCSet(0, 42) /\ TLCGet(0) = 42)
====
