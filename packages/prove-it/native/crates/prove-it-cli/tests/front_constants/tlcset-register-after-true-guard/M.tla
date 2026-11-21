---- MODULE M ----
EXTENDS Integers, TLC
D == (1 = 1) /\ TLCSet(1, 2)
Inv == D /\ PrintT(TLCGet(1))
VARIABLE x
Init == x = 0
Next == x' = x
====
