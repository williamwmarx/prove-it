---- MODULE M ----
EXTENDS Integers, TLC
D == (1 \div 0 = 1) /\ TLCSet(1, 2)
Inv == D
VARIABLE x
Init == x = 0
Next == x' = x
====
