---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
D == PrintT("d") /\ 1 \div 0 = 0
Init == D /\ x = 0
Next == UNCHANGED x
====
