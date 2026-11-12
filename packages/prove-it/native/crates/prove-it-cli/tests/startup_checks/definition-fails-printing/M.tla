---- MODULE M ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
D == PrintT(1 \div 0)
Init == x = 0
Next == x' = x
====
