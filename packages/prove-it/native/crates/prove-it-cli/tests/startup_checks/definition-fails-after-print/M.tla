---- MODULE M ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
D == PrintT(1) /\ 1 \div 0 = 1
ASSUME D
Init == x = 0
Next == x' = 1 - x

====
