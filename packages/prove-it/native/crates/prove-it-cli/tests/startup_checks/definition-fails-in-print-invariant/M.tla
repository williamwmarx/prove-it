---- MODULE M ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
D == {1 \div 0, PrintT(2)} = {}

Init == x = 0
Next == x' = 1 - x
Inv == x = 0 \/ D
====
