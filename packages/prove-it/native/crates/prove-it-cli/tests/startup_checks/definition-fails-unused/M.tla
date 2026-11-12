---- MODULE M ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
D == 1 \div 0
Init == x = 0
Next == x' = (x + 1) % 3
====
