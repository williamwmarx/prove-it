---- MODULE M ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
D == CHOOSE n \in {} : TRUE
Init == x = 0
Next == x' = (x + 1) % 3
Inv == x < 2 \/ D = 0
====
