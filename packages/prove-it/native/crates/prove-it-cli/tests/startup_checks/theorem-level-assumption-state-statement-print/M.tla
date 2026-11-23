---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 2
ASSUME A == x \in {0, 1}
C == PrintT("c") /\ A
====
