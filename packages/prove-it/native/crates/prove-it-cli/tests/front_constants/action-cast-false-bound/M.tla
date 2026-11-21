---- MODULE M ----
EXTENDS Naturals, TLC
CONSTANT c
VARIABLE x
Init == x = 0
Next == \E p \in {c} : p \/ x' = (x + 1) % 3
====
