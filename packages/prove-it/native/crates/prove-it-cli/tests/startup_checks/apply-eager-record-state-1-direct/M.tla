---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = ([k \in 1..2 |-> k])
Next == x' = x
Inv == x[0] = 0
====
