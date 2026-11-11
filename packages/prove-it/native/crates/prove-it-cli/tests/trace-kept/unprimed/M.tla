---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
P(F) == /\ F[0] = x /\ x' = x + 1
Next == P([i \in Nat |-> x])
Inv == x < 3
====
