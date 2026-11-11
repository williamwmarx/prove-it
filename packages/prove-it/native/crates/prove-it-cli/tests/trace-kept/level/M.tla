---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
P(F) == /\ x' = 1 - x /\ F[0] = F[0]
Next == P([i \in Nat |-> TLCGet("level")])
Inv == TLCGet("level") < 4
====
