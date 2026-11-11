---- MODULE M ----
EXTENDS TLCExt, Naturals, Integers, TLC, FiniteSets, Sequences
VARIABLE x
D == IF FALSE THEN TLCGet("level") ELSE <<[i \in Nat |-> i], {3, 1, 2}>>
Init == x = 0
Next == x < 3 /\ x' = x + 1
Inv == x < 2 \/ "x" \in D[2]

====
