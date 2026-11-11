---- MODULE M ----
EXTENDS Naturals, Integers, TLC, FiniteSets, Sequences
VARIABLE x
D1 == 3
Op == IF FALSE THEN x ELSE 3
D == <<[i \in Nat |-> i], {3, 1, 2}, D1>>
Init == x = 0
Next == x < 3 /\ x' = x + 1
Inv == x < 2 \/ "x" \in D[2]

====
