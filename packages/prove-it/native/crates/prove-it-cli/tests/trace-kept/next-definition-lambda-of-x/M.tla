---- MODULE M ----
EXTENDS Naturals, Integers, TLC, FiniteSets, Sequences
VARIABLE x
D == [i \in Nat |-> x' + i]
Init == x = 0
Next == \E k \in {1, 2} : x' = x + k /\ D[0] = x + k
Inv == x < 4

====
