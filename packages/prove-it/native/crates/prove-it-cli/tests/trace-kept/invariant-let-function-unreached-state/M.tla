---- MODULE M ----
EXTENDS Naturals, Integers, TLC, FiniteSets, Sequences
VARIABLE x
Op == IF FALSE THEN x ELSE 3
D == LET f == [i \in Nat |-> i] IN {f[3], f[1], Op - 1}
Init == x = 0
Next == x < 3 /\ x' = x + 1
Inv == x < 2 \/ "x" \in D

====
