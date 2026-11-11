---- MODULE M ----
EXTENDS Naturals, Integers, TLC, FiniteSets, Sequences
VARIABLE x
Op == IF FALSE THEN x ELSE 3
D == <<{n \in Nat : n > 5}, {3, 1, 2}, Op>>
Init == x = 0
Next == x' = x + 1
Inv == x < 2 \/ "x" \in D[2]

====
