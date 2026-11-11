---- MODULE M ----
EXTENDS Naturals, TLC, Sequences, FiniteSets
VARIABLE x
G(k) == x + k
Apply(F(_)) == {n \in Nat : n > F(1)}
D == <<[i \in {3, 1, 2} |-> i], Apply(G)>>
Init == x = 0
Next == x' = x + 1
Inv == x < 2
Alias == [x |-> x, d |-> IF x < 1 THEN 0 ELSE D[1]["a"]]
====
