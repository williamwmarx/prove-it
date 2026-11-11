---- MODULE M ----
EXTENDS Naturals, TLC, Sequences, FiniteSets
VARIABLE x
G(k) == x + k
Apply(F(_), S) == {n \in S : n > F(1)}
D == <<[i \in {3, 1, 2} |-> i], Apply(G, Nat)>>

Init == x = 0
Next == x' = x + 1
Inv == x < 1 \/ D[1]["a"] = 1
====
