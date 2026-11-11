---- MODULE M ----
EXTENDS Naturals, TLC, Sequences, FiniteSets
VARIABLE x
G(k) == x + k
Apply(F(_)) == {n \in Nat : n > F(1)}
Pass(H(_)) == Apply(H)
D == <<[i \in {3, 1, 2} |-> i], Pass(G)>>

Init == x = 0
Next == x' = x + 1
Inv == x < 1 \/ D[1]["a"] = 1
====
