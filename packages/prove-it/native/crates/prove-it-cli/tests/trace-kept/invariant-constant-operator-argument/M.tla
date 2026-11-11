---- MODULE M ----
EXTENDS Naturals, TLC, Sequences, FiniteSets
VARIABLE x
CONSTANT Op(_)
G(k) == x + k
Apply(F(_)) == {n \in Nat : n > F(1)}
D == <<[i \in {3, 1, 2} |-> i], Apply(Op)>>

Init == x = 0
Next == x' = x + 1
Inv == x < 1 \/ D[1]["a"] = 1
====
