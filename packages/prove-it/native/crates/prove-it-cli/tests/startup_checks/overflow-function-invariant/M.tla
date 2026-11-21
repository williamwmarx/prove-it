---- MODULE M ----
EXTENDS Naturals
VARIABLE x
G[n \in Nat] == G[n + 1]
Init == x = 0
Next == x < 2 /\ x' = x + 1
Inv == x < 2 \/ G[x] = 0
====
