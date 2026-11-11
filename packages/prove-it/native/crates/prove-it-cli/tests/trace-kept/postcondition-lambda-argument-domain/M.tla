---- MODULE M ----
EXTENDS Naturals, Integers, TLC, FiniteSets, Sequences
VARIABLE x
F(G(_)) == [i \in Nat |-> G(i)]
D == IF DOMAIN F(LAMBDA i : i + x) = Nat THEN {3, 1, 2} ELSE {}
Init == x = 0
Next == x' = x + 1 /\ x < 3
Post == "x" \in D

====
