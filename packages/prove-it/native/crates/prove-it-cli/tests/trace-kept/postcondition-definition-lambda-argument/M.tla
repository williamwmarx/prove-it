---- MODULE M ----
EXTENDS Naturals, Integers, TLC, FiniteSets, Sequences
VARIABLE x
F(G(_)) == [i \in Nat |-> G(i)]
D == <<F(LAMBDA i : i + x), {3, 1, 2}>>
Init == x = 0
Next == x' = x + 1 /\ x < 3
Post == "x" \in D[2]

====
