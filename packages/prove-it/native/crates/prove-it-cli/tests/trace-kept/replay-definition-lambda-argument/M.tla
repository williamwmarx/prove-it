---- MODULE M ----
EXTENDS Naturals, Integers, TLC, FiniteSets, Sequences
VARIABLE x
F(G(_)) == [i \in Nat |-> G(i)]
D == <<F(LAMBDA i : i + x), Cardinality({s \in SUBSET (1..13) : Cardinality(s) > 3}), {n \in Nat : n > 5}>>
Init == x = 0
Next == x' = x + 1
Inv == x < 2 \/ ((\A k \in 1..100 : D[2] > k /\ 7 \in D[3]) /\ "x" = 1)

====
