---- MODULE M ----
EXTENDS Naturals, Integers, TLC, FiniteSets, Sequences
CONSTANT C(_)
VARIABLE x
Op(i) == i + x
D == [i \in Nat |-> C(i)]
Init == x = 0
Next == x' = x + 1
Inv == x < 3
Alias == [x |-> x, e |-> x', d |-> D[2]]

====
