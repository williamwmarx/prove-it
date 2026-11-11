---- MODULE M ----
EXTENDS Naturals, TLC, FiniteSets, Sequences
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
T == {<<s, t>> \in {f \in [1..2 -> {1}] : TRUE} : TRUE} # {}
VARIABLE y
D == [i \in Nat |-> x']
Init2 == x = 0 /\ y = 0
Next2 == x' = (x + 1) % 3 /\ y' = D[5]
Inv == y < 2

====
