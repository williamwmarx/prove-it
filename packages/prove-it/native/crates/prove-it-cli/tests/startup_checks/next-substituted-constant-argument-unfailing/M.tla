---- MODULE M ----
EXTENDS Naturals, TLC, Randomization, Sequences
VARIABLE x
CONSTANT C(_)
Init == x = 0
Op(a) == x' = (x + 1) % 3
Next == C([n \in Nat |-> n][3]) \/ C(LET f[n \in Nat] == n IN f[2])
====
