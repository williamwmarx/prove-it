---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC, Randomization
CONSTANT C
F[n \in Nat] == F[n + 1]
D == F[0]
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
====
