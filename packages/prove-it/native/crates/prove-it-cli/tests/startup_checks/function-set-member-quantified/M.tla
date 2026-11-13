---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Init == x = \E f \in {<<1>>, <<2, 3>>} : f \in [Nat -> Nat]
Next == x' = x
====
