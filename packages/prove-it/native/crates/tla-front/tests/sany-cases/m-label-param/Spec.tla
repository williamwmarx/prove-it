---- MODULE Spec ----
EXTENDS Naturals, TLC, Sequences, FiniteSets
VARIABLE x
E == {n \in Nat : lab:: n > 1}
D == <<{3, 1, 2}, E, E!lab>>
Init == x = 0
Next == x' = x + 1
Inv == x < 2 \/ "a" \in D[1]
====
