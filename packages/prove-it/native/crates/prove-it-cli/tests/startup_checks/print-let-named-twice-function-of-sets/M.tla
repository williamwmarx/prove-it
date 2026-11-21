---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Test == LET f == [y \in 1..2 |-> {y}] IN LET g == f IN PrintT(g) /\ PrintT(<<g>>) /\ PrintT(f)
ASSUME Test
Init == x = 0
Next == x' = x
====
