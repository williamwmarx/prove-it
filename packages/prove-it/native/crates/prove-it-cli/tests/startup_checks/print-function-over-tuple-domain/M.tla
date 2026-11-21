---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Test == PrintT([y \in DOMAIN <<1, 2>> |-> {y}]) /\ LET f == [y \in DOMAIN <<1, 2>> |-> {y}] g == f IN PrintT(g)
ASSUME Test
Init == x = 0
Next == x' = x
====
