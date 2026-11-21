---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Test == PrintT([k \in DOMAIN (<<1, 2>> \o <<3>>) |-> {k}]) /\ PrintT([k \in DOMAIN [i \in 1..2 |-> i] |-> {k}]) /\ PrintT([k \in DOMAIN (2 :> 3) |-> {k}])
ASSUME Test
Init == x = 0
Next == x' = x
====
