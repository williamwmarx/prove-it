---- MODULE M ----
EXTENDS TLC, Integers, FiniteSets
CONSTANT m
VARIABLE x
ASSUME LET S == {"a"} W == {S,1..2} IN Cardinality({W,m})=2 /\ 1 \in S
Init == x = 0
Next == UNCHANGED x
====
