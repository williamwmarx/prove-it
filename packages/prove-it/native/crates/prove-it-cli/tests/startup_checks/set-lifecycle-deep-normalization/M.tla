---- MODULE M ----
EXTENDS TLC, Integers, FiniteSets
VARIABLE x
ASSUME LET S == {"a"} IN Cardinality({{}, {1..2,S}})=2 /\ 1 \in S
Init == x = 0
Next == UNCHANGED x
====
