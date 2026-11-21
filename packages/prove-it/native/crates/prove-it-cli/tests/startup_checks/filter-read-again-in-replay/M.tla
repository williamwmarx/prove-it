---- MODULE M ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
VARIABLE x
Test == LET F == {v \in SUBSET {1} : TRUE} IN IF TRUE THEN LET G == {v \in SUBSET {1} : Cardinality(F) >= 0} IN IF Cardinality(G) >= 0 THEN 1 \in F ELSE FALSE ELSE FALSE
Init == x = Test
Next == UNCHANGED x
====
