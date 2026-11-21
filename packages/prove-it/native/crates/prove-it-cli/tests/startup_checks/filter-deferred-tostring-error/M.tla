---- MODULE M ----
EXTENDS Integers, FiniteSets, Sequences, TLC, TLCExt
Test == LET F == {v \in SUBSET {1} : TRUE} G == {v \in SUBSET {1} : IF Cardinality(F) >= 0 THEN 1 \div 0 = 0 ELSE FALSE} IN IF Len(ToString(G)) >= 0 THEN 1 \in F ELSE FALSE
ASSUME Test
VARIABLE x
Init == x = 0
Next == x' = x
====
