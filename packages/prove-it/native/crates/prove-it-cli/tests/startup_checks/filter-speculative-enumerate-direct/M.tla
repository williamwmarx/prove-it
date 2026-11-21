---- MODULE M ----
EXTENDS Integers,TLC,FiniteSets
ASSUME PrintT(LET F == {v \in SUBSET {1} : TRUE} G == {v \in SUBSET {1} : Cardinality(F) >= 0} IN IF Cardinality(G) = 2 THEN 1 \in F ELSE FALSE)
VARIABLE x
Init == x=0
Next == UNCHANGED x
====
