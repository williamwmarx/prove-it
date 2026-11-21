---- MODULE M ----
EXTENDS Integers,TLC,FiniteSets
ASSUME PrintT(LET F == {v \in SUBSET {1} : TRUE} C == Cardinality(F) G == {v \in SUBSET {1} : C >= 0} IN IF IsFiniteSet(G) THEN 1 \in F ELSE FALSE)
VARIABLE x
Init == x=0
Next == UNCHANGED x
====
