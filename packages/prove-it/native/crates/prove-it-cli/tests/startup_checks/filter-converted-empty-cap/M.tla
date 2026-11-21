---- MODULE M ----
EXTENDS Integers,TLC,FiniteSets
ASSUME PrintT(LET F == {v \in SUBSET {1} : FALSE} IN ({1} \cap IF Cardinality(F)>=0 THEN F ELSE {}))
VARIABLE x
Init == x=0
Next == UNCHANGED x
====
