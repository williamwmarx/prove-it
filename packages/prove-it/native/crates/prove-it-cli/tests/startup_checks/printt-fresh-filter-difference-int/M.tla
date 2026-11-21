---- MODULE M ----
EXTENDS Integers,TLC,FiniteSets
ASSUME PrintT(({v \in SUBSET {1} : TRUE} \ {1}))
VARIABLE x
Init == x=0
Next == UNCHANGED x
====
