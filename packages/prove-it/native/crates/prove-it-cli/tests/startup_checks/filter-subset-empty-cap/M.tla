---- MODULE M ----
EXTENDS Integers,TLC,FiniteSets
ASSUME PrintT(({v \in SUBSET {1} : FALSE} \cap {}))
VARIABLE x
Init == x=0
Next == UNCHANGED x
====
