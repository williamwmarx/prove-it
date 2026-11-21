---- MODULE M ----
EXTENDS Integers,FiniteSets,TLC
VARIABLE x,y
Init == x = {1,2} /\ y = (Cardinality({1,TRUE})=0)
Next == UNCHANGED <<x,y>>
====
