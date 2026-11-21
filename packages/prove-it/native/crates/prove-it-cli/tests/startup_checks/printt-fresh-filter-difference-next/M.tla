---- MODULE M ----
EXTENDS Integers,TLC,FiniteSets
VARIABLE x
Init == x=0
Next == x<1 /\ x'=x+1 /\ PrintT(({v \in SUBSET {1} : IF v={} THEN FALSE ELSE TRUE} \ {1}))
====
