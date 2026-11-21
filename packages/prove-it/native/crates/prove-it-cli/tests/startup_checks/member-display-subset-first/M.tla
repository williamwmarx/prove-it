---- MODULE M ----
EXTENDS TLC,Integers,FiniteSets,TLCExt
VARIABLE x
ASSUME PrintT("before") /\ 3 \in [SUBSET Nat -> {1,"a"}]
Init==x=0
Next==UNCHANGED x
====
