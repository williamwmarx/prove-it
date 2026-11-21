---- MODULE M ----
EXTENDS TLC,Integers,FiniteSets,TLCExt
VARIABLE x
ASSUME PrintT("before") /\ 3 \in [Int -> {1,"a"}]
Init==x=0
Next==UNCHANGED x
====
