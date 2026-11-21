---- MODULE M ----
EXTENDS Integers,TLC
VARIABLE x
ASSUME 1 \in [a : 1 :> {1,"a"}]
Init==x=0
Next==UNCHANGED x
====
