---- MODULE M ----
EXTENDS TLC, Integers, FiniteSets
VARIABLE x
ASSUME -1 \in Nat \cup [a : {1,"a"}]
Init == x = 0
Next == UNCHANGED x
====
