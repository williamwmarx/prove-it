---- MODULE M ----
EXTENDS TLC, Integers, FiniteSets
VARIABLE x
ASSUME 3 \in ({1,"a"} \X {1})
Init == x = 0
Next == UNCHANGED x
====
