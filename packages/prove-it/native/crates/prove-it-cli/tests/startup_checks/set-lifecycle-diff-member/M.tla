---- MODULE M ----
EXTENDS TLC, Integers, FiniteSets
VARIABLE x
ASSUME PrintT({1,"a"} \ {1})
Init == x = 0
Next == UNCHANGED x
====
