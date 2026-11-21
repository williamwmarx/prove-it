---- MODULE M ----
EXTENDS TLC, Integers, FiniteSets
VARIABLE x
ASSUME PrintT({1,"a"} \ {})
Init == x = 0
Next == UNCHANGED x
====
