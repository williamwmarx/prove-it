---- MODULE M ----
EXTENDS TLC, Integers, FiniteSets
VARIABLE x
ASSUME PrintT({1,"a"} \cup (1..2))
Init == x = 0
Next == UNCHANGED x
====
