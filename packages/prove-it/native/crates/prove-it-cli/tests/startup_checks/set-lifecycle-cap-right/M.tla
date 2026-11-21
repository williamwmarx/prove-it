---- MODULE M ----
EXTENDS TLC, Integers, FiniteSets
VARIABLE x
ASSUME PrintT(FALSE \cap {1,"a"})
Init == x = 0
Next == UNCHANGED x
====
