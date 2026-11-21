---- MODULE M ----
EXTENDS TLC, Integers, FiniteSets
VARIABLE x
ASSUME 3 \in [{1} -> {1,"a"}]
Init == x = 0
Next == UNCHANGED x
====
