---- MODULE M ----
EXTENDS TLC, Integers, FiniteSets
VARIABLE x
ASSUME Permutations({1,"a"})
Init == x = 0
Next == UNCHANGED x
====
