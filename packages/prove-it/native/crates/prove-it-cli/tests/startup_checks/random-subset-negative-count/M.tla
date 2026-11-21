---- MODULE M ----
EXTENDS Randomization, FiniteSets, Integers
VARIABLE x
Init == x = RandomSubset(-1, 1..3)
Next == UNCHANGED x
====
