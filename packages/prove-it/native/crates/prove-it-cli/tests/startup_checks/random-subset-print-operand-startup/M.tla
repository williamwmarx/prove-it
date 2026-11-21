---- MODULE M ----
EXTENDS Integers, TLC, Randomization
VARIABLE x
Test == PrintT(RandomSubset(1, {Print(1, 1), 2}))
ASSUME Test
Init == x = 0
Next == x' = x
====
