---- MODULE M ----
EXTENDS Randomization, TLC
VARIABLE x
ASSUME PrintT(RandomSubset(2, {1, 2, 3}))
Init == x = 0
Next == x' = x
====
