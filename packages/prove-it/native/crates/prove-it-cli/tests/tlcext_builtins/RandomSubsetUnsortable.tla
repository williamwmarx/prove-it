---- MODULE RandomSubsetUnsortable ----
EXTENDS Naturals, TLC, Randomization
VARIABLE x
Init == x = 0
Next == x' = x
ASSUME RandomSubset(1, {1, "a"}) = {}
====
