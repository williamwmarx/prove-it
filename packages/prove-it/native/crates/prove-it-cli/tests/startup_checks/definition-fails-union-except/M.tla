---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE x
D == PrintT([UNION {{1}, {2}} EXCEPT ![1] = 9])
ASSUME D
Init == x = 0
Next == x' = x
====
