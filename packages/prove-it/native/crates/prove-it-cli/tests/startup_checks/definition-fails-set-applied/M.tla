---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE x
D == PrintT(({b \in {1, 2} : TRUE})[(<<5, 6>>)[-1]])
ASSUME D
Init == x = 0
Next == x' = x
====
