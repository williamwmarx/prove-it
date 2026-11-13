---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE x
D == PrintT((UNION {{1}, {2}}) \subseteq (TRUE))
ASSUME D
Init == x = 0
Next == x' = x
====
