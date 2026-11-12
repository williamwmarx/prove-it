---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE x
D == PrintT((2147483647) < (UNION {{1}, {2}}))
ASSUME D
Init == x = 0
Next == x' = x
====
