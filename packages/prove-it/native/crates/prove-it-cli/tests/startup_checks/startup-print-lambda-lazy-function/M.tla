---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE x
ASSUME PrintT([n \in Nat |-> SortSeq(<<2, 1>>, LAMBDA p, q : p < q)])
Init == x = 0
Next == UNCHANGED x
====
