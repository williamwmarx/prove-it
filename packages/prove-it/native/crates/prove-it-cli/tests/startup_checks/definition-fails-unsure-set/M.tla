---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE x
D == PrintT((SetToBag({1})) \cap (3..1))
ASSUME D
Init == x = 0
Next == x' = x
====
