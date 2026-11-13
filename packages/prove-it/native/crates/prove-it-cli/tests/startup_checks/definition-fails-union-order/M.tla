---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE x
D == PrintT({"a"} \cap (UNION {{2}, {1}}))
ASSUME D
Init == x = 0
Next == x' = x
====
