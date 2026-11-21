---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE x
M == "a" \in UNION {1..2, {"a"}}
Init == x = 0
Next == (M /\ x' = 1 - x) \/ (x = 1 /\ 1 = "a" /\ x' = x)
====
