---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, Bags, TLC
VARIABLE x
Member == "a" \in UNION {1..2, {"a"}}
Init == x = 0
Next == x' = 1 - x
Inv == x \in {0, 1} /\ Member
====
