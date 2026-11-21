---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Test == PrintT([y \in 1..2 |-> (1..y) \cup {}]) /\ PrintT([y \in 1..2 |-> {} \cup (1..y)]) /\ PrintT([y \in 1..2 |-> {{z} : z \in 1..y} \cup {{}}]) /\ PrintT([y \in 1..2 |-> {{y}} \cap SUBSET {y}])
ASSUME Test
Init == x = 0
Next == x' = x
====
