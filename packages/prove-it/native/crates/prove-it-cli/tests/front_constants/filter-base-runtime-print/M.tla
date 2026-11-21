---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
Bad == IF PrintT(x) THEN Cardinality({y \in {z \in <<x>> : TRUE} : TRUE}) = 0 ELSE TRUE
Init == x = 1
Next == x' = x /\ Bad
====
