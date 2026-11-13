---- MODULE M ----
EXTENDS Integers, FiniteSets
VARIABLE x
ASSUME Cardinality((1..65536) \X (1..65536)) = 0
Init == x = 0
Next == x' = x
====
