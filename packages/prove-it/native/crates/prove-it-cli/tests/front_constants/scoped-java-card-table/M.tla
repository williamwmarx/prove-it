---- MODULE M ----
EXTENDS FiniteSets
VARIABLE x
Init == x = 0
Next == x' = x
Inv == Cardinality({1,2}) = 2
====
