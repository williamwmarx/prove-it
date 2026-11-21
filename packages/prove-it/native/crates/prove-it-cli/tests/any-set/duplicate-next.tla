---- MODULE M ----
EXTENDS TLC, FiniteSets
VARIABLE x
Init == x = 0
Next == x' = Cardinality({Any, Any})
====
