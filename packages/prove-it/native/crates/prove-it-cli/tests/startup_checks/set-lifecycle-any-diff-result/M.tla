---- MODULE M ----
EXTENDS TLC, Integers, FiniteSets
VARIABLE x
ASSUME Cardinality({Any,Any} \ {}) = 1
Init == x = 0
Next == UNCHANGED x
====
