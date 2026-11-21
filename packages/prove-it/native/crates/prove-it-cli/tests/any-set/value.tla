---- MODULE M ----
EXTENDS TLC, Naturals
VARIABLE x
Init == x = Any
Next == x' = x
====
