---- MODULE M ----
EXTENDS TLC
ASSUME 1 \in Any
VARIABLE x
Init == x = 0
Next == x' = x
====
