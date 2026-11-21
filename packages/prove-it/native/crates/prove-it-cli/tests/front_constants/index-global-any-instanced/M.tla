---- MODULE M ----
EXTENDS N, TLC
ASSUME F
VARIABLE x
Init == x = 0
Next == x' = x
====
