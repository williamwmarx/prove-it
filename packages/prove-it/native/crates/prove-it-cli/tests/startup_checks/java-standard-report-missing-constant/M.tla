---- MODULE M ----
EXTENDS TLC
CONSTANT C
VARIABLE x
Init == x = 0
Next == x' = x
====
