---- MODULE M ----
EXTENDS TLC
VARIABLE x
Init == x = 0
Next == x' = x
Inv == x = 0
====
