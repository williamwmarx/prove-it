---- MODULE M ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x' = x + 1
Inv == x < 3
Bound == x < 5
====
