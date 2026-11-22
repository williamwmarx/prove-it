---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = 1 - x
F(p) == p
H == F(x = 1)
====
