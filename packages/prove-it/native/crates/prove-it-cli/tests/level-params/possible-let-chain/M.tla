---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 2
F(p) == LET A == p  B == A IN B
H == F(x' = 1)
====
