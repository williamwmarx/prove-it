---- MODULE M ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 2
F(p) == x = 0
H == F(x')
P == H
====
