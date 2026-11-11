---- MODULE Spec ----
EXTENDS Naturals
CONSTANT c
VARIABLE x, y
Init == x = 0
Next == x' = x
RECURSIVE R(_)
INSTANCE Naturals
R(n) == n
====
