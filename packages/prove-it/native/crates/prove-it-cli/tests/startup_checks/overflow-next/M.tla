---- MODULE M ----
EXTENDS Naturals
VARIABLE x
RECURSIVE R(_)
R(n) == R(n + 1)
Init == x = 0
Next == x' = R(0)
====
