---- MODULE M ----
EXTENDS Naturals
VARIABLE x
RECURSIVE R(_)
R(n) == R(n + 1)
Init == x = R(0)
Next == x' = x
====
