---- MODULE M ----
EXTENDS Naturals
VARIABLE x
RECURSIVE R(_)
R(n) == R(n + 1)
ASSUME R(0) = 0
Init == x = 0
Next == x' = x
====
