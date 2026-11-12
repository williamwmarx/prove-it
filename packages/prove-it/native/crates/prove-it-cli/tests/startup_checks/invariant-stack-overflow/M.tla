---- MODULE M ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
RECURSIVE R(_)
R(n) == R(n + 1)
Init == x = 0
Next == x < 2 /\ x' = x + 1
Inv == R(0) = 0
====