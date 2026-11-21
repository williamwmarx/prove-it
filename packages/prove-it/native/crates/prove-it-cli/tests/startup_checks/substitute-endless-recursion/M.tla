---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC, Randomization
CONSTANT C
RECURSIVE R(_)
R(n) == R(n + 1) + 1
D == R(0)
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
====
