---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
RECURSIVE R
R == R
Test == R /\ PrintT(1)
Init == x = 0
Next == x' = x
Inv == Test
====
