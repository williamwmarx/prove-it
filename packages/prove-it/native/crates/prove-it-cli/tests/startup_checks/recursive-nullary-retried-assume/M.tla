---- MODULE M ----
EXTENDS Integers, TLC
VARIABLE x
RECURSIVE R
R == <<R>>[1]
Test == R
ASSUME Test
Init == x = 0
Next == x' = x
====
