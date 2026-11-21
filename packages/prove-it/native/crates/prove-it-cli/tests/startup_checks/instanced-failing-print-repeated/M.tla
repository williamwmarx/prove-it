---- MODULE M ----
EXTENDS Integers, TLC
A == PrintT("a")
INSTANCE HA
B == PrintT("b")
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
====
