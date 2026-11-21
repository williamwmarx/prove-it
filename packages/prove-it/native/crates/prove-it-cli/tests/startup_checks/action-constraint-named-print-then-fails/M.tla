---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC, Randomization
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
Inv == PrintT(1) /\ <<1>>[2] = 1
====
